// An in-memory stand-in for RTCPeerConnection / RTCDataChannel, enough for the transport's unit
// tests (app/js/transport/webrtc.mjs). Two connections pair when the offerer applies an answer
// whose ICE ufrag names the other one. Behaviour modelled on what the probe measured
// (docs/net-design.md §1.4): a closed channel closes on both sides; pc.close() closes the other
// side's channels; vanish() leaves the other side's channels `open` and only moves its connection
// state to `disconnected`, then `failed` (Chromium).

const tick = () => new Promise((r) => setTimeout(r, 0));

export function fakeRTC({ connectDelay = 1 } = {}) {
  const byUfrag = new Map();
  const world = { pcs: [], reachable: () => true };
  let n = 0;

  class FakeDC extends EventTarget {
    constructor(pc, label, opts = {}) {
      super();
      Object.assign(this, { pc, label, id: opts.id ?? null, negotiated: !!opts.negotiated, readyState: 'connecting',
        bufferedAmount: 0, bufferedAmountLowThreshold: 0, binaryType: 'blob', peer: null, sent: [], failSend: null, hold: false });
    }
    send(d) {
      if (this.readyState !== 'open') throw new DOMException('not open', 'InvalidStateError');
      if (this.failSend) throw this.failSend;
      this.sent.push(d);
      const p = this.peer;
      if (this.hold) { this.bufferedAmount += d.length ?? d.byteLength ?? 0; return; }
      if (p) setTimeout(() => { if (p.readyState === 'open') p._fire('message', { data: typeof d === 'string' ? d : d.slice().buffer }); }, 0);
    }
    /** Back-pressure: release the held bytes and fire bufferedamountlow. */
    drain() { this.hold = false; this.bufferedAmount = 0; this._fire('bufferedamountlow', {}); }
    close() { if (this.readyState === 'closed' || this.readyState === 'closing') return; for (const d of [this, this.peer]) if (d) d._closed(); }
    _closed() { if (this.readyState === 'closed') return; this.readyState = 'closed'; setTimeout(() => this._fire('close', {}), 0); }
    _open() { if (this.readyState !== 'connecting') return; this.readyState = 'open'; setTimeout(() => this._fire('open', {}), 0); }
    _fire(type, props) { const e = Object.assign(new Event(type), props); this[`on${type}`]?.(e); this.dispatchEvent(e); }
  }

  class FakePC extends EventTarget {
    constructor(cfg = {}) {
      super();
      this.cfg = cfg; this.n = ++n; this.ufrag = `uf${n}`;
      Object.assign(this, { connectionState: 'new', iceGatheringState: 'new', localDescription: null, remoteDescription: null, chans: [], peer: null, closedHere: false });
      world.pcs.push(this);
    }
    _sdp(type, setup) {
      const fp = Array.from({ length: 32 }, (_, i) => ((i * 7 + this.n) & 255).toString(16).padStart(2, '0').toUpperCase()).join(':');
      const lines = ['v=0', 'o=- 1 2 IN IP4 127.0.0.1', 's=-', 't=0 0', 'a=group:BUNDLE 0', 'm=application 9 UDP/DTLS/SCTP webrtc-datachannel', 'c=IN IP4 0.0.0.0',
        `a=ice-ufrag:${this.ufrag}`, `a=ice-pwd:${'p'.repeat(22)}${String(this.n).padStart(2, '0')}`, `a=fingerprint:sha-256 ${fp}`, `a=setup:${setup}`, 'a=mid:0', 'a=sctp-port:5000',
        `a=candidate:1 1 udp 2113937151 192.0.2.${this.n % 250} ${10000 + this.n} typ host`];
      if ((this.cfg.iceServers ?? []).length) lines.push(`a=candidate:2 1 udp 1677729535 203.0.113.${this.n % 250} ${20000 + this.n} typ srflx raddr 0.0.0.0 rport 0`);
      return { type, sdp: lines.join('\r\n') + '\r\n' };
    }
    createDataChannel(label, opts) {
      if (this.closedHere) throw new DOMException('closed', 'InvalidStateError');
      const d = new FakeDC(this, label, opts);
      this.chans.push(d);
      if (!d.negotiated && this.connectionState === 'connected' && this.peer) setTimeout(() => world.link(this, d), 0);
      return d;
    }
    async createOffer() { return this._sdp('offer', 'actpass'); }
    async createAnswer() { return this._sdp('answer', 'active'); }
    async setLocalDescription(d) {
      this.localDescription = d ?? (this.remoteDescription ? await this.createAnswer() : await this.createOffer());
      byUfrag.set(this.ufrag, this);
      this.iceGatheringState = 'complete';
      setTimeout(() => this._fire('icegatheringstatechange', {}), 0);
    }
    async setRemoteDescription(d) {
      if (!/a=ice-ufrag:/.test(d.sdp) || !/a=fingerprint:sha-256 /.test(d.sdp)) throw new DOMException('bad sdp', 'InvalidAccessError');
      this.remoteDescription = d;
      if (d.type === 'answer') {
        if (!/a=setup:passive/.test(d.sdp)) world.activeAnswers = (world.activeAnswers ?? 0) + 1;
        const other = byUfrag.get(/a=ice-ufrag:(\S+)/.exec(d.sdp)[1]);
        if (other && !other.closedHere && world.reachable(this, other)) setTimeout(() => world.connect(this, other), connectDelay);
      }
    }
    close() {
      if (this.closedHere) return;
      this.closedHere = true; this.connectionState = 'closed';      // no event on the side that closed (spec)
      for (const d of this.chans) d.close();
    }
    /** The device vanished (browser killed): the peer's channels stay open, its state goes disconnected → failed. */
    vanish() {
      const p = this.peer; this.closedHere = true; this.connectionState = 'closed';
      for (const d of this.chans) { d.readyState = 'closed'; if (d.peer) d.peer.peer = null; }
      if (p) { p._state('disconnected'); world.later = () => p._state('failed'); }
    }
    _state(s) { if (this.closedHere) return; this.connectionState = s; this._fire('connectionstatechange', {}); }
    _fire(type, props) { const e = Object.assign(new Event(type), props); this[`on${type}`]?.(e); this.dispatchEvent(e); }
  }

  world.connect = (a, b) => {
    if (a.closedHere || b.closedHere) return;
    a.peer = b; b.peer = a;
    a._state('connected'); b._state('connected');
    for (const d of a.chans) {
      if (d.negotiated) { const m = b.chans.find((x) => x.negotiated && x.id === d.id && !x.peer); if (m) { d.peer = m; m.peer = d; d._open(); m._open(); } }
      else if (!d.peer) world.link(a, d);
    }
  };
  world.link = (pc, d) => {
    const p = pc.peer; if (!p || p.closedHere || d.peer) return;
    const cp = new FakeDC(p, d.label); cp.peer = d; d.peer = cp; p.chans.push(cp);
    p._fire('datachannel', { channel: cp });
    d._open(); cp._open();
  };
  world.RTC = FakePC;
  world.tick = tick;
  return world;
}
