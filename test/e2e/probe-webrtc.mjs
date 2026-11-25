// Feasibility probe for the WebRTC transport (docs/net-design.md). Throwaway: not part of the
// app or of scripts/test-app.sh. Each device is a separate headless browser process and profile;
// the offer and answer are passed by this driver, non-trickle (ICE gathering awaited).
//
//   node test/e2e/probe-webrtc.mjs [--phase connect|life|qr|cert|all] [--configs a,b] [--json file]
//   unshare -rn sh -c 'ip link set lo up && node test/e2e/probe-webrtc.mjs --netns'   (loopback only)
//   unshare -rn sh -c 'ip link set lo up && ip link add d0 type dummy && ip addr add 10.99.0.1/24 dev d0 &&
//     ip link set d0 up && ip route add default dev d0 && node test/e2e/probe-webrtc.mjs --netns ...'  (dummy NIC)
//
// Phase "connect": per configuration (mDNS on/off, loopback, STUN: none / fake local / Google /
//   unreachable) and browser pairing: candidates gathered, gathering time, connection with the
//   full SDP and with an SDP rebuilt from the minimal code, the selected pair, code sizes.
// Phase "life": message-size limits, back-pressure, throughput with the links.mjs scheme,
//   a second channel on the same connection, and what the other side sees on dc.close(),
//   pc.close(), tab close and SIGKILL of the browser.
// Phase "qr": BarcodeDetector availability. Phase "cert": persistent RTCCertificate in IndexedDB.
import { createServer } from 'node:http';
import { createSocket } from 'node:dgram';
import { createHash } from 'node:crypto';
import { writeFileSync } from 'node:fs';
import { launch, hasBrowser, browserVersion } from './driver.mjs';
import { cleanupAll, reportCleanup } from '../proc.mjs';

const args = process.argv.slice(2);
const opt = (n, d) => { const i = args.indexOf(n); return i >= 0 ? args[i + 1] : d; };
const NETNS = args.includes('--netns');
const PHASE = opt('--phase', 'all');
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const withTimeout = (p, ms, what) => Promise.race([p, new Promise((_, j) => setTimeout(() => j(new Error(`timeout ${ms} ms: ${what}`)), ms))]);

// ------------------------------------------------------------------ page helpers (run in the browser)
const PAGE = `<!doctype html><meta charset=utf-8><title>webrtc probe</title><script>
const P = window.P = { st: {}, n: 0,
  gathered(pc, ms) { return new Promise((res) => { if (pc.iceGatheringState === 'complete') return res(true);
    const t = setTimeout(() => res(false), ms);
    pc.addEventListener('icegatheringstatechange', () => { if (pc.iceGatheringState === 'complete') { clearTimeout(t); res(true); } }); }); },
  make(cfg) {
    const id = ++P.n, pc = new RTCPeerConnection(cfg);
    const s = P.st[id] = { id, pc, ev: [], cands: [], candMs: [], t0: performance.now(), dc: null, chans: [], txSeq: -1, rx: { n: 0, bytes: 0, sizes: [], seqOk: true, next: 0, first: 0, last: 0 } };
    s.log = (k, v) => s.ev.push([Date.now(), k, v]);
    pc.onconnectionstatechange = () => s.log('conn', pc.connectionState);
    pc.oniceconnectionstatechange = () => s.log('ice', pc.iceConnectionState);
    pc.onicecandidate = (e) => { if (e.candidate && e.candidate.candidate) { s.cands.push(e.candidate.candidate); s.candMs.push(Math.round(performance.now() - s.t0)); } };
    pc.ondatachannel = (e) => P.wire(s, e.channel);
    return s;
  },
  wire(s, dc) {
    s.dc = dc; s.chans.push(dc); dc.binaryType = 'arraybuffer'; dc.bufferedAmountLowThreshold = 256 * 1024;
    dc.onopen = () => s.log('open', dc.label); dc.onclose = () => s.log('close', dc.label);
    dc.onerror = (e) => s.log('error', dc.label + ': ' + String(e.error?.message ?? e.error ?? e));
    dc.onmessage = (e) => { const r = s.rx, n = e.data.byteLength; r.n++; r.bytes += n; if (!r.first) r.first = Date.now(); r.last = Date.now();
      if (r.sizes.length < 40) r.sizes.push(n);
      if (n >= 4) { const q = new DataView(e.data).getUint32(0, true); if (q !== r.next) r.seqOk = false; r.next = q + 1; } };
  },
  info(s) { return { id: s.id, sdp: s.pc.localDescription.sdp, cands: s.cands, candMs: s.candMs, gatherMs: s.gatherMs, gatherDone: s.gatherDone }; },
  async offer(cfg, ms) { const s = P.make(cfg); P.wire(s, s.pc.createDataChannel('sync')); const t0 = performance.now();
    await s.pc.setLocalDescription(); s.gatherDone = await P.gathered(s.pc, ms); s.gatherMs = Math.round(performance.now() - t0); return P.info(s); },
  async answer(cfg, sdp, ms, passive) { const s = P.make(cfg); await s.pc.setRemoteDescription({ type: 'offer', sdp }); const t0 = performance.now();
    if (passive) { const a = await s.pc.createAnswer(); await s.pc.setLocalDescription({ type: 'answer', sdp: a.sdp.replace(/a=setup:active/g, 'a=setup:passive') }); }
    else await s.pc.setLocalDescription(); s.gatherDone = await P.gathered(s.pc, ms); s.gatherMs = Math.round(performance.now() - t0); return P.info(s); },
  async accept(id, sdp) { await P.st[id].pc.setRemoteDescription({ type: 'answer', sdp }); return Date.now(); },
  state(id) { const s = P.st[id]; return { conn: s.pc.connectionState, ice: s.pc.iceConnectionState, dc: s.dc?.readyState ?? null,
    ev: s.ev, rx: s.rx, maxMsg: s.pc.sctp?.maxMessageSize ?? null, buffered: s.dc?.bufferedAmount ?? null, chans: s.chans.map((c) => c.label + ':' + c.readyState) }; },
  async pair(id) {
    const st = await P.st[id].pc.getStats(); const by = new Map(); let pair = null;
    st.forEach((r) => by.set(r.id, r));
    st.forEach((r) => { if (r.type === 'transport' && r.selectedCandidatePairId) pair = by.get(r.selectedCandidatePairId); });
    if (!pair) st.forEach((r) => { if (r.type === 'candidate-pair' && r.selected) pair = r; });
    if (!pair) st.forEach((r) => { if (r.type === 'candidate-pair' && r.nominated && r.state === 'succeeded') pair = r; });
    if (!pair) return null;
    const f = (c) => c && (c.candidateType + ' ' + (c.address ?? c.ip) + ':' + c.port);
    return { local: f(by.get(pair.localCandidateId)), remote: f(by.get(pair.remoteCandidateId)) };
  },
  seq(s, b) { new DataView(b.buffer).setUint32(0, ++s.txSeq, true); return b; },
  sizes(id, list) { const s = P.st[id], out = [];
    for (const n of list) { try { s.dc.send(P.seq(s, new Uint8Array(n))); out.push([n, 'ok']); } catch (e) { s.txSeq--; out.push([n, e.name + ': ' + e.message]); } }
    return { out, state: s.dc.readyState }; },
  async stream(id, total, frame, high) { const s = P.st[id], dc = s.dc; let sent = 0, maxBuf = 0, drains = 0;
    const start = Date.now(), base = new Uint8Array(frame); crypto.getRandomValues(base.subarray(0, Math.min(frame, 65536)));
    while (sent < total) {
      while (dc.bufferedAmount < high && sent < total) { const b = P.seq(s, base.slice(0, Math.min(frame, total - sent))); dc.send(b); sent += b.length; maxBuf = Math.max(maxBuf, dc.bufferedAmount); }
      if (sent < total) { await new Promise((r) => dc.addEventListener('bufferedamountlow', r, { once: true })); drains++; }
    }
    return { sent, start, maxBuf, drains }; },
  overflow(id, frame, cap) { const s = P.st[id], dc = s.dc; let sent = 0, err = null, at = null;
    try { while (sent < cap) { dc.send(P.seq(s, new Uint8Array(frame))); sent += frame; } } catch (e) { s.txSeq--; err = e.name + ': ' + e.message; at = dc.bufferedAmount; }
    return { sent, bufferedAtError: at, buffered: dc.bufferedAmount, err, state: dc.readyState }; },
  newChannel(id, label) { const s = P.st[id]; P.wire(s, s.pc.createDataChannel(label)); return true; },
  dcClose(id) { const t = Date.now(); P.st[id].dc.close(); return t; },
  pcClose(id) { const t = Date.now(); P.st[id].pc.close(); return t; },
};
</script><p>probe`;

// ------------------------------------------------------------------ minimal code: extract, encode, rebuild
function extract(sdp) {
  const L = sdp.split(/\r?\n/);
  const get = (re) => { for (const l of L) { const m = l.match(re); if (m) return m[1].trim(); } return null; };
  const cands = [];
  for (const l of L) {
    if (!l.startsWith('a=candidate:')) continue;
    const f = l.slice(12).split(' ');
    const c = { component: +f[1], proto: f[2].toLowerCase(), addr: f[4], port: +f[5], type: f[7] };
    if (c.component === 1 && c.proto === 'udp') cands.push(c);
  }
  return { ufrag: get(/^a=ice-ufrag:(.+)$/), pwd: get(/^a=ice-pwd:(.+)$/), fp: get(/^a=fingerprint:sha-256 (.+)$/i),
    setup: get(/^a=setup:(.+)$/), mid: get(/^a=mid:(.+)$/), mms: get(/^a=max-message-size:(\d+)/), cands };
}
const TYPES = ['host', 'srflx', 'prflx', 'relay'];
const crc32 = (b) => { let c = ~0; for (const x of b) { c ^= x; for (let k = 0; k < 8; k++) c = (c >>> 1) ^ (0xedb88320 & -(c & 1)); } return ~c >>> 0; };
function ipv6Bytes(a) {
  const [h, t = ''] = a.split('::'); const hs = h ? h.split(':') : [], ts = t ? t.split(':') : [];
  const parts = a.includes('::') ? [...hs, ...Array(8 - hs.length - ts.length).fill('0'), ...ts] : hs;
  return parts.flatMap((p) => { const v = parseInt(p || '0', 16); return [v >> 8, v & 255]; });
}
// Proposed binary layout (version 1), see docs/net-design.md §4:
//   u8 (version<<4 | kind)  [answer: 4-byte offer tag, u8 flags(bit0: setup active)]
//   u8 len + ufrag  u8 len + pwd  32 B fingerprint  u8 n  n × candidate  4 B CRC-32
//   candidate: u8 (type | addrKind<<2), addr (IPv4 4 / IPv6 16 / mDNS UUID 16 / u8 len + name), u16 port
function encode(x, kind, offerTag) {
  const out = [(1 << 4) | (kind === 'offer' ? 1 : 2)];
  if (kind === 'answer') { out.push(...offerTag, x.setup === 'active' ? 1 : 0); }
  for (const s of [x.ufrag, x.pwd]) { const b = Buffer.from(s, 'ascii'); out.push(b.length, ...b); }
  out.push(...x.fp.split(':').map((h) => parseInt(h, 16)));
  out.push(x.cands.length);
  for (const c of x.cands) {
    const t = TYPES.indexOf(c.type);
    let kindA, addr;
    if (/^\d+\.\d+\.\d+\.\d+$/.test(c.addr)) { kindA = 0; addr = c.addr.split('.').map(Number); }
    else if (c.addr.includes(':')) { kindA = 1; addr = ipv6Bytes(c.addr); }
    else if (/^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}\.local$/i.test(c.addr)) { kindA = 2; addr = [...Buffer.from(c.addr.slice(0, 36).replace(/-/g, ''), 'hex')]; }
    else { kindA = 3; const b = Buffer.from(c.addr); addr = [b.length, ...b]; }
    out.push(t | (kindA << 2), ...addr, c.port >> 8, c.port & 255);
  }
  const crc = crc32(out); out.push(crc >>> 24, (crc >>> 16) & 255, (crc >>> 8) & 255, crc & 255);
  return Uint8Array.from(out);
}
function decode(b) {
  if (b.length < 5 || crc32(b.subarray(0, b.length - 4)) !== Buffer.from(b.subarray(b.length - 4)).readUInt32BE(0)) throw new Error('bad check');
  let o = 0; const v = b[o++]; const kind = (v & 15) === 1 ? 'offer' : 'answer'; const x = { kind };
  if (kind === 'answer') { x.offerTag = [...b.subarray(o, o + 4)]; o += 4; x.setup = b[o++] & 1 ? 'active' : 'passive'; } else x.setup = 'actpass';
  const str = () => { const n = b[o++]; const s = Buffer.from(b.subarray(o, o + n)).toString('ascii'); o += n; return s; };
  x.ufrag = str(); x.pwd = str();
  x.fp = [...b.subarray(o, o + 32)].map((y) => y.toString(16).padStart(2, '0').toUpperCase()).join(':'); o += 32;
  const n = b[o++]; x.cands = [];
  for (let i = 0; i < n; i++) {
    const h = b[o++], type = TYPES[h & 3], k = h >> 2; let addr;
    if (k === 0) { addr = [...b.subarray(o, o + 4)].join('.'); o += 4; }
    else if (k === 1) { const s = []; for (let j = 0; j < 16; j += 2) s.push(((b[o + j] << 8) | b[o + j + 1]).toString(16)); addr = s.join(':'); o += 16; }
    else if (k === 2) { const hx = Buffer.from(b.subarray(o, o + 16)).toString('hex'); addr = `${hx.slice(0, 8)}-${hx.slice(8, 12)}-${hx.slice(12, 16)}-${hx.slice(16, 20)}-${hx.slice(20)}.local`; o += 16; }
    else { const m = b[o++]; addr = Buffer.from(b.subarray(o, o + m)).toString(); o += m; }
    x.cands.push({ type, addr, port: (b[o] << 8) | b[o + 1] }); o += 2;
  }
  if (o !== b.length - 4) throw new Error('length');
  return x;
}
function rebuild(x, type, mid, endOfCands = true) {
  const L = ['v=0', 'o=- 1 2 IN IP4 127.0.0.1', 's=-', 't=0 0', `a=group:BUNDLE ${mid}`,
    'm=application 9 UDP/DTLS/SCTP webrtc-datachannel', 'c=IN IP4 0.0.0.0', `a=mid:${mid}`,
    `a=ice-ufrag:${x.ufrag}`, `a=ice-pwd:${x.pwd}`, `a=fingerprint:sha-256 ${x.fp}`, `a=setup:${type === 'offer' ? 'actpass' : x.setup}`,
    'a=sctp-port:5000', 'a=max-message-size:262144'];
  x.cands.forEach((c, i) => {
    const tp = { host: 126, srflx: 100, prflx: 110, relay: 0 }[c.type];
    const prio = tp * 2 ** 24 + (65535 - i) * 2 ** 8 + 255;
    L.push(`a=candidate:${i + 1} 1 udp ${prio} ${c.addr} ${c.port} typ ${c.type}${c.type === 'host' ? '' : ' raddr 0.0.0.0 rport 0'}`);
  });
  if (endOfCands) L.push('a=end-of-candidates');
  return L.join('\r\n') + '\r\n';
}
// RFC 9285 base45 and QR versions (ISO/IEC 18004 capacity tables, versions 1-20)
const B45 = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ $%*+-./:';
function base45(b) { let s = ''; for (let i = 0; i < b.length; i += 2) {
  if (i + 1 < b.length) { let n = b[i] * 256 + b[i + 1]; const c = n % 45; n = (n - c) / 45; const d = n % 45; s += B45[c] + B45[d] + B45[(n - d) / 45]; }
  else { const n = b[i]; s += B45[n % 45] + B45[Math.floor(n / 45)]; } } return s; }
const CAP = { // [alnum L, alnum M, byte L, byte M]
  1: [25, 20, 17, 14], 2: [47, 38, 32, 26], 3: [77, 61, 53, 42], 4: [114, 90, 78, 62], 5: [154, 122, 106, 84],
  6: [195, 154, 134, 106], 7: [224, 178, 154, 122], 8: [279, 221, 192, 152], 9: [335, 262, 230, 180], 10: [395, 311, 271, 213],
  11: [468, 366, 321, 251], 12: [535, 419, 367, 287], 13: [619, 483, 425, 331], 14: [667, 528, 458, 362], 15: [758, 600, 520, 412],
  16: [854, 656, 586, 450], 17: [938, 734, 644, 504], 18: [1046, 816, 718, 560], 19: [1153, 909, 792, 624], 20: [1249, 970, 858, 666],
  25: [1853, 1451, 1273, 997], 30: [2520, 1994, 1732, 1370], 40: [4296, 3391, 2953, 2331] };
const qrVersion = (n, col) => { for (const [v, c] of Object.entries(CAP)) if (n <= c[col]) return `v${v} (${17 + 4 * v}×${17 + 4 * v})`; return 'too big'; };
function sizes(sdp, code) {
  const b45 = base45(code), b64 = Buffer.from(code).toString('base64url');
  return { sdpBytes: sdp.length, sdpQrByteM: qrVersion(sdp.length, 3), codeBytes: code.length, base45: b45.length,
    qrAlnumM: qrVersion(b45.length, 1), qrAlnumL: qrVersion(b45.length, 0), base64url: b64.length, qrByteM_b64: qrVersion(b64.length, 3) };
}

// ------------------------------------------------------------------ fake STUN server (local, no internet)
// Answers Binding requests with a made-up public address (203.0.113.x, TEST-NET-3) so the browsers
// produce srflx candidates of a realistic shape; used only to measure code sizes and SDP acceptance.
function fakeStun() {
  const s = createSocket('udp4');
  s.on('message', (m, r) => {
    if (m.length < 20 || m.readUInt16BE(0) !== 0x0001) return;
    const res = Buffer.alloc(32); res.writeUInt16BE(0x0101, 0); res.writeUInt16BE(12, 2); m.copy(res, 4, 4, 20);
    res.writeUInt16BE(0x0020, 20); res.writeUInt16BE(8, 22); res.writeUInt8(0, 24); res.writeUInt8(1, 25);
    res.writeUInt16BE(r.port ^ 0x2112, 26); res.writeUInt32BE((((203 << 24) | (0 << 16) | (113 << 8) | 7) ^ 0x2112A442) >>> 0, 28);
    s.send(res, r.port, r.address);
  });
  return new Promise((res) => s.bind(0, '127.0.0.1', () => res({ port: s.address().port, close: () => s.close() })));
}

// ------------------------------------------------------------------ browsers
const http = createServer((req, res) => { res.writeHead(200, { 'content-type': 'text/html' }); res.end(PAGE); });
await new Promise((r) => http.listen(0, '127.0.0.1', r));
const origin = `http://127.0.0.1:${http.address().port}/`;
const KINDS = ['chromium', 'firefox', 'firefox-esr'].filter(hasBrowser);
const short = { chromium: 'C', firefox: 'F', 'firefox-esr': 'E' };
const ver = Object.fromEntries(KINDS.map((k) => [k, browserVersion(k)]));
const CONFIGS = {
  default: { chromium: [], firefox: {} },
  nomdns: { chromium: ['--disable-features=WebRtcHideLocalIpsWithMdns'], firefox: { 'media.peerconnection.ice.obfuscate_host_addresses': false } },
  loopback: { chromium: ['--disable-features=WebRtcHideLocalIpsWithMdns', '--allow-loopback-in-peer-connection'],
    firefox: { 'media.peerconnection.ice.obfuscate_host_addresses': false, 'media.peerconnection.ice.loopback': true } },
};
async function open(kind, cfgName) {
  const c = CONFIGS[cfgName];
  const b = await launch(kind, kind === 'chromium' ? { args: c.chromium } : { prefs: c.firefox });
  const p = await b.newPage(origin);
  return { b, p, kind };
}
const ev = (d, e, ms = 60000) => withTimeout(d.p.eval(e), ms, e.slice(0, 60));
const results = { versions: ver, netns: NETNS, connect: [], gather: [], life: [], qr: {}, cert: {} };

async function connect(A, B, { ice = [], minimal = false, gatherMs = 30000, openMs = 20000, delayMs = 0, passive = false, offerMod = 'none' } = {}) {
  const cfg = JSON.stringify({ iceServers: ice });
  const o = await ev(A, `P.offer(${cfg}, ${gatherMs})`);
  const ox = extract(o.sdp);
  const offerCode = encode(ox, 'offer');
  // offerMod (experiments): 'unreach' = the answerer is given unreachable addresses for the offerer's
  // candidates (its own checks fail, as through a NAT that has not been opened yet); 'nocands' =
  // the answerer is given no offerer candidates at all (and no end-of-candidates).
  const dx = decode(offerCode);
  if (offerMod === 'unreach') dx.cands = dx.cands.map((c) => ({ ...c, addr: '192.0.2.1' }));
  if (offerMod === 'nocands') dx.cands = [];
  const offerSdp = minimal ? rebuild(dx, 'offer', '0', offerMod !== 'nocands') : o.sdp;
  const a = await ev(B, `P.answer(${cfg}, ${JSON.stringify(offerSdp)}, ${gatherMs}, ${passive})`);
  const tAnswer = Date.now();
  const ax = extract(a.sdp);
  const tag = [...createHash('sha256').update(offerCode).digest().subarray(0, 4)];
  const answerCode = encode(ax, 'answer', tag);
  const answerSdp = minimal ? rebuild(decode(answerCode), 'answer', ox.mid) : a.sdp;
  if (delayMs) await sleep(delayMs);           // the time a person takes to scan the answer
  const tAcc = await ev(A, `P.accept(${o.id}, ${JSON.stringify(answerSdp)})`);
  const r = { offer: { cands: o.cands, gatherMs: o.gatherMs, gatherDone: o.gatherDone, mid: ox.mid, setup: ox.setup, ufrag: ox.ufrag.length, pwd: ox.pwd.length, mms: ox.mms, sizes: sizes(o.sdp, offerCode) },
    answer: { cands: a.cands, gatherMs: a.gatherMs, gatherDone: a.gatherDone, setup: ax.setup, ufrag: ax.ufrag.length, pwd: ax.pwd.length, mms: ax.mms, sizes: sizes(a.sdp, answerCode) },
    ids: [o.id, a.id], tAnswer };
  const t0 = Date.now();
  while (Date.now() - t0 < openMs) {
    const [sa, sb] = [await ev(A, `P.state(${o.id})`), await ev(B, `P.state(${a.id})`)];
    if (sa.dc === 'open' && sb.dc === 'open') {
      r.ok = true; r.openMs = Math.max(sa.ev.find((e) => e[1] === 'open')[0], sb.ev.find((e) => e[1] === 'open')[0]) - tAcc;
      r.maxMsg = [sa.maxMsg, sb.maxMsg]; r.pair = await ev(A, `P.pair(${o.id})`); return r;
    }
    if (sa.conn === 'failed' || sb.conn === 'failed') break;
    await sleep(100);
  }
  r.ok = false; r.states = [await ev(A, `P.state(${o.id})`), await ev(B, `P.state(${a.id})`)];
  r.evB = r.states[1].ev.map((e) => [e[0] - tAnswer, e[1], e[2]]);   // ms after the answer was made
  return r;
}

// ------------------------------------------------------------------ phase: connect
async function phaseConnect() {
  let stun = null;
  const cfgs = (opt('--configs') ?? (NETNS ? 'default,loopback' : 'default,nomdns,fakestun,google')).split(',');
  const pairings = [['chromium', 'chromium'], ['firefox', 'firefox'], ['chromium', 'firefox'], ['firefox', 'chromium'], ['firefox-esr', 'chromium'], ['firefox-esr', 'firefox']]
    .filter(([a, b]) => KINDS.includes(a) && KINDS.includes(b));
  for (const cfgName of cfgs) {
    const flags = cfgName === 'fakestun' || cfgName === 'google' ? 'default' : cfgName;
    let ice = [];
    if (cfgName === 'fakestun') { stun ??= await fakeStun(); ice = [{ urls: `stun:127.0.0.1:${stun.port}` }]; }
    if (cfgName === 'google') ice = [{ urls: 'stun:stun.l.google.com:19302' }];
    const devs = {};
    try {
      for (const k of KINDS) devs[k] = [await open(k, flags), await open(k, flags)];
      for (const [ka, kb] of pairings) {
        const A = devs[ka][0], B = devs[kb][1];
        for (const minimal of [false, true]) {
          let r;
          try { r = await connect(A, B, { ice, minimal, passive: args.includes("--passive") }); } catch (e) { r = { ok: false, error: e.message }; }
          r.config = cfgName; r.pairing = `${short[ka]}→${short[kb]}`; r.minimal = minimal;
          results.connect.push(r);
          console.log(`[connect] ${cfgName.padEnd(9)} ${r.pairing} ${minimal ? 'minimal' : 'full   '} ${r.ok ? `OK ${r.openMs} ms` : 'FAIL ' + (r.error ?? JSON.stringify(r.states?.map((s) => [s.conn, s.ice, s.dc])))}` +
            (r.offer ? ` | A cands ${JSON.stringify(r.offer.cands.map(short1))} B cands ${JSON.stringify(r.answer.cands.map(short1))} pair ${JSON.stringify(r.pair)}` : ''));
        }
      }
    } finally { for (const k in devs) for (const d of devs[k]) await d.b.close(); }
  }
  stun?.close();
  // Gathering time when the STUN server cannot be reached (no internet): unroutable TEST-NET-1
  // address, and a closed port on loopback.
  for (const k of args.includes('--no-gather') ? [] : KINDS) {
    const d = await open(k, 'default');
    try {
      for (const [name, urls] of [['unroutable', 'stun:192.0.2.1:3478'], ['closed-port', 'stun:127.0.0.1:3479']]) {
        const o = await ev(d, `P.offer(${JSON.stringify({ iceServers: [{ urls }] })}, 60000)`, 70000);
        results.gather.push({ browser: short[k], stun: name, gatherMs: o.gatherMs, done: o.gatherDone, cands: o.cands.map(short1) });
        console.log(`[gather] ${short[k]} STUN ${name}: complete=${o.gatherDone} after ${o.gatherMs} ms; cands ${JSON.stringify(o.cands.map(short1))}`);
      }
    } finally { await d.b.close(); }
  }
}
const short1 = (c) => { const f = c.split(' '); return `${f[7]} ${f[2].toLowerCase()} ${f[4]}:${f[5]}`; };

// ------------------------------------------------------------------ phase: life
async function phaseLife() {
  const cfgName = opt('--life-config', NETNS ? 'loopback' : 'nomdns');
  const pairings = [['chromium', 'chromium'], ['firefox', 'firefox'], ['chromium', 'firefox'], ['firefox', 'chromium']].filter(([a, b]) => KINDS.includes(a) && KINDS.includes(b));
  for (const [ka, kb] of pairings) {
    const out = { pairing: `${short[ka]}→${short[kb]}`, config: cfgName };
    results.life.push(out);
    const A = await open(ka, cfgName), B = await open(kb, cfgName);
    const log = (k, v) => { out[k] = v; console.log(`[life] ${out.pairing} ${k}: ${JSON.stringify(v)}`); };
    try {
      // c1: limits, throughput, second channel, dc.close()
      let c = await connect(A, B); if (!c.ok) throw new Error('c1 did not connect');
      let [ia, ib] = c.ids;
      log('maxMessageSize[A,B]', c.maxMsg);
      const ladder = [16384 + 33, 65536, 65537, 262144];
      const sa = await ev(A, `P.sizes(${ia}, ${JSON.stringify(ladder)})`);
      const sb = await ev(B, `P.sizes(${ib}, ${JSON.stringify(ladder)})`);
      await sleep(1500);
      const ra = await ev(A, `P.state(${ia})`), rb = await ev(B, `P.state(${ib})`);
      log('sizes A→B (sent / received)', { sent: sa, received: rb.rx.sizes, dc: rb.dc });
      log('sizes B→A (sent / received)', { sent: sb, received: ra.rx.sizes, dc: ra.dc });
      const TOTAL = 32 * 1024 * 1024;
      const before = (await ev(B, `P.state(${ib})`)).rx.bytes;
      const st = await ev(A, `P.stream(${ia}, ${TOTAL}, ${16384 + 33}, ${1 << 20})`, 120000);
      let rx; const t0 = Date.now();
      do { await sleep(100); rx = (await ev(B, `P.state(${ib})`)).rx; } while (rx.bytes - before < TOTAL && Date.now() - t0 < 120000);
      log('stream 32 MiB, 16 KiB frames, high water 1 MiB, drain on bufferedamountlow(256 KiB)',
        { received: rx.bytes - before, seqOk: rx.seqOk, maxBuffered: st.maxBuf, drains: st.drains, MBps: +((TOTAL / 1048576) / ((rx.last - st.start) / 1000)).toFixed(1) });
      // a second channel on the same connection after the first is closed (engine restart without re-pairing)
      const tc = await ev(A, `P.dcClose(${ia})`);
      let sB; const t1 = Date.now();
      do { await sleep(20); sB = await ev(B, `P.state(${ib})`); } while (!sB.ev.some((e) => e[1] === 'close') && Date.now() - t1 < 30000);
      const ce = sB.ev.find((e) => e[1] === 'close');
      log('dc.close() by A: B sees close after ms', ce ? ce[0] - tc : 'no close in 30 s');
      log('B pc state after dc.close', [sB.conn, sB.ice]);
      await ev(A, `P.newChannel(${ia}, 'sync2')`);
      const t2 = Date.now(); let ok = false;
      while (Date.now() - t2 < 10000) { const x = await ev(B, `P.state(${ib})`), y = await ev(A, `P.state(${ia})`); if (x.dc === 'open' && y.dc === 'open') { ok = true; break; } await sleep(50); }
      if (ok) { await ev(A, `P.sizes(${ia}, [100])`); await sleep(300); }
      log('second channel on the same pc', { open: ok, ms: Date.now() - t2, Bchans: (await ev(B, `P.state(${ib})`)).chans });
      await ev(A, `P.pcClose(${ia})`); await ev(B, `P.pcClose(${ib})`);

      // c2 (minimal SDP): over-limit message, then queue overflow, then pc.close()
      c = await connect(A, B, { minimal: true }); if (!c.ok) throw new Error('c2 did not connect');
      [ia, ib] = c.ids;
      const over = await ev(A, `P.sizes(${ia}, [${c.maxMsg[1] ?? 262144} + 1, 1048576])`);
      await sleep(1000);
      const afterOver = await ev(B, `P.state(${ib})`);
      log('over-limit send A→B (remote max + 1, 1 MiB)', { sent: over, Bdc: afterOver.dc, Breceived: afterOver.rx.sizes });
      if ((await ev(A, `P.state(${ia})`)).dc === 'open') {
        const of = await ev(A, `P.overflow(${ia}, 65536, ${64 << 20})`, 120000);
        await sleep(1000);
        log('overflow: send 64 KiB without waiting, up to 64 MiB', { ...of, stateAfter1s: (await ev(A, `P.state(${ia})`)).dc });
      }
      const tp = await ev(A, `P.pcClose(${ia})`);
      const t3 = Date.now(); let s3;
      do { await sleep(20); s3 = await ev(B, `P.state(${ib})`); } while (s3.dc !== 'closed' && Date.now() - t3 < 60000);
      log('pc.close() by A: B timeline (ms after close)', s3.ev.filter((e) => e[0] >= tp).map((e) => [e[0] - tp, e[1], e[2]]));
      await ev(B, `P.pcClose(${ib})`);

      // c3 (minimal, B offers): A's tab is closed
      const A2 = { b: A.b, p: await A.b.newPage(origin), kind: ka };
      c = await connect(B, A2, { minimal: true }); if (!c.ok) throw new Error('c3 did not connect');
      const [ib3] = c.ids;
      const tt = Date.now(); await A2.p.close();
      const t4 = Date.now(); let s4;
      do { await sleep(20); s4 = await ev(B, `P.state(${ib3})`); } while (s4.dc !== 'closed' && Date.now() - t4 < 60000);
      log('tab of A closed: B timeline (ms after close)', s4.ev.filter((e) => e[0] >= tt).map((e) => [e[0] - tt, e[1], e[2]]));
      await ev(B, `P.pcClose(${ib3})`);

      // c4 (minimal): A's browser is killed (SIGKILL), no goodbye of any kind
      c = await connect(A, B, { minimal: true }); if (!c.ok) throw new Error('c4 did not connect');
      const [, ib4] = c.ids;
      const tk = Date.now(); await A.b.kill();
      const t5 = Date.now(); let s5;
      do { await sleep(100); s5 = await ev(B, `P.state(${ib4})`); } while ((s5.dc !== 'closed' || !['failed', 'closed'].includes(s5.conn)) && Date.now() - t5 < 75000);
      log('browser of A killed: B timeline (ms after kill)', s5.ev.filter((e) => e[0] >= tk).map((e) => [e[0] - tk, e[1], e[2]]));
      log('B final state 75 s max', [s5.conn, s5.ice, s5.dc]);
    } catch (e) { log('error', e.message); }
    finally { await A.b.close(); await B.b.close(); }
  }
}

// ------------------------------------------------------------------ phase: qr, cert
async function phaseQr() {
  for (const k of KINDS) {
    const d = await open(k, 'default');
    try {
      const r = await ev(d, `(async () => ({ BarcodeDetector: typeof BarcodeDetector, formats: typeof BarcodeDetector === 'function' ? await BarcodeDetector.getSupportedFormats() : null,
        mediaDevices: !!navigator.mediaDevices, getUserMedia: typeof navigator.mediaDevices?.getUserMedia, clipboardRead: typeof navigator.clipboard?.readText,
        compression: typeof CompressionStream }))()`);
      results.qr[short[k]] = r; console.log(`[qr] ${ver[k]}: ${JSON.stringify(r)}`);
    } finally { await d.b.close(); }
  }
}
async function phaseCert() {
  for (const k of KINDS) {
    const prof = (await import('../proc.mjs')).tempDir(`cert-${k}-`);
    const SAVE = `(async () => {
      const c = await RTCPeerConnection.generateCertificate({ name: 'ECDSA', namedCurve: 'P-256' });
      const db = await new Promise((res, rej) => { const r = indexedDB.open('cert', 1); r.onupgradeneeded = () => r.result.createObjectStore('kv'); r.onsuccess = () => res(r.result); r.onerror = () => rej(r.error); });
      try { await new Promise((res, rej) => { const tx = db.transaction('kv', 'readwrite'); tx.objectStore('kv').put(c, 'c'); tx.oncomplete = res; tx.onabort = () => rej(tx.error); }); }
      catch (e) { return { stored: false, err: e.name + ': ' + e.message }; }
      return { stored: true, expires: new Date(c.expires).toISOString(), fp: c.getFingerprints()[0] };
    })()`;
    const LOAD = `(async () => {
      const db = await new Promise((res, rej) => { const r = indexedDB.open('cert', 1); r.onsuccess = () => res(r.result); r.onerror = () => rej(r.error); });
      const c = await new Promise((res) => { const q = db.transaction('kv').objectStore('kv').get('c'); q.onsuccess = () => res(q.result); q.onerror = () => res(null); });
      if (!c) return { loaded: false };
      const pc = new RTCPeerConnection({ certificates: [c] }); pc.createDataChannel('x'); await pc.setLocalDescription();
      const fp = pc.localDescription.sdp.match(/a=fingerprint:(\\S+ \\S+)/)[1]; pc.close();
      return { loaded: true, isCert: c instanceof RTCCertificate, fpInSdp: fp };
    })()`;
    let b = await launch(k, { profile: prof });
    try {
      const s = await (await b.newPage(origin)).eval(SAVE);
      await b.close(); b = await launch(k, { profile: prof });
      const l = await (await b.newPage(origin)).eval(LOAD);
      const same = s.fp && l.fpInSdp && l.fpInSdp.toLowerCase() === `${s.fp.algorithm} ${s.fp.value}`.toLowerCase();
      results.cert[short[k]] = { ...s, ...l, sameFingerprintAfterRestart: same };
      console.log(`[cert] ${ver[k]}: ${JSON.stringify(results.cert[short[k]])}`);
    } catch (e) { console.log(`[cert] ${k}: ERROR ${e.message}`); }
    finally { await b.close(); }
  }
}

// ------------------------------------------------------------------ phase: delay, stungather
// The answer is applied by the offerer only after a person has scanned it: does the connection
// survive a delay between the answerer's setLocalDescription and the offerer's setRemoteDescription?
async function phaseDelay() {
  const cfgName = opt('--life-config', NETNS ? 'loopback' : 'nomdns');
  const delays = (opt('--delays') ?? '0,20000,40000,70000').split(',').map(Number);
  const pairings = [['chromium', 'chromium'], ['firefox', 'firefox'], ['chromium', 'firefox'], ['firefox', 'chromium']].filter(([a, b]) => KINDS.includes(a) && KINDS.includes(b))
    .filter(([a, b]) => !opt('--pairings') || opt('--pairings').split(',').includes(short[a] + short[b]));
  const ice = opt('--stun') ? [{ urls: opt('--stun') }] : [], gatherMs = Number(opt('--gather-ms', 30000));
  const passive = args.includes('--passive'), offerMod = opt('--offer-mod', 'none');
  await Promise.all(pairings.map(async ([ka, kb]) => {
    const A = await open(ka, cfgName), B = await open(kb, cfgName);
    try {
      const rs = await Promise.all(delays.map((d) => connect(A, B, { minimal: true, delayMs: d, openMs: 30000, passive, offerMod, ice, gatherMs }).catch((e) => ({ ok: false, error: e.message }))));
      rs.forEach((r, i) => {
        const row = { pairing: `${short[ka]}→${short[kb]}`, config: cfgName, offerMod, passive, answerSetup: r.answer?.setup, delayMs: delays[i], ok: r.ok, openMs: r.openMs, states: r.states?.map((s) => [s.conn, s.ice, s.dc]), evB: r.evB };
        (results.delay ??= []).push(row);
        console.log(`[delay] ${cfgName}/${offerMod} ${row.pairing} answer setup:${row.answerSetup} applied after ${row.delayMs} ms: ${r.ok ? `OK (open ${r.openMs} ms after)` : 'FAIL ' + JSON.stringify(row.states) + ' B events ' + JSON.stringify(row.evB)}`);
      });
    } finally { await A.b.close(); await B.b.close(); }
  }));
}
async function phaseStunGather() {
  for (const k of KINDS) {
    const d = await open(k, 'default');
    try {
      for (let i = 0; i < 2; i++) {
        const o = await ev(d, `P.offer(${JSON.stringify({ iceServers: [{ urls: 'stun:stun.l.google.com:19302' }] })}, 60000)`, 70000);
        const row = { browser: short[k], complete: o.gatherDone, gatherMs: o.gatherMs, cands: o.cands.map((c, j) => `${o.candMs[j]} ms ${short1(c)}`) };
        (results.stungather ??= []).push(row);
        console.log(`[stun-gather] ${short[k]} Google STUN: complete=${row.complete} after ${row.gatherMs} ms; ${JSON.stringify(row.cands)}`);
      }
    } finally { await d.b.close(); }
  }
}

console.log(`versions: ${JSON.stringify(ver)}${NETNS ? ' (network namespace: loopback only)' : ''}`);
try {
  if (PHASE === 'all' || PHASE === 'qr') await phaseQr();
  if (PHASE === 'all' || PHASE === 'cert') await phaseCert();
  if (PHASE === 'all' || PHASE === 'connect') await phaseConnect();
  if (PHASE === 'all' || PHASE === 'life') await phaseLife();
  if (PHASE === 'all' || PHASE === 'delay') await phaseDelay();
  if (PHASE === 'stungather') await phaseStunGather();
} catch (e) { console.log('ERROR', e.stack); }
finally {
  if (opt('--json')) writeFileSync(opt('--json'), JSON.stringify(results, null, 1));
  http.close();
  reportCleanup(await cleanupAll());
}
