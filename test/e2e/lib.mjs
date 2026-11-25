// End-to-end helpers: devices are separate headless browser processes with their own profile
// directories, served by the static dev server (dev/serve.mjs) and connected to each other over
// WebRTC after the test pairs them through the app's own pairing UI (codes pasted into the paste
// field, or shown to a fake camera). Every check compares against
// data the TEST generated (random names and contents, hashes computed here in Node), never
// against what the page claims it was given (carried-forward requirement 2).
//
// Instrumentation is injected from outside as init scripts, so the app's code stays identical
// to what ships:
//   DOWNLOADS   records what the app hands to an <a download> click (name, size, SHA-256)
//   TRAP        wraps the wasm instance's exports so that, on demand, `ls_process` first triggers a
//               real trap inside the module (a 4 GiB allocation: Lean's out-of-memory abort)
//   IDB_FAULT   (Chromium storage-failure test) aborts the IndexedDB transaction that writes the
//               record, as a quota failure would; Chromium ignores the CDP quota override for IDB
//   NET         wraps RTCPeerConnection / RTCDataChannel: counts connections and bytes, records the
//               ICE servers given, and on demand cuts a sync channel after N bytes, corrupts the
//               next blob frame or injects a garbage message (the faults the dev relay used to inject);
//               counts WebSocket / EventSource / foreign fetch (there must be none)
//   CAMERA      a fake camera: enumerateDevices lists one, getUserMedia returns a canvas stream
//               showing `__fakeCamera.image` (or is refused), so the app's real scanning loop runs;
//               `absent` makes the device list empty (this machine has a real webcam)
import { createHash, randomBytes } from 'node:crypto';
import { launch, browserVersion } from './driver.mjs';
import { tempDir, removeDir } from '../proc.mjs';

export const sha = (b) => createHash('sha256').update(b).digest('hex');
export const randomFile = (name, size) => { const bytes = randomBytes(size); return { name, bytes, sha: sha(bytes) }; };
export const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

const SS = `const __ss = (k) => { try { return sessionStorage.getItem(k); } catch { return null; } };`;
export const DOWNLOADS = `
  window.__downloads = [];
  const __click = HTMLAnchorElement.prototype.click;
  HTMLAnchorElement.prototype.click = function () {
    if (this.download && this.href.startsWith('blob:')) {
      const name = this.download;
      window.__downloads.push(fetch(this.href).then((r) => r.arrayBuffer()).then(async (b) => ({ name, size: b.byteLength,
        sha: Array.from(new Uint8Array(await crypto.subtle.digest('SHA-256', b)), (x) => x.toString(16).padStart(2, '0')).join('') })));
      return;
    }
    return __click.call(this);
  };`;

export const TRAP = `${SS}
  window.__trap = { next: 0, fired: 0, always: __ss('__trapAlways') === '1' };
  const __wrapInstance = (inst) => {
    const ex = inst.exports, out = {};
    for (const k of Object.keys(ex)) out[k] = ex[k];
    out.ls_process = function (...a) {
      if (window.__trap.always || window.__trap.next > 0) {
        if (window.__trap.next > 0) window.__trap.next--;
        window.__trap.fired++;
        ex.ls_input(0xffffffff);          // real trap inside the module (Lean: out of memory)
      }
      return ex.ls_process.apply(this, a);
    };
    return { exports: out };
  };
  const __is = WebAssembly.instantiateStreaming, __i = WebAssembly.instantiate;
  WebAssembly.instantiateStreaming = async (...a) => { const r = await __is.apply(WebAssembly, a); return { module: r.module, instance: __wrapInstance(r.instance) }; };
  WebAssembly.instantiate = async (...a) => { const r = await __i.apply(WebAssembly, a);
    return r instanceof WebAssembly.Instance ? __wrapInstance(r) : { module: r.module, instance: __wrapInstance(r.instance) }; };`;

export const IDB_FAULT = `${SS}
  // __idbFail: abort the transaction writing the record (a transaction-level failure, like quota)
  // __idbReqFail: make the request writing the record fail on its own (ConstraintError from add()
  //   on an existing key), leaving the transaction to its default behaviour: a correct host lets
  //   that abort the transaction; one that suppresses the error would see it complete.
  window.__idbFail = __ss('__idbFail') === '1';
  window.__idbFailed = 0; window.__idbReqFail = false; window.__idbReqFailed = 0;
  const __put = IDBObjectStore.prototype.put;
  IDBObjectStore.prototype.put = function (value, key) {
    if (window.__idbReqFail && key === 'record') { window.__idbReqFailed++; return this.add(value, key); }
    const r = __put.call(this, value, key);
    if (window.__idbFail && key === 'record') { window.__idbFailed++; const tx = this.transaction; queueMicrotask(() => { try { tx.abort(); } catch {} }); }
    return r;
  };`;

// __holdClose: OPFS writes of new files stay pending (at close) until __releaseCloses(), so a test can
// make something happen while a local add is being stored.
export const SLOW_STORE = `
  window.__holdClose = false; window.__held = [];
  const __close = FileSystemWritableFileStream.prototype.close;
  FileSystemWritableFileStream.prototype.close = function () {
    if (!window.__holdClose) return __close.call(this);
    return new Promise((res, rej) => window.__held.push(() => __close.call(this).then(res, rej)));
  };
  window.__releaseCloses = () => { window.__holdClose = false; const h = window.__held; window.__held = []; for (const f of h) f(); return h.length; };`;

// __failCreate = n: the next n creations of a temporary (non-hash-named) OPFS file reject, as a full
// disk would. __failMove = n: the next n FileSystemFileHandle.move() calls reject. __failWrite = n: the
// next n writes to an OPFS writable reject.
export const FS_FAULT = `
  window.__failCreate = 0; window.__failMove = 0; window.__failWrite = 0;
  const __wr = FileSystemWritableFileStream.prototype.write;
  FileSystemWritableFileStream.prototype.write = function (...a) {
    if (window.__failWrite > 0) { window.__failWrite--; return Promise.reject(new DOMException('injected', 'QuotaExceededError')); }
    return __wr.apply(this, a);
  };
  const __gfh = FileSystemDirectoryHandle.prototype.getFileHandle;
  window.__hashLookups = 0;                     // lookups of blobs/<hash> (counted, never altered)
  FileSystemDirectoryHandle.prototype.getFileHandle = function (name, opts) {
    if (/^[0-9a-f]{64}$/.test(name) && !(opts && opts.create)) window.__hashLookups++;
    if (window.__failCreate > 0 && opts && opts.create && !/^[0-9a-f]{64}$/.test(name)) { window.__failCreate--; return Promise.reject(new DOMException('injected', 'QuotaExceededError')); }
    return __gfh.call(this, name, opts);
  };
  const __mv = FileSystemFileHandle.prototype.move;
  FileSystemFileHandle.prototype.move = function (...a) {
    if (window.__failMove > 0) { window.__failMove--; return Promise.reject(new DOMException('injected', 'InvalidModificationError')); }
    return __mv.apply(this, a);
  };`;

export const NET = `
  const n = window.__net = { pcs: 0, pcList: [], ice: [], sent: 0, cutAfter: null, cuts: 0, corruptNext: false, corrupted: 0,
    lastSync: null, syncSeen: 0, sockets: 0, eventSources: 0, foreignFetch: 0 };
  const __RPC = window.RTCPeerConnection;
  if (__RPC) {
    const Wrapped = function (cfg, ...rest) { const pc = new __RPC(cfg, ...rest); n.pcs++; n.pcList.push(pc); n.ice.push(JSON.stringify(cfg?.iceServers ?? null)); return pc; };
    Wrapped.prototype = __RPC.prototype;
    Object.setPrototypeOf(Wrapped, __RPC);
    window.RTCPeerConnection = Wrapped;
    n.live = () => n.pcList.filter((p) => p.signalingState !== 'closed').length;
  }
  if (window.RTCDataChannel) {
    const __send = RTCDataChannel.prototype.send, seen = new WeakSet();
    RTCDataChannel.prototype.send = function (d) {
      if (this.label === 'sync') {
        if (!seen.has(this)) { seen.add(this); n.syncSeen++; }
        n.lastSync = this;
        n.sent += d.byteLength ?? d.length ?? 0;
        if (n.cutAfter !== null && n.sent >= n.cutAfter) { n.cutAfter = null; n.cuts++; this.close(); return; }
        if (n.corruptNext && d instanceof Uint8Array && d[0] === 3 && d.length > 33) { n.corruptNext = false; n.corrupted++; d = d.slice(); d[33] ^= 0xff; }
      }
      return __send.call(this, d);
    };
    // a complete, undecodable Lean message: host frame MSG (1), more=0, then garbage bytes
    window.__netGarbage = () => { const c = n.lastSync; if (!c || c.readyState !== 'open') return false; __send.call(c, new Uint8Array([1, 0, 1, 2, 99, 1, 2, 3])); return true; };
  }
  const __WS = window.WebSocket;
  window.WebSocket = function (...a) { n.sockets++; return new __WS(...a); };
  window.WebSocket.prototype = __WS.prototype;
  if (window.EventSource) { const __ES = window.EventSource; window.EventSource = function (...a) { n.eventSources++; return new __ES(...a); }; }
  const __fetch = window.fetch;
  window.fetch = function (input, ...rest) {
    try { const u = new URL(typeof input === 'string' ? input : input.url, location.href); if (u.origin !== location.origin && u.protocol !== 'blob:' && u.protocol !== 'data:') n.foreignFetch++; } catch {}
    return __fetch.call(this, input, ...rest);
  };`;

export const CAMERA = `
  const f = window.__fakeCamera = { enabled: false, absent: false, deny: false, image: null, starts: 0 };
  const md = navigator.mediaDevices;
  if (md) {
    const enumerate = md.enumerateDevices.bind(md), gum = md.getUserMedia.bind(md);
    md.enumerateDevices = async () => f.absent ? [] : f.enabled ? [{ kind: 'videoinput', deviceId: 'fake', groupId: 'fake', label: 'fake camera' }] : enumerate();
    md.getUserMedia = async (c) => {
      if (!f.enabled) return gum(c);
      f.starts++;
      if (f.deny) throw new DOMException('Permission denied', 'NotAllowedError');
      const canvas = document.createElement('canvas'); canvas.width = 640; canvas.height = 480;
      const g = canvas.getContext('2d'); g.imageSmoothingEnabled = false;
      const img = new Image();
      const draw = () => {
        g.fillStyle = '#9a9a9a'; g.fillRect(0, 0, 640, 480);
        if (f.image && img.src !== f.image) img.src = f.image;
        if (f.image && img.complete && img.naturalWidth) { const k = Math.floor(440 / img.naturalWidth) || 440 / img.naturalWidth; g.drawImage(img, 100, 20, img.naturalWidth * k, img.naturalHeight * k); }
      };
      draw(); setInterval(draw, 100);
      return canvas.captureStream(10);
    };
  }`;

const INIT_SCRIPTS = [DOWNLOADS, TRAP, IDB_FAULT, SLOW_STORE, FS_FAULT, NET, CAMERA];
// Browser settings for deterministic candidates: host addresses instead of mDNS names
// (docs/net-design.md §1.1). `browserDefaults: true` leaves the browser as shipped.
const NO_MDNS = { chromium: ['--disable-features=WebRtcHideLocalIpsWithMdns'], firefox: { 'media.peerconnection.ice.obfuscate_host_addresses': false } };

export const versions = {};
export function versionOf(kind) { return (versions[kind] ??= browserVersion(kind)); }

/**
 * Open (or reopen, with `profile`) a device: a browser process + the app page.
 * `stun`: the STUN list to set through the settings UI once running (default: none, so the tests
 * never depend on the internet); null leaves the stored or default list.
 */
export async function openDevice(server, kind, label, { prefs, profile, waitRunning = true, extraQuery = '', browserDefaults = false, stun = [] } = {}) {
  const dir = profile ?? tempDir(`lsync-${label}-`);
  const firefox = kind !== 'chromium';
  const browser = await launch(kind, {
    profile: dir, prefs: { ...(firefox && !browserDefaults ? NO_MDNS.firefox : {}), ...(prefs ?? {}) },
    args: !firefox && !browserDefaults ? NO_MDNS.chromium : [] });
  try {
    const url = `${server.url}/?device=${encodeURIComponent(label)}${extraQuery}`;
    const page = await browser.newPage(url, { initScripts: INIT_SCRIPTS.map((src) => `(() => {${src}\n})();`) });
    const d = makeDevice({ browser, page, kind, label, profile: dir, url, server, prefs, browserDefaults, stun });
    if (waitRunning) {
      await d.waitFor(`window.leansync && window.leansync.phase === 'running'`, 30000, 'app running');
      if (stun !== null) await d.setStun(stun);
    }
    return d;
  } catch (e) { await browser.close(); throw e; }
}

function makeDevice(d) {
  const page = () => d.page;
  Object.assign(d, {
    eval: (e) => page().eval(e),
    async waitFor(expr, ms = 30000, what = expr) {
      const t0 = Date.now(); let last;
      while (Date.now() - t0 < ms) {
        try { last = await page().eval(expr); if (last) return last; } catch (e) { last = e.message; }
        await sleep(100);
      }
      throw new Error(`${d.label}: timed out after ${ms} ms waiting for ${what} (last: ${JSON.stringify(last)?.slice(0, 300)})\nlog tail:\n${(await d.logTail().catch(() => []))?.join('\n')}`);
    },
    logTail: async () => (await page().eval('window.leansync && window.leansync.log ? window.leansync.log.slice(-25) : []')),
    /** Add files through the real file input (the same code path as the picker). */
    async add(files) {
      const spec = files.map((f) => ({ name: f.name, b64: f.bytes ? f.bytes.toString('base64') : null, zeroMiB: f.zeroMiB ?? 0 }));
      await page().eval(`(() => {
        const spec = ${JSON.stringify(spec)};
        const dt = new DataTransfer();
        for (const s of spec) {
          let parts;
          if (s.b64 !== null) { const bin = atob(s.b64); const u = new Uint8Array(bin.length); for (let i = 0; i < bin.length; i++) u[i] = bin.charCodeAt(i); parts = [u]; }
          else { const mib = new Uint8Array(1048576); parts = Array.from({ length: s.zeroMiB }, () => mib); parts.push(new Uint8Array(1)); }
          dt.items.add(new File(parts, s.name));
        }
        const input = document.querySelector('#add-input');
        input.files = dt.files;
        input.dispatchEvent(new Event('change'));
        return true;
      })()`);
    },
    /** The file list as displayed. */
    rows: () => page().eval(`[...document.querySelectorAll('#files tr:not(.version)')].map((tr) => ({ path: tr.dataset.path, status: tr.dataset.status, hashes: (tr.dataset.hashes || '').split(',').filter(Boolean),
      versions: [...document.querySelectorAll('#files tr.version')].filter((v) => v.dataset.path === tr.dataset.path).map((v) => ({ hex: v.dataset.version, status: v.dataset.status })) }))`),
    async waitRows(pred, ms = 30000, what = 'rows') {
      const t0 = Date.now(); let rows;
      while (Date.now() - t0 < ms) { rows = await d.rows(); if (pred(rows)) return rows; await sleep(150); }
      throw new Error(`${d.label}: timed out waiting for ${what}; rows: ${JSON.stringify(rows)}\nlog tail:\n${(await d.logTail()).join('\n')}`);
    },
    /** Wait until exactly these files are shown complete (name -> sha of the bytes). */
    async waitFiles(expected, ms = 60000) {
      const names = Object.keys(expected).sort();
      return d.waitRows((rows) => rows.length === names.length && rows.every((r) => r.status === 'complete') &&
        JSON.stringify(rows.map((r) => r.path).sort()) === JSON.stringify(names), ms, `files ${JSON.stringify(names)} complete`);
    },
    click: (sel) => page().eval(`(() => { const b = document.querySelector(${JSON.stringify(sel)}); if (!b) throw new Error('no element ' + ${JSON.stringify(sel)}); if (b.disabled) throw new Error('disabled: ' + ${JSON.stringify(sel)}); b.click(); return true; })()`),
    rowSel: (path, action, version) => version
      ? `#files tr.version[data-path="${CSS_escape(path)}"][data-version="${version}"] button[data-action="${action}"]`
      : `#files tr:not(.version)[data-path="${CSS_escape(path)}"] button[data-action="${action}"]`,
    /** Click Download; return {name, size, sha} of what the app handed to the browser. */
    async download(path, version) {
      const n = await page().eval('window.__downloads.length');
      await d.click(d.rowSel(path, 'download', version));
      await d.waitFor(`window.__downloads.length > ${n}`, 20000, 'download');
      return page().eval(`window.__downloads[${n}]`);
    },
    async reload() { await page().reload(); await d.waitFor(`window.leansync && window.leansync.phase === 'running'`, 30000, 'running after reload'); },
    async close() { await d.browser.close(); },
    async kill() { await d.browser.kill(); },
    /** Set the STUN list through the settings UI. */
    async setStun(list) {
      await page().eval(`(() => { document.querySelector('#settings').open = true; const t = document.querySelector('#stun'); t.value = ${JSON.stringify(list.join('\n'))};
        document.querySelector('#stun-status').dataset.state = ''; document.querySelector('#stun-save').click(); return true; })()`);
      return d.waitFor(`document.querySelector('#stun-status').dataset.state`, 10000, 'STUN setting saved or refused');
    },
    /** Paste text into the open pairing dialog's paste field and press its button. */
    async pasteCode(text) {
      await d.waitFor(`!!document.querySelector('#pair-input')`, 10000, 'paste field');
      return page().eval(`(() => { const i = document.querySelector('#pair-input'); i.value = ${JSON.stringify(text)}; document.querySelector('#pair-submit').click(); return true; })()`);
    },
    /** The code currently shown in the pairing dialog (invitation or the newest reply). */
    shownCode: () => page().eval(`document.querySelector('#pair-code')?.dataset.code ?? null`),
    qrImage: () => page().eval(`document.querySelector('#pair-qr')?.toDataURL() ?? null`),
    pairError: () => page().eval(`(() => { const e = document.querySelector('#pair-error'); return e && !e.hidden ? { text: e.textContent, reason: e.dataset.reason } : null; })()`),
    closeDialog: () => page().eval(`(() => { const p = document.querySelector('#pair'); if (p.open) p.close(); return true; })()`),
    connections: () => page().eval(`window.leansync.connections`),
    async reopen({ waitRunning = true } = {}) {
      const nd = await openDevice(d.server, d.kind, d.label, { prefs: d.prefs, profile: d.profile, waitRunning, browserDefaults: d.browserDefaults, stun: null });
      Object.assign(d, { browser: nd.browser, page: nd.page });
      return d;
    },
    destroy() { removeDir(d.profile); },
  });
  return d;
}
const CSS_escape = (s) => s.replace(/["\\]/g, '\\$&');

/**
 * Pair A (inviting) with B (joining) through the app's pairing UI.
 *   via: 'text' (paste fields) or 'qr' (each side shows its QR to the other's fake camera)
 *   offerFor(code): what B is given instead of A's invitation (e.g. with unreachable candidates)
 *   replyAfterMs: wait this long after B's first reply before A reads B's current reply
 *   linked: also wait until a link is up on both sides (false when the link is expected to be refused)
 * Returns the codes used. Both dialogs are closed at the end.
 */
export async function pair(A, B, { via = 'text', offerFor = null, replyAfterMs = 0, linked = true } = {}) {
  const linksBefore = { A: await A.eval(`window.leansync.connections.length`), B: await B.eval(`window.leansync.connections.length`) };
  await A.click('#invite');
  const offer = await A.waitFor(`document.querySelector('#pair-code')?.dataset.code`, 20000, 'invitation shown');
  await B.click('#join');
  const given = offerFor ? offerFor(offer) : offer;
  if (via === 'qr') {
    if (offerFor) throw new Error('offerFor needs the text path');
    await B.eval(`(window.__fakeCamera.enabled = true, window.__fakeCamera.image = ${JSON.stringify(await A.qrImage())}, true)`);
    await B.waitFor(`!document.querySelector('#pair-scan')?.hidden`, 10000, 'scan button (fake camera found)');
    await B.click('#pair-scan');
  } else await B.pasteCode(given);
  const first = await B.waitFor(`document.querySelector('#pair-code')?.dataset.code`, 20000, 'reply shown');
  if (replyAfterMs) await sleep(replyAfterMs);
  const reply = await B.shownCode();
  if (via === 'qr') {
    await A.eval(`(window.__fakeCamera.enabled = true, window.__fakeCamera.image = ${JSON.stringify(await B.qrImage())}, true)`);
    await A.waitFor(`!document.querySelector('#pair-scan')?.hidden`, 10000, 'scan button (fake camera found)');
    await A.click('#pair-scan');
  } else await A.pasteCode(reply);
  await A.waitFor(`document.querySelector('#pair-status')?.dataset.state === 'connected' || (document.querySelector('#pair-error') && !document.querySelector('#pair-error').hidden && document.querySelector('#pair-error').textContent)`, 45000, 'A: connected');
  const err = await A.pairError();
  if (err) throw new Error(`${A.label}: pairing failed: ${err.text}`);
  await B.waitFor(`document.querySelector('#pair-status')?.dataset.state === 'connected'`, 20000, 'B: connected');
  if (linked) for (const [D, n] of [[A, linksBefore.A], [B, linksBefore.B]]) {
    await D.waitFor(`window.leansync.connections.filter((c) => c.linkId !== null).length >= ${n + 1}`, 20000, 'link up');
  }
  await A.closeDialog(); await B.closeDialog();
  return { offer, given, first, reply };
}
