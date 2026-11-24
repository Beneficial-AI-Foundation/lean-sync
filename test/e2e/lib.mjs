// End-to-end helpers: devices are separate headless browser processes with their own profile
// directories, all talking through the dev relay (dev/serve.mjs). Every check compares against
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

const INIT_SCRIPTS = [DOWNLOADS, TRAP, IDB_FAULT, SLOW_STORE, FS_FAULT];

export const versions = {};
export function versionOf(kind) { return (versions[kind] ??= browserVersion(kind)); }

/** Open (or reopen, with `profile`) a device: a browser process + the app page. */
export async function openDevice(server, kind, label, { room, prefs, profile, waitRunning = true, extraQuery = '' } = {}) {
  const dir = profile ?? tempDir(`lsync-${label}-`);
  const browser = await launch(kind, { profile: dir, prefs });
  try {
    const url = `${server.url}/?device=${encodeURIComponent(label)}&room=${encodeURIComponent(room)}${extraQuery}`;
    const page = await browser.newPage(url, { initScripts: INIT_SCRIPTS.map((src) => `(() => {${src}\n})();`) });
    const d = makeDevice({ browser, page, kind, label, profile: dir, url, server, room, prefs });
    if (waitRunning) await d.waitFor(`window.leansync && window.leansync.phase === 'running'`, 30000, 'app running');
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
    async reopen({ waitRunning = true } = {}) {
      const nd = await openDevice(d.server, d.kind, d.label, { room: d.room, prefs: d.prefs, profile: d.profile, waitRunning });
      Object.assign(d, { browser: nd.browser, page: nd.page });
      return d;
    },
    destroy() { removeDir(d.profile); },
  });
  return d;
}
const CSS_escape = (s) => s.replace(/["\\]/g, '\\$&');

export async function admin(server, path, body) {
  const r = await fetch(`${server.url}/admin/${path}`, { method: 'POST', body: JSON.stringify(body) });
  const j = await r.json();
  if (!j.ok) throw new Error(`admin ${path}: ${j.error}`);
  return j;
}
