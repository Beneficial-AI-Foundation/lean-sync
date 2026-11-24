// Fakes for the Node unit tests of the host modules (no browser APIs needed).
import { join, dirname } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { createEngine, EngineTrap } from '../../app/js/engine.mjs';
import { sha256, hex } from '../../app/js/hash.mjs';

const root = join(dirname(fileURLToPath(import.meta.url)), '../..');
let factory = null;
export async function realEngine() {
  factory ??= (await import(pathToFileURL(join(root, 'build/sync/lean_sync.mjs')))).default;
  return createEngine(factory);
}

/** Wraps a real engine; `trap.next` > 0 makes the next call throw like a trapped instance. */
export function trappable(engine, trap) {
  let dead = false;
  return {
    process(b) {
      if (dead) { const e = new Error('dead'); e.name = 'EngineDead'; throw e; }
      if (trap.next > 0 || trap.always) { trap.next--; trap.fired++; dead = true; throw new EngineTrap(new Error('injected')); }
      trap.calls = (trap.calls ?? 0) + 1;
      return engine.process(b);
    },
    heapBytes: () => engine.heapBytes(),
  };
}

export function memoryStorage() {
  const s = {
    record: null, rotate: false, label: null, blobs: new Map(), saves: [], failSaves: 0, holdSaves: false, held: [],
    async loadRecord() { return s.record; },
    async getRotate() { return s.rotate; },
    async getLabel() { return s.label; },
    async setLabel(l) { s.label = l; },
    async setRotate() { s.rotate = true; },
    saveRecord(replica, state, { clearRotate = false } = {}) {
      const commit = () => { s.record = { replica, state: state.slice() }; if (clearRotate) s.rotate = false; s.saves.push(state.length); };
      if (s.failSaves > 0) { s.failSaves--; return Promise.reject(new Error('quota (fake)')); }
      if (s.holdSaves) return new Promise((res) => s.held.push(() => { commit(); res(); }));
      commit(); return Promise.resolve();
    },
    async listBlobs() { return [...s.blobs.keys()]; },
    async cleanIncoming() {},
    async hasBlob(hx) { return s.blobs.has(hx); },
    async blobFile(hx) { const b = s.blobs.get(hx); if (!b) throw new Error('NotFoundError'); return new Blob([b]); },
    async deleteBlob(hx) { s.blobs.delete(hx); },
    async storeLocal(blob) { const b = new Uint8Array(await blob.arrayBuffer()); const h = await sha256(b); s.blobs.set(hex(h), b); return { ok: true, hash: h, hex: hex(h), size: b.length }; },
    incoming: [], aborted: 0,
    async beginIncoming() {
      const parts = []; const me = { parts, done: false };
      s.incoming.push(me);
      return {
        async write(c) { parts.push(c); },
        async finish(expectedHex) {
          const all = new Uint8Array(parts.reduce((n, p) => n + p.length, 0)); let o = 0; for (const p of parts) { all.set(p, o); o += p.length; }
          const h = await sha256(all); const hx = hex(h); me.done = true;
          if (expectedHex && hx !== expectedHex) return { ok: false, hash: h, hex: hx };
          s.blobs.set(hx, all); return { ok: true, hash: h, hex: hx, size: all.length };
        },
        async abort() { s.aborted++; me.done = true; },
      };
    },
  };
  return s;
}

export function fakeLink(id = 1, remoteLabel = 'R') {
  const l = {
    id, remoteLabel, sent: [], closed: false, bufferedAmount: 0, _f: null, _c: null,
    send(f) { l.sent.push(f.slice()); return true; },
    close() { if (l.closed) return; l.closed = true; queueMicrotask(() => l._c?.()); },
    onFrame(cb) { l._f = cb; }, onClose(cb) { l._c = cb; }, onDrain(cb) { setTimeout(cb, 1); },
    deliver(f) { l._f(f); },
    drop() { l.closed = true; l._c?.(); },
  };
  return l;
}
export const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
