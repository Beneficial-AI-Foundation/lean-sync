// Durable storage of one device (docs/app-design.md §5).
//
// IndexedDB `leansync`, object store `kv`:
//   'record'   {v:1, hi:BigInt, lo:BigInt, state:Uint8Array}  the persisted protocol state (Lean's
//              `persist` bytes) and the replica id it belongs to, replaced atomically
//   'rotateId' true: the next start must use a fresh replica id (after rollbackDetected or reset)
//   'label'    the device name shown to the user and to other devices
// OPFS: blobs/<64 hex>  complete files whose SHA-256 was verified on the stored bytes
//       incoming/<rand> partial files (received streams, local adds); emptied at start-up
//
// A file reaches blobs/<hash> only by move() after its stored bytes were hashed, so a crash at any
// point leaves either no file or a verified one under that name. Any storage error (not only
// QuotaExceededError: Chromium's OPFS also reports AbortError) is a failure.
import { sha256, hex } from './hash.mjs';

export const MAX_FILE_BYTES = 256 * 1024 * 1024;   // per-file limit: WebCrypto hashes a whole buffer
const HEX64 = /^[0-9a-f]{64}$/;

const req = (r) => new Promise((res, rej) => { r.onsuccess = () => res(r.result); r.onerror = () => rej(r.error); });

export class StorageError extends Error {
  constructor(msg, cause) { super(msg); this.name = 'StorageError'; this.cause = cause; }
}

const openDb = () => new Promise((res, rej) => {
  const r = indexedDB.open('leansync', 1);
  r.onupgradeneeded = () => r.result.createObjectStore('kv');
  r.onsuccess = () => res(r.result);
  r.onerror = () => rej(r.error);
  r.onblocked = () => rej(new Error('database upgrade blocked'));
});

export async function openStorage() {
  let db = await openDb();
  const root = await navigator.storage.getDirectory();
  const blobsDir = await root.getDirectoryHandle('blobs', { create: true });
  const incomingDir = await root.getDirectoryHandle('incoming', { create: true });
  let tmpCounter = 0;

  async function get(key) {
    let tx;
    try { tx = db.transaction('kv', 'readonly'); } catch { try { db.close(); } catch {} db = await openDb(); tx = db.transaction('kv', 'readonly'); }
    return req(tx.objectStore('kv').get(key));
  }
  /** Write `entries` (key -> value; undefined = delete) in ONE strict transaction. Resolves only
   *  from the transaction's `complete` event; rejects on error, abort or exception.
   *  Firefox, after a transaction aborted for quota, throws InvalidStateError from the next
   *  db.transaction() call on that connection; then nothing was written, and the write is tried
   *  once more on a fresh connection. */
  async function write(entries) {
    try { return await writeOnce(entries); }
    catch (e) {
      if (e.cause?.name !== 'InvalidStateError' || !e.beforeTx) throw e;
      try { db.close(); } catch {}
      db = await openDb();
      return writeOnce(entries);
    }
  }
  function writeOnce(entries) {
    return new Promise((resolve, reject) => {
      let tx;
      try {
        tx = db.transaction('kv', 'readwrite', { durability: 'strict' });
      } catch (e) { const err = new StorageError(`save failed: ${e.name ?? e}`, e); err.beforeTx = true; reject(err); return; }
      try {
        const st = tx.objectStore('kv');
        for (const [k, v] of Object.entries(entries)) { if (v === undefined) st.delete(k); else st.put(v, k); }
      } catch (e) { try { tx.abort(); } catch {} reject(new StorageError(`save failed: ${e.name ?? e}`, e)); return; }
      tx.oncomplete = () => resolve();
      tx.onabort = () => reject(new StorageError(`save failed: ${tx.error?.name ?? 'transaction aborted'}`, tx.error));
      tx.onerror = (ev) => { ev.preventDefault?.(); /* onabort follows and rejects */ };
    });
  }

  async function newIncoming() {
    const name = `${Date.now().toString(36)}-${(tmpCounter++).toString(36)}-${Math.random().toString(36).slice(2, 8)}`;
    const fh = await incomingDir.getFileHandle(name, { create: true });
    return { name, fh };
  }

  /** Hash the stored bytes of an incoming file and publish it as blobs/<hash>. */
  async function publish(name, fh, expectedHex = null) {
    const file = await fh.getFile();
    if (file.size > MAX_FILE_BYTES) { await removeIncoming(name); throw new StorageError(`file larger than ${MAX_FILE_BYTES} bytes`); }
    const h = await sha256(new Uint8Array(await file.arrayBuffer()));
    const hx = hex(h);
    if (expectedHex && hx !== expectedHex) { await removeIncoming(name); return { ok: false, hash: h, hex: hx }; }
    if (await hasBlob(hx)) await removeIncoming(name);
    else await fh.move(blobsDir, hx);
    return { ok: true, hash: h, hex: hx, size: file.size };
  }
  async function removeIncoming(name) { try { await incomingDir.removeEntry(name); } catch {} }
  async function hasBlob(hx) { try { await blobsDir.getFileHandle(hx); return true; } catch { return false; } }

  return {
    async loadRecord() {
      const r = await get('record');
      if (!r) return null;
      if (typeof r.hi !== 'bigint' || typeof r.lo !== 'bigint' || !(r.state instanceof Uint8Array)) return { corrupt: true, state: new Uint8Array(0) };
      return { replica: { hi: r.hi, lo: r.lo }, state: r.state };
    },
    getRotate: async () => (await get('rotateId')) === true,
    getLabel: () => get('label'),
    setLabel: (label) => write({ label }),
    setRotate: () => write({ rotateId: true }),
    /** The persist of one Lean `persist` effect: record and (optionally) clearing rotateId, atomically. */
    saveRecord(replica, state, { clearRotate = false } = {}) {
      return write({ record: { v: 1, hi: replica.hi, lo: replica.lo, state }, ...(clearRotate ? { rotateId: undefined } : {}) });
    },
    /** Hex names of the stored blobs (anything else in blobs/ is ignored). */
    async listBlobs() {
      const out = [];
      for await (const [name, h] of blobsDir.entries()) if (h.kind === 'file' && HEX64.test(name)) out.push(name);
      return out;
    },
    async cleanIncoming() {
      const names = [];
      for await (const [name] of incomingDir.entries()) names.push(name);
      for (const n of names) await removeIncoming(n);
    },
    hasBlob,
    async blobFile(hx) { return (await blobsDir.getFileHandle(hx)).getFile(); },
    async deleteBlob(hx) { try { await blobsDir.removeEntry(hx); } catch {} },
    /** Store a local file (File/Blob) and return its verified hash. */
    async storeLocal(blob) {
      if (blob.size > MAX_FILE_BYTES) throw new StorageError(`file larger than the ${MAX_FILE_BYTES / 1048576} MiB limit`);
      const { name, fh } = await newIncoming();
      try {
        const w = await fh.createWritable();
        try { await w.write(blob); await w.close(); } catch (e) { try { await w.abort(); } catch {} throw e; }
        return await publish(name, fh);
      } catch (e) { await removeIncoming(name); throw e instanceof StorageError ? e : new StorageError(`could not store the file: ${e.name ?? e}`, e); }
    },
    /** A received stream: write chunks in order, then finish(expectedHex) verifies and publishes. */
    async beginIncoming() {
      const { name, fh } = await newIncoming();
      const w = await fh.createWritable();
      let chain = Promise.resolve(); let failed = null; let done = false;
      return {
        write(chunk) { chain = chain.then(() => w.write(chunk)).catch((e) => { failed ??= e; }); return chain; },
        async finish(expectedHex) {
          await chain; done = true;
          if (failed) { try { await w.abort(); } catch {} await removeIncoming(name); throw new StorageError(`write failed: ${failed.name ?? failed}`, failed); }
          try { await w.close(); } catch (e) { await removeIncoming(name); throw new StorageError(`write failed: ${e.name ?? e}`, e); }
          return publish(name, fh, expectedHex);
        },
        async abort() { if (done) return; done = true; await chain; try { await w.abort(); } catch {} await removeIncoming(name); },
      };
    },
  };
}
