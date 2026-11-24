// Probe the browser features the host design relies on (docs/app-design.md §11 point 5):
//   - OPFS FileSystemFileHandle.move() between directories (atomic publish of a verified blob)
//   - IndexedDB transactions with { durability: 'strict' }
//   - a real storage failure: Chromium via CDP Storage.overrideQuotaForOrigin, Firefox via the
//     dom.quotaManager.temporaryStorage.fixedLimit pref
//   - driving each browser (CDP / BiDi), including a second tab in the same profile.
// usage: node test/e2e/probe-features.mjs
import { createServer } from 'node:http';
import { launch, hasBrowser, browserVersion } from './driver.mjs';
import { cleanupAll, reportCleanup } from '../proc.mjs';

const server = createServer((req, res) => { res.writeHead(200, { 'content-type': 'text/html' }); res.end('<!doctype html><title>probe</title><p>probe'); });
await new Promise((r) => server.listen(0, '127.0.0.1', r));
const origin = `http://127.0.0.1:${server.address().port}`;

const PROBE = `(async () => {
  const out = {};
  const root = await navigator.storage.getDirectory();
  const inc = await root.getDirectoryHandle('incoming', { create: true });
  const blobs = await root.getDirectoryHandle('blobs', { create: true });
  const fh = await inc.getFileHandle('part1', { create: true });
  const w = await fh.createWritable(); await w.write(new Uint8Array([1,2,3,4])); await w.close();
  out.moveType = typeof fh.move;
  try {
    await fh.move(blobs, 'final1');
    const f = await (await blobs.getFileHandle('final1')).getFile();
    out.movedBytes = Array.from(new Uint8Array(await f.arrayBuffer()));
    let still = true; try { await inc.getFileHandle('part1'); } catch { still = false; }
    out.sourceGone = !still;
    out.handleFollows = (await fh.getFile()).size;   // handle refers to the moved file?
  } catch (e) { out.moveError = String(e); }
  const db = await new Promise((res, rej) => { const r = indexedDB.open('probe', 1); r.onupgradeneeded = () => r.result.createObjectStore('kv'); r.onsuccess = () => res(r.result); r.onerror = () => rej(r.error); });
  const tx = db.transaction('kv', 'readwrite', { durability: 'strict' });
  out.durability = tx.durability;
  tx.objectStore('kv').put(new Uint8Array(10), 'k');
  out.txOk = await new Promise((res) => { tx.oncomplete = () => res(true); tx.onabort = tx.onerror = () => res(String(tx.error)); });
  db.close();
  out.persisted = await navigator.storage.persisted();
  return out;
})()`;

const BIG_WRITE = `(async () => {
  const out = {};
  const big = new Uint8Array(30 * 1024 * 1024); for (let i = 0; i < big.length; i += 65536) crypto.getRandomValues(big.subarray(i, i + 65536));  // incompressible
  const db = await new Promise((res, rej) => { const r = indexedDB.open('probe', 1); r.onupgradeneeded = () => r.result.createObjectStore('kv'); r.onsuccess = () => res(r.result); r.onerror = () => rej(r.error); });
  try {
    const tx = db.transaction('kv', 'readwrite', { durability: 'strict' });
    tx.objectStore('kv').put(big, 'big');
    out.idb = await new Promise((res) => { tx.oncomplete = () => res('ok'); tx.onabort = () => res('abort: ' + (tx.error && tx.error.name)); });
  } catch (e) { out.idb = 'throw: ' + e.name; }
  db.close();
  try {
    const root = await navigator.storage.getDirectory();
    const fh = await root.getFileHandle('bigfile', { create: true });
    const w = await fh.createWritable(); await w.write(big); await w.close();
    out.opfs = 'ok';
  } catch (e) { out.opfs = 'throw: ' + e.name; }
  out.estimate = await navigator.storage.estimate();
  return out;
})()`;

for (const kind of ['chromium', 'firefox', 'firefox-esr'].filter(hasBrowser)) {
  const prefs = kind === 'chromium' ? {} : { 'dom.quotaManager.temporaryStorage.fixedLimit': 20480 }; // KiB
  const b = await launch(kind, { prefs });
  try {
    const p = await b.newPage(`${origin}/`);
    console.log(`== ${browserVersion(kind)}`);
    console.log('  features:', JSON.stringify(await p.eval(PROBE)));
    if (kind === 'chromium') await p.cdp('Storage.overrideQuotaForOrigin', { origin, quotaSize: 20 * 1024 * 1024 });
    console.log('  30 MiB writes under a 20 MiB quota:', JSON.stringify(await p.eval(BIG_WRITE)));
    const p2 = await b.newPage(`${origin}/`);
    console.log('  second tab, same profile, sees the first tab OPFS file:', await p2.eval(`navigator.storage.getDirectory().then(r => r.getDirectoryHandle('blobs')).then(d => d.getFileHandle('final1')).then(() => true, () => false)`));
  } catch (e) { console.log(`  ERROR ${e.stack}`); }
  await b.close();
}
server.close();
reportCleanup(await cleanupAll());
