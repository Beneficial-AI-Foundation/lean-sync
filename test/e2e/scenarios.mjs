// End-to-end scenarios (docs/app-design.md §10, docs/net-design.md §10). Each scenario gets fresh
// devices (browser processes with their own profiles); devices are paired through the app's own
// pairing UI, over WebRTC. `kinds` is the list of browsers for the devices A, B, C...;
// test/e2e/run.mjs runs each scenario on each of its configurations.
import assert from 'node:assert/strict';
import { cpSync } from 'node:fs';
import { tempDir, removeDir } from '../proc.mjs';
import { startServer } from '../../dev/serve.mjs';
import { randomFile, sleep, sha, pair } from './lib.mjs';
import { parseCode, encodePayload, formatCode, offerTag } from '../../app/js/netcode.mjs';

const CH = 'chromium', FF = 'firefox', ESR = 'firefox-esr';
const files = (...fs) => Object.fromEntries(fs.map((f) => [f.name, f.sha]));

/** Open the devices A, B, ...; two devices are paired (A invites, B joins) unless `paired: false`. */
async function devices(ctx, kinds, opts = {}) {
  const out = [];
  for (let i = 0; i < kinds.length; i++) {
    const label = String.fromCharCode(65 + i);
    out.push(await ctx.open(kinds[i], label, opts[label] ?? {}));
  }
  if (out.length === 2 && opts.paired !== false) await pair(out[0], out[1]);
  return out;
}
/** The invitation with every candidate address replaced by an unreachable one (TEST-NET-1): the
 *  joining device's own checks then fail, as when the inviting device is behind a NAT. */
function unreachableOffer(code) {
  const x = parseCode(code, 'offer');
  return formatCode('offer', encodePayload({ ...x, kind: 'offer', cands: x.cands.map((c) => ({ ...c, addr: '192.0.2.1' })) }));
}
/** B's reply to the altered invitation, carrying the real invitation's tag (only the candidate
 *  addresses B was given differ, so A accepts it as the reply to its invitation). */
async function retag(reply, offer) {
  const r = parseCode(reply, 'answer');
  return formatCode('answer', encodePayload({ ...r, kind: 'answer', tag: await offerTag(parseCode(offer, 'offer').payload) }));
}
const connIds = async (D) => (await D.connections()).map((c) => c.id).sort().join();
async function expectSha(dev, path, f, version) {
  const d = await dev.download(path, version);
  assert.equal(d.sha, f.sha, `${dev.label}: downloaded ${path} has the bytes the test generated`);
  return d;
}
const setOnline = (dev, v) => dev.eval(`(() => { const c = document.querySelector('#online'); if (c.checked !== ${v}) c.click(); return true; })()`);
const waitPeers = (dev, n) => dev.waitFor(`document.querySelectorAll('#peers .peer[data-status="inSync"]').length >= ${n}`, 30000, `${n} peer(s) in sync`);
const recordOf = (dev) => dev.eval(`new Promise((res, rej) => { const r = indexedDB.open('leansync'); r.onsuccess = () => {
  const g = r.result.transaction('kv').objectStore('kv').get('record'); g.onsuccess = () => { const v = g.result; r.result.close();
  res({ hi: v.hi.toString(), lo: v.lo.toString(), state: btoa(String.fromCharCode(...v.state)) }); }; g.onerror = () => rej(g.error); }; })`);
const writeRecord = (dev, rec) => dev.eval(`new Promise((res, rej) => { const r = indexedDB.open('leansync'); r.onsuccess = () => {
  const bin = atob(${JSON.stringify(rec.state)}); const st = new Uint8Array(bin.length); for (let i = 0; i < bin.length; i++) st[i] = bin.charCodeAt(i);
  const tx = r.result.transaction('kv', 'readwrite'); tx.objectStore('kv').put({ v: 1, hi: BigInt(${JSON.stringify(rec.hi)}), lo: BigInt(${JSON.stringify(rec.lo)}), state: st }, 'record');
  tx.oncomplete = () => { r.result.close(); res(true); }; tx.onabort = () => rej(tx.error); }; })`);
const incomingCount = (dev) => dev.eval(`navigator.storage.getDirectory().then((r) => r.getDirectoryHandle('incoming')).then(async (d) => { let n = 0; for await (const _ of d.keys()) n++; return n; })`);

const blobsDir = `navigator.storage.getDirectory().then((r) => r.getDirectoryHandle('blobs'))`;

const blobSize = (dev, hx) => dev.eval(`navigator.storage.getDirectory().then((r) => r.getDirectoryHandle('blobs')).then((d) => d.getFileHandle(${JSON.stringify(hx)})).then((h) => h.getFile()).then((f) => f.size, () => -1)`);

export const scenarios = [
  {
    name: 'cold-load-many-files',
    kinds: [[CH], [FF]],
    async run(ctx, kinds) {
      // A cold load of N files must render the table a bounded number of times (it used to render
      // once per file while loading sizes: quadratic).
      const N = Number(process.env.COLD_LOAD_N ?? 3000);   // COLD_LOAD_N=20000 for the larger measurement
      const [A] = await devices(ctx, kinds);
      // plus DUP paths that all have the same content: sizes must be looked up once per hash
      const DUP = 500, same = randomFile('x', 16);
      const fs = Array.from({ length: N }, (_, i) => randomFile(`f${String(i).padStart(5, '0')}-${ctx.id}.txt`, 16))
        .concat(Array.from({ length: DUP }, (_, i) => ({ ...same, name: `same${String(i).padStart(4, '0')}-${ctx.id}.txt` })));
      const t0 = Date.now();
      await A.add(fs);
      await A.waitRows((rows) => rows.length === N + DUP && rows.every((r) => r.status === 'complete'), 300000, `${N + DUP} files added`);
      const tAdd = Date.now() - t0;
      await A.waitFor(`document.querySelector('#saving').dataset.state === 'saved'`, 30000);
      const t1 = Date.now();
      await A.page.reload();
      await A.waitFor(`window.leansync && window.leansync.phase === 'running' && document.querySelectorAll('#files tr').length === ${N + DUP}`, 120000, 'all rows');
      const tRows = Date.now() - t1;
      await A.waitFor(`[...document.querySelectorAll('#files td.size')].every((c) => c.textContent !== '')`, 120000, 'all sizes');
      const tLoad = Date.now() - t1;
      const renders = await A.eval('window.leansync.renders');
      ctx.note(`${N} files: adding took ${(tAdd / 1000).toFixed(1)} s; reload to all rows shown ${(tRows / 1000).toFixed(1)} s, to every size shown ${(tLoad / 1000).toFixed(1)} s, ${renders} table renders`);
      assert.ok(renders <= 30, `table rendered ${renders} times for ${N} files`);
      const lookups = await A.eval('window.__hashLookups');
      ctx.note(`${lookups} OPFS lookups for ${N + DUP} paths and ${N + 1} distinct contents`);
      assert.ok(lookups <= N + 1 + 20, `sizes looked up per hash, not per path (${lookups} lookups)`);
    },
  },
  {
    name: 'incoming-write-or-publish-failure',
    kinds: [[CH, CH], [FF, FF]],
    async run(ctx, kinds) {
      const [A, B] = await devices(ctx, kinds);
      await waitPeers(A, 1);
      // 1. A write error on B stops the transfer early: reported as a local failure (the peer is not
      //    blamed), sender told, no more credit. Every write fails until the disk is "freed".
      const big = randomFile(`w-${ctx.id}.bin`, 12 * 1024 * 1024);
      const sent0 = await A.eval('window.__net.sent');
      await B.eval('(window.__failWrite = 1000000)');
      await A.add([big]);
      await B.waitRows((rows) => rows.length === 1 && rows[0].status === 'localFailure', 20000, 'write failure reported as local');
      assert.match(await B.eval(`document.querySelector('#files td.status').textContent`), /could not be stored on this device/);
      await sleep(1000);
      const bytes = (await A.eval('window.__net.sent')) - sent0;
      // the host retries with a back-off (1 s, 2 s, ...): each attempt must stop within the credit window
      const attempts = (await B.eval('window.leansync.log')).filter((l) => /could not write it/.test(l)).length;
      ctx.note(`bytes sent by A for a 12 MiB file whose writes fail on B: ${bytes} over ${attempts} attempt(s)`);
      assert.ok(attempts >= 1 && bytes < attempts * 4.5 * 1024 * 1024, `the sender stopped early each time (${bytes} bytes, ${attempts} attempts)`);
      await waitFor(async () => (await incomingCount(B)) === 0, 10000, 'temp file removed after the write failure');
      // Space comes back: the next automatic retry fetches the file again, from the same peer, with
      // no reconnect (the peer was never marked as lacking it).
      // The index is saved, so no "not saved" banner; but the user who frees space can retry now
      // instead of waiting for the back-off (up to 60 s).
      await B.waitFor(`!!document.querySelector('#retry-store')`, 10000, 'Retry now for contents that could not be stored');
      assert.ok(!(await B.eval(`!!document.querySelector('#banner-save')`)), 'no unsaved-changes banner: the index is saved');
      await B.eval('(window.__failWrite = 0)');
      const retriesBefore = (await B.eval('window.leansync.log')).filter((l) => /retrying storage/.test(l)).length;
      await B.click('#retry-store');
      await B.waitFor(`window.leansync.log.filter((l) => /retrying storage/.test(l)).length > ${retriesBefore}`, 500, 'retrySave sent at once by Retry now');
      await B.waitFiles(files(big), 30000);
      assert.ok(!(await B.eval(`!!document.querySelector('#retry-store')`)), 'the action goes away once stored');
      await expectSha(B, big.name, big);
      assert.equal(await A.eval('window.__net.syncSeen'), 1, 'same link, no reconnect');
      // 2. Publishing fails (move) after the stream completed: the temp file is removed too.
      const small = randomFile(`p-${ctx.id}.txt`, 2000);
      await B.eval('(window.__failMove = 1000000)');
      await A.add([small]);
      await B.waitRows((rows) => rows.find((r) => r.path === small.name)?.status === 'localFailure', 20000, 'publish failure reported as local');
      assert.ok(await B.eval('window.__failMove') < 1000000, 'the injected move failure was exercised');
      await waitFor(async () => (await incomingCount(B)) === 0, 10000, 'temp file removed after the publish failure');
      await B.eval('(window.__failMove = 0)');
      await B.waitFiles(files(big, small), 30000);
      await expectSha(B, small.name, small);
    },
  },
  {
    name: 'empty-file-then-normal-file',
    kinds: [[CH, CH], [FF, FF], [CH, FF]],
    async run(ctx, kinds) {
      // A zero-byte file needs no credit; its transfer must still end and free the sender's single
      // serving slot, or every later file waits.
      const [A, B] = await devices(ctx, kinds);
      await waitPeers(A, 1);
      const e = { name: `empty-${ctx.id}.txt`, bytes: Buffer.alloc(0), sha: sha(Buffer.alloc(0)) };
      const n = randomFile(`after-empty-${ctx.id}.bin`, 300000);
      await A.add([e]);
      await B.waitFor(`document.querySelectorAll('#files tr').length === 1`, 20000, 'B sees the empty file');
      await A.add([n]);
      await B.waitFiles(files(e, n), 30000);
      await expectSha(B, e.name, e); await expectSha(B, n.name, n);
    },
  },
  {
    name: 'incoming-file-creation-fails-then-next-file',
    kinds: [[CH, CH], [FF, FF]],
    async run(ctx, kinds) {
      // B cannot create the temporary file for an incoming stream larger than the initial credit
      // window: B must report the failure (the file shows `localFailure`, never stuck on `fetching`)
      // and abort, so A serves the next file. Creation fails until the disk is "freed".
      const [A, B] = await devices(ctx, kinds);
      await waitPeers(A, 1);
      const big = randomFile(`big-${ctx.id}.bin`, 6 * 1024 * 1024), small = randomFile(`small-${ctx.id}.txt`, 1000);
      await B.eval('(window.__failCreate = 1000000)');
      await A.add([big]);
      await B.waitRows((rows) => rows.length === 1 && rows[0].status === 'localFailure', 15000, 'the failed transfer is reported');
      assert.ok(await B.eval('window.__failCreate') < 1000000, 'the injected failure was exercised');
      await B.eval('(window.__failCreate = 0)');
      await A.add([small]);
      await B.waitRows((rows) => rows.find((r) => r.path === small.name)?.status === 'complete', 20000, 'the next file arrives');
      await expectSha(B, small.name, small);
      await B.waitFiles(files(big, small), 30000);           // the parked file is retried with the back-off
      await expectSha(B, big.name, big);
    },
  },
  {
    name: 'peer-leaves-mid-fetch-row-updates',
    kinds: [[CH, CH], [FF, FF]],
    async run(ctx, kinds) {
      // A disconnect moves B's request to `waiting` without any index or blob change: the row must
      // follow, not keep saying `fetching`.
      const [A, B] = await devices(ctx, kinds);
      await waitPeers(A, 1);
      const f = randomFile(`mid-${ctx.id}.bin`, 1024 * 1024);
      await B.eval('(window.__holdClose = true)');                 // B's copy cannot be completed
      await A.add([f]);
      await B.waitRows((rows) => rows.length === 1 && rows[0].status === 'fetching', 20000, 'fetching');
      await setOnline(A, false);
      await B.waitRows((rows) => rows.length === 1 && rows[0].status === 'waiting', 10000, 'waiting after the peer left');
      await setOnline(A, true);
      await B.eval('window.__releaseCloses()');
      await B.waitFiles(files(f), 30000);
    },
  },
  {
    name: 'existing-blob-kept-when-replacement-fails',
    kinds: [[CH], [FF]],
    async run(ctx, kinds) {
      const [A] = await devices(ctx, kinds);
      const f = randomFile(`keep-${ctx.id}.bin`, 5000), g = randomFile(`dmg-${ctx.id}.bin`, 5000);
      await A.add([f, g]); await A.waitFiles(files(f, g));
      // 1. Intact copy + re-adding the same content while move() fails: the intact copy stays, no error.
      await A.eval('(window.__failMove = 1)');
      await A.add([f]);
      await sleep(1500);
      assert.equal(await A.eval('window.__failMove'), 1, 'no move was needed');
      assert.equal(await blobSize(A, f.sha), f.bytes.length, 'the intact copy is still there');
      assert.equal(await A.eval(`document.querySelectorAll('#messages .msg.error').length`), 0);
      await expectSha(A, f.name, f);
      // 2. Damaged copy + the replacing move() fails: the add is refused, and the old file is not deleted.
      await A.eval(`navigator.storage.getDirectory().then((r) => r.getDirectoryHandle('blobs')).then((d) => d.getFileHandle(${JSON.stringify(g.sha)})).then(async (h) => { const w = await h.createWritable(); await w.write(new Uint8Array([1, 2, 3])); await w.close(); return true; })`);
      await A.add([g]);
      await A.waitFor(`[...document.querySelectorAll('#messages .msg.error')].some((m) => m.textContent.includes(${JSON.stringify(g.name)}))`, 10000, 'add refused');
      assert.equal(await blobSize(A, g.sha), 3, 'the old file was not deleted before the failed move');
      await A.add([g]);                                             // no fault now: replaced
      await A.waitFor(`navigator.storage.getDirectory().then((r) => r.getDirectoryHandle('blobs')).then((d) => d.getFileHandle(${JSON.stringify(g.sha)})).then((h) => h.getFile()).then((x) => x.size === ${g.bytes.length})`, 10000, 'replaced');
      await expectSha(A, g.name, g);
    },
  },
  {
    name: 'no-network-except-paired-devices',
    kinds: [[CH, FF], [FF, CH]],
    async run(ctx, kinds) {
      // The app talks to nothing but the devices the user paired (and the STUN servers of the
      // settings): no WebSocket, no server endpoint, no connection before the user pairs, and no
      // URL parameter changes that (the old `?relay=` finding).
      const before = ctx.server.stats.notFound.length;
      const A = await ctx.open(kinds[0], 'A', { extraQuery: `&relay=${encodeURIComponent('ws://127.0.0.1:1/relay')}&room=x&stun=stun:192.0.2.9` });
      const B = await ctx.open(kinds[1], 'B');
      await sleep(2000);
      for (const D of [A, B]) {
        const n = await D.eval(`({ sockets: window.__net.sockets, es: window.__net.eventSources, foreign: window.__net.foreignFetch, pcs: window.__net.pcs })`);
        assert.deepEqual(n, { sockets: 0, es: 0, foreign: 0, pcs: 0 }, `${D.label}: no network use before pairing`);
      }
      await pair(A, B);
      const f = randomFile(`n-${ctx.id}.txt`, 3000);
      await A.add([f]); await B.waitFiles(files(f));
      for (const D of [A, B]) {
        assert.equal(await D.eval('window.__net.sockets'), 0, `${D.label}: no WebSocket`);
        assert.equal(await D.eval('window.__net.foreignFetch'), 0);
        assert.deepEqual([...new Set(await D.eval('window.__net.ice'))], ['[]'], `${D.label}: ICE servers only from the setting (empty here)`);
      }
      const extra = ctx.server.stats.notFound.slice(before).filter((u) => !/favicon/.test(u));
      assert.deepEqual(extra, [], 'no request for anything but the app\'s own files');
      ctx.note(`connections made: A ${await A.eval('window.__net.pcs')}, B ${await B.eval('window.__net.pcs')} (B: one per renewed reply)`);
    },
  },
  {
    name: 'record-request-error-not-acknowledged',
    kinds: [[CH, CH], [FF, FF]],
    async run(ctx, kinds) {
      // A request-level IndexedDB error (not a transaction abort): the transaction must abort and
      // the save must never be acknowledged; the stored record must be unchanged.
      const [A, B] = await devices(ctx, kinds);
      const f = randomFile(`req-${ctx.id}.txt`, 500), g = randomFile(`keep-${ctx.id}.txt`, 500);
      await A.add([f, g]); await B.waitFiles(files(f, g));
      await A.waitFor(`document.querySelector('#saving').dataset.state === 'saved'`, 10000);
      const before = await recordOf(A);
      await A.eval('(window.__idbReqFail = true)');
      await A.click(A.rowSel(f.name, 'delete'));
      await A.waitFor(`!!document.querySelector('#banner-save')`, 20000, 'save-failed banner');
      await sleep(2500);
      assert.ok(await A.eval('window.__idbReqFailed') >= 1, 'the request-level error was exercised');
      assert.deepEqual(await recordOf(A), before, 'the stored record is unchanged');
      assert.ok(await A.eval(`!!document.querySelector('#banner-save') && document.querySelector('#saving').dataset.state === 'failed'`), 'still shown as not saved');
      assert.ok((await B.rows()).some((r) => r.path === f.name), 'the unsaved deletion did not reach B');
      assert.ok(!(await A.eval('window.leansync.log')).some((l) => /saving works again/.test(l)), 'never acknowledged');
      await A.eval('(window.__idbReqFail = false)');
      await A.eval(`(document.querySelector('#retry-save')?.click(), true)`);   // an automatic retry may already have succeeded
      await B.waitFiles(files(g));
      assert.notDeepEqual(await recordOf(A), before);
    },
  },
  {
    name: 'peer-edit-during-upload-becomes-conflict',
    kinds: [[CH, CH], [FF, FF], [CH, FF]],
    async run(ctx, kinds) {
      // The user replaces x on A while B's replacement of x arrives during A's upload. A's add
      // supersedes only the version A showed when the user acted, so B's edit must survive as a
      // conflict, not be silently removed.
      const [A, B] = await devices(ctx, kinds);
      const x0 = randomFile(`x-${ctx.id}.txt`, 800);
      await A.add([x0]); await B.waitFiles(files(x0));
      const x1 = randomFile(x0.name, 900), x2 = randomFile(x0.name, 1000);
      await A.eval('(window.__holdClose = true)');
      await A.add([x1]);                                             // user action on A; the store is held
      await A.waitFor('window.__held.length > 0', 10000, 'A is storing x1');
      await B.add([x2]);                                             // B replaces x meanwhile
      await A.waitRows((rows) => rows.length === 1 && rows[0].hashes.join() === sha(x2.bytes), 30000, 'A shows B\'s version');
      assert.ok(await A.eval('window.__releaseCloses()') >= 1);
      const conflict = (rows) => rows.length === 1 && rows[0].status === 'conflicted' && rows[0].versions.length === 2;
      for (const D of [A, B]) {
        const rows = await D.waitRows(conflict, 30000, 'x1 and x2 in conflict');
        assert.deepEqual(new Set(rows[0].versions.map((v) => v.hex)), new Set([sha(x1.bytes), sha(x2.bytes)]));
      }
    },
  },
  {
    name: 'damaged-or-missing-blob-recovers',
    kinds: [[CH, CH], [FF, FF]],
    async run(ctx, kinds) {
      const [A, B] = await devices(ctx, kinds);
      const f = randomFile(`dmg-${ctx.id}.bin`, 3000), g = randomFile(`gone-${ctx.id}.bin`, 3000);
      await A.add([f, g]); await B.waitFiles(files(f, g));
      // 1. A damaged copy is replaced when the same content is added again.
      await A.eval(`${blobsDir}.then((d) => d.getFileHandle(${JSON.stringify(f.sha)})).then(async (h) => { const w = await h.createWritable(); await w.write(new Uint8Array([1, 2, 3])); await w.close(); return true; })`);
      await A.add([f]);
      await A.waitFor(`${blobsDir}.then((d) => d.getFileHandle(${JSON.stringify(f.sha)})).then((h) => h.getFile()).then((x) => x.size === ${f.bytes.length})`, 20000, 'the stored copy replaced');
      await expectSha(A, f.name, f);
      assert.ok(!(await A.eval(`[...document.querySelectorAll('#messages .msg.error')].length`)), 'no error shown');
      // 2. A vanished copy is reported lost when a download finds it missing, and fetched again.
      await A.eval(`${blobsDir}.then((d) => d.removeEntry(${JSON.stringify(g.sha)})).then(() => true)`);
      await A.click(A.rowSel(g.name, 'download'));
      await A.waitFor(`[...document.querySelectorAll('#messages .msg.error')].some((m) => m.textContent.includes('missing'))`, 10000, 'missing-copy message');
      await A.waitFor(`${blobsDir}.then((d) => d.getFileHandle(${JSON.stringify(g.sha)})).then(() => true, () => false)`, 30000, 'fetched again from B');
      await A.waitFiles(files(f, g));
      await expectSha(A, g.name, g);
    },
  },
  {
    name: 'add-replace-delete-download',
    kinds: [[CH, CH], [FF, FF], [ESR, FF], [CH, FF]],
    async run(ctx, kinds) {
      const [A, B] = await devices(ctx, kinds);
      const f1 = randomFile(`notes-${ctx.id}.txt`, 2000), f2 = randomFile(`photo ünï-${ctx.id}.bin`, 700000);
      await A.add([f1, f2]);
      await A.waitFiles(files(f1, f2));
      await B.waitFiles(files(f1, f2));
      await expectSha(B, f1.name, f1); await expectSha(B, f2.name, f2); await expectSha(A, f2.name, f2);
      const f1b = randomFile(f1.name, 5000);                  // replace: same name, new content
      await A.add([f1b]);
      await B.waitRows((rows) => rows.length === 2 && rows.every((r) => r.status === 'complete'), 30000);
      await waitFor(async () => (await B.download(f1.name)).sha === f1b.sha, 30000, 'B has the replaced content');
      await A.click(A.rowSel(f2.name, 'delete'));
      await B.waitFiles(files(f1b));
      await A.waitFiles(files(f1b));
    },
  },
  {
    name: 'offline-edits-both-sides',
    kinds: [[CH, CH], [FF, FF], [FF, CH]],
    async run(ctx, kinds) {
      const [A, B] = await devices(ctx, kinds);
      const base = randomFile(`base-${ctx.id}.txt`, 3000);
      await A.add([base]); await B.waitFiles(files(base));
      const ids = [await connIds(A), await connIds(B)];
      await setOnline(A, false); await setOnline(B, false);
      const a = randomFile(`from-A-${ctx.id}.txt`, 4000), b = randomFile(`from-B-${ctx.id}.bin`, 90000);
      await A.add([a]); await B.add([b]);
      await B.click(B.rowSel(base.name, 'delete'));
      await A.waitFiles(files(base, a)); await B.waitFiles(files(b));
      await sleep(500);
      assert.deepEqual((await A.rows()).map((r) => r.path).sort(), [a.name, base.name].sort(), 'offline A did not get B\'s edits');
      await setOnline(A, true); await setOnline(B, true);
      await A.waitFiles(files(a, b)); await B.waitFiles(files(a, b));
      await expectSha(A, b.name, b); await expectSha(B, a.name, a);
      assert.deepEqual([await connIds(A), await connIds(B)], ids, 'offline and back online on the same connection: no re-pairing');
    },
  },
  {
    name: 'conflict-keep-one-and-keep-both',
    kinds: [[CH, CH], [FF, FF], [CH, FF]],
    async run(ctx, kinds) {
      const [A, B] = await devices(ctx, kinds);
      await setOnline(A, false); await setOnline(B, false);
      const name = `plan-${ctx.id}.md`, other = `report-${ctx.id}.txt`;
      const va = randomFile(name, 1500), vb = randomFile(name, 2500), oa = randomFile(other, 100), ob = randomFile(other, 200);
      await A.add([va, oa]); await B.add([vb, ob]);
      await A.waitFiles(files(va, oa)); await B.waitFiles(files(vb, ob));
      await setOnline(A, true); await setOnline(B, true);
      const conflicted = (rows) => rows.length === 2 && rows.every((r) => r.status === 'conflicted' && r.versions.length === 2 && r.versions.every((v) => v.status === 'complete'));
      await A.waitRows(conflicted, 30000, 'two conflicts with both versions present');
      const rowsB = await B.waitRows(conflicted, 30000, 'two conflicts on B');
      // Keep B's version of `name`, chosen on A.
      const hexB = sha(vb.bytes);
      assert.ok(rowsB.find((r) => r.path === name).versions.some((v) => v.hex === hexB), 'version hash is the SHA-256 of the bytes');
      await A.click(A.rowSel(name, 'keep', hexB));
      // Keep both for `other`, chosen on B.
      await B.click(B.rowSel(other, 'keep-both'));
      const third = other.replace('.txt', ' (2).txt');
      for (const D of [A, B]) {
        await D.waitRows((rows) => rows.length === 3 && rows.every((r) => r.status === 'complete'), 30000, 'resolved');
        await expectSha(D, name, vb);
      }
      const got = new Set([(await A.download(other)).sha, (await A.download(third)).sha]);
      assert.deepEqual(got, new Set([oa.sha, ob.sha]), 'keep both: both contents kept under two names');
    },
  },
  {
    name: 'edit-vs-delete',
    kinds: [[CH, CH], [FF, FF], [FF, CH]],
    async run(ctx, kinds) {
      const [A, B] = await devices(ctx, kinds);
      const x = randomFile(`x-${ctx.id}.txt`, 1000);
      await A.add([x]); await B.waitFiles(files(x));
      await setOnline(A, false); await setOnline(B, false);
      const x2 = randomFile(x.name, 1200);
      await A.add([x2]);                                         // edit on A
      await B.click(B.rowSel(x.name, 'delete'));                 // concurrent delete on B
      await B.waitRows((rows) => rows.length === 0, 10000, 'deleted on B');
      await setOnline(A, true); await setOnline(B, true);
      await A.waitFiles(files(x2)); await B.waitFiles(files(x2));
      await expectSha(B, x.name, x2);
    },
  },
  {
    name: 'three-device-chain',
    kinds: [[CH, CH, CH], [FF, FF, FF], [CH, FF, CH]],
    async run(ctx, kinds) {
      const [A, B, C] = await devices(ctx, kinds);
      await pair(A, B); await pair(B, C);                // A and C are never paired
      const f = randomFile(`chain-${ctx.id}.bin`, 400000), g = randomFile(`back-${ctx.id}.txt`, 777);
      await A.add([f]);
      await C.waitFiles(files(f));                       // A -> B -> C, index and content
      await expectSha(C, f.name, f);
      assert.equal((await A.connections()).length, 1, 'A is connected to B only');
      assert.equal((await C.connections()).length, 1, 'C is connected to B only');
      await C.add([g]);
      await A.waitFiles(files(f, g));
      await expectSha(A, g.name, g);
    },
  },
  {
    name: 'disconnect-mid-transfer-and-resume',
    kinds: [[CH, CH], [FF, FF], [CH, FF]],
    async run(ctx, kinds) {
      const [A, B] = await devices(ctx, kinds);
      await waitPeers(A, 1);
      const big = randomFile(`big-${ctx.id}.bin`, 6 * 1024 * 1024);
      await A.eval('(window.__net.cutAfter = window.__net.sent + 2 * 1024 * 1024, true)');   // A's channel closes mid-transfer
      await A.add([big]);
      await B.waitFor(`[...document.querySelectorAll('#files tr')].some((t) => t.dataset.status !== 'complete')`, 30000, 'B sees the file, content not yet complete');
      await B.waitFiles(files(big), 90000);
      await expectSha(B, big.name, big);
      assert.equal(await A.eval('window.__net.cuts'), 1, 'the link was cut mid-transfer');
      assert.ok(await A.eval('window.__net.syncSeen') >= 2, 'a new link on the same connection, no re-pairing');
      assert.equal((await A.connections()).length, 1);
      await waitFor(async () => (await incomingCount(B)) === 0, 10000, 'the partial file was discarded');
    },
  },
  {
    name: 'corrupted-blob-and-garbage-message',
    kinds: [[CH, CH], [FF, CH]],
    async run(ctx, kinds) {
      const [A, B] = await devices(ctx, kinds);
      await waitPeers(A, 1);
      await A.eval('(window.__net.corruptNext = true)');        // flip a byte of A's next blob frame
      const f = randomFile(`c-${ctx.id}.bin`, 50000);
      await A.add([f]);
      // The corrupted copy must never show as complete: B marks the content lacking at A for this session.
      await B.waitRows((rows) => rows.length === 1 && rows[0].status === 'waiting', 30000, 'waiting after a corrupted transfer');
      await sleep(1000);
      assert.equal((await B.rows())[0].status, 'waiting');
      assert.equal(await A.eval('window.__net.corrupted'), 1, 'the corruption was injected');
      assert.equal(await A.eval('window.__netGarbage()'), true);                // Lean closes the session (protocol error)
      await B.waitFiles(files(f), 60000);                                        // new session: fetched again, verified
      await expectSha(B, f.name, f);
      const log = (await B.eval('window.leansync.log')).join('\n');
      assert.match(log, /failed verification/); assert.match(log, /protocol error|closing peer/);
    },
  },
  {
    name: 'storage-failure',
    kinds: [[CH, CH], [FF, CH], [ESR, FF]],
    async run(ctx, kinds) {
      const firefox = kinds[0] !== CH;
      const [A, B] = await devices(ctx, kinds, { A: { prefs: firefox ? { 'dom.quotaManager.temporaryStorage.fixedLimit': 20480 } : undefined } });
      const keep = randomFile(`keep-${ctx.id}.txt`, 1000), gone = randomFile(`gone-${ctx.id}.txt`, 1000);
      await A.add([keep, gone]); await B.waitFiles(files(keep, gone));
      // 1. OPFS failure (real in both browsers): fill the quota, then add a file.
      if (firefox) {
        ctx.note('A: OPFS and IndexedDB failures are real (Firefox quota pref, storage filled with incompressible data)');
        await A.eval(`(async () => { const root = await navigator.storage.getDirectory(); const chunk = new Uint8Array(256 * 1024);
          let i = 0;
          for (let size = chunk.length; size >= 16; size >>= 2) {           // fill to the last few bytes
            for (;;) {
              for (let j = 0; j < size; j += 65536) crypto.getRandomValues(chunk.subarray(j, Math.min(size, j + 65536)));
              const name = 'filler-' + (i++);
              try { const fh = await root.getFileHandle(name, { create: true }); const w = await fh.createWritable(); await w.write(chunk.subarray(0, size)); await w.close(); }
              catch (e) { try { await root.removeEntry(name); } catch {} break; }
            }
          } return i; })()`);
      } else {
        ctx.note('A: OPFS failure is real (CDP quota override); the IndexedDB record failure is injected by the test driver (Chromium ignores the override for IndexedDB)');
        const origin = ctx.server.url;
        const usage = await A.eval('navigator.storage.estimate().then((e) => e.usage)');
        await A.page.cdp('Storage.overrideQuotaForOrigin', { origin, quotaSize: usage + 64 * 1024 });
      }
      const tooMuch = randomFile(`nope-${ctx.id}.bin`, 1024 * 1024);
      await A.add([tooMuch]);
      await A.waitFor(`[...document.querySelectorAll('#messages .msg.error')].some((m) => m.textContent.includes(${JSON.stringify(tooMuch.name)}))`, 20000, 'add refused with a message');
      assert.ok(!(await A.rows()).some((r) => r.path === tooMuch.name), 'the refused file is not listed');
      // 2. Record failure. Chromium: injected. Firefox: real; the record must grow to fail (a record
      //    rewritten in place fits in pages IndexedDB already owns), so B adds many files first and
      //    A's persist of the merged state hits the quota on every retry.
      if (!firefox) await A.eval('(window.__idbFail = true)');
      else {
        const many = Array.from({ length: 150 }, (_, i) => randomFile(`${'long-name-'.repeat(6)}${i}-${ctx.id}.txt`, 64));
        await B.add(many);
      }
      if (!firefox) await A.click(A.rowSel(gone.name, 'delete'));
      await A.waitFor(`!!document.querySelector('#banner-save') && document.querySelector('#saving').dataset.state === 'failed'`, 30000, 'save-failed banner');
      if (firefox) await A.click(A.rowSel(gone.name, 'delete'));      // a change made while saving fails
      const t0 = Date.now();
      await sleep(4000);                                              // several automatic retries (1 s, 2 s back-off)
      assert.ok(await A.eval(`!!document.querySelector('#banner-save') && document.querySelector('#saving').dataset.state === 'failed'`), 'banner still shown while saving fails');
      assert.ok((await B.rows()).some((r) => r.path === gone.name), 'B did not receive the unsaved deletion');
      const aLog = await A.eval('window.leansync.log');
      const failures = aLog.filter((l) => /persist \d+ failed/.test(l)).length;
      const retries = aLog.filter((l) => /retrying storage/.test(l)).length;
      assert.ok(failures >= 2, `the save was retried and failed again (${failures} failures)`);
      // Lean holds a failed save until the host's retrySave: one write per retry, not one per event
      // (before, 131-139 writes failed in about a second while the 150 files arrived).
      assert.ok(failures <= retries + 1, `no write without a retrySave (${failures} failures, ${retries} retries)`);
      const statuses = {}; for (const r of await A.rows()) statuses[r.status] = (statuses[r.status] ?? 0) + 1;
      ctx.note(`A: ${failures} failed saves and ${retries} retries in ${((Date.now() - t0) / 1000).toFixed(1)} s of failing storage; rows ${JSON.stringify(statuses)}`);
      if (firefox) assert.ok(!statuses.waiting, 'contents that could not be stored are not blamed on the peer');
      // 3. Recovery.
      if (firefox) await A.eval(`(async () => { const root = await navigator.storage.getDirectory(); const names = []; for await (const n of root.keys()) if (n.startsWith('filler-')) names.push(n); for (const n of names) await root.removeEntry(n); return names.length; })()`);
      else { await A.eval('(window.__idbFail = false)'); await A.page.cdp('Storage.overrideQuotaForOrigin', { origin: ctx.server.url }); }
      await A.eval(`(document.querySelector('#retry-save')?.click(), true)`);   // an automatic retry may already have succeeded
      await A.waitFor(`!document.querySelector('#banner-save') && document.querySelector('#saving').dataset.state === 'saved'`, 30000, 'banner gone after a successful save');
      await B.waitRows((rows) => !rows.some((r) => r.path === gone.name) && rows.some((r) => r.path === keep.name), 30000, 'B gets the deletion once it is saved');
      // Contents that could not be stored during the failure are fetched again after the retry,
      // in the same session.
      await A.waitRows((rows) => rows.length > 0 && rows.every((r) => r.status === 'complete'), 60000, 'every content stored after recovery');
      const failed = firefox ? null : await A.eval('window.__idbFailed');
      if (!firefox) assert.ok(failed >= 1, 'the injected failure was exercised');
    },
  },
  {
    name: 'reload-and-kill-mid-session',
    kinds: [[CH, CH], [FF, FF], [CH, FF]],
    async run(ctx, kinds) {
      const [A, B] = await devices(ctx, kinds);
      await waitPeers(A, 1);
      const big = randomFile(`r-${ctx.id}.bin`, 5 * 1024 * 1024);
      await A.add([big]);
      await B.waitFor(`[...document.querySelectorAll('#files tr')].length === 1`, 30000, 'B sees the file');
      await B.reload();                                           // reload while the content is arriving
      await pair(A, B);                                           // a reload ends the connection: pair again
      await B.waitFiles(files(big), 60000);
      await expectSha(B, big.name, big);
      // Kill A's browser right after an add (mid-persist or just after): on restart the add is
      // either fully there or not there, never shown complete without its bytes.
      const k = randomFile(`k-${ctx.id}.txt`, 3000);
      await A.add([k]);
      await sleep(30);
      await A.kill();
      await A.reopen();
      await pair(A, B);
      const rows = await A.waitRows((rs) => rs.some((r) => r.path === big.name), 20000, 'the file list after restart');
      for (const r of rows) assert.equal(r.status, 'complete', `${r.path} after the crash`);
      const after = randomFile(`after-${ctx.id}.txt`, 500);
      await A.add([after]);
      const want = rows.some((r) => r.path === k.name) ? files(big, k, after) : files(big, after);
      ctx.note(`kill right after add: the add ${rows.some((r) => r.path === k.name) ? 'survived' : 'was lost (never acknowledged)'}`);
      await A.waitFiles(want); await B.waitFiles(want);
    },
  },
  {
    name: 'second-tab-lock',
    kinds: [[CH, CH], [FF, FF]],
    async run(ctx, kinds) {
      const [A, B] = await devices(ctx, kinds);
      const tab2 = await A.browser.newPage(A.url);
      await waitFor(async () => (await tab2.eval(`window.leansync && window.leansync.phase`)) === 'locked', 20000, 'second tab locked');
      assert.equal(await tab2.eval(`!document.querySelector('#locked').hidden && document.querySelector('#app').hidden`), true, 'second tab shows the lock message and nothing else');
      const f = randomFile(`t-${ctx.id}.txt`, 100);
      await A.add([f]);
      await B.waitFiles(files(f));
      assert.equal(await tab2.eval(`window.leansync.phase`), 'locked');
      await tab2.close();
    },
  },
  {
    name: 'startup-failure-and-reset',
    kinds: [[CH, CH], [FF, CH]],
    async run(ctx, kinds) {
      const [A, B] = await devices(ctx, kinds);
      const f = randomFile(`s-${ctx.id}.txt`, 1500);
      await A.add([f]); await B.waitFiles(files(f));
      const before = await A.eval('window.leansync.replica');
      await writeRecord(A, { ...(await recordOf(A)), state: btoa('\x01\x01garbage') });   // damage the stored index
      await A.page.reload();
      await A.waitFor(`document.querySelector('#fatal').dataset.phase === 'startupFailed'`, 30000, 'start-up failure screen');
      await A.click('#retry-start');                              // retry keeps failing, changes nothing
      await A.waitFor(`document.querySelector('#fatal').dataset.phase === 'startupFailed'`, 30000);
      await A.click('#reset');
      await A.waitFor(`document.querySelector('#confirm').open`, 5000, 'confirmation dialog');
      assert.match(await A.eval(`document.querySelector('#confirm').textContent`), /lose/);
      await A.click('#confirm-ok');
      await A.waitFor(`window.leansync.phase === 'running'`, 30000);
      assert.notEqual(await A.eval('window.leansync.replica'), before, 'new identity');
      await pair(A, B);
      await A.waitFiles(files(f));                                // refilled from B
    },
  },
  {
    name: 'rollback-detected-then-new-identity',
    kinds: [[CH, CH], [FF, FF], [FF, CH]],
    async run(ctx, kinds) {
      const [A, B] = await devices(ctx, kinds);
      const f = randomFile(`f-${ctx.id}.txt`, 1000);
      await A.add([f]); await B.waitFiles(files(f));
      const old = await recordOf(A);                              // a "backup" of A's storage
      const g = randomFile(`g-${ctx.id}.txt`, 1000);
      await A.add([g]); await B.waitFiles(files(f, g));
      await setOnline(A, false);
      await writeRecord(A, old);                                  // restore the backup: A's storage rolls back
      await A.page.reload();
      await A.waitFor(`window.leansync && window.leansync.phase === 'running'`, 30000);
      await pair(A, B);                                           // a reload ends the pairing; B's state reveals the rollback
      await A.waitFor(`!!document.querySelector('#banner-rollback')`, 30000, 'rollback banner');
      assert.equal(await A.eval(`document.querySelector('#add-button').disabled`), true, 'editing blocked');
      const replicaBefore = await A.eval('window.leansync.replica');
      await A.click('#new-identity');
      await A.waitFor(`document.querySelector('#confirm').open`, 5000);
      const text = await A.eval(`document.querySelector('#confirm').textContent`);
      assert.match(text, /You keep/); assert.match(text, /You lose/);
      await A.click('#confirm-ok');
      await A.waitFor(`window.leansync.phase === 'running' && !document.querySelector('#banner-rollback')`, 30000, 'restarted');
      assert.notEqual(await A.eval('window.leansync.replica'), replicaBefore);
      await A.waitFiles(files(f, g));                             // same pairing: the restart re-links without re-pairing
      const h = randomFile(`h-${ctx.id}.txt`, 10);
      await A.add([h]);
      await B.waitFiles(files(f, g, h));
    },
  },
  {
    name: 'same-replica-id-refused',
    kinds: [[CH], [FF]],
    async run(ctx, kinds) {
      const [A] = await devices(ctx, [kinds[0]]);
      const f = randomFile(`own-${ctx.id}.txt`, 100);
      await A.add([f]); await A.waitFiles(files(f));
      await A.waitFor(`document.querySelector('#saving').dataset.state === 'saved'`, 10000);
      await A.close();
      const copy = tempDir('lsync-copy-');
      cpSync(A.profile, copy, { recursive: true, filter: (src) => !/Singleton(Lock|Socket|Cookie)$/.test(src) });   // a second profile restored from the same storage
      ctx.cleanup.push(async () => removeDir(copy));
      await A.reopen();
      const A2 = await ctx.open(kinds[0], 'A2', { profile: copy, stun: null });
      await pair(A, A2, { linked: false });                       // the devices pair; the host HELLO check refuses the link
      for (const D of [A, A2]) await D.waitFor(`[...document.querySelectorAll('#banners .banner')].some((b) => b.textContent.includes('own identity'))`, 30000, 'refused banner');
      await sleep(1500);
      assert.equal(await A.eval(`document.querySelectorAll('#peers .peer').length`), 0, 'no session');
      ctx.note(`links opened and refused at HELLO so far: ${await A.eval('window.__net.syncSeen')} (re-opened with a growing back-off)`);
    },
  },
  {
    name: 'trap-mid-sync-reinstantiates',
    kinds: [[CH, CH], [FF, FF]],
    async run(ctx, kinds) {
      const [A, B] = await devices(ctx, kinds);
      await waitPeers(A, 1);
      const fs = Array.from({ length: 12 }, (_, i) => randomFile(`t${i}-${ctx.id}.bin`, 200000));
      await B.eval('(window.__trap.next = 1)');                   // B's next call into the engine traps for real
      await A.add(fs);                                            // ... which is the arrival of A's new index
      await B.waitFiles(files(...fs), 90000);
      const d = await B.eval(`({ instances: window.leansync.instances, traps: window.leansync.traps, fired: window.__trap.fired, phase: window.leansync.phase })`);
      assert.deepEqual(d, { instances: 2, traps: 1, fired: 1, phase: 'running' }, 'one real trap, one new instance, the dead one never called again');
      assert.ok(await B.eval(`!!document.querySelector('#banner-restart')`), 'restart shown to the user');
      for (const f of fs.slice(0, 3)) await expectSha(B, f.name, f);
    },
  },
  {
    name: 'trap-at-startup-does-not-loop',
    kinds: [[CH], [FF]],
    async run(ctx, kinds) {
      const [A] = await devices(ctx, kinds);
      const f = randomFile(`st-${ctx.id}.txt`, 100);
      await A.add([f]); await A.waitFiles(files(f));
      await A.eval(`(sessionStorage.setItem('__trapAlways', '1'), true)`);   // every engine call traps, from page load on
      await A.page.reload();
      await A.waitFor(`document.querySelector('#fatal').dataset.phase === 'failed'`, 30000, 'failure screen');
      await sleep(3000);
      const d = await A.eval(`({ instances: window.leansync.instances, fired: window.__trap.fired, phase: window.leansync.phase })`);
      assert.deepEqual(d, { instances: 1, fired: 1, phase: 'failed' }, 'stopped after one start-up trap, no retry loop');
      await A.eval(`(sessionStorage.removeItem('__trapAlways'), window.__trap.always = false, true)`);
      await A.click('#retry-start');
      await A.waitFor(`window.leansync.phase === 'running'`, 30000, 'user retry works');
      await A.waitFiles(files(f));
    },
  },
  {
    name: 'repeated-edits-heap-bound',
    kinds: [[CH], [FF]],
    async run(ctx, kinds) {
      const [A] = await devices(ctx, kinds);
      const f = randomFile(`loop-${ctx.id}.txt`, 4000);
      const cycle = async () => {
        await A.add([f]); await A.waitRows((r) => r.length === 1 && r[0].status === 'complete', 10000);
        await A.click(A.rowSel(f.name, 'delete')); await A.waitRows((r) => r.length === 0, 10000);
      };
      for (let i = 0; i < 40; i++) await cycle();
      const h40 = await A.eval('window.leansync.heapBytes');
      for (let i = 40; i < 200; i++) await cycle();
      const h200 = await A.eval('window.leansync.heapBytes');
      ctx.note(`wasm heap ${h40} -> ${h200} bytes between cycles 40 and 200`);
      assert.ok(h200 - h40 <= 1024 * 1024, `heap grew by ${h200 - h40} bytes (bound 1 MiB)`);
    },
  },
  {
    name: 'file-size-limit-and-folder-drop',
    kinds: [[CH], [FF]],
    async run(ctx, kinds) {
      const [A] = await devices(ctx, kinds);
      await A.add([{ name: `huge-${ctx.id}.bin`, zeroMiB: 256 }]);    // 256 MiB + 1 byte
      await A.waitFor(`[...document.querySelectorAll('#messages .msg.error')].some((m) => m.textContent.includes('256 MB'))`, 20000, 'size-limit message');
      assert.equal((await A.rows()).length, 0);
      // A folder drop (synthetic: a DataTransfer whose item is a directory cannot be built from script in
      // every browser, so this checks the message path with a stub entry).
      const msg = await A.eval(`(() => { const ev = new Event('drop', { cancelable: true }); ev.dataTransfer = { items: [{ kind: 'file', webkitGetAsEntry: () => ({ isDirectory: true, name: 'photos' }), getAsFile: () => null }] };
        document.dispatchEvent(ev); return [...document.querySelectorAll('#messages .msg.error')].map((m) => m.textContent).join('|'); })()`);
      assert.match(msg, /photos.*folder/);
    },
  },
  // ------------------------------------------------------------------ pairing (docs/net-design.md §10)
  {
    name: 'pair-by-text',
    kinds: [[CH, CH], [FF, FF], [CH, FF], [FF, CH], [ESR, CH], [CH, ESR], [ESR, FF]],
    async run(ctx, kinds) {
      const [A, B] = await devices(ctx, kinds, { paired: false });
      const { offer, reply } = await pair(A, B);
      const o = parseCode(offer, 'offer'), r = parseCode(reply, 'answer');
      ctx.note(`invitation ${offer.length} chars (${o.cands.length} candidate(s)), reply ${reply.length} chars`);
      assert.ok([...o.cands, ...r.cands].every((c) => c.type === 'host'), 'no STUN configured: host candidates only');
      const a = randomFile(`ta-${ctx.id}.txt`, 3000), b = randomFile(`tb-${ctx.id}.bin`, 200000);
      await A.add([a]); await B.add([b]);
      await A.waitFiles(files(a, b)); await B.waitFiles(files(a, b));
      await expectSha(A, b.name, b); await expectSha(B, a.name, a);
      await A.waitFor(`[...document.querySelectorAll('#connections li .label')].some((e) => e.textContent === 'B')`, 10000, 'B listed by its name');
      await B.waitFor(`[...document.querySelectorAll('#connections li .label')].some((e) => e.textContent === 'A')`, 10000, 'A listed by its name');
    },
  },
  {
    name: 'pair-by-qr-fake-camera',
    kinds: [[CH, FF], [FF, CH], [CH, CH], [FF, FF]],
    async run(ctx, kinds) {
      const [A, B] = await devices(ctx, kinds, { paired: false });
      // The vendored decoder reads the QR the app draws, exactly (same decoder as the scanning loop).
      await A.click('#invite');
      const code = await A.waitFor(`document.querySelector('#pair-code')?.dataset.code`, 20000, 'invitation');
      const read = await A.eval(`(async () => { const { decodeQR } = await import('./vendor/qr/decode.js'); const c = document.querySelector('#pair-qr');
        return decodeQR(c.getContext('2d').getImageData(0, 0, c.width, c.height)); })()`);
      assert.equal(read, code, 'the rendered QR decodes to the code shown');
      await A.closeDialog();
      // Both codes go through the app's camera scanning loop (fake camera showing the other screen's QR).
      await pair(A, B, { via: 'qr' });
      assert.ok(await A.eval('window.__fakeCamera.starts') >= 1 && await B.eval('window.__fakeCamera.starts') >= 1, 'both scanned');
      const f = randomFile(`qr-${ctx.id}.txt`, 1000);
      await A.add([f]); await B.waitFiles(files(f));
    },
  },
  {
    name: 'pairing-codes-rejected',
    kinds: [[CH, FF, CH], [FF, CH, FF]],
    async run(ctx, kinds) {
      const [A, B, C] = await devices(ctx, kinds);
      const tryCode = async (D, text, reason, re) => {
        await D.eval(`(() => { const e = document.querySelector('#pair-error'); if (e) { e.hidden = true; e.dataset.reason = ''; } return true; })()`);
        await D.pasteCode(text);
        const e = await D.waitFor(`(() => { const e = document.querySelector('#pair-error'); return e && !e.hidden && e.dataset.reason ? { text: e.textContent, reason: e.dataset.reason } : null; })()`, 10000, `error for ${reason}`);
        assert.equal(e.reason, reason, `${D.label}: ${e.text}`); assert.match(e.text, re);
      };
      await A.click('#invite');
      const offer1 = await A.waitFor(`document.querySelector('#pair-code')?.dataset.code`, 20000, 'invitation');
      await B.click('#join');
      await tryCode(B, 'hello, this is not a code', 'notCode', /not a LeanSync pairing code/);
      await tryCode(B, offer1.slice(0, offer1.length - 7), 'damaged', /incomplete or mistyped/);           // truncated
      const i = 20, other = offer1[i] === 'Q' ? 'R' : 'Q';
      await tryCode(B, offer1.slice(0, i) + other + offer1.slice(i + 1), 'damaged', /incomplete or mistyped/);   // one character mistyped
      await tryCode(B, 'LSN2' + offer1.slice(4), 'version', /different version/);
      await tryCode(A, offer1, 'kind', /invitation code, not a reply/);                                  // A pastes its own invitation as the reply
      await B.pasteCode(offer1);
      const replyB1 = await B.waitFor(`document.querySelector('#pair-code')?.dataset.code`, 20000, 'reply');
      await C.click('#join');
      await tryCode(C, replyB1, 'kind', /reply code, not an invitation/);
      // A new invitation: a reply made for the old one is refused.
      await A.closeDialog(); await B.closeDialog();
      await A.click('#invite');
      const offer2 = await A.waitFor(`document.querySelector('#pair-code')?.dataset.code`, 20000, 'second invitation');
      assert.notEqual(offer2, offer1);
      await tryCode(A, replyB1, 'stale', /belongs to another invitation/);
      // C joins the same invitation as B; once B's reply is used, C's is refused.
      await C.closeDialog(); await C.click('#join'); await C.pasteCode(offer2);
      const replyC = await C.waitFor(`document.querySelector('#pair-code')?.dataset.code`, 20000, 'C reply');
      await B.click('#join'); await B.pasteCode(offer2);
      const replyB2 = await B.waitFor(`document.querySelector('#pair-code')?.dataset.code`, 20000, 'B reply');
      await A.pasteCode(replyB2);
      await A.waitFor(`document.querySelector('#pair-status')?.dataset.state === 'connected'`, 40000, 'A connected to B');
      await tryCode(A, replyC, 'used', /already used/);
      await C.closeDialog();
      await B.waitFor(`document.querySelector('#pair-status')?.dataset.state === 'connected'`, 20000);
      const f = randomFile(`r-${ctx.id}.txt`, 500);
      await A.add([f]); await B.waitFiles(files(f));
      assert.equal((await C.connections()).length, 0, 'C was never connected');
    },
  },
  {
    name: 'reply-renewal',
    kinds: [[CH, FF], [FF, FF], [FF, CH], [CH, CH]],
    async run(ctx, kinds) {
      // B is given A's invitation with unreachable addresses, so B's own checks fail (as when A is
      // behind a NAT): the connection forms only from A's side, while B's reply attempt is still
      // alive. A Firefox answerer gives up 11 s after it starts (measured); the reply A reads 12 s
      // after B joined works only because B renewed it.
      const [A, B] = await devices(ctx, kinds, { paired: false });
      await A.click('#invite');
      const offer = await A.waitFor(`document.querySelector('#pair-code')?.dataset.code`, 20000, 'invitation');
      await B.click('#join');
      await B.pasteCode(unreachableOffer(offer));
      const first = await B.waitFor(`document.querySelector('#pair-code')?.dataset.code`, 20000, 'first reply');
      const t0 = Date.now(), seen = new Set([first]);
      let maxLive = 0;
      while (Date.now() - t0 < 12000) { seen.add(await B.shownCode()); maxLive = Math.max(maxLive, await B.eval('window.__net.live()')); await sleep(250); }
      assert.ok(seen.size >= 4, `the reply was renewed (${seen.size} different replies in 12 s)`);
      assert.ok(maxLive <= 6, `at most 6 reply attempts alive (${maxLive})`);
      await A.pasteCode(await retag(await B.shownCode(), offer));
      await A.waitFor(`document.querySelector('#pair-status')?.dataset.state === 'connected' || !document.querySelector('#pair-error').hidden`, 45000, 'A: result');
      const err = await A.pairError();
      assert.equal(err, null, `pairing with a renewed reply: ${err?.text}`);
      await B.waitFor(`document.querySelector('#pair-status')?.dataset.state === 'connected'`, 20000, 'B connected');
      await sleep(1000);
      assert.equal(await B.eval('window.__net.live()'), 1, 'the other attempts were closed');
      const f = randomFile(`rr-${ctx.id}.txt`, 800);
      await A.add([f]); await B.waitFiles(files(f));
      ctx.note(`${seen.size} replies in 12 s, at most ${maxLive} attempts alive`);
    },
  },
  {
    name: 'peer-killed-files-recover',
    kinds: [[CH, CH], [FF, FF], [CH, FF], [FF, CH]],
    async run(ctx, kinds) {
      const [A, B] = await devices(ctx, kinds);
      await waitPeers(A, 1);
      const f = randomFile(`k-${ctx.id}.bin`, 1024 * 1024);
      await B.eval('(window.__holdClose = true)');                // B's copy cannot complete before A vanishes
      await A.add([f]);
      await B.waitRows((rows) => rows.length === 1 && rows[0].status === 'fetching', 20000, 'fetching');
      const t0 = Date.now();
      await A.kill();                                             // no goodbye of any kind
      await B.waitRows((rows) => rows[0].status === 'waiting', 60000, 'waiting after the peer vanished');
      const tDown = Date.now() - t0;
      await B.waitFor(`window.leansync.connections.length === 0`, 60000, 'connection dropped');
      const tGone = Date.now() - t0;
      await B.waitFor(`[...document.querySelectorAll('#messages .msg.error')].some((m) => /Pair again/.test(m.textContent))`, 5000, 'lost-connection message');
      ctx.note(`A killed: B's link down after ${(tDown / 1000).toFixed(1)} s, connection dropped after ${(tGone / 1000).toFixed(1)} s`);
      await B.eval('window.__releaseCloses()');
      await A.reopen();
      await pair(A, B);                                           // pair again: the file in flight arrives
      await B.waitFiles(files(f), 60000);
      await expectSha(B, f.name, f);
      // A closes its tab: its connections are closed on pagehide, so B learns at once.
      await A.page.close();
      const t1 = Date.now();
      await B.waitFor(`window.leansync.connections.length === 0`, 40000, 'connection dropped after A closed its tab');
      const tTab = Date.now() - t1;
      ctx.note(`A's tab closed: B dropped the connection after ${tTab} ms`);
      assert.ok(tTab < 5000, `B learned of the closed tab after ${tTab} ms`);
    },
  },
  {
    name: 'three-devices-pairwise',
    kinds: [[CH, FF, CH], [FF, CH, FF]],
    async run(ctx, kinds) {
      const [A, B, C] = await devices(ctx, kinds);
      await pair(A, B); await pair(B, C); await pair(C, A);
      for (const D of [A, B, C]) assert.equal((await D.connections()).length, 2, `${D.label}: two connections`);
      const fa = randomFile(`a-${ctx.id}.txt`, 100), fb = randomFile(`b-${ctx.id}.txt`, 200), fc = randomFile(`c-${ctx.id}.bin`, 300000);
      await A.add([fa]); await B.add([fb]); await C.add([fc]);
      for (const D of [A, B, C]) await D.waitFiles(files(fa, fb, fc));
      await expectSha(A, fc.name, fc);
      await setOnline(B, false);                                  // the triangle still syncs without B
      const fd = randomFile(`d-${ctx.id}.txt`, 50);
      await A.add([fd]); await C.waitFiles(files(fa, fb, fc, fd));
      await setOnline(B, true); await B.waitFiles(files(fa, fb, fc, fd));
    },
  },
  {
    name: 'stun-settings',
    kinds: [[CH], [FF]],
    async run(ctx, kinds) {
      const firefox = kinds[0] !== CH;
      const A = await ctx.open(kinds[0], 'A', { stun: null });
      assert.equal(await A.eval(`document.querySelector('#stun').value`), 'stun:stun.l.google.com:19302', 'default: Google\'s STUN server');
      assert.equal(await A.setStun(['http://example.org']), 'error', 'not a STUN address: refused');
      if (firefox) assert.equal(await A.setStun(['stun:127.0.0.1:9']), 'error', 'Firefox refuses a blocked port: caught when saving');
      // An unreachable STUN server: the invitation is ready within the gathering cap, with a warning.
      assert.equal(await A.setStun(['stun:192.0.2.1:3478']), 'saved');
      const t0 = Date.now();
      await A.click('#invite');
      await A.waitFor(`document.querySelector('#pair-code')?.dataset.code`, 60000, 'invitation');
      const ms = Date.now() - t0;
      ctx.note(`invitation ready ${ms} ms after the click, with an unreachable STUN server`);
      assert.ok(ms < 6000, `invitation ready after ${ms} ms (Chromium reports gathering complete only after ~40 s)`);
      assert.ok(await A.eval(`!!document.querySelector('#pair-warn')`), 'STUN warning shown');
      assert.equal(await A.eval('window.__net.ice.at(-1)'), JSON.stringify([{ urls: 'stun:192.0.2.1:3478' }]), 'the configured server is used');
      await A.closeDialog();
      // An empty list: no STUN at all; the setting survives a reload.
      assert.equal(await A.setStun([]), 'saved');
      await A.reload();
      assert.equal(await A.eval(`document.querySelector('#stun').value`), '');
      await A.click('#invite');
      const code = await A.waitFor(`document.querySelector('#pair-code')?.dataset.code`, 20000, 'invitation');
      assert.equal(await A.eval('window.__net.ice.at(-1)'), '[]');
      assert.ok(parseCode(code, 'offer').cands.every((c) => c.type === 'host'));
      assert.ok(!(await A.eval(`!!document.querySelector('#pair-warn')`)), 'no warning without STUN');
    },
  },
  {
    name: 'pairing-ui-phone-viewport',
    kinds: [[CH, FF], [FF, CH]],
    async run(ctx, kinds) {
      const [A, B] = await devices(ctx, kinds, { paired: false });
      for (const D of [A, B]) await D.page.setViewport(360, 740);
      const fit = (D) => D.eval(`(() => { const d = document.querySelector('#pair'), r = d.getBoundingClientRect(), q = document.querySelector('#pair-qr')?.getBoundingClientRect();
        const t = document.querySelector('#pair-code')?.getBoundingClientRect();
        if (!d.open) return { vw: innerWidth, docW: document.documentElement.scrollWidth, left: 0, right: 0, overflow: 0, qr: null, code: null };
        return { vw: innerWidth, docW: document.documentElement.scrollWidth, left: r.left, right: r.right, overflow: d.scrollWidth - d.clientWidth, qr: q ? Math.round(q.width) : null, code: t ? Math.round(t.right) : null }; })()`);
      const check = (f, who) => {
        assert.equal(f.vw, 360, `${who}: viewport`);
        assert.ok(f.docW <= 360, `${who}: no horizontal page scroll (${f.docW})`);
        assert.ok(f.left >= 0 && f.right <= 360, `${who}: dialog inside the screen (${f.left}..${f.right})`);
        assert.ok(f.overflow <= 1, `${who}: no horizontal scroll inside the dialog (${f.overflow})`);
        if (f.qr !== null) assert.ok(f.qr >= 200 && f.qr <= 340, `${who}: QR ${f.qr} px wide`);
        if (f.code !== null) assert.ok(f.code <= 360, `${who}: code box fits`);
      };
      check(await fit(A), 'A main page');
      await A.click('#invite');
      const offer = await A.waitFor(`document.querySelector('#pair-code')?.dataset.code`, 20000, 'invitation');
      check(await fit(A), 'A invitation');
      // No camera on this device: the dialog says so and offers the text path.
      await B.eval('(window.__fakeCamera.absent = true)');
      await B.click('#join');
      await B.waitFor(`!document.querySelector('#pair-camera-note').hidden`, 10000, 'no-camera note');
      assert.match(await B.eval(`document.querySelector('#pair-camera-note').textContent`), /No camera/);
      assert.ok(await B.eval(`document.querySelector('#pair-scan').hidden`), 'no scan button without a camera');
      await B.closeDialog();
      // A camera whose permission is refused: a clear message, and the text path still works.
      await B.eval('(window.__fakeCamera.absent = false, window.__fakeCamera.enabled = true, window.__fakeCamera.deny = true, true)');
      await B.click('#join');
      await B.waitFor(`!document.querySelector('#pair-scan').hidden`, 10000, 'scan button');
      await B.click('#pair-scan');
      await B.waitFor(`!document.querySelector('#pair-camera-note').hidden`, 10000, 'camera refused note');
      assert.match(await B.eval(`document.querySelector('#pair-camera-note').textContent`), /Camera access was refused/);
      await B.pasteCode(offer);
      const reply = await B.waitFor(`document.querySelector('#pair-code')?.dataset.code`, 20000, 'reply')
        .catch(async (e) => { throw new Error(`${e.message}\ndialog: ${await B.eval('document.querySelector("#pair").innerText.slice(0, 600)')}`); });
      check(await fit(B), 'B reply');
      await A.pasteCode(reply);
      await A.waitFor(`document.querySelector('#pair-status')?.dataset.state === 'connected'`, 40000, 'connected');
      await A.closeDialog();
      check(await fit(A), 'A main page with a device');
    },
  },
  {
    name: 'runs-from-sub-path',
    kinds: [[CH, FF]],
    async run(ctx, kinds) {
      // The app is plain static files and works from any path of any static server.
      const sub = await startServer({ port: 0, base: '/some/sub/dir/' });
      ctx.cleanup.push(() => sub.close());
      const A = await ctx.open(kinds[0], 'A', { server: sub }), B = await ctx.open(kinds[1], 'B', { server: sub });
      assert.match(await A.eval('location.pathname'), /^\/some\/sub\/dir\//);
      await pair(A, B);
      const f = randomFile(`sub-${ctx.id}.bin`, 70000);
      await A.add([f]); await B.waitFiles(files(f)); await expectSha(B, f.name, f);
      assert.deepEqual(sub.stats.notFound.filter((u) => !/favicon/.test(u)), [], 'every request was for a file of the site');
    },
  },
  {
    name: 'pair-with-browser-defaults',
    kinds: [[CH, CH], [FF, FF], [CH, FF], [FF, CH]],
    async run(ctx, kinds) {
      // The browsers as shipped (mDNS names instead of host addresses).
      const [A, B] = await devices(ctx, kinds, { A: { browserDefaults: true }, B: { browserDefaults: true }, paired: false });
      const { offer } = await pair(A, B);
      ctx.note(`invitation candidates: ${parseCode(offer, 'offer').cands.map((c) => c.addr.endsWith('.local') ? 'mDNS name' : c.addr).join(', ')}`);
      const f = randomFile(`d-${ctx.id}.txt`, 4000);
      await A.add([f]); await B.waitFiles(files(f));
    },
  },
];

async function waitFor(fn, ms, what) {
  const t0 = Date.now(); let last;
  while (Date.now() - t0 < ms) { try { if (await fn()) return; } catch (e) { last = e.message; } await sleep(200); }
  throw new Error(`timed out waiting for ${what}${last ? ` (${last})` : ''}`);
}
