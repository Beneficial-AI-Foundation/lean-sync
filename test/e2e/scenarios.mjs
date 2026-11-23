// End-to-end scenarios (docs/app-design.md §10). Each scenario gets fresh devices (browser
// processes with their own profiles) in its own relay room. `kinds` is the list of browsers for
// the devices A, B, C...; test/e2e/run.mjs runs each scenario on each of its configurations.
import assert from 'node:assert/strict';
import { cpSync } from 'node:fs';
import { tempDir, removeDir } from '../proc.mjs';
import { openDevice, randomFile, sleep, admin, sha } from './lib.mjs';

const CH = 'chromium', FF = 'firefox', ESR = 'firefox-esr';
const files = (...fs) => Object.fromEntries(fs.map((f) => [f.name, f.sha]));

async function devices(ctx, kinds, opts = {}) {
  const out = [];
  for (let i = 0; i < kinds.length; i++) {
    const label = String.fromCharCode(65 + i);
    out.push(await ctx.open(kinds[i], label, opts[label] ?? {}));
  }
  return out;
}
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

export const scenarios = [
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
      await admin(ctx.server, 'topology', { room: ctx.room, allow: [['A', 'B'], ['B', 'C']] });
      const [A, B, C] = await devices(ctx, kinds);
      const f = randomFile(`chain-${ctx.id}.bin`, 400000), g = randomFile(`back-${ctx.id}.txt`, 777);
      await A.add([f]);
      await C.waitFiles(files(f));                       // A -> B -> C, index and content
      await expectSha(C, f.name, f);
      const st = await (await fetch(`${ctx.server.url}/admin/state?room=${ctx.room}`)).json();
      assert.ok(!st.links.some((l) => (l.a === 'A' && l.b === 'C') || (l.a === 'C' && l.b === 'A')), 'A and C were never linked');
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
      await admin(ctx.server, 'cut', { room: ctx.room, a: 'A', b: 'B', afterBytes: 2 * 1024 * 1024 });
      await A.add([big]);
      await B.waitFor(`[...document.querySelectorAll('#files tr')].some((t) => t.dataset.status !== 'complete')`, 30000, 'B sees the file, content not yet complete');
      await B.waitFiles(files(big), 90000);
      await expectSha(B, big.name, big);
      const st = await (await fetch(`${ctx.server.url}/admin/state?room=${ctx.room}`)).json();
      assert.ok(st.links.length === 1, 'reconnected');
      assert.equal(st.cuts, 1, 'the link was cut mid-transfer');
      await waitFor(async () => (await incomingCount(B)) === 0, 10000, 'the partial file was discarded');
    },
  },
  {
    name: 'corrupted-blob-and-garbage-message',
    kinds: [[CH, CH], [FF, CH]],
    async run(ctx, kinds) {
      const [A, B] = await devices(ctx, kinds);
      await waitPeers(A, 1);
      await admin(ctx.server, 'corrupt', { room: ctx.room, from: 'A', to: 'B' });
      const f = randomFile(`c-${ctx.id}.bin`, 50000);
      await A.add([f]);
      // The corrupted copy must never show as complete: B marks the content lacking at A for this session.
      await B.waitRows((rows) => rows.length === 1 && rows[0].status === 'waiting', 30000, 'waiting after a corrupted transfer');
      await sleep(1000);
      assert.equal((await B.rows())[0].status, 'waiting');
      await admin(ctx.server, 'garbage', { room: ctx.room, from: 'A', to: 'B' });   // Lean closes the session (protocol error)
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
      await sleep(4000);                                              // several automatic retries (1 s, 2 s back-off)
      assert.ok(await A.eval(`!!document.querySelector('#banner-save') && document.querySelector('#saving').dataset.state === 'failed'`), 'banner still shown while saving fails');
      assert.ok((await B.rows()).some((r) => r.path === gone.name), 'B did not receive the unsaved deletion');
      const failures = (await A.eval('window.leansync.log')).filter((l) => /persist \d+ failed/.test(l)).length;
      assert.ok(failures >= 2, `the save was retried and failed again (${failures} failures)`);
      ctx.note(`A: ${failures} failed saves before recovery`);
      // 3. Recovery.
      if (firefox) await A.eval(`(async () => { const root = await navigator.storage.getDirectory(); const names = []; for await (const n of root.keys()) if (n.startsWith('filler-')) names.push(n); for (const n of names) await root.removeEntry(n); return names.length; })()`);
      else { await A.eval('(window.__idbFail = false)'); await A.page.cdp('Storage.overrideQuotaForOrigin', { origin: ctx.server.url }); }
      await A.eval(`(document.querySelector('#retry-save')?.click(), true)`);   // an automatic retry may already have succeeded
      await A.waitFor(`!document.querySelector('#banner-save') && document.querySelector('#saving').dataset.state === 'saved'`, 30000, 'banner gone after a successful save');
      await B.waitRows((rows) => !rows.some((r) => r.path === gone.name) && rows.some((r) => r.path === keep.name), 30000, 'B gets the deletion once it is saved');
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
      await B.waitFiles(files(big), 60000);
      await expectSha(B, big.name, big);
      // Kill A's browser right after an add (mid-persist or just after): on restart the add is
      // either fully there or not there, never shown complete without its bytes.
      const k = randomFile(`k-${ctx.id}.txt`, 3000);
      await A.add([k]);
      await sleep(30);
      await A.kill();
      await A.reopen();
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
      await A.waitFiles(files(f, g));
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
      const A2 = await ctx.open(kinds[0], 'A2', { profile: copy });
      for (const D of [A, A2]) await D.waitFor(`[...document.querySelectorAll('#banners .banner')].some((b) => b.textContent.includes('own identity'))`, 30000, 'refused banner');
      const st = await (await fetch(`${ctx.server.url}/admin/state?room=${ctx.room}`)).json();
      assert.equal(await A.eval(`document.querySelectorAll('#peers .peer').length`), 0, 'no session');
      ctx.note(`relay links seen: ${st.links.length} (each closed at the host HELLO)`);
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
];

async function waitFor(fn, ms, what) {
  const t0 = Date.now(); let last;
  while (Date.now() - t0 < ms) { try { if (await fn()) return; } catch (e) { last = e.message; } await sleep(200); }
  throw new Error(`timed out waiting for ${what}${last ? ` (${last})` : ''}`);
}
