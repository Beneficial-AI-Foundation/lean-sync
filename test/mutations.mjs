// Mutation audit of the host-obligations table (docs/app-design.md §4): for each row, break the
// mechanism in the app's source and check that the test the table names FAILS. Every mutant is
// reverted in a `finally`, and at the end the app's sources must be byte-identical to before.
//   node test/mutations.mjs [--only id,id]        (needs scripts/build-site.sh and the vectors)
// e2e checks run in Chromium only, to keep this affordable.
import { readFileSync, writeFileSync } from 'node:fs';
import { execFileSync, spawnSync } from 'node:child_process';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
const unit = (f) => ['node', ['--test', `test/unit/${f}.test.mjs`]];
const e2e = (s) => ['node', ['test/e2e/run.mjs', '--only', s, '--browsers', 'chromium']];

const M = [
  { id: 'persisted-before-commit', row: 'persist, then persisted', file: 'app/js/core.mjs',
    from: 'await o.storage.saveRecord(replica, state, { clearRotate });', to: 'o.storage.saveRecord(replica, state, { clearRotate }).catch(() => {});', check: unit('core') },
  { id: 'idb-request-error-suppressed', row: 'never acknowledge a failed write', file: 'app/js/storage.mjs',
    from: 'tx.oncomplete = () => resolve();', to: 'tx.onerror = (ev) => ev.preventDefault(); tx.oncomplete = () => resolve();', check: e2e('record-request-error-not-acknowledged') },
  { id: 'persist-failure-ignored', row: 'never acknowledge a failed write', file: 'app/js/core.mjs',
    from: "emit({ type: 'persistFailed', tag }, ep);", to: '', check: unit('core') },
  { id: 'persist-slot-race', row: 'one persist in flight / restart waits', file: 'app/js/core.mjs',
    from: 'const done = () => { if (st.persist === slot) st.persist = null; };', to: 'const done = () => {}; queueMicrotask(() => queueMicrotask(() => { st.persist = null; }));', check: unit('core') },
  // The original loop: the UI refreshed its status on saveFailed, and refresh queries were not held
  // back while saves failed (both parts restored; either alone was fixed).
  { id: 'host-events-while-save-fails', row: 'retry after back-off', file: 'app/js/core.mjs',
    from: ['if (st.refreshTimer || st.saveFailed) return;', '        st.saveFailed = true;\n', '      if (st.saveFailed) return;                     // deferred to the nudge\n'],
    to: ['if (st.refreshTimer) return;', "        st.saveFailed = true; refresh('status');\n", ''], check: unit('core') },
  { id: 'save-banner-removed', row: 'surface saveFailed', file: 'app/js/ui.mjs',
    from: 'if (state.saveFailed) b.append(', to: 'if (false) b.append(', check: e2e('storage-failure') },
  { id: 'supersede-after-await', row: 'supersession = what was shown', file: 'app/js/core.mjs',
    from: 'items.push({ path: name, hash: r.hash, supersedes: seen[i] });', to: 'items.push({ path: name, hash: r.hash, supersedes: versionsOf(name) });', check: unit('core') },
  { id: 'supersede-after-await (e2e)', row: 'supersession = what was shown', file: 'app/js/core.mjs',
    from: 'items.push({ path: name, hash: r.hash, supersedes: seen[i] });', to: 'items.push({ path: name, hash: r.hash, supersedes: versionsOf(name) });', check: e2e('peer-edit-during-upload-becomes-conflict') },
  { id: 'accept-peers-before-inventory', row: 'inventory before any peer', file: 'app/js/core.mjs',
    from: "    st.startupFailedNotice = null;\n", to: "    st.startupFailedNotice = null;\n    o.links.setAccepting(true);\n", check: unit('core') },
  { id: 'own-replica-accepted', row: 'refuse own replica id', file: 'app/js/links.mjs',
    from: 'if (self.replica && replicaKey(self.replica) === replicaKey(c.remote)) {', to: 'if (false) {', check: unit('links') },
  { id: 'no-web-lock', row: 'one owner (Web Lock)', file: 'app/js/main.mjs',
    from: "if (!owner) { show('#locked');", to: "if (false) { show('#locked');", check: e2e('second-tab-lock') },
  { id: 'blob-not-verified', row: 'blob verified before blobStored', file: 'app/js/links.mjs',
    from: 'sink.finish(hx)', to: 'sink.finish(null)', check: unit('links') },
  { id: 'size-limit-not-enforced', row: 'fetch: size limit', file: 'app/js/links.mjs',
    from: 'if (size > MAX_FILE_BYTES) {', to: 'if (false) {', check: unit('links') },
  { id: 'credit-not-enforced', row: 'fetch: bounded buffering', file: 'app/js/links.mjs',
    from: 'if (s.received + bytes.length > s.granted) {', to: 'if (false) {', check: unit('links') },
  { id: 'message-limit-not-enforced', row: 'received: message limit', file: 'app/js/links.mjs',
    from: 'if (c.inSize > MAX_MESSAGE_BYTES) {', to: 'if (false) {', check: unit('links') },
  { id: 'stale-epoch-delivered', row: 'persist answers only for persists given', file: 'app/js/core.mjs',
    from: '    if (ep !== st.epoch) {\n', to: '    if (false) {\n', check: unit('core') },
  { id: 'startup-trap-retried', row: 'no loop on a start-up trap', file: 'app/js/core.mjs',
    from: 'if (during) {', to: 'if (false) {', check: e2e('trap-at-startup-does-not-loop') },
  { id: 'no-restart-after-trap', row: 're-instantiate after a trap', file: 'app/js/core.mjs',
    from: "    restart('trap').catch((err) => fail(`restart failed: ${err.message}`));", to: '', check: e2e('trap-mid-sync-reinstantiates') },
  { id: 'restart-stays-running', row: 're-instantiate after a trap', file: 'app/js/core.mjs',
    from: "    setPhase('starting');                  // leave `running` first", to: '    //', check: unit('core') },
  { id: 'edits-allowed-in-rollback', row: 'rollback mode surfaced', file: 'app/js/core.mjs',
    from: "const canEdit = () => st.phase === 'running' && !st.rollback;", to: "const canEdit = () => st.phase === 'running';", check: e2e('rollback-detected-then-new-identity') },
  { id: 'missing-blob-not-reported', row: 'blobLost when found gone', file: 'app/js/core.mjs',
    from: "        if (e?.name === 'NotFoundError') {", to: '        if (false) {', check: e2e('damaged-or-missing-blob-recovers') },
  { id: 'damaged-copy-kept', row: 'blob verified and durable', file: 'app/js/storage.mjs',
    from: '    if (await hasBlob(hx)) await blobsDir.removeEntry(hx);\n    await fh.move(blobsDir, hx);', to: '    if (await hasBlob(hx)) await removeIncoming(name); else await fh.move(blobsDir, hx);', check: e2e('damaged-or-missing-blob-recovers') },
  { id: 'peer-ids-reused', row: 'PeerIds never reused', file: 'app/js/links.mjs',
    from: 'c.peer = nextPeer++;', to: 'c.peer = byPeer.size + 1;', check: unit('links') },
  { id: 'close-before-queued-bytes', row: 'close after queued bytes', file: 'app/js/links.mjs',
    from: "function closePeer(peer) { const c = byPeer.get(peer); if (c && c.alive) push(c, 'CLOSE'); }", to: 'function closePeer(peer) { const c = byPeer.get(peer); if (c && c.alive) kill(c); }', check: unit('links') },
  { id: 'unreadable-blob-not-lost', row: 'serveBlob: unreadable -> blobLost', file: 'app/js/links.mjs',
    from: "      o.emit({ type: 'blobLost', hash: s.hash }, ep);\n", to: '', check: unit('links') },
  { id: 'corrupt-record-reset-silently', row: 'startupFailed; reset only on confirmation', file: 'app/js/core.mjs',
    from: 'if (reset || !rec) {', to: 'if (reset || !rec || rec.corrupt || rec.state.length < 5) {', check: unit('core') },
  { id: 'rotate-flag-ignored', row: 'start-up: new id when the record cannot be vouched for', file: 'app/js/core.mjs',
    from: 'else if (rotate || rec.corrupt) {', to: 'else if (rec.corrupt) {', check: unit('core') },
  { id: 'empty-blob-never-ends', row: 'serving slot released: empty blob', file: 'app/js/links.mjs',
    from: "    if (data.length === 0) { push(s.conn, u8(T.END, s.hash)); finishServing(); return; }   // no credit will come\n", to: '', check: e2e('empty-file-then-normal-file') },
  { id: 'empty-blob-never-ends (unit)', row: 'serving slot released: empty blob', file: 'app/js/links.mjs',
    from: "    if (data.length === 0) { push(s.conn, u8(T.END, s.hash)); finishServing(); return; }   // no credit will come\n", to: '', check: unit('links') },
  { id: 'sink-failure-ignored', row: 'fetch: failure reported, sender released', file: 'app/js/links.mjs',
    from: '      if (c.recv.get(hx) !== s || s.failed) return;\n', to: '      return;\n', check: e2e('incoming-file-creation-fails-then-next-file') },
  { id: 'sink-failure-ignored (unit)', row: 'fetch: failure reported, sender released', file: 'app/js/links.mjs',
    from: '      if (c.recv.get(hx) !== s || s.failed) return;\n', to: '      return;\n', check: unit('links') },
  { id: 'no-stall-timeout', row: 'serving slot released: stalled receiver', file: 'app/js/links.mjs',
    from: '      if (serving !== s) return;\n      o.log(`blob ${s.hx.slice(0, 8)}: no credit', to: '      if (true) return;\n      o.log(`blob ${s.hx.slice(0, 8)}: no credit', check: unit('links') },
  { id: 'delete-before-replace', row: 'blob durable: old copy kept until the new one is in place', file: 'app/js/storage.mjs',
    from: '    if (await hasBlob(hx) && await existingIsIntact(hx)) { await removeIncoming(name); return { ok: true, hash: h, hex: hx, size: file.size }; }\n',
    to: '    if (await hasBlob(hx)) await blobsDir.removeEntry(hx);\n', check: e2e('existing-blob-kept-when-replacement-fails') },
  { id: 'no-pending-refresh-on-peer-change', row: 'UI never shows a false state', file: 'app/js/core.mjs',
    from: "    if (['peerStatus', 'peerLeft', 'peerClosed', 'pendingSummary'].includes(e.notice)) refresh('pending');\n", to: '', check: e2e('peer-leaves-mid-fetch-row-updates') },
  { id: 'relay-from-url', row: 'transport only to the serving origin', file: 'app/js/main.mjs',
    from: 'const relayUrl = `${location.protocol', to: "const relayUrl = params.get('relay') || `${location.protocol", check: e2e('relay-parameter-ignored') },
  { id: 'sendAgain-wrong', row: 'sendAgain', file: 'app/js/codec.mjs',
    from: "out.push({ type: 'send', peer, bytes: lastState, again: true });", to: "out.push({ type: 'send', peer, bytes: new Uint8Array(0), again: true });", check: unit('codec') },
];

const only = (() => { const i = process.argv.indexOf('--only'); return i > 0 ? process.argv[i + 1].split(',') : null; })();
const appFiles = ['app/js/core.mjs', 'app/js/storage.mjs', 'app/js/links.mjs', 'app/js/ui.mjs', 'app/js/main.mjs', 'app/js/codec.mjs'];
const pristine = Object.fromEntries(appFiles.map((f) => [f, readFileSync(join(root, f), 'utf8')]));
const site = () => execFileSync(join(root, 'scripts/build-site.sh'), { stdio: 'ignore' });
const results = [];
for (const m of M) {
  if (only && !only.includes(m.id)) continue;
  const path = join(root, m.file), src = pristine[m.file];
  const froms = [m.from].flat(), tos = [m.to].flat();
  if (froms.some((f) => src.split(f).length !== 2)) { results.push({ ...m, verdict: 'MUTANT DID NOT APPLY' }); console.log(`MUTANT DID NOT APPLY ${m.id}`); continue; }
  try {
    writeFileSync(path, froms.reduce((acc, f, i) => acc.replace(f, tos[i]), src));
    site();
    const [cmd, args] = m.check;
    const r = spawnSync(cmd, args, { cwd: root, encoding: 'utf8', timeout: 600000 });
    results.push({ ...m, verdict: r.status === 0 ? 'NOT CAUGHT' : 'caught' });
  } finally {
    writeFileSync(path, src);
  }
  console.log(`${results.at(-1).verdict.padEnd(10)} ${m.id}  [${m.row}]  by: ${m.check[1].join(' ')}`);
}
site();
const intact = appFiles.every((f) => readFileSync(join(root, f), 'utf8') === pristine[f]);
console.log(`sources restored: ${intact ? 'yes' : 'NO'}`);
const bad = results.filter((r) => r.verdict !== 'caught');
console.log(`${results.length - bad.length}/${results.length} mutants caught`);
process.exit(bad.length || !intact ? 1 : 0);
