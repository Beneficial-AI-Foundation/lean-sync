// Mutation audit of the host-obligations table (docs/app-design.md §4): for each row, break the
// mechanism in the app's source and check that the test the table names FAILS. Every mutant is
// reverted in a `finally`, and at the end the app's sources must be byte-identical to before.
//   node test/mutations.mjs [--only id,id]        (needs scripts/build-site.sh and the vectors)
// e2e checks run in Chromium only, to keep this affordable, unless a mutant names its browsers (a
// scenario that needs Firefox, e.g. as the answering device). A check that runs no test at all
// (exit 3 from run.mjs) is reported as NO TEST RAN, never as caught.
import { readFileSync, writeFileSync } from 'node:fs';
import { execFileSync, spawnSync } from 'node:child_process';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
const unit = (f) => ['node', ['--test', `test/unit/${f}.test.mjs`]];
const e2e = (s, browsers = 'chromium') => ['node', ['test/e2e/run.mjs', '--only', s, '--browsers', browsers]];

const M = [
  { id: 'persisted-before-commit', row: 'persist, then persisted', file: 'app/js/core.mjs',
    from: 'await o.storage.saveRecord(replica, state, { clearRotate });', to: 'o.storage.saveRecord(replica, state, { clearRotate }).catch(() => {});', check: unit('core') },
  { id: 'idb-request-error-suppressed', row: 'never acknowledge a failed write', file: 'app/js/storage.mjs',
    from: 'tx.oncomplete = () => resolve();', to: 'tx.onerror = (ev) => ev.preventDefault(); tx.oncomplete = () => resolve();', check: e2e('record-request-error-not-acknowledged') },
  { id: 'persist-failure-ignored', row: 'never acknowledge a failed write', file: 'app/js/core.mjs',
    from: "emit({ type: 'persistFailed', tag }, ep);", to: '', check: unit('core') },
  { id: 'persist-slot-race', row: 'one persist in flight / restart waits', file: 'app/js/core.mjs',
    from: 'const done = () => { if (st.persist === slot) st.persist = null; };', to: 'const done = () => {}; queueMicrotask(() => queueMicrotask(() => { st.persist = null; }));', check: unit('core') },
  // Lean holds a failed save and parks a blob it could not store until `retrySave`: the host must
  // send it, after a back-off, and only then.
  { id: 'retry-without-back-off', row: 'retry after back-off', file: 'app/js/core.mjs',
    from: 'if (ep === st.epoch && st.retryOwed) sendRetry(ep); }, st.retryBackoff);', to: 'if (ep === st.epoch && st.retryOwed) sendRetry(ep); }, 0);', check: unit('core') },
  { id: 'retry-never-sent', row: 'retry after back-off', file: 'app/js/core.mjs',
    from: 'if (ep === st.epoch && st.retryOwed) sendRetry(ep); }', to: 'if (false) sendRetry(ep); }', check: unit('core') },
  { id: 'store-failure-not-retried', row: 'blob store failure: retried', file: 'app/js/core.mjs',
    from: "if (ev.type === 'persistFailed' || ev.type === 'blobStoreFailed') owesRetry(ep);", to: "if (ev.type === 'persistFailed') owesRetry(ep);", check: e2e('incoming-write-or-publish-failure') },
  { id: 'store-failure-not-retried (unit)', row: 'blob store failure: retried', file: 'app/js/core.mjs',
    from: "if (ev.type === 'persistFailed' || ev.type === 'blobStoreFailed') owesRetry(ep);", to: "if (ev.type === 'persistFailed') owesRetry(ep);", check: unit('core') },
  { id: 'store-failure-blames-peer', row: 'blob store failure: not the peer\'s fault', file: 'app/js/links.mjs',
    from: "o.emit(local ? { type: 'blobStoreFailed', hash } : { type: 'blobFailed', peer: c.peer, hash }, c.epoch);", to: "o.emit({ type: 'blobFailed', peer: c.peer, hash }, c.epoch);", check: unit('links') },
  { id: 'store-failure-blames-peer (e2e)', row: 'blob store failure: not the peer\'s fault', file: 'app/js/links.mjs',
    from: "o.emit(local ? { type: 'blobStoreFailed', hash } : { type: 'blobFailed', peer: c.peer, hash }, c.epoch);", to: "o.emit({ type: 'blobFailed', peer: c.peer, hash }, c.epoch);", check: e2e('incoming-file-creation-fails-then-next-file') },
  { id: 'publish-failure-blames-peer', row: 'blob store failure: not the peer\'s fault', file: 'app/js/links.mjs',
    from: "if (c.alive) o.emit({ type: 'blobStoreFailed', hash: s.hash }, ep);", to: "if (c.alive) o.emit({ type: 'blobFailed', peer, hash: s.hash }, ep);", check: unit('links') },
  { id: 'late-store-failure-after-close', row: 'blob store failure: not the peer\'s fault', file: 'app/js/links.mjs',
    from: "if (c.alive) o.emit({ type: 'blobStoreFailed', hash: s.hash }, ep);", to: "o.emit({ type: 'blobStoreFailed', hash: s.hash }, ep);", check: unit('links') },
  { id: 'no-retry-now-for-store-failures', row: 'blob store failure: shown as such', file: 'app/js/ui.mjs',
    from: 'if (!state.saveFailed && state.summary?.localFailure > 0) b.append(', to: 'if (false) b.append(', check: e2e('incoming-write-or-publish-failure') },
  { id: 'local-failure-shown-as-waiting', row: 'blob store failure: shown as such', file: 'app/js/view.mjs',
    from: "localFailure: 'could not be stored on this device',", to: "localFailure: 'waiting: nobody reachable has it',", check: unit('view') },
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
    from: 'if (await hasBlob(hx) && await existingIsIntact(hx)) {', to: 'if (await hasBlob(hx)) {', check: e2e('damaged-or-missing-blob-recovers') },
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
  // In the browser, a failed file creation is also caught by the write-error handler as soon as the
  // first DATA arrives (the stream's chain is rejected), so the e2e mutant removes both handlers; the
  // unit mutant below removes only the START-time one (no DATA is sent there).
  { id: 'sink-failure-ignored', row: 'fetch: failure reported, sender released', file: 'app/js/links.mjs',
    from: ['      if (c.recv.get(hx) !== s || s.failed) return;\n      o.onStorageError?.(e);\n      failStream(c, hash,', '      if (c.recv.get(hx) !== s || s.failed) return;\n      o.onStorageError?.(e);\n      failStream(c, s.hash,'],
    to: ['      return;\n      o.onStorageError?.(e);\n      failStream(c, hash,', '      return;\n      o.onStorageError?.(e);\n      failStream(c, s.hash,'], check: e2e('incoming-file-creation-fails-then-next-file') },
  { id: 'sink-failure-ignored (unit)', row: 'fetch: failure reported, sender released', file: 'app/js/links.mjs',
    from: '      if (c.recv.get(hx) !== s || s.failed) return;\n      o.onStorageError?.(e);\n      failStream(c, hash,', to: '      return;\n      o.onStorageError?.(e);\n      failStream(c, hash,', check: unit('links') },
  { id: 'no-stall-timeout', row: 'serving slot released: stalled receiver', file: 'app/js/links.mjs',
    from: '      if (serving !== s) return;\n      o.log(`blob ${s.hx.slice(0, 8)}: no credit', to: '      if (true) return;\n      o.log(`blob ${s.hx.slice(0, 8)}: no credit', check: unit('links') },
  { id: 'delete-before-replace', row: 'blob durable: old copy kept until the new one is in place', file: 'app/js/storage.mjs',
    from: '    if (await hasBlob(hx) && await existingIsIntact(hx)) { await removeIncoming(name); return { ok: true, hash: h, hex: hx, size: file.size }; }\n',
    to: '    if (await hasBlob(hx)) await blobsDir.removeEntry(hx);\n', check: e2e('existing-blob-kept-when-replacement-fails') },
  { id: 'no-pending-refresh-on-peer-change', row: 'UI never shows a false state', file: 'app/js/core.mjs',
    from: "    if (['peerStatus', 'peerLeft', 'peerClosed', 'pendingSummary'].includes(e.notice)) refresh('pending');\n", to: '', check: e2e('peer-leaves-mid-fetch-row-updates') },
  // ---- the WebRTC transport and pairing (docs/net-design.md; app-design §4)
  { id: 'connection-failure-ignored', row: 'link down when the connection is lost', file: 'app/js/transport/webrtc.mjs',
    from: "} else if (s === 'failed' || s === 'closed') {", to: '} else if (false) {', check: unit('webrtc') },
  { id: 'connection-failure-ignored (e2e)', row: 'link down when the connection is lost', file: 'app/js/transport/webrtc.mjs',
    from: "} else if (s === 'failed' || s === 'closed') {", to: '} else if (false) {', check: e2e('peer-killed-files-recover') },
  { id: 'channel-close-only', row: 'link down when the connection is lost', file: 'app/js/transport/webrtc.mjs',
    from: ["} else if (s === 'failed' || s === 'closed') {", "      if (!c.lossTimer && c.state !== 'pairing') c.lossTimer"], to: ['} else if (false) {', "      if (false) c.lossTimer"], check: e2e('peer-killed-files-recover') },
  { id: 'closing-channel-kept', row: 'link down when the connection is lost', file: 'app/js/transport/webrtc.mjs',
    from: "if (dc.readyState !== 'open') { if (L.announced) closeLink(L, `channel ${dc.readyState}`); return false; }", to: "if (dc.readyState !== 'open') return false;", check: unit('webrtc') },
  { id: 'stale-link-blocks-new-channel', row: 'link down when the connection is lost', file: 'app/js/transport/webrtc.mjs',
    from: "    if (c.link) closeLink(c.link, 'replaced by a new channel from the other device');", to: '    if (c.link) { try { dc.close(); } catch {} return; }', check: unit('webrtc') },
  { id: 'onclose-twice', row: 'onClose once per link', file: 'app/js/transport/webrtc.mjs',
    from: '    if (!L || L.closed) return;', to: '    if (!L) return;', check: unit('webrtc') },
  { id: 'frames-after-close', row: 'onClose once per link', file: 'app/js/transport/webrtc.mjs',
    from: 'if (!L.closed && L.announced) L._onFrame', to: 'if (true) L._onFrame', check: unit('webrtc') },
  { id: 'answerer-active', row: 'answerer is the DTLS server', file: 'app/js/transport/webrtc.mjs',
    from: "sdp: ans.sdp.replace(/a=setup:(active|actpass)/g, 'a=setup:passive') }", to: 'sdp: ans.sdp }', check: unit('webrtc') },
  { id: 'answerer-active (e2e)', row: 'answerer is the DTLS server', file: 'app/js/transport/webrtc.mjs',
    from: "sdp: ans.sdp.replace(/a=setup:(active|actpass)/g, 'a=setup:passive') }", to: 'sdp: ans.sdp }', check: e2e('pair-by-text', 'chromium,firefox') },
  { id: 'no-reply-renewal', row: 'a reply stays usable while shown', file: 'app/js/transport/webrtc.mjs',
    from: '    renew = setInterval(attempt, t.RENEW_MS);', to: '    renew = null;', check: unit('webrtc') },
  { id: 'no-reply-renewal (e2e)', row: 'a reply stays usable while shown', file: 'app/js/transport/webrtc.mjs',
    from: '    renew = setInterval(attempt, t.RENEW_MS);', to: '    renew = null;', check: e2e('reply-renewal', 'chromium,firefox') },
  { id: 'unbounded-attempts', row: 'a reply stays usable while shown', file: 'app/js/transport/webrtc.mjs',
    from: '      while (attempts.filter((a) => !a.dropped).length > t.MAX_ATTEMPTS)', to: '      while (false)', check: unit('webrtc') },
  { id: 'crc-unchecked', row: 'codes are checked before use', file: 'app/js/netcode.mjs',
    from: '  if (crc32(body) !== crc) bad();\n', to: '', check: unit('netcode') },
  { id: 'invitation-reusable', row: 'an invitation accepts one reply', file: 'app/js/transport/webrtc.mjs',
    from: "        if (inv.state !== 'waiting') throw", to: '        if (false) throw', check: unit('webrtc') },
  { id: 'invitation-reusable (e2e)', row: 'an invitation accepts one reply', file: 'app/js/transport/webrtc.mjs',
    from: "        if (inv.state !== 'waiting') throw", to: '        if (false) throw', check: e2e('pairing-codes-rejected', 'chromium,firefox') },
  { id: 'stale-reply-accepted', row: 'codes are checked before use', file: 'app/js/transport/webrtc.mjs',
    from: '        if (!sameBytes(r.tag, tag)) throw', to: '        if (false) throw', check: e2e('pairing-codes-rejected', 'chromium,firefox') },
  { id: 'gathering-uncapped', row: 'gathering never blocks for long', file: 'app/js/transport/webrtc.mjs',
    from: '      const cap = setTimeout(finish, t.GATHER_CAP_MS);', to: '      const cap = null;', check: e2e('stun-settings') },
  { id: 'restart-drops-connection', row: 'engine restart keeps the pairing', file: 'app/js/transport/webrtc.mjs',
    from: '    if (!c.dropped) maybeOpen(c);\n    changed();', to: "    if (!c.dropped) dropConn(c, 'link closed');\n    changed();", check: e2e('trap-mid-sync-reinstantiates') },
  { id: 'offline-drops-connection', row: 'going offline keeps the pairing', file: 'app/js/transport/webrtc.mjs',
    from: "      if (!online) closeLink(c.link, 'offline (by you)');", to: "      if (!online) dropConn(c, 'offline');", check: e2e('offline-edits-both-sides') },
  { id: 'send-error-swallowed', row: 'a failing send closes the link', file: 'app/js/transport/webrtc.mjs',
    from: "closeLink(L, 'send failed'); return false; }", to: 'return false; }', check: unit('webrtc') },
  { id: 'drain-missed', row: 'back-pressure: onDrain never waits for an event that already fired', file: 'app/js/transport/webrtc.mjs',
    from: '        if (dc.bufferedAmount <= t.DRAIN_AT) queueMicrotask(fireDrain);\n', to: '', check: unit('webrtc') },
  { id: 'remote-close-ignored', row: 'link down when the connection is lost', file: 'app/js/transport/webrtc.mjs',
    from: "    c.ctl.onclose = () => { if (c.state !== 'pairing') dropConn(c, 'closed by the other device'); };\n", to: '', check: unit('webrtc') },
  { id: 'no-close-on-pagehide', row: 'closing the page tells the other devices', file: 'app/js/main.mjs',
    from: "  addEventListener('pagehide', () => transport.stop());\n", to: '', check: e2e('peer-killed-files-recover') },
  { id: 'stun-setting-ignored', row: 'no transport except paired devices and STUN', file: 'app/js/main.mjs',
    from: 'getIceServers: () => stun.map((urls) => ({ urls }))', to: 'getIceServers: () => DEFAULT_STUN.map((urls) => ({ urls }))', check: e2e('stun-settings') },
  { id: 'other-endpoint-contacted', row: 'no transport except paired devices and STUN', file: 'app/js/main.mjs',
    from: "  addEventListener('pagehide', () => transport.stop());\n", to: "  try { new WebSocket(`ws://${location.host}/relay`); } catch {}\n  addEventListener('pagehide', () => transport.stop());\n", check: e2e('no-network-except-paired-devices', 'chromium,firefox') },
  { id: 'camera-refusal-silent', row: 'pairing: camera refused or absent falls back to text with a message', file: 'app/js/pairing-ui.mjs',
    from: "        camNote.dataset.reason = e?.name ?? 'error';\n        return;", to: "        camNote.hidden = true;\n        return;", check: e2e('pairing-ui-phone-viewport', 'chromium,firefox') },
  { id: 'scan-video-not-muted', row: 'pairing: the QR scanning loop reads the camera', file: 'app/js/pairing-ui.mjs',
    from: '    video.muted = true; video.autoplay = true;', to: '    ;', check: e2e('pair-by-qr-fake-camera') },
  { id: 'late-dialog-close-ends-session', row: 'pairing: the dialog shows what is happening', file: 'app/js/pairing-ui.mjs',
    from: '    d.onclose = () => { if (!d.open) closeSession(); };', to: '    d.onclose = () => closeSession();', check: e2e('pairing-ui-phone-viewport', 'chromium,firefox') },
  { id: 'render-per-file', row: 'UI scales with the file count', file: 'app/js/ui.mjs',
    from: "for (const hx of todo) { try { state.sizes.set(hx, (await storage.blobFile(hx)).size); } catch { state.sizes.set(hx, null); } }",
    to: "for (const hx of todo) { try { state.sizes.set(hx, (await storage.blobFile(hx)).size); } catch { state.sizes.set(hx, null); } renderFiles(); }", check: e2e('cold-load-many-files') },
  { id: 'bom-stripped', row: 'paths round-trip byte for byte', file: 'app/js/codec.mjs',
    from: "{ fatal: true, ignoreBOM: true }", to: '{ fatal: true }', check: unit('codec') },
  { id: 'add-across-restart', row: 'supersession = what was shown (same machine)', file: 'app/js/core.mjs',
    from: 'if (st.epoch !== ep) {', to: 'if (false) {', check: unit('core') },
  { id: 'temp-kept-after-publish-failure', row: 'no temp files accumulate', file: 'app/js/storage.mjs',
    from: '          try { return await publish(name, fh, expectedHex); }\n          catch (e) { await removeIncoming(name);', to: '          try { return await publish(name, fh, expectedHex); }\n          catch (e) {', check: e2e('incoming-write-or-publish-failure') },
  { id: 'write-error-swallowed', row: 'fetch: storage failure stops the transfer', file: 'app/js/storage.mjs',
    from: 'return p.catch((e) => { throw new StorageError(', to: 'return p.catch((e) => { return; throw new StorageError(', check: e2e('incoming-write-or-publish-failure') },
  { id: 'write-error-ignored-by-links', row: 'fetch: storage failure stops the transfer', file: 'app/js/links.mjs',
    from: '      if (c.recv.get(hx) !== s || s.failed) return;\n      o.onStorageError?.(e);\n      failStream(c, s.hash,', to: '      return;\n      o.onStorageError?.(e);\n      failStream(c, s.hash,', check: unit('links') },
  { id: 'fragment-size-unchecked', row: 'received: bounded reassembly', file: 'app/js/links.mjs',
    from: 'if (more && part.length !== FRAME_PAYLOAD) {', to: 'if (false) {', check: unit('links') },
  { id: 'sink-not-aborted-after-end', row: 'no temp files accumulate', file: 'app/js/links.mjs',
    from: '      s.sink.then((sink) => sink.abort(), () => {});\n      o.log(`peer ${peer}: could not store blob', to: '      o.log(`peer ${peer}: could not store blob', check: unit('links') },
  { id: 'blobs-dropped-while-starting', row: 'blob durable before blobStored (reported to the machine that runs)', file: 'app/js/core.mjs',
    from: "          emit({ type: 'blobsStored', hashes: items.map((it) => it.hash) });   // queued until running",
    to: "          if (st.phase === 'running') emit({ type: 'blobsStored', hashes: items.map((it) => it.hash) });", check: unit('core') },
  { id: 'size-lookup-per-path', row: 'UI scales with the file count', file: 'app/js/ui.mjs',
    from: '        const todo = new Set();', to: "        const todo = []; todo.add = todo.push; Object.defineProperty(todo, 'size', { get: () => todo.length });", check: e2e('cold-load-many-files') },
  { id: 'sendAgain-wrong', row: 'sendAgain', file: 'app/js/codec.mjs',
    from: "out.push({ type: 'send', peer, bytes: lastState, again: true });", to: "out.push({ type: 'send', peer, bytes: new Uint8Array(0), again: true });", check: unit('codec') },
];

const only = (() => { const i = process.argv.indexOf('--only'); return i > 0 ? process.argv[i + 1].split(',') : null; })();
const appFiles = ['app/js/core.mjs', 'app/js/storage.mjs', 'app/js/links.mjs', 'app/js/ui.mjs', 'app/js/main.mjs', 'app/js/codec.mjs', 'app/js/view.mjs',
  'app/js/transport/webrtc.mjs', 'app/js/netcode.mjs', 'app/js/pairing-ui.mjs'];
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
    results.push({ ...m, verdict: r.status === 0 ? 'NOT CAUGHT' : r.status === 3 ? 'NO TEST RAN' : 'caught' });
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
