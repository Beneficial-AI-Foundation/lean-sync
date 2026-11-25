// View model (app/js/view.mjs): what a row may claim.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { buildRows, uniqueName, splitPath, STATUS_TEXT } from '../../app/js/view.mjs';

const h = (n) => new Uint8Array(32).fill(n);
test('complete only when present; otherwise the pending status, never complete', () => {
  const rows = buildRows([
    { path: 'a', versions: [{ hash: h(1), present: true }] },
    { path: 'b', versions: [{ hash: h(2), present: false }] },
    { path: 'c', versions: [{ hash: h(3), present: false }] },
    { path: 'd', versions: [{ hash: h(4), present: false }] },
    { path: 'e', versions: [{ hash: h(5), present: false }] },
    { path: 'f', versions: [{ hash: h(6), present: true }, { hash: h(7), present: false }] },
    { path: 'g', versions: [{ hash: h(8), present: false }] },
  ], [{ hash: h(2), status: 'requested', peer: 3 }, { hash: h(3), status: 'queued' }, { hash: h(4), status: 'waiting' }, { hash: h(7), status: 'waiting' },
    { hash: h(8), status: 'localFailure' }]);
  assert.deepEqual(rows.map((r) => r.status), ['complete', 'fetching', 'queued', 'waiting', 'pending', 'conflicted', 'localFailure']);
  assert.equal(STATUS_TEXT.localFailure, 'could not be stored on this device');
  assert.notEqual(STATUS_TEXT.localFailure, STATUS_TEXT.waiting, 'a local failure does not read as a peer problem');
  assert.deepEqual(rows[5].versions.map((v) => v.status), ['complete', 'waiting']);
});
test('names with slashes from other devices are shown with a folder prefix', () => {
  assert.deepEqual(splitPath('docs/2026/plan.md'), { dir: 'docs/2026/', base: 'plan.md' });
  assert.deepEqual(splitPath('plan.md'), { dir: '', base: 'plan.md' });
  assert.deepEqual(splitPath('odd/'), { dir: 'odd/', base: 'odd/' });
});
test('keep-both names', () => {
  assert.equal(uniqueName('a.txt', new Set(['a.txt'])), 'a (2).txt');
  assert.equal(uniqueName('a.txt', new Set(['a.txt', 'a (2).txt'])), 'a (3).txt');
  assert.equal(uniqueName('d/README', new Set()), 'd/README (2)');
});
