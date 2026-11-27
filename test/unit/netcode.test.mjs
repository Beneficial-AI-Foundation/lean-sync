// Pairing codes (app/js/netcode.mjs): format, checks, SDP extraction and rebuild (docs/net-design.md §4).
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { base32, unbase32, crc32, extractSdp, selectCandidates, rebuildSdp, encodePayload, decodePayload,
  formatCode, parseCode, groupCode, offerTag, CodeError } from '../../app/js/netcode.mjs';

const fx = (n) => readFileSync(join(dirname(fileURLToPath(import.meta.url)), 'fixtures', n), 'utf8');
const SDPS = ['chromium', 'chromium-mdns', 'firefox', 'firefox-mdns'].flatMap((b) => ['offer', 'answer'].map((k) => ({ name: `${b}-${k}`, kind: k, sdp: fx(`sdp-${b}-${k}.txt`) })));
const TAG = Uint8Array.of(1, 2, 3, 4);
const codeOf = ({ kind, sdp }) => { const x = extractSdp(sdp); x.cands = selectCandidates(x.cands); return formatCode(kind, encodePayload({ kind, tag: TAG, ...x })); };
const rejects = (fn, reason) => assert.throws(fn, (e) => e instanceof CodeError && e.reason === reason && e.message.length > 10);

test('base32 round trip, every length, and only canonical padding accepted', () => {
  for (let n = 0; n < 40; n++) {
    const b = Uint8Array.from({ length: n }, (_, i) => (i * 37 + n) & 255);
    assert.deepEqual(unbase32(base32(b)), b);
  }
  assert.equal(unbase32('0U'), null, 'U is not a Crockford digit');
  assert.equal(unbase32(base32(Uint8Array.of(255)).slice(0, 1) + 'Z'), null, 'non-zero padding bits rejected');
  assert.equal(crc32(new TextEncoder().encode('123456789')), 0xcbf43926, 'standard CRC-32 check value');
});

test('real SDPs from Chromium and Firefox: code round trip, sizes, rebuilt SDP keeps every field', () => {
  for (const s of SDPS) {
    const x = extractSdp(s.sdp);
    assert.ok(x.ufrag && x.pwd && x.fp && x.mid !== null && x.cands.length >= 1, s.name);
    const code = codeOf(s);
    assert.match(code, /^LS[NR]1[0-9A-HJKMNP-TV-Z]+$/, 'upper-case letters and digits only');
    assert.ok(code.length <= 210, `${s.name}: ${code.length} characters`);
    const r = parseCode(code, s.kind);
    assert.equal(r.ufrag, x.ufrag); assert.equal(r.pwd, x.pwd); assert.equal(r.fp, x.fp.toUpperCase());
    assert.deepEqual(r.cands, selectCandidates(x.cands));
    if (s.kind === 'answer') assert.deepEqual(r.tag, TAG);
    const again = extractSdp(rebuildSdp(r, s.kind, x.mid));
    assert.deepEqual({ ...again, setup: null }, { ...x, cands: selectCandidates(x.cands), fp: x.fp.toUpperCase(), setup: null });
    assert.equal(again.setup, s.kind === 'offer' ? 'actpass' : 'passive', 'the answerer is always passive');
  }
});

test('tolerant reading: case, spaces, dashes, line breaks, O/I/L', () => {
  const code = codeOf(SDPS[0]);
  const ref = parseCode(code, 'offer');
  const messy = groupCode(code).toLowerCase().replace(/ /g, (m, i) => (i % 3 ? ' ' : '-\n'));
  assert.deepEqual(parseCode(messy, 'offer'), ref);
  const body = code.slice(4);
  const alt = code.slice(0, 4) + body.replace(/0/g, 'O').replace(/1/g, 'I');
  assert.deepEqual(parseCode(alt, 'offer'), ref);
});

test('every proper prefix and every single-character change is rejected', () => {
  for (const s of [SDPS[0], SDPS[3]]) {
    const code = codeOf(s);
    for (let n = 0; n < code.length; n++) {
      assert.throws(() => parseCode(code.slice(0, n), s.kind), CodeError, `prefix of ${n}`);
    }
    const alphabet = '0123456789ABCDEFGHJKMNPQRSTVWXYZ';
    for (let i = 4; i < code.length; i++) {
      for (const ch of alphabet) {
        if (ch === code[i]) continue;
        const bad = code.slice(0, i) + ch + code.slice(i + 1);
        assert.throws(() => parseCode(bad, s.kind), CodeError, `change at ${i} to ${ch}`);
      }
    }
    assert.throws(() => parseCode(code + '0', s.kind), CodeError, 'an extra character');
  }
});

test('wrong kind, version, foreign text: clear reasons', () => {
  const offer = codeOf(SDPS[0]), answer = codeOf(SDPS[1]);
  rejects(() => parseCode(offer, 'answer'), 'kind');
  rejects(() => parseCode(answer, 'offer'), 'kind');
  rejects(() => parseCode('LSN2' + offer.slice(4), 'offer'), 'version');
  rejects(() => parseCode('hello world', 'offer'), 'notCode');
  rejects(() => parseCode('   ', 'offer'), 'empty');
  rejects(() => parseCode('LSN1' + 'A'.repeat(2000), 'offer'), 'damaged');
  // a payload whose version nibble is not 1 (CRC recomputed so only the version is wrong)
  const p = encodePayload({ kind: 'offer', ...extractSdp(SDPS[0].sdp), cands: [] });
  p[0] = 0x21;
  const body = p.subarray(0, p.length - 4), c = crc32(body);
  p.set([c >>> 24, (c >>> 16) & 255, (c >>> 8) & 255, c & 255], p.length - 4);
  rejects(() => decodePayload(p), 'version');
});

test('candidates: at most two host and two srflx; IPv6, mDNS and names encode exactly', () => {
  const base = extractSdp(SDPS[0].sdp);
  const cands = [{ type: 'host', addr: '192.0.2.1', port: 1 }, { type: 'host', addr: '2001:db8::1', port: 2 }, { type: 'host', addr: '192.0.2.2', port: 3 },
    { type: 'srflx', addr: '203.0.113.5', port: 4 }, { type: 'srflx', addr: 'fe80::1:2:3', port: 5 }, { type: 'srflx', addr: '203.0.113.6', port: 6 }];
  const sel = selectCandidates(cands);
  assert.deepEqual(sel.map((c) => c.port), [1, 2, 4, 5]);
  const odd = [{ type: 'host', addr: '0a1b2c3d-0000-4000-8000-123456789abc.local', port: 9 }, { type: 'host', addr: 'my-host.example', port: 65535 }];
  for (const cs of [sel, odd, []]) {
    const r = decodePayload(encodePayload({ kind: 'offer', ...base, cands: cs }));
    assert.deepEqual(r.cands.map((c) => c.port), cs.map((c) => c.port));
    assert.deepEqual(r.cands.map((c) => c.addr), cs.map((c) => (c.addr === '2001:db8::1' ? '2001:db8:0:0:0:0:0:1' : c.addr === 'fe80::1:2:3' ? 'fe80:0:0:0:0:1:2:3' : c.addr)));
  }
  assert.throws(() => encodePayload({ kind: 'offer', ...base, cands: [...sel, sel[0]] }), /too many/);
});

test('the offer tag binds a reply to its invitation', async () => {
  const offer = codeOf(SDPS[0]);
  const t1 = await offerTag(parseCode(offer, 'offer').payload);
  const t2 = await offerTag(parseCode(codeOf(SDPS[4]), 'offer').payload);
  assert.equal(t1.length, 4);
  assert.notDeepEqual(t1, t2);
  assert.throws(() => encodePayload({ kind: 'answer', ...extractSdp(SDPS[1].sdp), cands: [] }), /tag/);
});
