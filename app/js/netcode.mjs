// Pairing codes (docs/net-design.md §4): what one device shows and the other pastes.
// Pure functions, no DOM and no WebRTC (unit-tested in Node).
//
// Text form: 'LS' + kind ('N' invitation = offer, 'R' reply = answer) + format version ('1') +
// the payload in Crockford base32. Upper-case letters and digits only (easy to read back and
// to type). The reader ignores case, spaces, line breaks and '-', and reads O as 0 and
// I/L as 1 in the payload.
//
// Payload (version 1):
//   u8   0x10 | kind (1 offer, 2 answer)
//   [answer] 4 B offer tag = SHA-256(offer payload)[0..4]
//   ufrag, password: u8 len + ASCII; len | 0x80 = lower-case hex packed two digits per byte
//   32 B DTLS fingerprint (SHA-256)
//   u8 n (≤ 4) candidates: u8 type | addrKind << 2, address, u16 port
//      type 0 host, 1 srflx; addrKind 0 IPv4 (4 B), 1 IPv6 (16 B), 2 mDNS UUID (16 B), 3 name (u8 len + bytes)
//   4 B CRC-32 (big-endian) of everything before it
// Not carried (known to the receiver): a=setup (offer actpass, answer always passive), the
// offerer's mid, the SCTP port and max-message-size, the session lines.

export const FORMAT_VERSION = 1;
const PREFIX = { offer: 'LSN', answer: 'LSR' };
const KIND_BYTE = { offer: 1, answer: 2 };
const MAX_CANDIDATES = 4;
const MAX_TEXT = 1000;

export class CodeError extends Error {
  constructor(reason, message) { super(message); this.name = 'CodeError'; this.reason = reason; }
}
const MSG = {
  notCode: 'This is not a LeanSync pairing code.',
  version: 'This code was made by a different version of the app. Use the same version on both devices.',
  wantOffer: 'This is a reply code, not an invitation. On this device, paste the invitation shown by the other device.',
  wantAnswer: 'This is an invitation code, not a reply. Paste the reply that the other device shows after it joined.',
  damaged: 'This code is incomplete or mistyped. Copy it again in full.',
};

// ------------------------------------------------------------------ base32 (Crockford) and CRC-32
const B32 = '0123456789ABCDEFGHJKMNPQRSTVWXYZ';
const B32_VAL = (() => { const m = new Map(); [...B32].forEach((c, i) => m.set(c, i)); m.set('O', 0); m.set('I', 1); m.set('L', 1); return m; })();
export function base32(bytes) {
  let out = '', acc = 0, bits = 0;
  for (const b of bytes) { acc = (acc << 8) | b; bits += 8; while (bits >= 5) { bits -= 5; out += B32[(acc >>> bits) & 31]; } acc &= (1 << bits) - 1; }
  if (bits) out += B32[(acc << (5 - bits)) & 31];
  return out;
}
export function unbase32(text) {
  const out = []; let acc = 0, bits = 0;
  for (const ch of text) {
    const v = B32_VAL.get(ch);
    if (v === undefined) return null;
    acc = (acc << 5) | v; bits += 5;
    if (bits >= 8) { bits -= 8; out.push((acc >>> bits) & 255); }
    acc &= (1 << bits) - 1;
  }
  if (bits >= 5 || acc !== 0) return null;              // only zero padding bits, fewer than 5
  return Uint8Array.from(out);
}
const CRC_TABLE = (() => { const t = new Uint32Array(256); for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1; t[n] = c >>> 0; } return t; })();
export function crc32(bytes) { let c = 0xffffffff; for (const b of bytes) c = CRC_TABLE[(c ^ b) & 255] ^ (c >>> 8); return (c ^ 0xffffffff) >>> 0; }

// ------------------------------------------------------------------ SDP
/** The parts of an SDP the other side needs. Candidates: UDP, component 1, host or srflx. */
export function extractSdp(sdp) {
  const L = sdp.split(/\r?\n/);
  const get = (re) => { for (const l of L) { const m = l.match(re); if (m) return m[1].trim(); } return null; };
  const cands = [];
  for (const l of L) {
    if (!l.startsWith('a=candidate:')) continue;
    const f = l.slice(12).trim().split(/\s+/);
    if (f.length < 8 || f[1] !== '1' || f[2].toLowerCase() !== 'udp') continue;
    const type = f[7];
    if (type !== 'host' && type !== 'srflx') continue;
    cands.push({ type, addr: f[4], port: Number(f[5]) });
  }
  return { ufrag: get(/^a=ice-ufrag:(.+)$/), pwd: get(/^a=ice-pwd:(.+)$/), fp: get(/^a=fingerprint:sha-256 (.+)$/i),
    setup: get(/^a=setup:(.+)$/), mid: get(/^a=mid:(.+)$/), cands };
}
/** At most 4 candidates: up to two host, then up to two srflx, in the browser's order, no duplicates. */
export function selectCandidates(cands) {
  const seen = new Set(), pick = (type, n) => cands.filter((c) => c.type === type && addrKind(c.addr) !== null)
    .filter((c) => { const k = `${c.addr} ${c.port}`; if (seen.has(k)) return false; seen.add(k); return true; }).slice(0, n);
  return [...pick('host', 2), ...pick('srflx', 2)];
}
/** An SDP the browser accepts as remote description, rebuilt from the code's fields. */
export function rebuildSdp(x, type, mid) {
  const L = ['v=0', 'o=- 1 2 IN IP4 127.0.0.1', 's=-', 't=0 0', `a=group:BUNDLE ${mid}`,
    'm=application 9 UDP/DTLS/SCTP webrtc-datachannel', 'c=IN IP4 0.0.0.0', `a=mid:${mid}`,
    `a=ice-ufrag:${x.ufrag}`, `a=ice-pwd:${x.pwd}`, `a=fingerprint:sha-256 ${x.fp}`,
    `a=setup:${type === 'offer' ? 'actpass' : 'passive'}`, 'a=sctp-port:5000', 'a=max-message-size:262144'];
  x.cands.forEach((c, i) => {
    const prio = (c.type === 'host' ? 126 : 100) * 2 ** 24 + (65535 - i) * 2 ** 8 + 255;
    L.push(`a=candidate:${i + 1} 1 udp ${prio} ${c.addr} ${c.port} typ ${c.type}${c.type === 'host' ? '' : ' raddr 0.0.0.0 rport 0'}`);
  });
  L.push('a=end-of-candidates');
  return L.join('\r\n') + '\r\n';
}

// ------------------------------------------------------------------ addresses
const UUID_LOCAL = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}\.local$/i;
function addrKind(a) {
  if (/^\d{1,3}(\.\d{1,3}){3}$/.test(a) && a.split('.').every((p) => Number(p) <= 255)) return 0;
  if (a.includes(':') && ipv6Bytes(a)) return 1;
  if (UUID_LOCAL.test(a)) return 2;
  if (/^[A-Za-z0-9.-]{1,255}$/.test(a)) return 3;
  return null;
}
function ipv6Bytes(a) {
  if (a.includes('%') || a.includes('.')) return null;
  const halves = a.split('::');
  if (halves.length > 2) return null;
  const hs = halves[0] ? halves[0].split(':') : [], ts = halves.length === 2 && halves[1] ? halves[1].split(':') : [];
  const fill = halves.length === 2 ? 8 - hs.length - ts.length : 0;
  if (fill < 0 || (halves.length === 1 && hs.length !== 8)) return null;
  const parts = [...hs, ...Array(fill).fill('0'), ...ts];
  if (parts.length !== 8 || parts.some((p) => !/^[0-9a-f]{1,4}$/i.test(p))) return null;
  return parts.flatMap((p) => { const v = parseInt(p, 16); return [v >> 8, v & 255]; });
}

// ------------------------------------------------------------------ payload
function putString(out, s) {
  if (/^[0-9a-f]+$/.test(s) && s.length % 2 === 0 && s.length / 2 < 128) {
    out.push(0x80 | (s.length / 2)); for (let i = 0; i < s.length; i += 2) out.push(parseInt(s.slice(i, i + 2), 16));
  } else {
    if (s.length >= 128 || !/^[\x21-\x7e]+$/.test(s)) throw new Error(`cannot encode ICE credential "${s}"`);
    out.push(s.length); for (const ch of s) out.push(ch.charCodeAt(0));
  }
}
/** Encode the fields of an offer or answer (from extractSdp, candidates already selected). */
export function encodePayload({ kind, tag, ufrag, pwd, fp, cands }) {
  const out = [(FORMAT_VERSION << 4) | KIND_BYTE[kind]];
  if (kind === 'answer') { if (!tag || tag.length !== 4) throw new Error('answer needs a 4-byte offer tag'); out.push(...tag); }
  putString(out, ufrag); putString(out, pwd);
  const fpb = fp.split(':').map((h) => parseInt(h, 16));
  if (fpb.length !== 32 || fpb.some((b) => !(b >= 0 && b <= 255))) throw new Error('fingerprint must be SHA-256');
  out.push(...fpb);
  if (cands.length > MAX_CANDIDATES) throw new Error('too many candidates');
  out.push(cands.length);
  for (const c of cands) {
    const k = addrKind(c.addr);
    if (k === null) throw new Error(`cannot encode address ${c.addr}`);
    out.push((c.type === 'srflx' ? 1 : 0) | (k << 2));
    if (k === 0) out.push(...c.addr.split('.').map(Number));
    else if (k === 1) out.push(...ipv6Bytes(c.addr));
    else if (k === 2) { const h = c.addr.slice(0, 36).replace(/-/g, ''); for (let i = 0; i < 32; i += 2) out.push(parseInt(h.slice(i, i + 2), 16)); }
    else { out.push(c.addr.length); for (const ch of c.addr) out.push(ch.charCodeAt(0)); }
    out.push(c.port >> 8, c.port & 255);
  }
  const crc = crc32(out);
  out.push(crc >>> 24, (crc >>> 16) & 255, (crc >>> 8) & 255, crc & 255);
  return Uint8Array.from(out);
}
/** Decode a payload; throws CodeError('damaged') on any inconsistency. */
export function decodePayload(b) {
  const bad = () => { throw new CodeError('damaged', MSG.damaged); };
  if (b.length < 1 + 2 + 2 + 32 + 1 + 4) bad();
  const body = b.subarray(0, b.length - 4);
  const crc = ((b[b.length - 4] << 24) | (b[b.length - 3] << 16) | (b[b.length - 2] << 8) | b[b.length - 1]) >>> 0;
  if (crc32(body) !== crc) bad();
  let o = 0;
  const need = (n) => { if (o + n > body.length) bad(); };
  const v = body[o++];
  if (v >> 4 !== FORMAT_VERSION) throw new CodeError('version', MSG.version);
  const kind = (v & 15) === 1 ? 'offer' : (v & 15) === 2 ? 'answer' : bad();
  const x = { kind };
  if (kind === 'answer') { need(4); x.tag = body.slice(o, o + 4); o += 4; }
  const str = () => {
    need(1); const l = body[o++];
    if (l & 0x80) { const n = l & 0x7f; if (!n) bad(); need(n); const s = Array.from(body.subarray(o, o + n), (y) => y.toString(16).padStart(2, '0')).join(''); o += n; return s; }
    if (!l) bad(); need(l); const s = String.fromCharCode(...body.subarray(o, o + l)); o += l;
    if (!/^[\x21-\x7e]+$/.test(s)) bad();
    return s;
  };
  x.ufrag = str(); x.pwd = str();
  need(32); x.fp = Array.from(body.subarray(o, o + 32), (y) => y.toString(16).padStart(2, '0').toUpperCase()).join(':'); o += 32;
  need(1); const n = body[o++]; if (n > MAX_CANDIDATES) bad();
  x.cands = [];
  for (let i = 0; i < n; i++) {
    need(1); const h = body[o++], t = h & 3, k = h >> 2;
    if (t > 1 || k > 3) bad();
    let addr;
    if (k === 0) { need(4); addr = Array.from(body.subarray(o, o + 4)).join('.'); o += 4; }
    else if (k === 1) { need(16); const p = []; for (let j = 0; j < 16; j += 2) p.push(((body[o + j] << 8) | body[o + j + 1]).toString(16)); addr = p.join(':'); o += 16; }
    else if (k === 2) { need(16); const hx = Array.from(body.subarray(o, o + 16), (y) => y.toString(16).padStart(2, '0')).join(''); addr = `${hx.slice(0, 8)}-${hx.slice(8, 12)}-${hx.slice(12, 16)}-${hx.slice(16, 20)}-${hx.slice(20)}.local`; o += 16; }
    else { need(1); const m = body[o++]; if (!m) bad(); need(m); addr = String.fromCharCode(...body.subarray(o, o + m)); o += m; if (!/^[A-Za-z0-9.-]+$/.test(addr)) bad(); }
    need(2); const port = (body[o] << 8) | body[o + 1]; o += 2;
    if (!port) bad();
    x.cands.push({ type: t ? 'srflx' : 'host', addr, port });
  }
  if (o !== body.length) bad();
  return x;
}

// ------------------------------------------------------------------ text form
export const formatCode = (kind, payload) => `${PREFIX[kind]}${FORMAT_VERSION}${base32(payload)}`;
/** For display: groups of four characters. */
export const groupCode = (code) => code.match(/.{1,4}/g).join(' ');
/**
 * Read a code typed or pasted. `expect`: 'offer' or 'answer'. Returns the decoded fields
 * plus `payload` (the bytes, for the offer tag). Throws CodeError with a message for the user.
 */
export function parseCode(text, expect) {
  if (typeof text !== 'string' || text.length > MAX_TEXT) throw new CodeError('damaged', MSG.damaged);
  const t = text.replace(/[\s-]/g, '').toUpperCase();
  if (!t) throw new CodeError('empty', 'Paste a code first.');
  if (!/^LS[NR]/.test(t)) throw new CodeError('notCode', MSG.notCode);
  const kind = t[2] === 'N' ? 'offer' : 'answer';
  if (t.length < 4) throw new CodeError('damaged', MSG.damaged);
  if (t[3] !== String(FORMAT_VERSION)) throw new CodeError('version', MSG.version);
  if (kind !== expect) throw new CodeError('kind', expect === 'offer' ? MSG.wantOffer : MSG.wantAnswer);
  const payload = unbase32(t.slice(4));
  if (!payload) throw new CodeError('damaged', MSG.damaged);
  const x = decodePayload(payload);
  if (x.kind !== kind) throw new CodeError('damaged', MSG.damaged);
  return { ...x, payload };
}
/** First 4 bytes of SHA-256(offer payload): binds a reply to its invitation. */
export async function offerTag(payload) {
  return new Uint8Array(await crypto.subtle.digest('SHA-256', payload)).slice(0, 4);
}
export const sameBytes = (a, b) => a.length === b.length && a.every((v, i) => v === b[i]);
