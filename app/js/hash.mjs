// SHA-256 via WebCrypto (user decision 6). WebCrypto has no incremental digest, so callers hash
// one in-memory buffer; that is why files are limited to MAX_FILE_BYTES (storage.mjs).
export async function sha256(bytes) {
  return new Uint8Array(await crypto.subtle.digest('SHA-256', bytes));
}
export const hex = (b) => Array.from(b, (x) => x.toString(16).padStart(2, '0')).join('');
export function fromHex(s) {
  const out = new Uint8Array(s.length / 2);
  for (let i = 0; i < out.length; i++) out[i] = parseInt(s.slice(2 * i, 2 * i + 2), 16);
  return out;
}
