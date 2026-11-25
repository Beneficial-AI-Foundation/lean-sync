# Vendored: `qr` (QR code encoder and decoder)

Unmodified files from the npm package **`qr` 0.7.2** by Paul Miller, licence **MIT OR Apache-2.0**
(both licence texts are here: `LICENSE` is Apache-2.0, `LICENSE-MIT` is MIT).

- Source: https://registry.npmjs.org/qr/-/qr-0.7.2.tgz (repository https://github.com/paulmillr/qr,
  commit `951806df842fb7c9214012a73b00e60b259243d3` per the registry's `gitHead`)
- Tarball integrity as published by the registry and checked on download:
  `sha512-yovYRuacJBJkG9fWSwcB2bKZhr58c04DpOXguDU+rAAoJZdi6/J3DtlomkKqdd1MutIptIK+kigWmT7LKz8y7A==`
  (sha1 `47b4b6b018fdd27331bea034c111fb8db01bbc16`)
- Only the two files the app loads are vendored (`package/index.js`, `package/decode.js`), plus the
  licences. `decode.js` imports `./index.js`; neither imports anything else.

| File | Bytes | SHA-256 |
|---|---|---|
| `index.js` (encoder) | 43,717 | `3e3d38c37ecc5691b1edcc5b0dd6882b78280dc7f2130168bd7df074d1b21e47` |
| `decode.js` (decoder) | 148,131 | `9d7c0bb9a53cf58db5499b437a92512847d560d2ac20eebfb17b1e3820552f29` |
| `LICENSE` (Apache-2.0) | 11,361 | `f9946796a8a5bd5981565142fa42e3b0cc36aef6f80e86beaf5905b3c0fef1b5` |
| `LICENSE-MIT` | 1,109 | `07a9f887e9215644439b808628b09f8eece932d79130ff563f958f3a1783e684` |

Used by `app/js/pairing-ui.mjs` (`encodeQR` to draw codes, `decodeQR` to read camera frames). The
end-to-end test `pair-by-qr-fake-camera` checks the round trip in Chromium and Firefox through the
app's own scanning loop. To update: replace both files from a new tarball, check its integrity
against the registry, and update this table.
