# Peer-to-peer transport (WebRTC data channels): design, measurements, and what was built

Branch `webrtc-transport`. **Stage 1** (probe and design, §1 and the first version of §2–§13) and
**stage 2** (built: `app/js/transport/webrtc.mjs`, `app/js/netcode.mjs`, `app/js/pairing-ui.mjs`,
`app/vendor/qr/`; the relay is gone). §2–§11 now describe what was built; each deviation from the
stage-1 design is marked **Deviation** with its reason, and every number is marked measured or
designed. `LeanCrdt/` and `LeanSync/` are unchanged. Companion notes: `docs/app-design.md` (host,
links, tests, host-obligations table §4), `docs/sync-design.md` §8 (host obligations).

Decisions taken by the user, and the constraints this note works within:
- **Manual signalling at every connection, no server of ours.** Device A shows an offer as a QR
  code; device B scans it and shows an answer QR; A scans that. A copy-paste text code is the
  fallback when there is no camera. Automatic reconnect (pair once, rendezvous, device keys) comes
  later: the signalling is an interface so that it can be added (§3), and it is not built.
- **A public STUN server**, default Google's, configurable, and the app must work with none. No TURN.
- Trust model unchanged: all devices are the user's; robust to corruption and disconnects, not to
  malicious peers. The manual code exchange is the authentication (the codes carry the DTLS
  fingerprints).
- **The app is served as static files over HTTPS** by an ordinary web server (§8). Every device is
  a secure context, so the camera is available wherever a camera exists. No hosting setup,
  certificates or service worker in this project for now; this stage is built and tested between
  browsers on one machine.

What is **measured** is marked as such and comes from the probe (§1). What is read in
documentation or believed is said to be so.

## 1. Feasibility probe (measured)

The stage-1 probe (`test/e2e/probe-webrtc.mjs`, `test/e2e/probe-static.mjs`, in commit `5db05ec`;
removed in stage 2, their findings now covered by tests) drove two separate headless browser
processes with separate profiles through the e2e driver, the driver passing offer and answer.
Browsers: Chromium 154.0.8037.92, Firefox 146.0, Firefox ESR 140.16.0esr, all headless, on Linux.
Pairings are written offerer→answerer: C = Chromium, F = Firefox, E = Firefox ESR.

### 1.1 Candidates and connectivity (no STUN unless stated)

| Configuration | Chromium candidates | Firefox / ESR candidates | C→C | F→F | C→F | F→C | E→C | E→F |
|---|---|---|---|---|---|---|---|---|
| default (browser settings) | 1 × host UDP, **mDNS name** (`<uuid>.local`) | 2 × host UDP mDNS (IPv4 + IPv6 interface), 2 × host TCP mDNS port 9 (active) | ok | ok | ok | ok | ok | ok |
| mDNS off (C: `--disable-features=WebRtcHideLocalIpsWithMdns`; F: `media.peerconnection.ice.obfuscate_host_addresses=false`) | 1 × host UDP 192.168.0.207 | host UDP 192.168.0.207 and fd35:…::1bc, host TCP both | ok | ok | ok | ok | ok | ok |
| fake local STUN (Node, answers with 203.0.113.7) | + srflx 203.0.113.7 | no srflx (Firefox ignores a STUN server on 127.0.0.1, believed: not investigated) | ok | ok | ok | ok | ok | ok |
| Google STUN `stun:stun.l.google.com:19302` (this machine has internet) | + srflx (public IPv4), arrives after 7–14 ms, **gathering "complete" only after ~39.9 s** | + srflx after 9–15 ms, complete after 23–34 ms | ok | ok | ok | **fail** (4/4) | **fail** (2/2) | ok |
| loopback-only network namespace | see §1.8 | see §1.8 | | | | | | |

- Every connection above was made twice, once with the full SDP and once with the SDP **rebuilt from
  the minimal code** (§4); the results were identical in every pairing, so both browsers accept the
  rebuilt SDP. ICE gathering was awaited (non-trickle).
- The selected pair was host↔host (or host↔prflx) in all successful runs, including with STUN
  (same machine). Connections with mDNS candidates succeeded in every pairing when the answer was
  applied at once (sometimes through a peer-reflexive candidate, i.e. one side never resolved the name).
- **Gathering time with an unreachable STUN server:** Chromium 39.9 s (unroutable 192.0.2.1 and a
  closed local port alike), Firefox 11.1 s (unroutable). Chromium also took ~40 s with Google's
  server reachable (the srflx arrived in 14 ms; what it waits for is not identified, probably the
  IPv6 address of `stun.l.google.com` on a host without IPv6 routing). **So the app must not wait
  for "gathering complete"**: it finalises the code after complete, or after the first srflx plus
  a short quiet time, or after a cap of ~2 s, whichever comes first (§5).
- The F→C/E→C failures with Google STUN are explained in §1.2: they are a consequence of the
  answerer waiting, not of STUN.
- Firefox throws `NS_ERROR_UNEXPECTED` from the `RTCPeerConnection` constructor for a STUN URL
  with port 9 (a blocked port); the settings UI must validate STUN URLs by constructing a
  throw-away connection and must not break pairing if that throws.

### 1.2 The answerer waits for a human: delayed answers (the most important finding)

Between B creating its answer (B starts ICE checks at that moment) and A applying it, a person
scans B's QR or pastes its text. The probe inserts a delay there.

| Experiment (minimal SDP, mDNS off unless stated) | C→C | F→F | C→F | F→C |
|---|---|---|---|---|
| answerer `setup:active` (browser default), delay 0 / 20 / 40 / 70 s | all ok | all ok | all ok | ok / ok, **open 5.6 s late** / ok, **11.2 s late** / **fail** |
| answerer `setup:passive`, delay 0 / 20 / 70 / 150 / 300 s | all ok, open ≤ 5 ms after | all ok | all ok | all ok |
| passive, B given **unreachable** addresses for A's candidates (B's own checks fail, as through A's NAT), delay 0 / 10 / 20 / 40 s (C→C, F→C also 70, 150 s) | all ok | ok, ok, **fail**, **fail** | ok, ok, **fail**, **fail** | all ok |
| passive, B given **no** candidates of A, delay 0 / 20 / 70 / 150 s | all ok | ok, then **fail** | ok, then **fail** | all ok |
| passive, browser default (mDNS on), delay 0 / 20 / 70 s | all ok | ok, **fail**, **fail** | ok, ok, **fail** | all ok |
| passive, mDNS on, Google STUN, gathering capped at 2 s, delay 0 / 20 s | ok, ok | ok, **fail** | ok, ok | ok, **fail** |

What this shows:
1. **DTLS role.** Measured: with the default role a Firefox offerer and a Chromium answerer open
   the channel 5.6 s late after a 20 s delay, 11.2 s late after 40 s, never after 70 s, although ICE
   is connected. Inferred mechanism (not traced): the Chromium answerer is the DTLS client and sends
   its ClientHello as soon as ICE connects, before A has the answer (A already answers ICE checks);
   Firefox drops it, and Chromium's retransmission back-off grows. **Fix: the answerer always takes `a=setup:passive`** (it edits
   its own answer before `setLocalDescription`; both browsers accept this). Then A, the DTLS
   client, starts the handshake when it applies the answer. With this, every pairing survived a
   300 s delay when B could reach A.
2. **ICE timeout of the answerer.** If B's checks cannot succeed before A applies the answer — B
   cannot resolve A's mDNS name, or (the real-world case) **A is behind a NAT that drops B's checks
   until A itself sends** — the answerer's ICE agent gives up: **Firefox 11.1 s** after it starts
   checking (5.0 s if it has no candidates at all), and Chromium in the Google-STUN case 15.1 s
   (`disconnected`, then `failed`; cause not identified; Chromium survived 150 s with unreachable
   candidates). A failed agent does not answer A's later checks, so the connection never forms.
   Across networks this is the normal situation, so **an answer is good for only ~10 s** after it
   is made, unless B reaches A on its own (same LAN, IP addresses visible).
3. The earlier Google-STUN F→C failures are case 2 (the probe waited 30 s for Chromium's
   gathering before handing over the answer).

Consequences for the design (§5, §6): the answerer's code is **live** — B makes a fresh answer
every ~5 s and shows the newest, so the QR that A scans is at most ~5 s old plus the scan time;
the slow manual leg (paste, send-to-self) should carry the **offer**, which does not age (A's
connection waited 300 s without harm); the fast leg (QR scan) should carry the answer.

### 1.3 Data channel limits and back-pressure

| Measured (mDNS off, no STUN) | C→C | F→F | C→F | F→C |
|---|---|---|---|---|
| `pc.sctp.maxMessageSize` (full SDP) | 262,144 | 1,073,741,823 | 262,144 | 262,144 |
| same, rebuilt SDP (we state `a=max-message-size:262144`) | 262,144 | 262,144 | 262,144 | 262,144 |
| 16,417 / 65,536 / 65,537 / 262,144 B, both directions | all delivered intact | same | same | same |
| send of 262,145 B and 1 MiB | `TypeError` thrown synchronously, channel stays open | same | same | same |
| send 64 KiB messages without waiting, up to 64 MiB | Chromium: `OperationError: send queue is full` at bufferedAmount = **16 MiB**, channel stays open | Firefox: no error at 64 MiB buffered | as C | as F |
| 32 MiB as 16,417 B frames, high water 1 MiB, refill on `bufferedamountlow` (threshold 256 KiB) | 107 MiB/s, max buffered 1.06 MB, in order | 52 MiB/s | 56 MiB/s | 63 MiB/s |

**Fit with `links.mjs`: as is.** Frames are ≤ 16 KiB + 33 B, far below 256 KiB; `links.mjs` keeps
`bufferedAmount` under 1 MiB (`HIGH_WATER`), far below Chromium's 16 MiB cap; the receiver's credit
(4 MiB window) and the 256 MiB file limit are independent of the transport. Unlike the WebSocket,
a data channel has a drain event (`bufferedamountlow`), so `onDrain` needs no polling, and
`bufferedAmount` is per link instead of shared by all links of the socket. Ordered, reliable
channels (the default) give the "ordered and reliable" the interface promises.

### 1.4 Closing and loss: what the other side sees

Times are after the action, as seen by B (B's browser listed second).

| Action on A | C→C | F→F | C→F | F→C |
|---|---|---|---|---|
| `dc.close()` | B: channel `close` after 3 ms; connection stays `connected` | 2 ms | 3 ms | 1 ms |
| new channel on the same connection after that | opens in ~300 ms | same | same | same |
| `pc.close()` | B: `close` (with `error` "User-Initiated Abort") after 2 ms | 5 ms | 2 ms | 0 ms |
| A's tab closed | **B: `disconnected` 6.2 s, `failed` 16.2 s, channel stays `open`** | `close` 10 ms | B: `disconnected` 10.6 s, `failed` + `close` 29.9 s | `close` 8 ms |
| A's browser killed (SIGKILL) | **B: `disconnected` 5.0 s, `failed` 15.0 s, channel still `open` at 75 s** | B: `disconnected` 10.3 s, `failed` + `close` 29.9 s | as F→F | as C→C (6.3 s, 16.3 s, channel open) |

- Firefox closes its connections when a tab closes; Chromium (headless, tab closed through CDP)
  does not. Whether a `pagehide` handler calling `pc.close()` makes Chromium send the abort is not
  measured.
- **A Chromium receiver never closes the channel after a silent loss**: the transport must take
  the connection state into account (§5), not only the channel's `close` event.

### 1.5 Code sizes (measured on the real SDPs)

Binary layout of §4.2 (proposed format, version 1); the probe encoder kept a setup byte that the
final format drops. QR version needed at error-correction level M, alphanumeric mode for
base32/base45, byte mode for the raw SDP.

| Code | Full SDP | QR for full SDP | Minimal code | base32 chars → QR (M) |
|---|---|---|---|---|
| Chromium offer, mDNS, no STUN (code computed from the layout) | ~590 B (586 B measured for a Chromium answer with one candidate) | v19 (93×93) | 87 B | 140 → v6 (41×41) |
| Chromium offer, mDNS off, no STUN (code computed) | ~580 B (estimate) | v19 | 75 B | 120 → v5 (37×37) |
| Chromium offer, mDNS + srflx (measured) | 716–720 B | v25 (117×117) | 94 B | 151 → v6 |
| Chromium answer, mDNS + srflx (measured) | 586–714 B | v19–v25 | 92–99 B | 148–159 → v6–v7 |
| Firefox offer, 2 × mDNS, no STUN (measured) | 927 B | v25 | 118 B | 189 → v8 (49×49) |
| Firefox offer/answer, 2 × mDNS + srflx (measured) | 1,022–1,044 B | v30 (137×137) | 125–130 B | 200–208 → v8 |

So the minimal code is about **8× smaller** than the SDP: QR version 5–8 (37–49 modules) instead of
19–30 (93–137); version 5–8 codes are routinely scanned by phone cameras from screens (belief, not
measured here). The bulk is fixed: the
fingerprint (32 B) and the ICE password (24 or 32 B). Firefox's ufrag/password are hex and could be
packed to half (saves 20 B); a host candidate costs 7 B (IPv4) or 19 B (IPv6 or mDNS). Not
measured: real scanning from a screen (needs a phone).

### 1.6 QR availability

`BarcodeDetector` is **undefined** in headless Chromium 154 on Linux, Firefox 146 and Firefox ESR
140 (measured). It exists in Chrome on Android and macOS and Safari 17+ (read; not measured). So a
decoder must be shipped. `getUserMedia`, `navigator.clipboard.readText` and `CompressionStream`
exist in all three (measured).

### 1.7 Persistent certificates (for the later "pair once" stage)

`RTCPeerConnection.generateCertificate({name:'ECDSA', namedCurve:'P-256'})` stored in IndexedDB,
the browser restarted, the certificate read back and given to a new connection: the SDP shows the
same fingerprint (Chromium 154, Firefox 146, ESR 140: measured). Default expiry is **30 days**
(measured), so a later stage must set `expires` explicitly and handle renewal. Not needed now.

### 1.8 Loopback only (no network interface)

Run inside `unshare -rn` (a new user and network namespace, no root needed), so the browsers see
no network at all:

| Namespace | Candidates | Result (C→C, F→F, C→F, F→C, E→C, E→F; full and rebuilt SDP) |
|---|---|---|
| only `lo` up; browser default, mDNS off, and mDNS off + loopback allowed (C: `--allow-loopback-in-peer-connection`; F: `media.peerconnection.ice.loopback=true`) | **none** in either browser | all fail (Chromium stays `new`, Firefox `failed`) |
| `lo` + a dummy interface `d0` 10.99.0.1/24 with a default route | host 10.99.0.1 (mDNS off) or mDNS names | **all connect**, with mDNS on and off |

So the loopback flags do not help (in these versions), and a test machine without a network
interface can still run the WebRTC tests inside a namespace with a dummy interface:
`unshare -rn sh -c 'ip link set lo up && ip link add d0 type dummy && ip addr add 10.99.0.1/24 dev d0 && ip link set d0 up && ip route add default dev d0 && …'`
(needs unprivileged user namespaces, enabled here). In the namespace, Chromium with an unreachable
STUN server did not even finish gathering within 60 s.

### 1.9 Stage 2 gate: reply renewal (measured before building)

B makes a fresh answer from the same offer every *period*, keeping at most 6 attempts alive; after
*apply* seconds A applies the newest answer at least *age* old (the scan time). "Actual age" is the
age when A applied it, including the driver's overhead. Minimal SDP, passive answerer, probe of
stage 2 (in the history of this branch).

| Case | Period | Result |
|---|---|---|
| simulated cross-NAT (B given unreachable addresses for A), mDNS off; apply at 12 / 31 / 62 s; ages 0.5 / 4.5 / 8 s; C→C, F→F, C→F, F→C | 5 s | **all actual ages 0.7–6.9 s connected in every pairing**; at 10.8–12.0 s a Firefox answerer fails (4 of 6), a Chromium answerer connects; no other attempt ever opened a channel |
| reachable (mDNS off), same grid without 8 s | 5 s | 24/24 connected |
| browser defaults (mDNS on), no STUN | 5 s | Chromium answerer all ok; Firefox answerer fails at actual ages 5.8–7.0 s: it cannot resolve the offerer's mDNS names here, which is its 5.0 s "no candidates" timeout of §1.2 |
| browser defaults, no STUN | **2.5 s** | F→F, C→F, C→C all ok (ages 0.7–4.4 s) |
| browser defaults, Google STUN | 5 s | C→C, C→F, F→F ok up to 6.9 s; F→C one failure among concurrent runs |
| F→C, browser defaults, one pairing at a time in fresh browsers | 5 s | 6/6 with renewal, 8/8 without (control): the F→C failures came only with several pairings running at once in the same browsers (mDNS name resolution) |

**Deviation (period): 2.5 s instead of 5 s**, so that the reply on screen is fresh enough for the
5 s case (Firefox answerer, offerer candidates it cannot resolve, no STUN). The e2e scenario
`reply-renewal` repeats the cross-NAT simulation in all four pairings through the real UI (§10).

## 2. The transport (as built)

Interface (header of `app/js/transport/webrtc.mjs`), the relay's plus pairing:
```
transport.start({ onLink(link), onStatus(text) })   transport.setOnline(bool)   transport.stop()   transport.online
link: { id, remoteLabel, send(frame) → bool, close(), bufferedAmount, onFrame(cb), onClose(cb), onDrain(cb) }
invite() → { code, expiresAt, state, noSrflx, accept(replyText) → Promise, cancel() }
respond(inviteText) → { code, state, noSrflx, attempts, onCode(cb), done: Promise, cancel() }   (throws CodeError at once)
connections() → [{ id, role, state, since, linkId, remoteOnline }]   disconnect(id)   onChange(cb)
```
One pairing = one `RTCPeerConnection` (a *connection*) carrying:
- a **control channel** `ctl` (negotiated, id 0) for the connection's life. It carries only
  `{t:'online', v}`, so that a device that goes offline is not re-linked by the other one until
  it is back, and its closing means the other device closed the connection (Disconnect, page
  closed). **Deviation (addition):** the stage-1 design had no control channel; "offline keeps the
  connection" (decision 5) needs one, otherwise the inviting device would keep reopening links to
  an offline device;
- at most one **sync channel** (ordered, reliable) = one link = one PeerId in `links.mjs`. The
  inviting device opens it when the control channel is open and both sides are online; the
  joining device accepts it. When a link closes on a live connection (engine restart via
  `links.resetAll()`, a protocol error, the other side's restart or offline), the inviting device
  opens a new one after a back-off (0.5 s doubling to 30 s, reset after a link lived 20 s; the
  relay's rule, so a refused link cannot spin; measured in e2e `same-replica-id-refused`: 3
  attempts in ~4 s).

| Interface | As built |
|---|---|
| `send` | `dc.send`; false if closed. An exception closes the link. **A channel no longer `open` while the link is up takes the link down at once** (measured in e2e `disconnect-mid-transfer-and-resume`, C→F: a Chromium channel closed with ~1 MiB buffered stayed `closing` and never reached Firefox, so frames were dropped silently and the transfer hung) |
| `onDrain` | `bufferedamountlow` (threshold 256 KiB); fires at once if the buffer is already below it |
| `onClose` exactly once | first of: channel `close`; connection `failed`/`closed`; `disconnected` for 5 s; control channel closed; `link.close()`; a failing send; **a new incoming channel on the joining side replaces its current link** (the inviting device opens one only after its own link is down, and the old one's close may never arrive) |
| `remoteLabel` | "paired device"; the label comes with HELLO (`links.labelOfLink`) |
| `setOnline(false)` | closes links, keeps connections, tells the other device (decision 5) |
| `stop()` | closes every connection; called on `pagehide` |

Measured (e2e `peer-killed-files-recover`, this machine, in the test network namespace): after the
other browser is killed, the link goes down after 11.1 s (Chromium receiver) and 14.7–16.5 s
(Firefox receiver); the connection is dropped (state `failed`) after 15.9 s and ~29.8 s. After the
other device closes its tab, the connection is dropped after ~0.1 s in every pairing (the test
polls every 100 ms), thanks to `pagehide` (Chromium does not close by itself, §1.4).

## 3. Signalling (as built)

Exactly one offer goes from A to B and one answer from B to A; the codes are opaque strings to
everything but `netcode.mjs`. The manual method is the UI (§6). A later rendezvous (not built)
would carry the same strings; it would also need persistent certificates (§1.7) and a device list.

## 4. Code format (as built: `app/js/netcode.mjs`)

**Text:** `LSN1` (invitation) or `LSR1` (reply) + the payload in Crockford base32 (digits and
capitals without I, L, O, U). Reading ignores case, spaces, line breaks and `-`, and reads O as 0
and I/L as 1 in the payload. The QR holds the text in alphanumeric mode. Shown in groups of four.
**Deviation:** prefix `LSN1`/`LSR1` instead of `LS1O`/`LS1A` (the letter O in a prefix would
collide with the O→0 rule).

**Payload (version 1):** as designed (§4.2 of stage 1): kind byte; reply: 4-byte offer tag =
SHA-256(invitation payload)[0..4]; ufrag and password (lower-case hex packed two digits per
byte); 32-byte SHA-256 fingerprint; ≤ 4 UDP candidates (≤ 2 host, then ≤ 2 srflx; IPv4, IPv6,
mDNS UUID or name); CRC-32. Not carried: setup (invitation `actpass`, reply always `passive`), the
inviting device's mid, SCTP port, `max-message-size` (always 262,144).

**Sizes (measured, e2e `pair-by-text`, no STUN, mDNS off, one host candidate):** invitation 124
characters from Chromium, 112 from Firefox; reply 131 from Chromium, 118 from Firefox. Unit tests
encode real SDPs of both browsers (fixtures, addresses replaced by documentation ranges) in ≤ 210
characters.

**Checks (measured, unit `netcode`):** every proper prefix and every single-character change of a
code is rejected; also a wrong kind, version, foreign text, empty input, over-long input. Messages:
"not a LeanSync pairing code", "made by a different version of the app", "a reply code, not an
invitation" (and vice versa), "incomplete or mistyped", "belongs to another invitation", "already
used", "expired". e2e `pairing-codes-rejected` checks them through the UI.

**Reuse and staleness (as built):** an invitation is single-use and lives in A's page: void when
its dialog is closed, the page reloads, after the first accepted reply, or after 10 minutes. A
second reply is refused ("already used"); a reply made for another invitation is refused ("belongs
to another invitation"). B keeps renewing its reply for **2 minutes**, then says "The other device
did not answer. Start again on the device that made the invitation." **Deviation:** 2 min instead
of 30 s: B cannot tell a void invitation from one not yet scanned.

## 5. Connection lifecycle (as built)

```
A invite()                                   B respond(invitation)
  pc + ctl; offer; gather (≤ 2 s)              every 2.5 s while waiting (≤ 6 alive, oldest closed; 2 min max):
  show the invitation                            pc + ctl; offer rebuilt; answer with a=setup:passive;
                                                 gather (≤ 2 s); show the newest reply
  accept(reply): checks; rebuild; setRemote  → ICE, DTLS (A client), SCTP → ctl open on both
  30 s without ctl open → "could not connect"   the attempt whose ctl opens wins; the others are closed
A opens the sync channel → link on both sides → links.mjs HELLO → Lean `connected p`
```
Gathering is finished on `complete`, on the first srflx + 300 ms, or after 2 s (measured, e2e
`stun-settings`: with an unreachable STUN server the invitation is shown 2.06–2.09 s after the
click in both browsers; Chromium alone reports completion after ~40 s, §1.1). Nothing is
persisted except the STUN list; a reload ends every connection (decision 1).

## 6. Pairing UI (as built: `app/js/pairing-ui.mjs`)

A **Devices** panel (connected devices with their label and state — connected, connecting…,
reconnecting…, paired (you are offline / the other device is offline) — and *Disconnect*),
*Invite a device*, *Join a device*, the *online* box, and *Connection settings* (STUN list).
The pairing dialog:
- **Invite:** the invitation QR, its text with *Copy* (and *Share…* where available), "valid for
  one device, until HH:MM", a STUN warning if a STUN server was configured but unreachable; then
  "read the reply": *Scan the reply with the camera* and a paste field.
- **Join:** *Scan the invitation* / paste; then the reply QR and text, renewed every 2.5 s, with
  "Sending it as text instead? Paste it on the first device right away: when the devices are on
  different networks a reply is good for only about 10 seconds."; the no-camera rule ("If one of
  your two devices has no camera, start the invitation on the device that has one") is stated on
  the Join screen.
- **Camera:** no `videoinput` → "No camera found on this device: paste the code instead." and no
  scan button; permission refused → "Camera access was refused: paste the code instead."; other
  errors named. The scanning loop draws the video into a canvas (≤ 640 px wide) every 200 ms and
  decodes it with the vendored `qr` decoder.
- **Results:** "Connecting…", "Connected. You can close this window." (the dialog stays open until
  the user closes it: **Deviation**, so that a mistaken second reply still gets its message), the
  connection-failure help of stage 1 §6, and a message when a connection ends ("…ended (lost, or
  closed by the other device). Pair again to reconnect.").
- **Phone size (measured, e2e `pairing-ui-phone-viewport` at 360×740):** no horizontal scroll of
  the page or the dialog, dialog inside the screen, QR 200–340 px wide, code box inside.

Two browser behaviours found while building (both fixed in the app, both caught by tests): a
`<video>` made by script must be muted by **property** (the attribute does not mute it, `play()`
is then refused and the frame stays frozen: the camera never scanned); a dialog's `close` event
is queued, and in Chromium a late one arrived after the next dialog had opened and cancelled its
reply (the handler now ignores it while the dialog is open).

## 7. STUN configuration (as built)

*Connection settings*: one `stun:`/`stuns:` URL per line; default `stun:stun.l.google.com:19302`;
empty = none. Stored in IndexedDB (`stun`), never read from the URL. Each URL is checked by
constructing a throw-away `RTCPeerConnection` (Firefox refuses e.g. port 9 there); a refused list
is not saved and says why. Changes apply to the next pairing. With no STUN, codes carry host
candidates only (measured in e2e). The tests never use the internet: every device's list is set to
empty through this UI, except in `stun-settings`, which checks the default, refusals, an
unreachable server and the empty list.

## 8. Static hosting (as built)

The app is `build/site/` as plain files; nothing in it uses a server endpoint. Measured:
`runs-from-sub-path` serves the site under `/some/sub/dir/` and pairs two devices there; every
request was for a site file. `no-network-except-paired-devices` checks that a page makes no
WebSocket, EventSource or foreign fetch, no connection before the user pairs, uses only the ICE
servers of the setting, and that URL parameters `relay`, `room`, `stun` are ignored. Server
requirements (unchanged from stage 1 §8): HTTPS; `.mjs` served as JavaScript; `.wasm` preferably as
`application/wasm`; revalidation (`Cache-Control: no-cache`) because file names are not
versioned; no COOP/COEP. Storage is per origin: each device has its own; moving the app to another
origin gives every device a fresh store there; two copies under different paths of one origin
share one store and one Web Lock.

## 9. The relay (done: option (a))

Removed from the app (`app/js/transport/relay.mjs`), from `dev/serve.mjs` (now a static server
with an optional base path) and from the tests (`test/unit/relay.test.mjs`). The faults it
injected are injected by the `NET` init script of `test/e2e/lib.mjs`, which wraps
`RTCPeerConnection` and `RTCDataChannel.send` on the sending device: cut the sync channel after N
bytes, flip a byte of the next blob frame, send a garbage message; it also counts connections,
bytes, ICE servers and any WebSocket/EventSource/foreign fetch.

## 10. Tests (as built)

**Network for the e2e tests.** `test/e2e/run.mjs` re-runs itself inside `unshare -rn` (new user and
network namespace, no root) with `lo` and a dummy interface 10.99.0.1/24 plus a default route:
WebRTC needs a non-loopback interface (§1.8), and the tests then never touch the real network or
the internet. Without user namespaces it uses the host network if it has a non-loopback IPv4
address, else it stops with an explanation. Devices launch with mDNS off (Chromium flag, Firefox
pref) except in `pair-with-browser-defaults`.

**Pairing in tests** goes through the real UI: `pair(A, B)` in `test/e2e/lib.mjs` clicks *Invite* and
*Join*, pastes the codes into the paste fields, or shows each side's QR (the canvas, as an image)
to the other side's fake camera (init script `CAMERA`: `enumerateDevices` and `getUserMedia`
replaced by a canvas stream; also "absent" and "refused" modes).

**Scenarios added:** `pair-by-text` (C+C, F+F, C+F, F+C, E+C, C+E, E+F), `pair-by-qr-fake-camera`
(C+F, F+C, C+C, F+F; also decodes the drawn QR directly), `pairing-codes-rejected` (C+F+C, F+C+F:
foreign, truncated, one character changed, wrong version, wrong kind both ways, stale, reused),
`reply-renewal` (C+F, F+F, F+C, C+C: B given unreachable candidates, reply read 12 s after B
joined; measured 5 replies in 12 s, at most 5 attempts alive), `peer-killed-files-recover` (C+C,
F+F, C+F, F+C), `three-devices-pairwise` (C+F+C, F+C+F), `stun-settings` (C, F),
`pairing-ui-phone-viewport` (C+F, F+C), `runs-from-sub-path` (C+F), `pair-with-browser-defaults`
(C+C, F+F, C+F, F+C), `no-network-except-paired-devices` (C+F, F+C; replaces
`relay-parameter-ignored`). **Every existing scenario runs over WebRTC**, with pairing in place of a
relay room; a page reload or a killed browser is followed by pairing again; `three-device-chain`
pairs A–B and B–C only. None had to be dropped.

**Unit:** `netcode` (7 tests, real SDP fixtures of both browsers) and `webrtc` (13 tests, the
transport against an in-memory fake `RTCPeerConnection` that keeps a vanished peer's channel open
as Chromium does).

**Not testable automatically here:** real cameras and screens (glare, distance, focus); phones
(Chrome on Android, Firefox on Android; Safari is unsupported: Memory64); real NATs and networks
(the cross-NAT case is simulated by unreachable candidates); Google's STUN; mDNS between
separate machines; background tabs and sleeping phones; `navigator.share` and the clipboard.

## 11. Host obligations

The rows are in `docs/app-design.md` §4, each with its mechanism, test and mutant
(`node test/mutations.mjs`).

## 12. Decisions (taken by the user after stage 1)

1. A reload, crash or sleep means pairing again; nothing about pairings is persisted.
2. Codes as base32 text.
3. `qr` (Paul Miller) vendored unmodified (`app/vendor/qr/`, README with version, source, integrity
   and file hashes), no `BarcodeDetector` path; its round trip is tested in Chromium and Firefox
   through the app's scanning loop (`pair-by-qr-fake-camera`).
4. The reply renews itself while shown (2.5 s, §1.9); no-camera rule and text-path warning shown.
5. Going offline closes links and keeps connections.
6. No heartbeat; loss from the connection state (and the channel treated as dead).
7. Relay removed; faults injected by init scripts; `dev/serve.mjs` a static server.
8. Default STUN Google's, user-editable, empty works.

## 13. What remains to verify on real devices (checklist: one phone, one desktop)

Serve `build/site/` over HTTPS from any static host; open it on the desktop (Chrome or Firefox) and
on the phone (Chrome or Firefox for Android; Safari is unsupported, it lacks WebAssembly Memory64).
1. **QR, desktop invites:** desktop *Invite*, phone *Join* → *Scan*, then the desktop scans the
   phone's reply with its webcam. Both say "Connected"; add a file on each side; both lists show
   both files complete.
2. **QR, phone invites:** the same with roles swapped.
3. **Desktop without camera** (or camera permission refused): invite on the phone; send the
   invitation text to the desktop (mail/chat to yourself), paste it in *Join*; the phone scans the
   desktop's reply. Check the "No camera found" / "Camera access was refused" messages.
4. **Text both ways:** copy the reply and paste it on the other device at once (expect success);
   on different networks, also wait 30 s before pasting (expect the "Could not connect" help: the
   documented limit, §1.2).
5. **Different networks:** phone on mobile data, desktop on Wi-Fi, default STUN; pair by QR.
   Record whether it connects (it cannot when both sides are behind symmetric NATs: no TURN).
6. **Same Wi-Fi, STUN list emptied on both:** pair; expect a connection over the LAN (mDNS names).
7. **Sleep and background:** lock the phone or switch apps for 1–2 minutes during a transfer; on
   return the device shows "reconnecting…" or the connection ended; after pairing again the
   transfer completes.
8. **Closing:** close the desktop tab; the phone lists the connection as ended within a second.
9. **Offline toggle:** untick and tick *online* on the phone; the devices re-link without pairing.
10. **Phone UI:** portrait and landscape; the dialog fits, buttons are reachable, the QR scans from
    20–40 cm, the code text can be copied.
11. **Volume:** a 100 MB file phone ↔ desktop over Wi-Fi; note the time and that it completes.
