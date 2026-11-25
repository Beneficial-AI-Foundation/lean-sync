# Peer-to-peer transport (WebRTC data channels): design note and feasibility probe

Branch `webrtc-transport` · stage 1 of the networking task: probe and design only. Nothing in
`app/`, `LeanCrdt/` or `LeanSync/` changes in this stage; the Lean libraries need no change for
the design below. Companion notes: `docs/app-design.md` (host, links, tests),
`docs/sync-design.md` §8 (host obligations).

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

`test/e2e/probe-webrtc.mjs` (throwaway; not run by `scripts/test-app.sh`) drives two separate
headless browser processes with separate profiles through the existing e2e driver
(`test/e2e/driver.mjs`, which gained an `args` option for extra Chromium flags). The driver passes
the offer and the answer. `test/e2e/probe-static.mjs` checks the built site on a plain static
server (§8). Browsers: Chromium 154.0.8037.92, Firefox 146.0, Firefox ESR 140.16.0esr, all
headless, on Linux (one Wi-Fi interface with IPv4 and IPv6 ULA addresses, docker bridges down).
Pairings are written offerer→answerer: C = Chromium, F = Firefox, E = Firefox ESR.

```
node test/e2e/probe-webrtc.mjs --phase connect|life|delay|stungather|qr|cert [--configs default,nomdns,fakestun,google]
    delay options: --passive --offer-mod none|unreach|nocands --delays 0,20000 --pairings CC,FC --stun URL --gather-ms N
unshare -rn sh -c 'ip link set lo up && node test/e2e/probe-webrtc.mjs --netns --phase connect'   # loopback only
node test/e2e/probe-static.mjs
```

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

## 2. The transport interface today, and what WebRTC must provide

Today (`app/js/transport/relay.mjs` header, used by `main.mjs`, `links.mjs`, `ui.mjs`):

```
transport.start({ onLink(link), onStatus(text) })   transport.setOnline(bool)   transport.stop()
transport.online (getter)                           transport.closeAll()        (defined, never called)
link: { id, remoteLabel, send(frame) → bool, close(), bufferedAmount,
        onFrame(cb(frame)), onClose(cb()), onDrain(cb()) }
```
Promises: links are ordered and reliable; frames ≤ 16 KiB + a few bytes; `onClose` exactly once per
link, whoever closed it; `bufferedAmount`/`onDrain` give back-pressure. `links.mjs` attaches each
link, sends HELLO, and turns it into a Lean peer only after the remote's HELLO; PeerIds are a
page-lifetime counter in `links.mjs` (never reused). An engine restart (`core.mjs`) calls
`links.resetAll()`, which closes every link with `link.close()`; the relay then re-links after its
back-off.

WebRTC fits with these mappings:

| Interface | WebRTC |
|---|---|
| link | one ordered, reliable `RTCDataChannel` (label `sync`, binaryType `arraybuffer`) on a connection (`RTCPeerConnection`) made by one pairing |
| `link.send(frame)` | `dc.send(frame)`; returns false if the channel is not open; **an exception closes the link** (it can only be the 16 MiB cap or a size error, i.e. a bug; never lose a frame silently) |
| `bufferedAmount`, `onDrain` | `dc.bufferedAmount`; `bufferedamountlow` with threshold 256 KiB (measured to fire, §1.3) |
| `onFrame` | `dc.onmessage` (ArrayBuffer → Uint8Array) |
| `onClose`, exactly once | first of: channel `close`; connection `failed` or `closed`; connection `disconnected` for longer than `LOSS_MS` (5 s); `link.close()`. After it fires the transport closes the channel so nothing late is delivered |
| `link.close()` | `dc.close()` (the connection stays up: a new channel can replace it, §5) |
| `remoteLabel` | not known before HELLO: the transport passes "paired device"; `links.mjs` takes the label from HELLO as today |
| `setOnline(false)` | close every channel; keep the connections (open question Q5) |
| engine restart (`link.close()` on every link) | closes every channel; connections stay; channels are reopened (§5) |
| `start` / `stop` | `stop` closes every connection |

New, beyond the relay's interface: **pairing** (§3) and a connection list for the UI
(`transport.connections()`: id, state, label once known, since when). The relay transport never
needed these because the relay decided the topology.

## 3. Signalling interface

Signalling moves exactly one offer from A to B and one answer from B to A. It is separate from the
transport so that a later rendezvous service can replace the human without touching the transport:

```
// webrtc transport: pairing operations (codes are opaque strings to everything else)
const inv = await transport.invite();         // A: { code, expiresAt, accept(answerCode) → Promise, cancel() }
const rsp = await transport.respond(offerCode); // B: { code, onCode(cb(newCode)), cancel() }  — code is live (§5)
// both: connection becomes a link through onLink when its channel opens; failures through onPairing(id, state, reason)

// a signalling method carries those strings between two devices
interface Signalling {
  sendOffer(code) / receiveOffer() → code      // manual: show QR+text / scan or paste
  sendAnswer(code) / receiveAnswer() → code
}
```
The manual method is the UI of §6: "send" = show a QR and a text with Copy/Share; "receive" = scan
with the camera or paste. A later automatic method (not built) would post the same codes to a
rendezvous, keyed by something both devices learnt in a first manual pairing (a shared secret, and
the peer's persistent certificate fingerprint, §1.7), so that the user is not involved: it needs
only this interface plus persistent certificates and a device list. Nothing in the code format
below prevents that: a rendezvous can carry the same codes.

## 4. Code format

### 4.1 Text form
`LS1` + kind (`O` offer, `A` answer) + payload in **Crockford base32** (digits and upper-case
letters without I, L, O, U). The reader ignores case, spaces, line breaks and `-`, and maps
`O→0`, `I/L→1`, so a code survives being pasted through chat apps, line-wrapped or read aloud. In
the QR the code is upper-case only, which QR encodes in **alphanumeric mode** (5.5 bits per char).
base45 was considered: 7 % shorter but it contains space, `%`, `$`, `*` and `/`, which chat apps and
editors trim or rewrite; at error-correction level M both give the same QR versions for our sizes.
Displayed in groups of four characters.

### 4.2 Payload (version 1)
```
u8   0x10 | kind (1 offer, 2 answer)            version 1 in the high nibble
[answer only] 4 B offer tag = SHA-256(offer payload)[0..4]
u8 len + ufrag      u8 len + password            (ASCII; hex ones packed: flag in the length's top bit)
32 B DTLS fingerprint (SHA-256)
u8 n, then n candidates (UDP, component 1 only, at most 4):
     u8 type(host/srflx/prflx) | addr kind<<2 (IPv4, IPv6, mDNS UUID, other name)
     address (4 / 16 / 16 / u8 len + bytes)   u16 port
4 B CRC-32 of everything before it
```
Not carried because the receiver knows it: `a=setup` (offer `actpass`; answer always `passive`,
§1.2), `mid` (the offerer keeps its own; the answer is rebuilt with it), SCTP port 5000, the
`max-message-size` (always stated as 262,144: §1.3), the session lines. Candidates kept: first
IPv4 host, first IPv6 host, srflx; TCP candidates are dropped (the probe connected over UDP in
every case). The rebuilt SDP is the probe's `rebuild()` (§1.1: accepted by both browsers).

### 4.3 Checks and their messages
A code is rejected before any WebRTC call if: the prefix is not `LS`; the version is not one this
app reads ("made by a different version of the app"); the kind is wrong ("this is an invitation,
not a reply" and vice versa); the CRC fails or the length does not match the structure ("this code
is incomplete or mistyped": CRC-32 detects every burst error up to 32 bits and anything else with
probability 1 − 2⁻³²; a truncated code fails the CRC or the length); an answer's offer tag is not
the one of the invitation on screen ("this reply belongs to another invitation"). A QR has its own
Reed-Solomon correction; the CRC is for the text path.

### 4.4 Reuse and staleness
- **An offer is single-use** and lives in A's memory: it is void when A's pairing screen is closed,
  the page reloads, the first answer has been accepted, or after a time limit (proposal: 10 min; A
  then makes a fresh one on screen). A second answer to a used offer is refused ("this invitation
  was already used"); two devices that scanned the same invitation: only the one whose reply A
  scans connects, the other's reply times out.
- **B with a void offer** produces an answer that nobody accepts: B shows "could not connect — the
  other device is no longer waiting for this code; start again there" after its attempt times out
  (30 s).
- **An answer is good for ~10 s** across networks (§1.2), so B's code is live (§5) and an answer
  pasted much later may fail on a Firefox device or across NATs; the UI says so.
- An old answer pasted into a new invitation is refused by the offer tag. Replaying codes needs
  the user to scan the attacker's code, i.e. outside the trust model. The codes contain local and
  public IP addresses: the UI says not to post them publicly.

## 5. Connection lifecycle

```
A invite()                      B respond(offer)                          (manual or later automatic signalling)
  new pc(iceServers), dc "sync"    every 5 s while not connected (max 6 live attempts):
  setLocalDescription                new pc, setRemoteDescription(rebuilt offer)
  wait: gathering complete,          answer with a=setup:passive; setLocalDescription
    or first srflx + 300 ms,         wait for candidates as A does; publish the newest code
    or 2 s                         when any attempt's channel opens: close the other attempts
  show code                        
  accept(answer): rebuild SDP, setRemoteDescription   → ICE, DTLS (A is the client), SCTP, channel open
both: channel open → onLink(link) → links.mjs HELLO → Lean `connected p`
```
- **Renewed answers are a design, not yet measured as such**: the probe measured one answer per
  offer with a delay (§1.2). That A answers ICE checks from several of B's attempts harmlessly, and
  that the attempt A scanned wins, is to be tested first in stage 2 (unit with the probe's
  "unreachable" mode, then e2e).
- **Peer ids.** Unchanged: `links.mjs` assigns PeerIds on HELLO (page-lifetime counter). Every new
  channel is a new link, hence a new PeerId and a fresh Lean session, as with the relay.
- **Loss.** `onClose` fires on channel `close`, on connection `failed`/`closed`, or after
  `disconnected` has lasted `LOSS_MS` = 5 s (measured detection after a silent loss: Chromium 5 s
  to `disconnected`, Firefox 10 s, so links go down after ~10 s and ~15 s). Lean then gets
  `disconnected p` and re-plans. The connection is kept while it is only `disconnected`; if ICE
  recovers to `connected`, a new channel is opened (new PeerId). `failed` is final: **the user must
  pair again** (no signalling channel exists for an ICE restart).
- **Channel closed, connection alive** (engine restart via `links.resetAll()`, `links.mjs` killing a link
  for a protocol error, own-replica refusal, the remote's restart): the device that made the offer
  opens a new channel after a back-off (0.5 s doubling to 30 s, reset after a channel lived 20 s —
  the relay's rule, so a link closed for an error cannot spin); the answerer accepts incoming
  channels as new links. Measured: a replacement channel opens in ~300 ms (§1.4). So **an engine
  restart does not need re-pairing**.
- **Page closing.** On `pagehide` the transport closes every connection, so that peers learn at
  once (Firefox does this itself; Chromium does not — §1.4; whether it works from `pagehide` is to
  be measured in stage 2).
- **Nothing is persisted**: connections, codes, ICE passwords and certificates live only in the
  page. Reloading the page drops every connection; every device must pair again. (See Q1.)

## 6. Pairing UI, step by step

A "Devices" panel replaces the relay's status: the connected devices (label from HELLO, since when,
Disconnect), and two buttons, **Invite a device** and **Join a device**.

Device A (inviting):
1. *Invite a device* → "Preparing…" (≤ 2 s, gathering) → the invitation QR, the code as text with
   *Copy* (and *Share…* where `navigator.share` exists), and "On the other device choose *Join a
   device* and scan this code. If that device has no camera, send it this text." A timer shows the
   invitation's remaining validity (10 min).
2. *Scan the reply* (opens the camera; the video and a frame for aiming) or *Paste the reply*.
3. On a valid reply: "Connecting…" → "Connected to *label*" (label from HELLO), the panel closes.
   Errors: messages of §4.3; after 30 s without a channel: "Could not connect" (below).

Device B (joining):
1. *Join a device* → *Scan invitation* (camera) or *Paste invitation*.
2. On a valid invitation: the reply QR, its text with Copy/Share, and "Now scan this code with the
   first device". The QR is replaced by a fresh one every 5 s (a small progress ring shows it);
   that is invisible to someone scanning, and keeps the reply usable (§1.2).
3. When the channel opens: "Connected to *label*". After 2 minutes without success B stops making
   attempts: "The first device did not answer. Start again on the first device."

**No camera.** The slow manual leg must carry the invitation, the fast leg the reply (§1.2). So:
if one device has no camera, **start on the device that has one** (it invites; the camera-less
device pastes the invitation, which does not age, and shows the reply QR, which the first device
scans at once). Both devices without a camera: both codes go by text (send-to-self, chat); the
reply must then be pasted within about 10 s when the devices are on different networks — the UI
says "paste the reply quickly" and offers "make a new reply". The UI detects a missing camera
(`enumerateDevices` has no `videoinput`, or permission denied) and hides the scan buttons.

**Failure messages.**
- Camera denied: "Camera access was refused; you can paste the code instead."
- No STUN reachable while one is configured (no srflx candidate gathered): shown before the code:
  "Could not reach the connection helper (*host*); devices on different networks may not be able to
  connect. Same Wi-Fi works."
- No channel after 30 s: "Could not connect to *the other device*. Both devices must keep this
  page open. Devices on different networks connect only if their routers allow direct
  connections; this app does not relay data through a server. Try on the same Wi-Fi network, or
  try again."
- Connection lost later: the device disappears from the list with "connection lost — pair again
  to reconnect" (after `failed`), or "reconnecting…" while `disconnected`.

## 7. STUN configuration

- A setting "Connection helper (STUN)": a list of `stun:` URLs, default
  `stun:stun.l.google.com:19302`, and "none". Stored in IndexedDB next to the label (one more
  row in "nothing else persisted"); not settable by URL parameter (the reasoning of the old
  `?relay=` finding: a crafted link must not change where the app talks to; here it would only
  leak the IP address to another STUN server, but the rule stays simple). Changes apply to the next
  pairing.
- With "none": no srflx candidates, only host candidates; devices connect on the same LAN (and the
  same machine), not across NATs. The pairing screen says so once.
- What STUN reveals: the STUN server sees the device's public address; the codes contain it. With
  mDNS on (browser default), local addresses are hidden behind `.local` names (§1.1), which works
  between devices of one LAN when multicast works there (not measured beyond this machine).
- Gathering is capped (§1.1), so an unreachable STUN server costs at most 2 s per code, not
  Chromium's 40 s.

## 8. Static hosting

The shipped app is `build/site/` served as plain files over HTTPS by any static web server. The
WebRTC path uses nothing of `dev/serve.mjs`.
- **Measured** (`test/e2e/probe-static.mjs`): the site runs from a **sub-path**
  (`/some/sub/path/`) in Chromium and Firefox; every URL is relative (`js/main.mjs`, `app.css`,
  `../lean/lean_sync.mjs`, `new URL("lean_sync.wasm", import.meta.url)` in the glue).
- **MIME types**: `.mjs` must be served as JavaScript (`text/javascript`): module scripts are
  rejected otherwise (read: HTML spec, strict MIME check for modules). `.wasm` should be
  `application/wasm` for streaming compilation; served as `application/octet-stream` the app still
  starts in both browsers (measured: the Emscripten glue falls back to ArrayBuffer instantiation).
- **No special headers**: the engine uses no threads and no `SharedArrayBuffer` (none in the glue),
  so cross-origin isolation (COOP/COEP) is not needed. HTTPS is needed for a secure context (OPFS,
  Web Locks, camera); `http://127.0.0.1` and `http://localhost` count as secure for local tests.
- **Caching**: file names are not versioned, so the server should make browsers revalidate
  (`Cache-Control: no-cache` with ETag/Last-Modified), or a device may run a new `lean_sync.mjs`
  with an old `.wasm`. A future build could hash file names instead.
- **Storage is per origin** (scheme, host, port), not per path: two devices that load the same URL
  each have their own storage (that is the point: each is one replica). Two copies of the app
  under different paths of one origin would **share** one store and one Web Lock. Moving the app
  to another origin later gives every device a fresh, empty store under the new origin (a new
  replica: its files come back by syncing from a device that still has them; edits made only on
  that device under the old origin stay behind until it is opened there again).
- **What happens to `/relay` today** (measured): on a static server the relay client retries every
  0.5 s doubling to 10 s forever and logs "relay unreachable"; the app otherwise runs. In the
  design the relay client leaves `app/` (§9), so the shipped app makes no request to its origin
  beyond loading its files, and no network traffic except STUN and paired peers.

## 9. What the relay transport becomes

Options:
- **(a, recommended) Removed from the app.** The app has one transport, WebRTC. The end-to-end
  tests pair devices through the real UI (§10), and the faults that the relay injected (cut at a
  byte offset, corrupt the next blob frame, inject a garbage message, topology) are injected from
  outside by init scripts that wrap `RTCPeerConnection`/`RTCDataChannel` — the same practice as the
  existing storage and trap faults, keeping the app byte-identical to what ships. `dev/serve.mjs`
  becomes a static server (still with the `no-store` header); the relay and admin API are deleted
  with their unit test, after every scenario passes over WebRTC.
- (b) Kept in the app and enabled only when the origin offers it (e.g. the dev server serves a
  `transport.json`). No test-only code, but a second transport in the shipped app that real use
  never exercises, and a server file that would switch it on anywhere.
- (c) Chosen at build time. Then the tested app is not the shipped app: rejected.

The relay was also what decided topology; with manual pairing the topology is exactly the pairs
the driver makes, which is simpler for the tests.

## 10. Test plan

Unit (`node --test`, no browser):
- code format: round trip; every proper prefix rejected; every single-character substitution of
  the text rejected; kind swap; wrong version; foreign offer tag; tolerant reading (case, spaces,
  `-`, line breaks, `O/I/L`); size bound (≤ 4 candidates).
- SDP extract/rebuild against SDPs captured from both browsers (fixtures from the probe).
- transport with fake `RTCPeerConnection`/`RTCDataChannel` objects: `onClose` exactly once across
  every combination of channel close / `failed` / `closed` / `disconnected` timeout / own close;
  `send` exception closes the link; channel reopen back-off; offer single-use; answer attempts
  rotate and are all closed when one opens.

End-to-end (headless, each device its own browser process and profile, as today):
- **Pairing through the real UI**: the driver reads the invitation text from A's page, types it into
  B's paste field, reads B's reply text and pastes it into A (no hook into the app). One scenario
  per pairing also exercises the **QR path**: an init script replaces `getUserMedia` with
  `canvas.captureStream()` of the other device's rendered QR (taken from its page as an image), so
  the real scanning loop and decoder run; the decoder is also checked directly on the rendered
  canvas. A camera cannot be used headless.
- **Every existing scenario** runs over WebRTC (same browser configurations), with `pair()` in place
  of joining a room; three-device chains pair A–B and B–C only.
- New scenarios: answer applied after 30 s (passive role; same LAN); invitation reused (second
  reply refused); stale reply (offer tag); peer browser killed → link down within ~15 s and a
  re-pair works; engine trap → a new channel on the same connection, no re-pairing; STUN "none"
  and an unreachable STUN server (gathering cap: code within 2 s in Chromium); no network
  request other than loading files (init script counts `WebSocket`/`fetch`/`EventSource`).
- **Browser settings for tests**: mDNS off (Chromium
  `--disable-features=WebRtcHideLocalIpsWithMdns`, Firefox
  `media.peerconnection.ice.obfuscate_host_addresses=false`) for deterministic candidates, no STUN;
  plus one scenario with default browser settings (mDNS on) in each pairing, which worked on this
  machine when the answer is applied at once. The tests need a network interface (loopback alone
  gives no candidates, §1.8); `scripts/test-app.sh` can run the e2e step inside `unshare -rn` with
  a dummy interface, which also isolates the tests from the real network and from Google's STUN.

Not testable automatically here: real cameras and scanning from a screen; phones (Safari, Chrome
on Android); different networks and NAT types (the probe can only simulate "B cannot reach A");
Google's STUN availability (one optional check when online); background tabs and sleeping phones.

## 11. Host-obligation rows this adds (app-design §4)

| Obligation | Mechanism | Test | Mutant |
|---|---|---|---|
| A link goes down when its connection is lost, even if the channel still says open | `onClose` on `failed`/`closed`/`disconnected` > 5 s | e2e peer browser killed (Chromium receiver) | channel `close` only |
| `onClose` once per link | one guard in the link | unit (fake RTC) | guard removed |
| Answerer is the DTLS server | answer edited to `a=setup:passive` | e2e delayed reply (F→C) | default role |
| A reply stays usable while shown | answer attempts renewed every 5 s, others closed on success | e2e reply scanned/pasted 20 s after B joined, B cannot reach A first (driver gives B unreachable candidates, as in the probe) | no renewal |
| Codes are checked before use | version, kind, CRC, structure, offer tag | unit (prefixes, substitutions) | CRC skipped |
| An invitation accepts one reply | state per invitation | unit; e2e invitation reused | second reply accepted |
| Gathering never blocks for long | finalise on complete / srflx + 300 ms / 2 s | e2e unreachable STUN (Chromium) | wait for complete |
| No transport except to paired devices and STUN | no relay client; STUN only from the setting | e2e network-request count; STUN "none" → no srflx in the code | relay kept; default ignored |
| A failing `send` closes the link | exception → close | unit | exception swallowed |
| Engine restart keeps the pairing | reopen a channel on the live connection with back-off | e2e trap mid-sync | close the connection instead |
| Nothing else persisted | IDB holds record, `rotateId`, label, STUN setting | review | — |

The row "Transport only to the serving origin" (relay) is replaced by "No transport except to
paired devices and STUN".

## 12. Open questions for the user

**Q1. Reload or tab closed = pair again?** Connections live in the page. Options: (a) accept — every
reload, crash or phone sleep needs a new QR exchange; (b) keep the pairing across reloads with a
persisted certificate and a stored peer list, which still cannot reconnect without a signalling
channel, so it only helps the later rendezvous stage. *Recommendation: (a) now; the first item of
the "pair once" stage is (b) plus rendezvous.*

**Q2. Codes as base32 text** (≈ 120–210 characters, QR v5–v8) vs base45 (7 % shorter, same QR
versions, worse for chat apps and typing). *Recommendation: base32.*

**Q3. The QR library.** None of the browsers measured has `BarcodeDetector` on Linux. Proposal:
vendor **`qr` by Paul Miller** (npm `qr` 0.7.2, Sep 2026, licence MIT OR Apache-2.0, zero
dependencies, plain ES modules: `index.js` 43.7 KB encoder, `decode.js` 148 KB decoder, `dom.js`
49 KB camera/canvas helpers, unminified with comments; read from the package, not run here). One
library encodes and decodes, so the test can decode the QR the app renders with the same code the
app uses for scanning, and it can be loaded with relative imports, no bundler. Alternatives:
`jsqr` 1.4.0 (Apache-2.0, decoder only, 257 KB UMD file that would need wrapping, last release
2021) with `nayuki-qr-code-generator` (MIT, encoder); `qr-scanner` (MIT, last release 2022);
`zxing-wasm` (MIT, 3.5 MB). Use `BarcodeDetector` where present? *Recommendation: `qr` only, one
code path everywhere (the native detector would be an untested path in our CI).* Licence and
copyright notice to be kept next to the vendored files under `app/vendor/qr/`.

**Q4. Answer lifetime across networks.** Measured: an answer is good for ~10 s when the answerer
cannot reach the offerer first (Firefox 11 s). Options: (a) live reply QR + "start on the device
with the camera" rule + a warning on the text path; (b) a third code (the offerer's "go" signal) —
does not help, the answerer still starts too early; (c) accept failures across networks with
text-only pairing. *Recommendation: (a).* To be confirmed on real networks with phones.

**Q5. "Go offline" with manual pairing.** Options: (a) close channels but keep connections, so
"online" again reopens channels without re-pairing (the connection still uses ICE keep-alives);
(b) close connections, re-pair after. *Recommendation: (a).*

**Q6. Loss detection.** Options: (a) connection state only (link down after ~10–15 s, browser
dependent); (b) add a host-level heartbeat frame to `links.mjs` (e.g. every 2 s, down after 6 s),
uniform across browsers. *Recommendation: (a) now; (b) only if 15 s proves too slow.*

**Q7. The relay.** §9 (a) remove from the app, faults by init scripts; (b) keep behind a server
switch. *Recommendation: (a).*

**Q8. Default STUN server.** Google's, as decided; a second default (e.g. another public
operator) would avoid depending on one company, at the cost of revealing the IP to two. *Recommend:
Google only, user-editable list.*

## 13. Surprises, and points that touch the decisions

1. **The decided flow "A shows the offer, B scans and shows the answer, A scans" works only with
   two changes**: the answerer must take the passive DTLS role, and its answer must be renewed
   while shown, because the answerer starts ICE a human scan earlier than the offerer, and
   Firefox gives up after 11 s when it cannot reach the offerer first (the usual case across NATs).
   The text fallback is therefore asymmetric: pasting the invitation is fine, pasting the reply
   is reliable only on the same network or if done within ~10 s. This does not contradict the
   decisions, but it changes the no-camera instruction ("start on the device with the camera").
2. **"Wait for ICE gathering to finish" is not usable as such**: Chromium reports completion after
   ~40 s whenever a STUN server is configured (reachable or not, on this machine).
3. **A Chromium receiver keeps a dead channel open** indefinitely; only the connection state
   reveals the loss.
4. Every disconnect that reaches `failed` (phone asleep, network change, reload) needs a new manual
   pairing until the "pair once" stage exists (Q1). This is the main usability cost of the decided
   signalling.
5. Two copies of the app under different paths of one origin share storage (§8).
