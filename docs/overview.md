# lean-crdt: overview and demo guide

Status on 2026-11-25: the CRDT, the sync protocol and the browser app are on `main`. Peer-to-peer
networking (WebRTC with QR pairing) is on the branch `webrtc-transport`, not yet merged or
reviewed. This guide describes that branch.

## What it is

A file-sync app for one person's devices that runs entirely in the browser. There is no sync
server: devices connect directly to each other and exchange files when both are open.

- **The sync logic is written and proved in Lean 4.** It is compiled to WebAssembly and runs in the
  page.
- **A thin JavaScript host does the rest:** storage, hashing, networking and the UI.
- **Files live in browser storage** (OPFS for contents, IndexedDB for the index). The app does not
  read or write folders on disk.

How conflicts are handled:

- Each file name maps to a set of content hashes. Normally the set has one element.
- If two devices edit the same file while apart, both versions are kept and the file is shown as a
  conflict. You choose which to keep, or keep both.
- An edit wins over a concurrent delete.
- A rename is a delete plus an add.

The parts:

| Part | Where | What it does |
|---|---|---|
| CRDT | `LeanCrdt/` | The mergeable index of files, with its laws proved |
| Sync protocol | `LeanSync/` | A pure function from (state, event) to (state, effects), and the wire format |
| Engine | `build/sync/` | The two Lean libraries compiled to wasm64 |
| Host | `app/` | Plain JavaScript modules, no framework, no bundler |
| Tests | `Tests/`, `test/`, `scripts/` | Native Lean tests, JS unit tests, browser end-to-end tests |

File contents never enter Lean. Lean handles names, hashes and the protocol; the host moves the
bytes and verifies each file's hash on arrival.

## How to run the demo

### What you need

- elan with Lean `v4.36.0`, Debian's `emcc` 6.0.5, Node 24 or newer, git and python3.
- Chrome 133+ or Firefox 134+. Safari does not work (see limitations).

### Build

```sh
git checkout webrtc-transport
scripts/wasm/build.sh        # Lean -> wasm; the first run downloads about 830 MB and takes a few minutes
scripts/build-site.sh        # app + engine -> build/site/
```

### Serve

```sh
node dev/serve.mjs --port 8000
```

This is a plain static server on `127.0.0.1`. Any static web server works; over a real network it
must be HTTPS.

### Open two devices

Each "device" is a browser profile with its own storage. On one machine:

```sh
chromium --user-data-dir=/tmp/dev-a 'http://127.0.0.1:8000/?device=laptop'
firefox --no-remote --profile "$(mktemp -d)" 'http://127.0.0.1:8000/?device=phone'
```

### Pair them

1. On the first device choose **Invite a device**. It shows a QR code and the same code as text.
2. On the second device choose **Join a device**. Scan the QR code, or paste the text.
3. The second device now shows a reply code. Scan or paste it on the first device.
4. Both say "Connected".

On one machine, pasting is the practical route. If only one device has a camera, start the
invitation on the device that has it: the invitation can be sent as text, and the reply is then
the code that gets scanned.

### Try it

- Add files with the button or by dropping them. They appear on the other device.
- Untick **online** on both devices, change the same file on each, then tick it again. The file is
  shown as a conflict with both versions.
- Delete a file on one device while offline and replace it on the other. The edit wins.
- Reload a page. The files are still there, but the devices must be paired again.

### With a real phone

Serve `build/site/` over HTTPS from a static host and open the same address on both devices.
This has not been tried yet. `docs/net-design.md` §13 has an eleven-step checklist.

## What is proved

All proofs are checked by `scripts/check-proofs.sh`. It rejects `sorry`, new axioms and unsafe
constructs in the two libraries, and prints the axioms each headline theorem depends on: only the
three standard ones.

**The CRDT** (`LeanCrdt/Laws.lean`):

- Merge is commutative, associative and idempotent, so devices that have seen the same changes
  hold the same index, whatever the order of merging.
- No lost update: after a merge, every version is either still present or was knowingly replaced
  by the other side.
- An edit survives a concurrent delete, and two concurrent edits are both kept.
- Resolving a conflict replaces exactly the versions that were seen.
- The batch operations equal the same operations applied one at a time.

**The protocol** (`LeanSync/`, 33 headline theorems including two from the CRDT):

- The wire encoding round-trips, and decoding accepts only canonical encodings.
- Save before send: the only state ever sent to a peer is one the host has confirmed saved.
- At most one save is in flight, and save tags are never reused.
- Every effect the engine emits is one the host can execute, and its output always decodes.
- After a failed save, no new save is attempted until the host asks for a retry.
- If stored state is found to be older than what peers have seen, the device refuses edits and
  stops sending state.
- A file this device could not store is set aside without blaming the peer, and a retry releases
  it.

**Not proved:**

- That the protocol converges, and that every missing file is eventually fetched. These are tested
  by simulation only.
- Anything in the JavaScript host. The rules it must follow are listed in `docs/sync-design.md` §8
  and `docs/app-design.md` §4, each with a test.
- The path from Lean source to wasm: the Lean compiler, Emscripten and the hand-built Lean runtime
  are trusted.

## What is tested

| Script | What it covers |
|---|---|
| `scripts/test-crdt.sh` | CRDT unit tests and random simulation, natively |
| `scripts/test-sync.sh` | Protocol tests and a multi-device simulator with random disconnects and storage failures |
| `scripts/wasm/check-engine.sh` | The wasm engine gives byte-identical output to the native one over about 80,000 recorded events; memory leak check; 20,000-file scale run |
| `scripts/test-app.sh` | JS unit tests, the JS codec against vectors produced by Lean, and end-to-end scenarios in headless Chromium and Firefox |
| `node test/mutations.mjs` | Breaks each host rule in turn and checks that a test fails |

The end-to-end scenarios drive the real UI in separate browser profiles, including mixed
Chromium–Firefox pairs. They cover pairing by text and by QR with a fake camera, rejected codes,
conflicts, deletes, storage failures, a killed peer, offline and online, three devices, and large
and empty files.

Not tested: real phones, real cameras, real home routers and mobile networks, sleeping or
backgrounded phones.

## Known limitations

**Browsers and devices**

- Chrome 133+ and Firefox 134+ only. Safari and all iOS browsers lack the 64-bit WebAssembly
  memory the engine needs.
- Nothing has been run on a real phone yet.
- Sync happens only while the page is open on both devices at the same time.
- One tab per browser profile; a second tab does nothing.

**Pairing and networking**

- Pairing is manual and is needed again after every reload, crash or sleep.
- Across different networks the reply code goes stale in about 10 seconds, so it renews itself
  while shown and should be scanned, not typed.
- There is no relay server. Devices behind some restrictive networks cannot connect at all.
- The default STUN server is Google's; it sees each device's IP address. The list can be emptied
  for same-network use.
- A vanished peer is noticed after 10 to 30 seconds, depending on the browser.

**Files and storage**

- Files live in browser storage, not in a folder on disk.
- A flat list of files; folders are not supported.
- 256 MiB per file.
- Every device stores every file.
- Files are sent whole. A transfer that is interrupted starts again.
- Contents of deleted or replaced files are never cleaned up.
- Storage belongs to the address the page is served from. A different address means an empty
  store on that device.
- A file whose name differs from an existing one only in Unicode normalisation becomes a second
  file.

**Protocol**

- Devices exchange the whole index, not differences.
- Built for one person's own devices: it tolerates corruption and disconnects, not a malicious
  device.
- The "could not store" report does not name the peer, so a late report could cancel a transfer
  that has moved to another peer. The host suppresses the known case
  (`docs/sync-design.md` §5).

**Build**

- Lean is pinned to 4.36.0 with a hand-built wasm runtime and two patches
  (`docs/spike-lean-wasm.md`).

## Where to read more

- `docs/crdt-design.md`: the CRDT and its theorems.
- `docs/sync-design.md`: the protocol, the wire format and the host rules.
- `docs/app-design.md`: the browser host.
- `docs/net-design.md`: WebRTC, pairing and the real-device checklist.
- `docs/spike-lean-wasm.md`: compiling Lean to wasm.
