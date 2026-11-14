module

public import Silmaril.Wasi.Versions.P2OverP3.Fs.Defs
public import Silmaril.Raw.Wasi.Versions.P2OverP3.FsSat

@[expose] public section

/-!
# WASI 0.2 over 0.3 with `wasi:filesystem`: an implementation morphism (header)

PROVED (proofs unrefined, in `Silmaril.Raw.Wasi.Versions.P2OverP3.Fs*`), for every buffer size
`cap` and all file contents `F`:

* **`p2OverP3Fs_sat`**: `(agP (t3F F) (retG (p2F F))).holds (p2OverP3Fs cap)`. Under the WASI 0.3
  clock theory and the loose 0.3 read theory `fsReadTh3w F` (`Silmaril.Wasi.Versions.P3OverP2.Theory`)
  on the host's answers, every return of the component satisfies the loose WASI 0.2 theory
  `p2Th .loose` **and** the loose 0.2 read theory `fsRead2 F`: an input stream of
  `read-via-stream(d, off)` delivers consecutive bytes of `(F d).drop off`, and reports an error
  only when nothing is left.
* **`p2OverP3Fs_model`**: the implementation morphism. For every host `η` (over any lower
  interface) of `t3F F`, `link η (p2OverP3Fs cap)` is a host of `p2F F`.
  `p2OverP3Fs_loose`: over the loose host of `t3F F`.

The invariant (`RdInv`): a 0.2 input stream the 0.2 read theory tracks is in the component's
table; if it is live, the bytes the 0.2 theory has left equal the bytes the 0.3 theory has left
on its readable end, and live streams have distinct ends. Reads of other ends by the `p2OverP3`
code are ruled out by sanitizing (`san`, `badK`), so they never disturb a live file stream.

**Input pollables** (task: remove the "always ready" simplification). `eager_inp_ready`: in
`p2OverP3` (the eager variant, kept as it is) the pollable of an input stream is ready without
any call. `probe_inp`: in `p2OverP3Fs` it is ready only when a zero-length `stream.read(r, 0)`
of the stream's readable end does not report `BLOCKED`; `block`/`poll` wait on pending probes.
Both satisfy the loose 0.2 theory (neither 0.2 reading constrains the answer of `ready` on an
input pollable); the probe is the readiness test the reference machine supports
(`Silmaril.Wasm.Component.Async.RefZero`).

What this does **not** say: that `open-at` opens the file `F` describes (descriptors and their
contents are related only through `F`, on both sides alike); anything about `skip` of a file
stream (the 0.2 read theory does not track skips, and the component skips nothing); that a
`blocking-read` returns bytes (the loose theory allows `ok([])`, and the loop gives up after
`rounds` waits).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component (Val)

/-- **WASI 0.2 with the filesystem read slice over WASI 0.3 satisfies the loose 0.2 theories**
under the 0.3 clock and read theories. -/
theorem p2OverP3Fs_sat (cap : Nat) (F : BitVec 32 → List (BitVec 8)) :
    (agP (t3F F) (retG (p2F F))).holds (p2OverP3Fs cap) :=
  ag_of_wpInv (wpInvF cap F)

/-- **The implementation morphism**: over every host of the WASI 0.3 clock and read theories,
the composite is a host of the loose WASI 0.2 theory and the loose 0.2 read theory. -/
theorem p2OverP3Fs_model (cap : Nat) (F : BitVec 32 → List (BitVec 8)) {Y : Sig.{0}}
    {η : Host Y impF} (hη : (hostSat (t3F F).Accepts).holds η) :
    (hostSat (p2F F).Accepts).holds (link η (p2OverP3Fs cap)) :=
  link_model (p2OverP3Fs_sat cap F) hη

/-- Over the loose host of the WASI 0.3 theories. -/
theorem p2OverP3Fs_loose (cap : Nat) (F : BitVec 32 → List (BitVec 8)) {Y : Sig.{0}} :
    (hostSat (p2F F).Accepts).holds (link (loose (Y := Y) (I := impF) (t3F F)) (p2OverP3Fs cap)) :=
  p2OverP3Fs_model cap F (loose_sat (t3F F))

/-- **The eager variant** `p2OverP3`: an input pollable is ready, without any call. -/
theorem eager_inp_ready (st : ISt) {p h : BitVec 32} (hp : look st.polls p = some (.inp h)) :
    readyNow st p = .pure (st, true) := by
  unfold readyNow
  rw [hp]

/-- **The probed variant** `p2OverP3Fs`: an input pollable with a readable end `r` is ready when
the zero-length probe `stream.read(r, 0)` is not `BLOCKED`. -/
theorem probe_inp (t : FsTab) (st : ISt) {p h : BitVec 32} {r : Val}
    (hp : look st.polls p = some (.inp h)) (hr : inEnd st t h = some r) :
    readyNowI t st p = (probe r).bind fun b => .pure (st, b, if b then [] else [r]) := by
  unfold readyNowI
  rw [hp]
  dsimp only
  rw [hr]

end Silmaril.Wasi.Versions.P2OverP3
