module

public import Silmaril.Wasi.Versions.P3OverP2.Impl.Defs

@[expose] public section

/-!
# WASI 0.3 over 0.2: the runs and the variant behind the counterexamples

* `wrapRun`: a run of `host3 wrapFile` of `2^31 + 2` answers. Its first `read-via-stream` gets
  the readable end `1`; after `2^31 - 1` filler answers (`stream.drop-readable()`, answered `[]`)
  a second `read-via-stream` of another file gets `2 · 2^31 + 1`, which wraps to `1` as a `u32`.
  `host3` keeps reading the first file on `1`; `fsReadTh3w` expects the second.
* `bigRun`: a run of `host3 bigFile` with a file of exactly `2^28` bytes. A `stream.read` of all
  of them is answered `COMPLETED 2^28`, packed as `16 · 2^28 = 2^32`, which wraps to `0` =
  `COMPLETED 0`, with `2^28` items.
* `bodyU`, `p3OverP2u`: the component `p3OverP2` with **`now` not clamped**: it answers the 0.2
  instant as it is. `lateCalls`: `now` (the 0.2 host says `5`), `wait-for 10` (the pollable of
  `subscribe-duration` is reported ready at once), `now` (the 0.2 host says `6`).
* `noRd2`: an event that is not a 0.2 read (`read-via-stream`, `read`, `blocking-read`).

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (packCopy CopyResult)
open Silmaril.Wasi.Versions.P3
open Silmaril.Wasi.Versions.P2 (p2Command)

/-! ## The handle wrap-around (`2^31` answers) -/

/-- The filler answer: `stream.drop-readable()` answered `[]`. -/
def fillEv : WEv := .imp cStreamDropR [] (some [])

/-- Two one-byte files: `[0]` behind the descriptor `0`, `[1]` behind the others. -/
def wrapFile (d : BitVec 32) : List (BitVec 8) := if d = 0 then [0] else [1]

/-- `read-via-stream(0, 0)` as the first answer: the readable end `1`. -/
def wrapEv0 : WEv := .imp readVia3 [.u32 0, .u64 0] (some [.record [natV 1, natV 2]])

/-- `read-via-stream(1, 0)` after `2^31` answers: the readable end `2 · 2^31 + 1` (`1` as a
`u32`). -/
def wrapEv1 : WEv := .imp readVia3 [.u32 1, .u64 0]
  (some [.record [natV (2 * 2 ^ 31 + 1), natV (2 * 2 ^ 31 + 2)]])

/-- The answers before the read: `wrapEv0`, `2^31 - 1` fillers, `wrapEv1`. -/
abbrev wrapPre : List WEv := [wrapEv0] ++ List.replicate (2 ^ 31 - 1) fillEv ++ [wrapEv1]

/-- `stream.read(1, 1)`, answered with the byte of the first file. -/
def wrapEv2 : WEv :=
  .imp cStreamRead [natV 1, natV 1] (some [natV (packCopy .completed 1), bytesV [0]])

/-- **The wrap-around run.** -/
def wrapRun : List WEv := wrapPre ++ [wrapEv2]

/-! ## The packed count (a file of `2^28` bytes) -/

/-- Every descriptor holds `2^28` zero bytes. -/
def bigFile (_ : BitVec 32) : List (BitVec 8) := List.replicate (2 ^ 28) 0

/-- `stream.read(1, 2^28)`, answered as `host3` does: all bytes, `COMPLETED 2^28` packed. -/
def bigEv1 : WEv := .imp cStreamRead [natV 1, natV (2 ^ 28)]
  (some [natV (packCopy .completed (2 ^ 28)), bytesV (List.replicate (2 ^ 28) 0)])

/-- **The packed-count run.** -/
def bigRun : List WEv := [wrapEv0, bigEv1]

/-! ## The unclamped clock -/

/-- **The unclamped variant**: as `body`, except that `now` answers the 0.2 instant. -/
def bodyU : SBody St p2Command.imports p3World.imports := fun s q =>
  match cls q.1.1 with
  | .now => thenFin ioNow fun x => (s, some [.u64 (BitVec.ofNat 64 x)])
  | _ => body s q

/-- The unclamped variant as a strategy. -/
def p3OverP2u : Strategy (nsig p2Command.imports) (nsig p3World.imports) := ofSBody bodyU init

/-- `now ∈ p3World.imports`. -/
theorem now3_mem : now3 ∈ p3World.imports := by simp [p3World, wasiFns3_eq]

/-- `wait-for ∈ p3World.imports`. -/
theorem waitFor3_mem : waitFor3 ∈ p3World.imports := by simp [p3World, wasiFns3_eq]

/-- The export call `now()`. -/
def nowQ : (nsig p3World.imports).Op := (⟨now3, now3_mem⟩, [])

/-- The export call `wait-for(d)`. -/
def waitQ (d : BitVec 64) : (nsig p3World.imports).Op := (⟨waitFor3, waitFor3_mem⟩, [.u64 d])

/-- `now` (0.2: `5`), `wait-for 10` (`subscribe-duration` gives the pollable `7`, `poll` reports
it ready, the drop returns), `now` (0.2: `6`). -/
def lateCalls : List ((nsig p3World.imports).Op × List (Option (List Val))) :=
  [(nowQ, [some [.u64 5]]),
   (waitQ 10, [some [.u32 7], some [.record [.u32 0]], some []]),
   (nowQ, [some [.u64 6]])]

/-- Not a 0.2 read. -/
def noRd2 : WEv → Bool
  | .imp f _ _ =>
    !(decide (f = P2.fdReadStream) || decide (f = P2.isBread) || decide (f = P2.isRead))
  | _ => true

end Silmaril.Wasi.Versions.P3OverP2
