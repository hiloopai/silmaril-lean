module

public import Silmaril.Wasi.Versions.P2OverP3.Comp.Defs

@[expose] public section

/-!
# WASI 0.2 over 0.3: a play separating the strict reading

## Running a stateful component on given answers

`drive p ns` runs the program `p` on the host answers `ns` (one per import call, in order) and
returns its moves and result; `session h s calls` runs a sequence of export calls, each with its
answers. `Silmaril.Proofs.Wasi.Versions.P2OverP3.Sep` proves that a session is a reachable play.

## The separating play

`sepCalls cap` is a session of `p2OverP3 cap` against a WASI 0.3 host whose stdout reader makes
**zero-length reads** (in `Silmaril.Wasm.Component.Async`, a zero-length `stream.read` meeting a
pending `stream.write` completes the write with `COMPLETED 0`, and a `stream.write` meeting a
pending zero-length read completes at once with `COMPLETED 0`):

1. `get-stdout()`: `stream.new` → ends `1` (readable), `2` (writable); `write-via-stream(1)` →
   future `3`; the 0.2 output stream is `0`.
2. `check-write(0)` → `ok(cap)`.
3. `write-zeroes(0, cap)`: `stream.write(2, 0^cap)` → `BLOCKED`; answers `ok`.
4. `subscribe(0)` → pollable `1`.
5. `block(1)`: the write is in flight, so the pollable (the waitable of the writable end) is not
   ready: `waitable-set.new` → `4`, `waitable.join(2, 4)`, `waitable-set.wait(4)` →
   `stream-write` event (code `3`) on `2` with `COMPLETED 0`; no copy is in flight any more;
   the buffer is written again, `stream.write(2, 0^cap)` → `COMPLETED 0`; the pollable is ready,
   `block` returns.
6. `check-write(0)`: `stream.write(2, 0^cap)` → `BLOCKED`; the buffer is still full: **`ok(0)`**.

The host answers are those of the store model `Silmaril.Wasm.Component.Async` for a reader that
makes zero-length reads (`Silmaril.Wasi.Versions.P2OverP3.Sep.Thms`), and the WASI 0.3 theory
`p3Th` accepts them.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (packCopy CopyResult blocked)
open Silmaril.Wasi.Versions.P3
open Silmaril.Wasi.Versions.P2

variable {S : Type} {I X : Set FnName}

/-- Run a program on the given answers: its moves and result (`none` if the answers do not
match its calls). -/
def drive : SProg S I → List (Option (List Val)) →
    Option (List (Move (nsig I) (nsig X)) × (S × Option (List Val)))
  | .pure x, [] => some ([], x)
  | .pure _, _ :: _ => none
  | .call _ _, [] => none
  | .call m k, n :: ns => (drive (k n) ns).map fun y => (.inl (.ask m) :: .inl (.ans m n) :: y.1, y.2)

/-- Run a sequence of export calls, each with the answers of its import calls. -/
def session (h : SBody S I X) : S → List ((nsig X).Op × List (Option (List Val))) →
    Option (List (Move (nsig I) (nsig X)) × S)
  | s, [] => some ([], s)
  | s, (q, ns) :: rest =>
    match drive (h s q) ns with
    | some (ms, s', r) =>
      (session h s' rest).map fun y => (.inr (.ask q) :: ms ++ .inr (.ans q r) :: y.1, y.2)
    | none => none

/-! ## The separating play -/

theorem exp2_getStdout : getStdout ∈ exp2 := by simp [exp2, cliImports_eq]
theorem exp2_checkWrite : osCheckWrite ∈ exp2 := by simp [exp2, ioImports_eq]
theorem exp2_writeZeroes : osWriteZeroes ∈ exp2 := by simp [exp2, ioImports_eq]
theorem exp2_subscribe : osSubscribe ∈ exp2 := by simp [exp2, ioImports_eq]
theorem exp2_block : pollBlock ∈ exp2 := by simp [exp2, ioImports_eq]

/-- An export call of WASI 0.2. -/
abbrev XOp : Type := (nsig exp2).Op

/-- `get-stdout()`. -/
def xGetStdout : XOp := (⟨getStdout, exp2_getStdout⟩, [])
/-- `check-write(h)`. -/
def xCheckWrite (h : BitVec 32) : XOp := (⟨osCheckWrite, exp2_checkWrite⟩, [.u32 h])
/-- `write-zeroes(h, n)`. -/
def xWriteZeroes (h : BitVec 32) (n : Nat) : XOp :=
  (⟨osWriteZeroes, exp2_writeZeroes⟩, [.u32 h, .u64 (BitVec.ofNat 64 n)])
/-- `subscribe(h)`. -/
def xSubscribe (h : BitVec 32) : XOp := (⟨osSubscribe, exp2_subscribe⟩, [.u32 h])
/-- `block(p)`. -/
def xBlock (p : BitVec 32) : XOp := (⟨pollBlock, exp2_block⟩, [.u32 p])

/-- **The export calls of the separating play, with the host's answers.** -/
def sepCalls (cap : Nat) : List (XOp × List (Option (List Val))) :=
  [(xGetStdout, [some [natV 1, natV 2], some [natV 3]]),
   (xCheckWrite 0, []),
   (xWriteZeroes 0 cap, [some [natV blocked]]),
   (xSubscribe 0, []),
   (xBlock 1, [some [natV 4], some [], some [natV 3, natV 2, natV (packCopy .completed 0)],
     some [natV (packCopy .completed 0)]]),
   (xCheckWrite 0, [some [natV blocked]])]

/-- The session of the separating play. -/
def sepSession (cap : Nat) : Option (List (Move (nsig imp3) (nsig exp2)) × St) :=
  session (body cap) St.init (sepCalls cap)

/-- **The separating play.** -/
def sepPlay (cap : Nat) : List (Move (nsig imp3) (nsig exp2)) :=
  ((sepSession cap).map (·.1)).getD []

/-- The answer list ends with `block` returning, then `check-write` answering `ok(0)`. -/
def blockThenZero (t : List WEv) : Bool :=
  match t.reverse with
  | .imp f _ r :: .imp g _ r' :: _ =>
    decide (f = osCheckWrite) && isOkZero r && decide (g = pollBlock) && isOkUnitList r'
  | _ => false
where
  /-- The answer `[]` of `block`. -/
  isOkUnitList : Option (List Val) → Bool
    | some [] => true
    | _ => false

end Silmaril.Wasi.Versions.P2OverP3
