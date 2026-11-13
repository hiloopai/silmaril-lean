module

public import Silmaril.Wasm.SpecTec.Institution.Nondet.Defs

/-!
# Choice cover on round 6's domain: definitions

`Nondet.Task.choiceCover` asked for every Core successor on round 6's domain `Dom` to be a step
fact of *some* admissible `stepModel B`. It holds with the single choice `B := Round4Int.BI`
(`Cover.Thms`). This header names the witness that shows the off-`DomDet` statements are not
vacuous: a point of `Dom` with two Core successors.

* `nanCfg`: `f32.const nan; f64.promote_f32` on the empty store, in a frame over the empty
  module, with `nan = 0x7FC00000` (the canonical `f32` NaN). Under the spec NaN profile Core may
  promote it to the canonical `f64` NaN of either sign.
* `nanDone neg`: those two successors, `f64.const ±nan`.

Unlike round 6's `Refute.promCfg` (the vector `f64x2.promote_low_f32x4`, which is `FloatMissel`
and hence not `BoundedSel`), the scalar `f64.promote_f32` is inside SpecTec's typed syntax, and
SpecTec's scalar `$cvtop__` returns the whole set of allowed results.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Cover

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- The canonical `f32` NaN. -/
def nanF32 : BitVec 32 := 0x7FC00000#32

/-- The canonical `f64` NaN, negative when `neg`. -/
def nanF64 (neg : Bool) : BitVec 64 :=
  if neg then 0xFFF8000000000000#64 else 0x7FF8000000000000#64

/-- **The witness**: `f32.const nan; f64.promote_f32` on the empty store, in a frame over the
empty module. -/
def nanCfg : Config H :=
  ⟨{}, ⟨[], {}⟩, [(Val.num ⟨.float .f32, nanF32⟩).toAdmin, .plain (.convert .promote)]⟩

/-- Its successors: `f64.const` of the canonical `f64` NaN of either sign. -/
def nanDone (neg : Bool) : Config H :=
  ⟨{}, ⟨[], {}⟩, [(Val.num ⟨.float .f64, nanF64 neg⟩).toAdmin]⟩

end Silmaril.Wasm.SpecTec.Institution.Cover
