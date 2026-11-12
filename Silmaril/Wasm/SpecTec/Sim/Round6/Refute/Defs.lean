module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Target.Defs

/-!
# SpecTec ↔ Core 3.0, round 6, track refute: the two witnesses

Round 5 left `Round5.Task.wholeStepValidSel` open and argued it false for two reasons
(`docs/projects/spectec/README.md`). This track checks both formally. The witnesses
are defined here; see `Round6/Refute/Thms.lean` for what is proved about them.

* **`ref.null; ref.test (ref null any)`** (`testCfg`): the null reference followed by
  `ref.test (ref null any)`, on the empty store, in a frame over the empty module. Core types
  `null` at `REF NULL ANY` and steps only to `i32.const 1` (`testOne`); SpecTec's `Ref_ok` types
  `null` at `REF NULL BOT` only, so its `otherwise` rule `ref.test-false` steps to `i32.const 0`
  (`testZero`). This refutes `Round5.Task.wholeStepValidSel`.
* **`v128.const nanLane0; f64x2.promote_low_f32x4`** (`promCfg`): under the spec NaN profile Core
  steps to two different results (`promDone false`, `promDone true`). The instruction is a
  `SimdTy.FloatMissel` instruction, so the configuration is not `Target.BoundedSel` and is no
  counterexample to `Round5.Task.wholeStepValidSel`; SpecTec does not step from it at all.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Refute

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-! ## `ref.null; ref.test (ref null any)` -/

/-- The source reference type `ref null any`. -/
def nullAnyR : RefType := ⟨true, .abstract .any⟩

/-- **The first witness**: `null` and `ref.test (ref null any)` on the empty store, in a frame
over the empty module. -/
def testCfg : Config H := ⟨{}, ⟨[], {}⟩, [.ref .null, .plain (.refTest nullAnyR)]⟩

/-- `i32.const 0` on the same state: SpecTec's successor. -/
def testZero : Config H := ⟨{}, ⟨[], {}⟩, [constI32 0]⟩

/-- `i32.const 1` on the same state: Core's successor. -/
def testOne : Config H := ⟨{}, ⟨[], {}⟩, [constI32 1]⟩

/-! ## `v128.const nanLane0; f64x2.promote_low_f32x4` -/

/-- `f64x2.promote_low_f32x4`. -/
def promoteI : Instr := .vecConvert (.float .f32x4) (.float .f64x2) .promoteLow

/-- **The second witness**: `v128.const nanLane0; f64x2.promote_low_f32x4` on the empty store,
in a frame over the empty module (`nanLane0` is `Round5.Simd.nanLane0`,
`0x7FC00000`: a canonical NaN in the first `f32` lane). -/
def promCfg : Config H := ⟨{}, ⟨[], {}⟩, [vconst 0x7FC00000#128, .plain promoteI]⟩

/-- Its successors: the canonical `f64` NaN of either sign, then `+0`. -/
def promDone (neg : Bool) : Config H :=
  ⟨{}, ⟨[], {}⟩, [vconst (FloatShape.f64x2.invLanes
    [if neg then 0xFFF8000000000000#64 else 0x7FF8000000000000#64, 0])]⟩

end Silmaril.Wasm.SpecTec.Sim.Round6.Refute
