module

public import Silmaril.Wasm.Binaryen.EqzPair.Defs
public import Silmaril.Wasm.Binaryen.IfSwapAny
public import Silmaril.Wasm.Binaryen.ConstSelectSim
import Silmaril.Proofs.Wasm.Binaryen.EqzPair.Sound
public import Silmaril.Wasm.Binaryen.Exe.StageContract
public import Silmaril.Wasm.Binaryen.ArbitraryProfile

@[expose] public section

/-! # Double `i32.eqz` before a boolean consumer: soundness

The proofs are in `Silmaril.Proofs.Wasm.Binaryen.EqzPair.{Sim,Sound}`:

* `bool_head`: the consumer fact for `br_if`, `select` and `i32.eqz`;
* `sourceBaseSim` / `resultBaseSim`: untyped simulations in both directions at an
  arbitrary profile under the closed host (two stuttering `eqz` phases);
* `eqzPair_sound_any`, `eqzPairChecked_sound_any`: exact export equivalence of the
  raw and checked stages, the latter needing only input validity.

This header packages the stage for silmaril's executable stage contract and the
arbitrary-profile shared pass contract.
-/

namespace Silmaril.Wasm.Binaryen.EqzPair

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

section Soundness

variable {H : Type} {P : Profile}

/-- **The raw rewrite is exactly export-equivalent** for valid input and output, at every
numerical profile under the closed host. -/
theorem eqzPair_sound_any {m : BModule} (hm : m.Ok) (hm' : (eqzPair m).Ok) :
    ExportEquiv (· = ·) P (closedHost (H := H)) (eqzPair m).lower m.lower :=
  Silmaril.Proofs.Wasm.Binaryen.EqzPair.eqzPair_sound_any hm hm'

/-- **The checked stage keeps validity and is exactly export-equivalent**, with validity of
the input as its only premise, at every numerical profile under the closed host. -/
theorem eqzPairChecked_sound_any {m : BModule} (hm : m.Ok) :
    (eqzPairChecked m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) (eqzPairChecked m).lower m.lower :=
  Silmaril.Proofs.Wasm.Binaryen.EqzPair.eqzPairChecked_sound_any hm

end Soundness

/-- **The double-`eqz` stage satisfies silmaril's executable stage contract.** -/
theorem eqzPair_stageOk {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type} :
    Exe.StageOk o H eqzPairChecked :=
  fun _ hm => eqzPairChecked_sound_any hm.ok

/-- **The double-`eqz` stage as an arbitrary-profile shared pass.** -/
def eqzPairP {H : Type} (P : Profile) :
    ArbitraryProfile.EquivPass P (closedHost (H := H)) where
  run := eqzPairChecked
  inv_run hm := (eqzPairChecked_sound_any (P := P) (H := H) hm).1
  sound hm := (eqzPairChecked_sound_any hm).2

/-! ## Facts about `eqz` (`Silmaril.Wasm.FnInst.Ground` uses them) -/

theorem eqz_eqz_eq_zero (c : BitVec 32) :
    intTestOp .i32 .eqz (intTestOp .i32 .eqz c) = 0 ↔ c = 0 :=
  Silmaril.Proofs.Wasm.Binaryen.EqzPair.eqz_eqz_eq_zero c

theorem eqz_congr {b c : BitVec 32} (h : b = 0 ↔ c = 0) :
    intTestOp .i32 .eqz b = intTestOp .i32 .eqz c :=
  Silmaril.Proofs.Wasm.Binaryen.EqzPair.eqz_congr h

/-- Every original function body is related to its rewritten body (`Silmaril.Wasm.FnInst.Ground`
reuses it). -/
theorem eqzPair_bodiesRel (m : BModule) : ModuleBodiesRel eBI m.lower (eqzPair m).lower :=
  Silmaril.Proofs.Wasm.Binaryen.EqzPair.eqzPair_bodiesRel m

/-- The boolean consumers. -/
theorem boolConsumer_cases {X : Instr} (h : boolConsumer X = true) :
    (∃ l, X = .brIf l) ∨ (∃ ts, X = .select ts) ∨ X = .intTestOp .i32 .eqz :=
  Silmaril.Proofs.Wasm.Binaryen.EqzPair.boolConsumer_cases h

end Silmaril.Wasm.Binaryen.EqzPair
