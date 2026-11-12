module

public import Silmaril.Wasm.Binaryen.NeutralOps.Defs
public import Silmaril.Wasm.Binaryen.IfSwapAny
public import Silmaril.Wasm.Binaryen.AddChainAny
import Silmaril.Proofs.Wasm.Binaryen.NeutralOps.Sound
public import Silmaril.Wasm.Binaryen.Exe.StageContract
public import Silmaril.Wasm.Binaryen.ArbitraryProfile

@[expose] public section

/-! # Neutral-operand elimination: soundness

The proofs are in `Silmaril.Proofs.Wasm.Binaryen.NeutralOps.{Sim,Sound}`:

* `sourceBaseSim` / `resultBaseSim`: the original and the rewritten code simulate
  each other (untyped `BaseSim`s at an arbitrary profile, closed host);
* `elimL_rel`: every body is related to its rewrite by the base pairs;
* `neutralOps_sound_any`: the raw rewrite is exactly export-equivalent for valid
  input and output, at every numerical profile;
* `neutralOpsChecked_sound_any`: the checked stage keeps validity and is exactly
  export-equivalent, with validity of the input as its only premise.

This header packages the stage for silmaril's two pass contracts: the executable
stage contract `Exe.StageOk` (deterministic profiles, `ExeC`) and the
arbitrary-profile shared contract `ArbitraryProfile.EquivPass` used by the
selected-stage byte driver.
-/

namespace Silmaril.Wasm.Binaryen.NeutralOps

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

section Soundness

variable {H : Type} {P : Profile}

/-- **The raw rewrite is exactly export-equivalent** for valid input and output, at every
numerical profile under the closed host. -/
theorem neutralOps_sound_any {m : BModule} (hm : m.Ok) (hm' : (neutralOps m).Ok) :
    ExportEquiv (· = ·) P (closedHost (H := H)) (neutralOps m).lower m.lower :=
  Silmaril.Proofs.Wasm.Binaryen.NeutralOps.neutralOps_sound_any hm hm'

/-- **The checked stage keeps validity and is exactly export-equivalent**, with validity of
the input as its only premise, at every numerical profile under the closed host. -/
theorem neutralOpsChecked_sound_any {m : BModule} (hm : m.Ok) :
    (neutralOpsChecked m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) (neutralOpsChecked m).lower m.lower :=
  Silmaril.Proofs.Wasm.Binaryen.NeutralOps.neutralOpsChecked_sound_any hm

end Soundness

/-- **The neutral-operand stage satisfies silmaril's executable stage contract.** -/
theorem neutralOps_stageOk {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type} :
    Exe.StageOk o H neutralOpsChecked :=
  fun _ hm => neutralOpsChecked_sound_any hm.ok

/-- **The neutral-operand stage as an arbitrary-profile shared pass.** -/
def neutralOpsP {H : Type} (P : Profile) :
    ArbitraryProfile.EquivPass P (closedHost (H := H)) where
  run := neutralOpsChecked
  inv_run hm := (neutralOpsChecked_sound_any (P := P) (H := H) hm).1
  sound hm := (neutralOpsChecked_sound_any hm).2

/-- A neutral pair leaves the other operand (`Silmaril.Wasm.FnInst.Ground` uses it). -/
theorem neutral_sound {t : IntType} {op : IntBinOp} {k : BitVec t.width}
    (h : neutral op k = true) (x : BitVec t.width) : intBinOp t op x k = .ok x :=
  Silmaril.Proofs.Wasm.Binaryen.NeutralOps.neutral_sound h x

/-- The head step of an integer binary operator (`Silmaril.Wasm.FnInst.Ground` uses it). -/
theorem head_binop {H : Type} {P : Profile} {s : Store H} {f : Frame} {args : List Val}
    {t : IntType} {op : IntBinOp} {c₀ : Config H}
    (h : Silmaril.Wasm.SingleThreaded.Det.Head P s f args (.plain (.intBinOp t op)) c₀) :
    ∃ a b : BitVec t.width, args = [.num ⟨.int t, a⟩, .num ⟨.int t, b⟩] ∧
      ((∃ z, intBinOp t op a b = .ok z ∧ c₀ = ⟨s, f, [.plain (.intConst t z)]⟩) ∨
        (∃ e, intBinOp t op a b = .error e ∧ c₀ = ⟨s, f, [.trap]⟩)) :=
  Silmaril.Proofs.Wasm.Binaryen.NeutralOps.head_binop h

/-- Every original function body is related to its rewritten body (`Silmaril.Wasm.FnInst.Ground`
reuses it). -/
theorem neutralOps_bodiesRel (m : BModule) : ModuleBodiesRel nBI m.lower (neutralOps m).lower :=
  Silmaril.Proofs.Wasm.Binaryen.NeutralOps.neutralOps_bodiesRel m

/-- The consumers the rewrite accepts. -/
theorem topIntType_cases {X : Instr} {t : IntType} (h : topIntType? X = some t) :
    (∃ op, X = .intUnOp t op) ∨ (∃ op, X = .intBinOp t op) ∨ (∃ op, X = .intTestOp t op) ∨
      (∃ op, X = .intRelOp t op) :=
  Silmaril.Proofs.Wasm.Binaryen.NeutralOps.topIntType_cases h

end Silmaril.Wasm.Binaryen.NeutralOps
