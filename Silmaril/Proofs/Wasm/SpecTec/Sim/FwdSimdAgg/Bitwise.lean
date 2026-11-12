module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.FwdSimdAgg.BitwiseEval

/-!
# Track `fwd-simd-agg`: the bitwise vector instructions, forward

Operator typing and the forward lemmas; the dispatchers are evaluated in `BitwiseEval.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d531 Original.d532 Original.d533 Original.d443
  Original.d446 Original.d453)

attribute [local simp] Equiv.Execution.findVal?_empty Equiv.Execution.findVal?_bindVal_lit

variable {B : Builtins}

/-! ## Typing of the operator values -/

set_option maxRecDepth 100000 in
theorem typedV_vvunop (op : VecUnOp) : TypedV (simEnv B) (.varT "vvunop" []) (Vec.vvunopV op) :=
  fun _ hρ => by cases op; exact IntNumeric.hasTyp_closedNullary hρ rfl rfl

set_option maxRecDepth 100000 in
theorem typedV_vvbinop (op : VecBinOp) :
    TypedV (simEnv B) (.varT "vvbinop" []) (Vec.vvbinopV op) :=
  fun _ hρ => by cases op <;> exact IntNumeric.hasTyp_closedNullary hρ rfl rfl

set_option maxRecDepth 100000 in
theorem typedV_vvternop (op : VecTernOp) :
    TypedV (simEnv B) (.varT "vvternop" []) (Vec.vvternopV op) :=
  fun _ hρ => by cases op; exact IntNumeric.hasTyp_closedNullary hρ rfl rfl

/-! ## Forward -/

variable {H : Type} {hn : H → String} {s : Store H} {f : Frame}

/-- `VectorStep.vecUnOp`, forward, in `simEnv B`. -/
theorem fwd_vecUnOp (hV : VVB B) (op : VecUnOp) (a : V128) :
    FwdP (simEnv B) hn ⟨s, f, [vconst a, .plain (.vecUnOp op)]⟩ ⟨s, f, [vconst (vvunop op a)]⟩ :=
  Vec.fwd_of_spure (Typing.typingFacts_simEnv B hn) (hasStepRules_simEnv B).pure
    (Vec.spure_vvunop (Vec.hasVectorRules_simEnv B).vvunop (Typing.typedV_vecT a)
      (typedV_vvunop op) (Typing.typedV_vecT _) (applies_vvunop hV op a) List.mem_cons_self)

/-- `VectorStep.vecBinOp`, forward, in `simEnv B`. -/
theorem fwd_vecBinOp (hI : IntNumeric.IntB B) (hV : VVB B) (op : VecBinOp) (a b : V128) :
    FwdP (simEnv B) hn ⟨s, f, [vconst a, vconst b, .plain (.vecBinOp op)]⟩
      ⟨s, f, [vconst (vvbinop op a b)]⟩ :=
  Vec.fwd_of_spure (Typing.typingFacts_simEnv B hn) (hasStepRules_simEnv B).pure
    (Vec.spure_vvbinop (Vec.hasVectorRules_simEnv B).vvbinop (Typing.typedV_vecT a)
      (Typing.typedV_vecT b) (typedV_vvbinop op) (Typing.typedV_vecT _)
      (applies_vvbinop hI hV op a b) List.mem_cons_self)

/-- `VectorStep.vecTernOp`, forward, in `simEnv B`. -/
theorem fwd_vecTernOp (hV : VVB B) (op : VecTernOp) (a b c : V128) :
    FwdP (simEnv B) hn ⟨s, f, [vconst a, vconst b, vconst c, .plain (.vecTernOp op)]⟩
      ⟨s, f, [vconst (vvternop op a b c)]⟩ :=
  Vec.fwd_of_spure (Typing.typingFacts_simEnv B hn) (hasStepRules_simEnv B).pure
    (Vec.spure_vvternop (Vec.hasVectorRules_simEnv B).vvternop (Typing.typedV_vecT a)
      (Typing.typedV_vecT b) (Typing.typedV_vecT c) (typedV_vvternop op) (Typing.typedV_vecT _)
      (applies_vvternop hV op a b c) List.mem_cons_self)

/-- `VectorStep.vecTestOp`, forward, in `simEnv B`. -/
theorem fwd_vecTestOp (op : VecTestOp) (a : V128) :
    FwdP (simEnv B) hn ⟨s, f, [vconst a, .plain (.vecTestOp op)]⟩
      ⟨s, f, [constI32 (vvtestop op a)]⟩ := by
  cases op
  exact Vec.fwd_of_spure (Typing.typingFacts_simEnv B hn) (hasStepRules_simEnv B).pure
    (Vec.spure_vvtestop (Vec.hasVectorRules_simEnv B).vvtestop (Typing.typedV_vecT a)
      ((Floats.floatTyping_simEnv B).i32 _) applies_vsize (applies_inez a))

end Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg
