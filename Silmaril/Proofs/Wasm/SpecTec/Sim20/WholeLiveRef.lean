module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeLiveCtrl
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StateRefNull
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.NumEnv

/-!
# `ref.is_null` and `local.tee` of `Step_pure`, backwards, at arbitrary code

`ref.is_null-true` (28), `ref.is_null-false` (29) and `local.tee` (55) of wasm-2.0 `Step_pure`,
at the image of any V2 code. The `ref`-typed operand of `ref.is_null` is decoded through the IL
type `ref` (`refHead_of_typed`: a typed `ref` has one of its three constructors). `ref.is_null`'s
`otherwise` premise is read with the typing of null references (`typedV_refNull20`), proved here
from the closed variant types `ref` and `reftype`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk ValsOnly TypedV)

variable {B : Builtins}

/-! ## The IL type `ref` -/

/-- The constructors of the wasm-2.0 IL type `ref` (`Scripts.Wasm20.Original.d281`). -/
def refHeads20 : List MixopS := ["REF.NULL", "REF.FUNC_ADDR", "REF.HOST_ADDR"]

set_option maxRecDepth 100000 in
/-- The wasm-2.0 `ref`, as `simEnv20 B` finds it. -/
theorem findTyp_ref20 : (simEnv20 B).findTyp? "ref" =
    some ([], [.instD [] [] (.variantT
      (Silmaril.Wasm.SpecTec.Sim.IntNumeric.instCases
        Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d281 0))]) := rfl

set_option maxRecDepth 100000 in
/-- The constructors of `ref`, read off the script. -/
theorem refCases20_heads :
    (Silmaril.Wasm.SpecTec.Sim.IntNumeric.instCases
        Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d281 0).map
      (fun c : TypCase => match c with | .mk o _ _ _ => o) = refHeads20 := rfl

/-- **A typed wasm-2.0 `ref` has a reference head.** -/
theorem refHead_of_typed {ρ : VarEnv} (hρ : ValsOnly ρ) {v : Value}
    (h : HasTyp (simEnv20 B) ρ (.varT "ref" []) v) : ∃ op w, v = .case op w ∧ op ∈ refHeads20 := by
  have hl : localTyp? ρ "ref" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [findTyp_ref20] at htd
  obtain rfl := (Option.some.inj htd).symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, -, hd⟩ | hrest
  · obtain ⟨op, w, rfl, hc⟩ := hasTypDef_variantT_iff.1 hd
    obtain ⟨t, qs, prems, hm, -⟩ := hasTypCase_mem hc
    have hmem := List.mem_map_of_mem (f := fun c : TypCase => match c with | .mk o _ _ _ => o) hm
    rw [refCases20_heads] at hmem
    exact ⟨op, w, rfl, hmem⟩
  · exact absurd hrest not_hasTypInsts_nil

/-- An image with a `ref` constructor is a reference. -/
theorem admin_of_head_ref {a : Admin} (h : adminHead20 a ∈ refHeads20) : ∃ r : Ref, a = aref r := by
  revert h
  cases a with
  | plain i =>
    cases i <;> simp [adminHead20, instrHead20, refHeads20]
    case refNull t => exact ⟨.null t, rfl⟩
  | refFuncAddr x => exact fun _ => ⟨.funcAddr x, rfl⟩
  | refHostAddr x => exact fun _ => ⟨.hostAddr x, rfl⟩
  | _ => simp [adminHead20, refHeads20]

/-- A coerced `ref` variable of a left-hand side, at a well-typed scope, is a reference. -/
theorem ref20_of_var {σ : List (IL.Id × Value)} {qs : List Param} {x : IL.Id} {a : Admin}
    (hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ) qs)
    (hm : Param.expP x (.varT "ref" []) ∈ qs)
    (h : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.subE (.varE x) (.varT "ref" []) (.varT "admininstr" [])) (adminToV a)) :
    ∃ r : Ref, a = aref r := by
  obtain ⟨R, fR, tR⟩ := hq x _ hm
  have e : adminToV a = R := EvalExp.unique (evalExp_subE_iff.1 h) (evalExp_var fR)
  obtain ⟨op, w, he, hop⟩ := refHead_of_typed (Pure.valsOnly_bindVals σ) (e ▸ tR)
  exact admin_of_head_ref (adminToV_case20 he ▸ hop)

set_option maxRecDepth 100000 in
/-- The wasm-2.0 `reftype`. -/
theorem findTyp_reftype20 : (simEnv20 B).findTyp? "reftype" =
    some ([], [.instD [] [] (.variantT (Silmaril.Wasm.SpecTec.Sim.IntNumeric.instCases
      Silmaril.Wasm.SpecTec.Scripts.Wasm20.Original.d59 0))]) := rfl

/-- Every reference type is an IL `reftype`. -/
theorem typedV_refType20 (t : V2.RefType) : TypedV (simEnv20 B) State.reftypeT (refTypeV t) := by
  cases t <;> exact Pure.typedV_closedCase20 findTyp_reftype20 rfl hasTyp_tupT_nil

/-- Every null reference is an IL `ref`. -/
theorem typedV_refNull20 (t : V2.RefType) : TypedV (simEnv20 B) State.refT (refV (.null t)) :=
  Pure.typedV_closedCase20 findTyp_ref20 rfl (typedV_refType20 t _ ⟨rfl, rfl, rfl⟩)

/-! ## The rules -/

/-- The left-hand side `ref REF.IS_NULL`, read back. -/
theorem refIsNull_lhs {i : Nat} {r : Rule} {code : List Admin} {w : List Value}
    (hr : r = State.refIsNullTrueRule ∨ r = State.refIsNullFalseRule)
    (h : Silmaril.SpecTec.Equiv.Validation.HasRuleAt (simEnv20 B) "Step_pure" "%~>%" i r)
    (hf : Fires (simEnv20 B) "Step_pure" i (.tuple [.list (adminsToV code), .list w])) :
    ∃ r : Ref, code = [aref r, .plain .refIsNull] := by
  rcases hr with rfl | rfl
  all_goals
    obtain ⟨σ, hq, hes⟩ := fires_list20 h hf
    obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes20_two hes
    obtain ⟨r, rfl⟩ := ref20_of_var hq (by simp) h₁
    obtain rfl := head20_refIsNull (head20_of_caseE h₂)
    exact ⟨r, rfl⟩

/-- `Step_pure/ref.is_null-true` at any code. -/
theorem bwdPure_refIsNullTrue (P : Profile) {code : List Admin} {w : List Value}
    (hf : Fires (simEnv20 B) "Step_pure" 28 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd P code w := by
  obtain ⟨r, rfl⟩ := refIsNull_lhs (Or.inl rfl) (State.hasRuleAt_refIsNullTrue B) hf
  have hB := firesB_pure hf
  rw [(State.adminsToV_refIsNull r).1] at hB
  obtain ⟨⟨t, rfl⟩, hw⟩ := State.refIsNullTrue_inv B hB
  exact pureBwd_of (code' := [constI32 1])
    (by rw [(State.adminsToV_refIsNull (.null t)).2]; exact hw) .refIsNullTrue

/-- `Step_pure/ref.is_null-false` at any code. -/
theorem bwdPure_refIsNullFalse (P : Profile) {code : List Admin} {w : List Value}
    (hf : Fires (simEnv20 B) "Step_pure" 29 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd P code w := by
  obtain ⟨r, rfl⟩ := refIsNull_lhs (Or.inr rfl) (State.hasRuleAt_refIsNullFalse B) hf
  have hB := firesB_pure hf
  rw [(State.adminsToV_refIsNull r).1] at hB
  obtain ⟨hnn, hw⟩ := State.refIsNullFalse_inv B
    (fun t ht => ⟨ht ▸ typedV_refNull20 t, typedV_refType20 t⟩) hB
  exact pureBwd_of (code' := [constI32 0]) (by rw [State.adminsToV_const0]; exact hw)
    (.refIsNullFalse hnn)

/-- `Step_pure/local.tee` at any code. -/
theorem bwdPure_localTee (P : Profile) {code : List Admin} {w : List Value}
    (hf : Fires (simEnv20 B) "Step_pure" 55 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd P code w := by
  obtain ⟨σ, hq, hes⟩ := fires_list20 (State.hasRuleAt_localTee B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes20_two hes
  obtain ⟨v, rfl⟩ := val20_of_var hq (by simp) h₁
  obtain ⟨x, rfl⟩ := head20_localTee (head20_of_caseE h₂)
  have hB := firesB_pure hf
  rw [(State.adminsToV_localTee v x).1] at hB
  obtain ⟨σ', hq', he, -⟩ := Pure.firesB20_inv (State.hasRuleAt_localTee B) hB
  obtain ⟨u, fu⟩ := Pure.quant_val (x := "val") (t := .varT "val" []) hq' (by simp)
  obtain ⟨X, fx⟩ := Pure.quant_val (x := "x") (t := State.idxT) hq' (by simp)
  have hu := EvalExp.unique he (State.eval_localTee fu fx)
  simp only [Value.tuple.injEq, Value.list.injEq, List.cons.injEq, Value.case.injEq, true_and,
    and_true] at hu
  obtain ⟨⟨rfl, rfl⟩, hw⟩ := hu
  refine ⟨[v.toAdmin, v.toAdmin, .plain (.localSet x)], ?_, .localTee⟩
  rw [hw, ← (State.adminsToV_localTee v x).2]

end Silmaril.Wasm.SpecTec.Sim20.Whole
