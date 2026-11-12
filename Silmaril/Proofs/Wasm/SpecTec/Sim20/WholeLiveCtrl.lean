module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeDecode
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PureControl

/-!
# The live control rules of `Step_pure`, backwards, at arbitrary code

For each live control rule of wasm-2.0 `Step_pure` (`nop` 1, `drop` 2, `select-*` 3–4, `if-*`
5–6, `br_if-*` 10–11, `br_table-*` 12–13): a firing at the image of **any** V2 code sequence is
the image of a V2 `PureStep`. The code is read back with the decoders of `WholeDecode`; the rule
is then inverted at the decoded code by the per-rule `*_inv` lemmas of `Sim20.PureControl`.
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
open Silmaril.Wasm.SpecTec.Sim (Fires)

variable {B : Builtins}

/-- The conclusion of a live `Step_pure` obligation. -/
def PureBwd (P : Profile) (code : List Admin) (w : List Value) : Prop :=
  ∃ code', w = adminsToV code' ∧ PureStep P code code'

/-- From the backend reading's result `.list w = .list (adminsToV code')`. -/
theorem pureBwd_of {P : Profile} {code code' : List Admin} {w : List Value}
    (hw : Value.list w = .list (adminsToV code')) (hs : PureStep P code code') :
    PureBwd P code w :=
  ⟨code', Value.list.inj hw, hs⟩

/-- `Fires` on `Step_pure` as the backend reading. -/
theorem firesB_pure {i : Nat} {v : Value} (h : Fires (simEnv20 B) "Step_pure" i v) :
    Sim.Round6.Reading.FiresB (simEnv20 B) "Step_pure" i v :=
  (Pure.firesB_pure20_iff B).2 h

/-- A `CONST I32 e` element of a left-hand side is an `i32` constant. -/
theorem constI32_of_lhs {env : Env} {ρ : VarEnv} {e : Exp} {a : Admin}
    (h : EvalExp env ρ (.caseE "CONST" (.tupE [.caseE "I32" (.tupE []), e])) (adminToV a)) :
    ∃ c : BitVec 32, a = constI32 c := by
  obtain ⟨u, hu, he⟩ := evalExp_caseE_iff.1 h
  obtain ⟨u₁, u₂, hu₁, -, rfl⟩ := Sim.State.evalExp_tup2_inv hu
  have e₁ : u₁ = caseNilV "I32" := by
    obtain ⟨z, hz, rfl⟩ := evalExp_caseE_iff.1 hu₁
    obtain ⟨zs, hzs, rfl⟩ := evalExp_tupE_iff.1 hz
    rw [Silmaril.SpecTec.Sem.evalExps_nil_iff.1 hzs]
    rfl
  subst e₁
  rcases head20_const (adminToV_case20 he) with ⟨t, b, rfl⟩ | ⟨t, b, rfl⟩
  · cases t
    · exact ⟨b, rfl⟩
    · simp [adminToV, instrToV, valV, numTypeV, caseNilV] at he
  · cases t <;> simp [adminToV, instrToV, valV, numTypeV, caseNilV] at he

/-- `Step_pure/nop` at any code. -/
theorem bwdPure_nop (P : Profile) {code : List Admin} {w : List Value}
    (hf : Fires (simEnv20 B) "Step_pure" 1 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd P code w := by
  obtain ⟨σ, -, hes⟩ := fires_list20 (Pure.hasRuleAt_nop B) hf
  obtain ⟨a₁, rfl, h₁⟩ := codes20_one hes
  obtain rfl := head20_nop (head20_of_caseE h₁)
  exact pureBwd_of ((Pure.nop_iff B).1 (firesB_pure hf)) .nop

/-- `Step_pure/drop` at any code. -/
theorem bwdPure_drop (P : Profile) {code : List Admin} {w : List Value}
    (hf : Fires (simEnv20 B) "Step_pure" 2 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd P code w := by
  obtain ⟨σ, hq, hes⟩ := fires_list20 (Pure.hasRuleAt_drop B) hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes20_two hes
  obtain ⟨v, rfl⟩ := val20_of_var hq (by simp) h₁
  obtain rfl := head20_drop (head20_of_caseE h₂)
  exact pureBwd_of (Pure.drop_inv B (firesB_pure hf)) (.drop v)

/-- The four elements of a `select` left-hand side, read back. -/
theorem select_lhs {i : Nat} {r : Rule} {code : List Admin} {w : List Value}
    (hr : r = Pure.selectTrueRule ∨ r = Pure.selectFalseRule)
    (h : Silmaril.SpecTec.Equiv.Validation.HasRuleAt (simEnv20 B) "Step_pure" "%~>%" i r)
    (hf : Fires (simEnv20 B) "Step_pure" i (.tuple [.list (adminsToV code), .list w])) :
    ∃ (v₁ v₂ : Val) (c : BitVec 32) (ts : Option (List V2.ValType)),
      code = [v₁.toAdmin, v₂.toAdmin, constI32 c, .plain (.select ts)] := by
  rcases hr with rfl | rfl
  all_goals
    obtain ⟨σ, hq, hes⟩ := fires_list20 h hf
    obtain ⟨a₁, a₂, a₃, a₄, rfl, h₁, h₂, h₃, h₄⟩ := codes20_four hes
    obtain ⟨v₁, rfl⟩ := val20_of_var hq (by simp) h₁
    obtain ⟨v₂, rfl⟩ := val20_of_var hq (by simp) h₂
    obtain ⟨c, rfl⟩ := constI32_of_lhs h₃
    obtain ⟨ts, rfl⟩ := head20_select (head20_of_caseE h₄)
    exact ⟨v₁, v₂, c, ts, rfl⟩

/-- `Step_pure/select-true` at any code. -/
theorem bwdPure_selectTrue (P : Profile) {code : List Admin} {w : List Value}
    (hf : Fires (simEnv20 B) "Step_pure" 3 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd P code w := by
  obtain ⟨v₁, v₂, c, ts, rfl⟩ := select_lhs (Or.inl rfl) (Pure.hasRuleAt_selectTrue B) hf
  obtain ⟨hc, hw⟩ := Pure.selectTrue_inv B (firesB_pure hf)
  exact pureBwd_of hw (.selectTrue hc)

/-- `Step_pure/select-false` at any code. -/
theorem bwdPure_selectFalse (P : Profile) {code : List Admin} {w : List Value}
    (hf : Fires (simEnv20 B) "Step_pure" 4 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd P code w := by
  obtain ⟨v₁, v₂, c, ts, rfl⟩ := select_lhs (Or.inr rfl) (Pure.hasRuleAt_selectFalse B) hf
  obtain ⟨rfl, hw⟩ := Pure.selectFalse_inv B (firesB_pure hf)
  exact pureBwd_of hw (.selectFalse v₁ v₂ ts)

/-- A two-instruction left-hand side `CONST I32 c; op …`, read back. -/
theorem constOp_lhs {i : Nat} {nm : IL.Id} {qs : List Param} {e₀ e₂ rh : Exp} {op : MixopS}
    {prems : List Prem} {code : List Admin} {w : List Value}
    (h : Silmaril.SpecTec.Equiv.Validation.HasRuleAt (simEnv20 B) "Step_pure" "%~>%" i
      (.ruleD nm qs "%~>%" (.tupE [.listE [.caseE "CONST" (.tupE [.caseE "I32" (.tupE []), e₀]),
        .caseE op e₂], rh]) prems))
    (hf : Fires (simEnv20 B) "Step_pure" i (.tuple [.list (adminsToV code), .list w])) :
    ∃ (c : BitVec 32) (a : Admin), code = [constI32 c, a] ∧ adminHead20 a = op := by
  obtain ⟨σ, -, hes⟩ := fires_list20 h hf
  obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := codes20_two hes
  obtain ⟨c, rfl⟩ := constI32_of_lhs h₁
  exact ⟨c, a₂, rfl, head20_of_caseE h₂⟩

/-- `Step_pure/if-true` at any code. -/
theorem bwdPure_ifTrue (P : Profile) {code : List Admin} {w : List Value}
    (hf : Fires (simEnv20 B) "Step_pure" 5 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd P code w := by
  obtain ⟨c, a, rfl, ha⟩ := constOp_lhs (Pure.hasRuleAt_ifTrue B) hf
  obtain ⟨bt, b₁, b₂, rfl⟩ := head20_if ha
  obtain ⟨hc, hw⟩ := Pure.ifTrue_inv B (firesB_pure hf)
  exact pureBwd_of hw (.ifTrue hc)

/-- `Step_pure/if-false` at any code. -/
theorem bwdPure_ifFalse (P : Profile) {code : List Admin} {w : List Value}
    (hf : Fires (simEnv20 B) "Step_pure" 6 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd P code w := by
  obtain ⟨c, a, rfl, ha⟩ := constOp_lhs (Pure.hasRuleAt_ifFalse B) hf
  obtain ⟨bt, b₁, b₂, rfl⟩ := head20_if ha
  obtain ⟨rfl, hw⟩ := Pure.ifFalse_inv B (firesB_pure hf)
  exact pureBwd_of hw .ifFalse

/-- `Step_pure/br_if-true` at any code. -/
theorem bwdPure_brIfTrue (P : Profile) {code : List Admin} {w : List Value}
    (hf : Fires (simEnv20 B) "Step_pure" 10 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd P code w := by
  obtain ⟨c, a, rfl, ha⟩ := constOp_lhs (Pure.hasRuleAt_brIfTrue B) hf
  obtain ⟨l, rfl⟩ := head20_brIf ha
  obtain ⟨hc, hw⟩ := Pure.brIfTrue_inv B (firesB_pure hf)
  exact pureBwd_of hw (.brIfTrue hc)

/-- `Step_pure/br_if-false` at any code. -/
theorem bwdPure_brIfFalse (P : Profile) {code : List Admin} {w : List Value}
    (hf : Fires (simEnv20 B) "Step_pure" 11 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd P code w := by
  obtain ⟨c, a, rfl, ha⟩ := constOp_lhs (Pure.hasRuleAt_brIfFalse B) hf
  obtain ⟨l, rfl⟩ := head20_brIf ha
  obtain ⟨rfl, hw⟩ := Pure.brIfFalse_inv B (firesB_pure hf)
  exact pureBwd_of hw .brIfFalse

/-- `Step_pure/br_table-lt` at any code. -/
theorem bwdPure_brTableLt (P : Profile) {code : List Admin} {w : List Value}
    (hf : Fires (simEnv20 B) "Step_pure" 12 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd P code w := by
  obtain ⟨c, a, rfl, ha⟩ := constOp_lhs (Pure.hasRuleAt_brTableLt B) hf
  obtain ⟨ls, l', rfl⟩ := head20_brTable ha
  obtain ⟨l, hl, hw⟩ := Pure.brTableLt_inv B (firesB_pure hf)
  exact pureBwd_of hw (.brTableLt hl)

/-- `Step_pure/br_table-ge` at any code. -/
theorem bwdPure_brTableGe (P : Profile) {code : List Admin} {w : List Value}
    (hf : Fires (simEnv20 B) "Step_pure" 13 (.tuple [.list (adminsToV code), .list w])) :
    PureBwd P code w := by
  obtain ⟨c, a, rfl, ha⟩ := constOp_lhs (Pure.hasRuleAt_brTableGe B) hf
  obtain ⟨ls, l', rfl⟩ := head20_brTable ha
  obtain ⟨hl, hw⟩ := Pure.brTableGe_inv B (firesB_pure hf)
  exact pureBwd_of hw (.brTableGe hl)

end Silmaril.Wasm.SpecTec.Sim20.Whole
