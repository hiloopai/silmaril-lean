module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Exn.Forward

/-!
# Family X: inverting evaluations of rule conclusions

Small inversion lemmas for `EvalExp` on the expression forms rule conclusions are built from
(tuples, cases, list literals, concatenations), and shape lemmas: which instruction patterns can
evaluate to a one-instruction sequence. `not_ruleBody_of_code` turns a shape lemma into a proof
that a rule does not fire on a configuration.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Exn

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

section Invert
variable {env : Env} {ρ : VarEnv}

theorem evalExps_length : ∀ {es : List Exp} {vs : List Value}, EvalExps env ρ es vs →
    vs.length = es.length
  | [], _, h => by rw [evalExps_nil_iff.1 h]; rfl
  | _ :: _, _, h => by
      obtain ⟨w, ws, -, hws, rfl⟩ := evalExps_cons_iff.1 h
      simp [evalExps_length hws]

theorem evalExps_two_inv {e₁ e₂ : Exp} {v₁ v₂ : Value}
    (h : EvalExps env ρ [e₁, e₂] [v₁, v₂]) : EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ := by
  obtain ⟨w, ws, hw, hws, he⟩ := evalExps_cons_iff.1 h
  obtain ⟨u, us, hu, -, he'⟩ := evalExps_cons_iff.1 hws
  simp only [List.cons.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  simp only [List.cons.injEq] at he'
  obtain ⟨rfl, -⟩ := he'
  exact ⟨hw, hu⟩

theorem evalExp_tup2_inv {e₁ e₂ : Exp} {v₁ v₂ : Value}
    (h : EvalExp env ρ (.tupE [e₁, e₂]) (.tuple [v₁, v₂])) :
    EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ := by
  obtain ⟨vs, hvs, he⟩ := evalExp_tupE_iff.1 h
  cases he
  exact evalExps_two_inv hvs

theorem evalExp_tup3_inv {e₁ e₂ e₃ : Exp} {v₁ v₂ v₃ : Value}
    (h : EvalExp env ρ (.tupE [e₁, e₂, e₃]) (.tuple [v₁, v₂, v₃])) :
    EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ ∧ EvalExp env ρ e₃ v₃ := by
  obtain ⟨vs, hvs, he⟩ := evalExp_tupE_iff.1 h
  cases he
  obtain ⟨w, ws, hw, hws, he⟩ := evalExps_cons_iff.1 hvs
  simp only [List.cons.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨hw, evalExps_two_inv hws⟩

theorem evalExp_case_inv {op op' : MixopS} {e : Exp} {w : Value}
    (h : EvalExp env ρ (.caseE op e) (.case op' w)) : op = op' ∧ EvalExp env ρ e w := by
  obtain ⟨u, hu, he⟩ := evalExp_caseE_iff.1 h
  cases he
  exact ⟨rfl, hu⟩

theorem cat?_list_inv {v₁ v₂ : Value} {l : List Value} (h : Value.cat? v₁ v₂ = some (.list l)) :
    ∃ a b, v₁ = .list a ∧ v₂ = .list b ∧ l = a ++ b := by
  match v₁, v₂, h with
  | .list a, .list b, h => exact ⟨a, b, rfl, rfl, by simpa [Value.cat?] using h.symm⟩
  | .opt none, .opt o, h => simp [Value.cat?] at h
  | .opt (some _), .opt none, h => simp [Value.cat?] at h

theorem evalExp_cat_inv {e₁ e₂ : Exp} {l : List Value}
    (h : EvalExp env ρ (.catE e₁ e₂) (.list l)) :
    ∃ a b, EvalExp env ρ e₁ (.list a) ∧ EvalExp env ρ e₂ (.list b) ∧ l = a ++ b := by
  obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_catE_iff.1 h
  obtain ⟨a, b, rfl, rfl, rfl⟩ := cat?_list_inv hc
  exact ⟨a, b, h₁, h₂, rfl⟩

theorem evalExp_list_inv {es : List Exp} {l : List Value}
    (h : EvalExp env ρ (.listE es) (.list l)) : EvalExps env ρ es l := by
  obtain ⟨vs, hvs, he⟩ := evalExp_listE_iff.1 h
  cases he
  exact hvs

theorem evalExp_list1_inv {e : Exp} {v : Value}
    (h : EvalExp env ρ (.listE [e]) (.list [v])) : EvalExp env ρ e v := by
  obtain ⟨w, ws, hw, -, he⟩ := evalExps_cons_iff.1 (evalExp_list_inv h)
  simp only [List.cons.injEq] at he
  obtain ⟨rfl, -⟩ := he
  exact hw

/-- A one-element list evaluates to a one-element list. -/
theorem evalExp_list1_len {e : Exp} {l : List Value} (h : EvalExp env ρ (.listE [e]) (.list l)) :
    l.length = 1 := evalExps_length (evalExp_list_inv h)

end Invert

section Shapes
variable {env : Env} {ρ : VarEnv}

/-- `[C e]` evaluates to a singleton with head tag `C`. -/
theorem shape_list1Case {op op' : MixopS} {e : Exp} {w : Value}
    (h : EvalExp env ρ (.listE [.caseE op e]) (.list [.case op' w])) : op = op' :=
  (evalExp_case_inv (evalExp_list1_inv h)).1

/-- A two-element list literal is never a singleton. -/
theorem shape_list2 {e₁ e₂ : Exp} {v : Value}
    (h : EvalExp env ρ (.listE [e₁, e₂]) (.list [v])) : False := by
  have := evalExps_length (evalExp_list_inv h)
  simp at this

/-- `A ++ [C e]` evaluates to a singleton only with head tag `C`. -/
theorem shape_catCase {A e : Exp} {op op' : MixopS} {w : Value}
    (h : EvalExp env ρ (.catE A (.listE [.caseE op e])) (.list [.case op' w])) : op = op' := by
  obtain ⟨a, b, -, hb, hab⟩ := evalExp_cat_inv h
  have hb1 : b.length = 1 := evalExp_list1_len hb
  obtain ⟨x, rfl⟩ : ∃ x, b = [x] := List.length_eq_one_iff.1 hb1
  have ha : a = [] := by
    have hl : 1 = a.length + 1 := by simpa using congrArg List.length hab
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst ha
  simp only [List.nil_append, List.cons.injEq, and_true] at hab
  subst hab
  exact (evalExp_case_inv (evalExp_list1_inv hb)).1

/-- `A ++ [x] ++ ([y] ++ B)` is never a singleton. -/
theorem shape_cat2 {A B e₁ e₂ : Exp} {v : Value}
    (h : EvalExp env ρ (.catE A (.catE (.listE [e₁]) (.catE (.listE [e₂]) B))) (.list [v])) :
    False := by
  obtain ⟨a, b, -, hb, hab⟩ := evalExp_cat_inv h
  obtain ⟨c, d, hc, hd, hcd⟩ := evalExp_cat_inv hb
  obtain ⟨g, k, hg, -, hgk⟩ := evalExp_cat_inv hd
  have h1 := evalExp_list1_len hc
  have h2 := evalExp_list1_len hg
  have := congrArg List.length hab
  simp [hcd, hgk, h1, h2] at this
  omega

/-- `(A ++ [C e]) ++ B` contains a `C`. -/
theorem shape_memCase {A B e : Exp} {op : MixopS} {l : List Value}
    (h : EvalExp env ρ (.catE (.catE A (.listE [.caseE op e])) B) (.list l)) :
    ∃ w, Value.case op w ∈ l := by
  obtain ⟨a, b, ha, -, rfl⟩ := evalExp_cat_inv h
  obtain ⟨c, d, -, hd, rfl⟩ := evalExp_cat_inv ha
  obtain ⟨x, rfl⟩ : ∃ x, d = [x] := List.length_eq_one_iff.1 (evalExp_list1_len hd)
  obtain ⟨w, -, rfl⟩ := evalExp_caseE_iff.1 (evalExp_list1_inv hd)
  exact ⟨w, by simp⟩

/-- The conclusion `z; code ~> rhs` of a `Step_read` rule, inverted. -/
theorem evalExp_concl_inv {ze ce re : Exp} {z c' : Value} {code : List Value}
    (h : EvalExp env ρ (.tupE [.caseE "%;%" (.tupE [ze, ce]), re])
      (.tuple [cfgV z code, c'])) :
    EvalExp env ρ ze z ∧ EvalExp env ρ ce (.list code) ∧ EvalExp env ρ re c' := by
  obtain ⟨h₁, h₂⟩ := evalExp_tup2_inv h
  obtain ⟨-, h₃⟩ := evalExp_case_inv h₁
  obtain ⟨h₄, h₅⟩ := evalExp_tup2_inv h₃
  exact ⟨h₄, h₅, h₂⟩

/-- A rule whose instruction pattern cannot evaluate to `[hv]` does not fire on a
configuration whose code is `[hv]`. -/
theorem not_ruleBody_of_code {D : Interp} {els : Prop} {op : MixopS} {nm : IL.Id}
    {qs : List Param} {op' : MixopS} {ze ce re : Exp} {prems : List Prem} {z c' hv : Value}
    (hce : ∀ ρ : VarEnv, ¬ EvalExp env ρ ce (.list [hv])) :
    ¬ RuleBody env D els [] [] op
      (.ruleD nm qs op' (.tupE [.caseE "%;%" (.tupE [ze, ce]), re]) prems)
      (.tuple [cfgV z [hv], c']) := by
  rintro ⟨-, ρ₀, σ, -, -, he, -⟩
  exact hce _ (evalExp_concl_inv he).2.1

end Shapes

end Silmaril.Wasm.SpecTec.Sim.Exn
