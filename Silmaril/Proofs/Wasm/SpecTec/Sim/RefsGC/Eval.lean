module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.RefsGC.Otherwise
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Assembly

/-!
# Evaluating rule instances

Introduction rules for `EvalExp` in the shapes the rule conclusions use, and `eval_tac`, which
applies them structurally: a rule conclusion is built from variables, injections, tuples, lists,
coercions and numerals, and its value under an explicit assignment is read off by these rules
alone. Comparisons, calls and iterations are left to the caller.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.RefsGC

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

variable {env : Env} {ρ : VarEnv}

/-- The empty list of expressions. -/
theorem evalExps_nil' : EvalExps env ρ [] [] := evalExps_nil_iff.2 rfl

/-- A non-empty list of expressions. -/
theorem evalExps_cons' {e : Exp} {es : List Exp} {v : Value} {vs : List Value}
    (h : EvalExp env ρ e v) (hs : EvalExps env ρ es vs) : EvalExps env ρ (e :: es) (v :: vs) :=
  evalExps_cons_iff.2 ⟨v, vs, h, hs, rfl⟩

/-- A tuple. -/
theorem evalExp_tupE_of {es : List Exp} {vs : List Value} (h : EvalExps env ρ es vs) :
    EvalExp env ρ (.tupE es) (.tuple vs) := evalExp_tupE_iff.2 ⟨vs, h, rfl⟩

/-- A list. -/
theorem evalExp_listE_of {es : List Exp} {vs : List Value} (h : EvalExps env ρ es vs) :
    EvalExp env ρ (.listE es) (.list vs) := evalExp_listE_iff.2 ⟨vs, h, rfl⟩

/-- A subtype coercion. -/
theorem evalExp_sub_of {e : Exp} {t₁ t₂ : Typ} {v : Value} (h : EvalExp env ρ e v) :
    EvalExp env ρ (.subE e t₁ t₂) v := evalExp_subE_iff.2 h

/-- A numeral. -/
theorem evalExp_num' {m : IL.Num} : EvalExp env ρ (.numE m) (.num m) := evalExp_numE_iff.2 rfl

/-- `e₁ = e₂` on two values. -/
theorem evalExp_eq {e₁ e₂ : Exp} {t : OpTyp} {v₁ v₂ : Value} (h₁ : EvalExp env ρ e₁ v₁)
    (h₂ : EvalExp env ρ e₂ v₂) : EvalExp env ρ (.cmpE .eqOp t e₁ e₂) (.bool (decide (v₁ = v₂))) :=
  evalExp_cmpE_iff.2 ⟨v₁, v₂, h₁, h₂, rfl⟩

/-- `e₁ = e₂` on two equal values is true. -/
theorem evalExp_eq_true {e₁ e₂ : Exp} {t : OpTyp} {v : Value} (h₁ : EvalExp env ρ e₁ v)
    (h₂ : EvalExp env ρ e₂ v) : EvalExp env ρ (.cmpE .eqOp t e₁ e₂) (.bool true) := by
  have h := evalExp_eq (t := t) h₁ h₂
  simpa using h

/-- `p && q` on two true booleans. -/
theorem evalExp_and_true {e₁ e₂ : Exp} {t : OpTyp} (h₁ : EvalExp env ρ e₁ (.bool true))
    (h₂ : EvalExp env ρ e₂ (.bool true)) : EvalExp env ρ (.binE .andOp t e₁ e₂) (.bool true) :=
  evalExp_binE_iff.2 ⟨_, h₁, .inr ⟨by simp [boolShort], _, h₂, by simp [binValues, boolBin]⟩⟩

/-- `p && q` on two booleans. -/
theorem evalExp_and {e₁ e₂ : Exp} {t : OpTyp} {b₁ b₂ : Bool} (h₁ : EvalExp env ρ e₁ (.bool b₁))
    (h₂ : EvalExp env ρ e₂ (.bool b₂)) : EvalExp env ρ (.binE .andOp t e₁ e₂) (.bool (b₁ && b₂)) := by
  refine evalExp_binE_iff.2 ⟨_, h₁, ?_⟩
  cases b₁
  · exact .inl (by simp [boolShort])
  · exact .inr ⟨by simp [boolShort], _, h₂, by simp [binValues, boolBin]⟩

/-- The natural number inside a `%`-wrapped numeral. -/
theorem evalExp_unpct {e : Exp} {n : Nat}
    (h : EvalExp env ρ e (Silmaril.SpecTec.Equiv.Execution.pctV n)) :
    EvalExp env ρ (.projE (.uncaseE e "%") 0) (.num (.natN n)) :=
  evalExp_projE_iff.2 ⟨_, evalExp_uncaseE_iff.2 h, le_refl _, rfl⟩

/-- Addition of naturals. -/
theorem evalExp_addNat {e₁ e₂ : Exp} {t : OpTyp} {a b : Nat} (h₁ : EvalExp env ρ e₁ (.num (.natN a)))
    (h₂ : EvalExp env ρ e₂ (.num (.natN b))) :
    EvalExp env ρ (.binE .addOp t e₁ e₂) (.num (.natN (a + b))) :=
  evalExp_binE_iff.2 ⟨_, h₁, .inr ⟨rfl, _, h₂, rfl⟩⟩

/-- Multiplication of naturals. -/
theorem evalExp_mulNat {e₁ e₂ : Exp} {t : OpTyp} {a b : Nat} (h₁ : EvalExp env ρ e₁ (.num (.natN a)))
    (h₂ : EvalExp env ρ e₂ (.num (.natN b))) :
    EvalExp env ρ (.binE .mulOp t e₁ e₂) (.num (.natN (a * b))) :=
  evalExp_binE_iff.2 ⟨_, h₁, .inr ⟨rfl, _, h₂, rfl⟩⟩

/-- A comparison of naturals. -/
theorem evalExp_cmpNat {e₁ e₂ : Exp} {op : CmpOp} {t : OpTyp} {a b : Nat} {c : Bool}
    (h₁ : EvalExp env ρ e₁ (.num (.natN a))) (h₂ : EvalExp env ρ e₂ (.num (.natN b)))
    (hc : Num.cmp op (.natN a) (.natN b) = some c) :
    EvalExp env ρ (.cmpE op t e₁ e₂) (.bool c) := by
  refine evalExp_cmpE_iff.2 ⟨_, _, h₁, h₂, ?_⟩
  cases op <;> simp_all [cmpValues, Num.cmp, Res.ofOption]

/-- `a > b` on naturals, when it holds. -/
theorem evalExp_gtNat {e₁ e₂ : Exp} {t : OpTyp} {a b : Nat} (h₁ : EvalExp env ρ e₁ (.num (.natN a)))
    (h₂ : EvalExp env ρ e₂ (.num (.natN b))) (h : b < a) :
    EvalExp env ρ (.cmpE .gtOp t e₁ e₂) (.bool true) :=
  evalExp_cmpNat h₁ h₂ (by simp [Num.cmp, h])

/-- `a ≥ b` on naturals, when it holds. -/
theorem evalExp_geNat {e₁ e₂ : Exp} {t : OpTyp} {a b : Nat} (h₁ : EvalExp env ρ e₁ (.num (.natN a)))
    (h₂ : EvalExp env ρ e₂ (.num (.natN b))) (h : b ≤ a) :
    EvalExp env ρ (.cmpE .geOp t e₁ e₂) (.bool true) :=
  evalExp_cmpNat h₁ h₂ (by simp [Num.cmp, h])

/-- `a ≤ b` on naturals, when it holds. -/
theorem evalExp_leNat {e₁ e₂ : Exp} {t : OpTyp} {a b : Nat} (h₁ : EvalExp env ρ e₁ (.num (.natN a)))
    (h₂ : EvalExp env ρ e₂ (.num (.natN b))) (h : a ≤ b) :
    EvalExp env ρ (.cmpE .leOp t e₁ e₂) (.bool true) :=
  evalExp_cmpNat h₁ h₂ (by simp [Num.cmp, h])

/-- `a < b` on naturals, when it holds. -/
theorem evalExp_ltNat {e₁ e₂ : Exp} {t : OpTyp} {a b : Nat} (h₁ : EvalExp env ρ e₁ (.num (.natN a)))
    (h₂ : EvalExp env ρ e₂ (.num (.natN b))) (h : a < b) :
    EvalExp env ρ (.cmpE .ltOp t e₁ e₂) (.bool true) :=
  evalExp_cmpNat h₁ h₂ (by simp [Num.cmp, h])

/-- The length of a list. -/
theorem evalExp_len {e : Exp} {l : List Value} (h : EvalExp env ρ e (.list l)) :
    EvalExp env ρ (.lenE e) (.num (.natN l.length)) :=
  evalExp_lenE_iff.2 ⟨l, h, rfl⟩

/-- Indexing into a list. -/
theorem evalExp_idx {e₁ e₂ : Exp} {l : List Value} {i : Nat} {v : Value}
    (h₁ : EvalExp env ρ e₁ (.list l)) (h₂ : EvalExp env ρ e₂ (.num (.natN i))) (h : l[i]? = some v) :
    EvalExp env ρ (.idxE e₁ e₂) v :=
  evalExp_idxE_iff.2 ⟨_, _, h₁, h₂, h⟩

/-- Field selection. -/
theorem evalExp_dot {e : Exp} {a : AtomS} {w v : Value} (h : EvalExp env ρ e w)
    (hf : w.field? a = some v) : EvalExp env ρ (.dotE e a) v :=
  evalExp_dotE_iff.2 ⟨w, h, hf⟩

/-- `$(n - 1)` written through `int`, as the iterating rules write it, for `n ≥ 1`. -/
theorem evalExp_predNat {e : Exp} {n : Nat} (h : EvalExp env ρ e (.num (.natN n))) (hn : 1 ≤ n) :
    EvalExp env ρ (.cvtE (.binE .subOp (.numT .intT) (.cvtE e .natT .intT)
      (.cvtE (.numE (.natN 1)) .natT .intT)) .intT .natT) (.num (.natN (n - 1))) := by
  have h₁ : EvalExp env ρ (.cvtE e .natT .intT) (.num (.intN n)) :=
    evalExp_cvtE_iff.2 ⟨_, _, h, rfl, rfl⟩
  have h₂ : EvalExp env ρ (.cvtE (.numE (.natN 1)) .natT .intT) (.num (.intN 1)) :=
    evalExp_cvtE_iff.2 ⟨_, _, evalExp_num', rfl, rfl⟩
  have h₃ : EvalExp env ρ (.binE .subOp (.numT .intT) (.cvtE e .natT .intT)
      (.cvtE (.numE (.natN 1)) .natT .intT)) (.num (.intN ((n : Int) - 1))) :=
    evalExp_binE_iff.2 ⟨_, h₁, .inr ⟨rfl, _, h₂, rfl⟩⟩
  refine evalExp_cvtE_iff.2 ⟨_, _, h₃, ?_, rfl⟩
  have hle : (0 : Int) ≤ (n : Int) - 1 := by omega
  simp only [Num.cvt, hle, ite_true, Option.some.injEq, Num.natN.injEq]
  omega

/-- An option iteration `x?` over a bound domain `y`. -/
theorem evalExp_optPat {x y : IL.Id} (hx : x ≠ "_") {o : Option Value}
    (h : ρ.findVal? y = some (.opt o)) :
    EvalExp env ρ (.iterE (.varE x) (.mk .opt [.mk x (.varE y)])) (.opt o) := by
  refine evalExp_iterE_iff.mpr ⟨4, ?_⟩
  have hdoms : evalDoms 3 env ρ [.mk x (.varE y)] = .ok [(x, Value.opt o)] := by
    simp [evalDoms, domVar, domSrc, evalExp, h]
  rw [evalIterE, hdoms]
  cases o with
  | none => simp [Value.asOpt?, Res.assert, Res.ofOption]
  | some w =>
      simp [Value.asOpt?, Res.assert, Res.ofOption, evalExp, VarEnv.findVal?, VarEnv.bindVals,
        Map.binds, Map.bind, hx]

end Silmaril.Wasm.SpecTec.Sim.RefsGC

/-- Evaluate a rule's conclusion structurally under an explicit assignment. -/
macro "eval_tac" : tactic =>
  `(tactic| repeat (first
    | exact Silmaril.Wasm.SpecTec.Sim.RefsGC.evalExps_nil'
    | apply Silmaril.Wasm.SpecTec.Sim.RefsGC.evalExps_cons'
    | apply Silmaril.Wasm.SpecTec.Sim.RefsGC.evalExp_tupE_of
    | apply Silmaril.Wasm.SpecTec.Sim.RefsGC.evalExp_listE_of
    | apply Silmaril.Wasm.SpecTec.Sim.evalExp_case
    | apply Silmaril.Wasm.SpecTec.Sim.RefsGC.evalExp_sub_of
    | exact Silmaril.Wasm.SpecTec.Sim.RefsGC.evalExp_num'
    | (apply Silmaril.Wasm.SpecTec.Sim.evalExp_var; rfl)
    | (apply Silmaril.Wasm.SpecTec.Sim.RefsGC.evalExp_optPat (by decide); rfl)
    | (apply Silmaril.SpecTec.Equiv.Execution.evalExp_iterPat (by decide); rfl)))
