module

public import Silmaril.Wasm.Component.Algebra.Term.Defs
public import Silmaril.Wasm.Component.Algebra.Equiv.Thms

/-!
# Terms of the component algebra: theorems

* `denU_eval`: **compositionality**: the meaning of an instantiated term is the
  compositional semantics `Tm.sem` of the term applied to the meanings (and widths) of
  the components substituted for its variables;
* `eval_refines`, `eval_equiv`, `eval_parEquiv`: **congruence**: substituting refining
  (equivalent) components for the variables of any term gives a refining (equivalent)
  component. This covers instantiation with arguments, nesting and every operator that
  is the evaluation of a term (`Silmaril.Wasm.Component.Algebra.Ops`);
* `eval_subst`, `eval_ofComp`, `subst_var`: substitution is evaluation of a
  substituted term; components are closed terms;
* `ctxEquiv_iff`, `ctxRefines_iff`: contextual equivalence (refinement) is denotational
  equivalence (refinement); with `ifaceEquiv_iff`, all four notions coincide.
-/

public section

namespace Silmaril.Wasm.Component.Algebra

open Silmaril.Games Silmaril.Wasm.Component

variable {M : Type}

namespace Tm

/-! ## Syntax -/

mutual
/-- Substitution then instantiation is instantiation by the instantiated substitution. -/
theorem eval_subst (σ : Nat → Tm M) (P : Nat → Comp M) :
    ∀ t : Tm M, (t.subst σ).eval P = t.eval fun k => (σ k).eval P
  | .var _ => rfl
  | .mk I ns xs => by
    simp only [subst, eval, evalNodes_substNodes σ P ns]

theorem evalNodes_substNodes (σ : Nat → Tm M) (P : Nat → Comp M) :
    ∀ ns : List (TNode M), evalNodes P (substNodes σ ns) = evalNodes (fun k => (σ k).eval P) ns
  | [] => rfl
  | n :: ns => by
    simp only [substNodes, evalNodes, evalNode_substNode σ P n, evalNodes_substNodes σ P ns]

theorem evalNode_substNode (σ : Nat → Tm M) (P : Nat → Comp M) :
    ∀ n : TNode M, evalNode P (substNode σ n) = evalNode (fun k => (σ k).eval P) n
  | .core _ _ => rfl
  | .inst t args => by simp only [substNode, evalNode, eval_subst σ P t]
end

mutual
/-- A component is the evaluation of its closed term. -/
theorem eval_ofComp (P : Nat → Comp M) : ∀ c : Comp M, (ofComp c).eval P = c
  | .mk I ns xs => by simp only [ofComp, eval, evalNodes_ofNodes P ns]

theorem evalNodes_ofNodes (P : Nat → Comp M) :
    ∀ ns : List (Node M), evalNodes P (ofNodes ns) = ns
  | [] => rfl
  | n :: ns => by simp only [ofNodes, evalNodes, evalNode_ofNode P n, evalNodes_ofNodes P ns]

theorem evalNode_ofNode (P : Nat → Comp M) : ∀ n : Node M, evalNode P (ofNode n) = n
  | .core _ _ => rfl
  | .inst c args => by simp only [ofNode, evalNode, eval_ofComp P c]
end

mutual
/-- Substituting the variables by themselves. -/
theorem subst_var : ∀ t : Tm M, t.subst Tm.var = t
  | .var _ => rfl
  | .mk I ns xs => by simp only [subst, substNodes_var ns]

theorem substNodes_var : ∀ ns : List (TNode M), substNodes Tm.var ns = ns
  | [] => rfl
  | n :: ns => by simp only [substNodes, substNode_var n, substNodes_var ns]

theorem substNode_var : ∀ n : TNode M, substNode Tm.var n = n
  | .core _ _ => rfl
  | .inst t args => by simp only [substNode, subst_var t]
end

/-- The imports of an instantiated term. -/
theorem imports_eval (P : Nat → Comp M) (t : Tm M) :
    (t.eval P).imports = match t with
      | .var k => (P k).imports
      | .mk I _ _ => I := by
  cases t <;> rfl

variable [CoreModule M]

/-! ## Compositionality -/

/-- The export widths of the components `P`. -/
abbrev widths (P : Nat → Comp M) : Nat → Nat := fun k => (P k).exports.length

/-- The meanings of the components `P`. -/
abbrev meanings (C : CoreSem M) (P : Nat → Comp M) : Nat → Strategy sigU sigU :=
  fun k => (P k).denU C

theorem width_eval (P : Nat → Comp M) :
    ∀ t : Tm M, (t.eval P).exports.length = t.width (widths P)
  | .var _ => rfl
  | .mk _ _ _ => rfl

theorem width_evalNode (P : Nat → Comp M) :
    ∀ n : TNode M, (evalNode P n).width = nodeWidth (widths P) n
  | .core _ _ => rfl
  | .inst t _ => width_eval P t

theorem envAfter_evalNodes (P : Nat → Comp M) :
    ∀ (e : Nat) (ns : List (TNode M)),
      Component.envAfter e (evalNodes P ns) = Tm.envAfter (widths P) e ns
  | _, [] => rfl
  | e, n :: ns => by
    simp only [evalNodes, Component.envAfter, Tm.envAfter, width_evalNode,
      envAfter_evalNodes P _ ns]

mutual
/-- **Compositionality of instantiation.** -/
theorem denU_eval (C : CoreSem M) (P : Nat → Comp M) :
    ∀ t : Tm M, (t.eval P).denU C = t.sem C (widths P) (meanings C P)
  | .var _ => by simp only [eval, sem]
  | .mk I ns xs => by
    simp only [eval, Comp.denU, sem, envAfter_evalNodes, denNodes_evalNodes C P I.length ns]

theorem denNodes_evalNodes (C : CoreSem M) (P : Nat → Comp M) {X : Sig.{0}} :
    ∀ (e : Nat) (ns : List (TNode M)) (E : Strategy X sigU),
      denNodes C e (evalNodes P ns) E = semNodes C (widths P) (meanings C P) e ns E
  | _, [], _ => by simp only [evalNodes, denNodes, semNodes]
  | e, n :: ns, E => by
    simp only [evalNodes, denNodes, semNodes, width_evalNode, den_evalNode C P e n,
      denNodes_evalNodes C P _ ns]

theorem den_evalNode (C : CoreSem M) (P : Nat → Comp M) :
    ∀ (e : Nat) (n : TNode M),
      (evalNode P n).den C e = semNode C (widths P) (meanings C P) e n
  | _, .core _ _ => by simp only [evalNode, Node.den, semNode]
  | e, .inst t args => by simp only [evalNode, Node.den, semNode, denU_eval C P t]
end

mutual
/-- The semantics of a term is monotone in the meanings of its variables. -/
theorem sem_mono (C : CoreSem M) (W : Nat → Nat) {D D' : Nat → Strategy sigU sigU}
    (h : ∀ k, D k ≤ D' k) : ∀ t : Tm M, t.sem C W D ≤ t.sem C W D'
  | .var k => by simpa only [sem] using h k
  | .mk I ns xs => by
    simp only [sem]
    exact Strategy.comp_mono (semNodes_mono C W h I.length ns le_rfl) le_rfl

theorem semNodes_mono (C : CoreSem M) (W : Nat → Nat) {D D' : Nat → Strategy sigU sigU}
    (h : ∀ k, D k ≤ D' k) {X : Sig.{0}} :
    ∀ (e : Nat) (ns : List (TNode M)) {E E' : Strategy X sigU}, E ≤ E' →
      semNodes C W D e ns E ≤ semNodes C W D' e ns E'
  | _, [], _, _, hE => by simpa only [semNodes] using hE
  | e, n :: ns, _, _, hE => by
    simp only [semNodes]
    exact semNodes_mono C W h _ ns (ext_mono e hE (semNode_mono C W h e n))

theorem semNode_mono (C : CoreSem M) (W : Nat → Nat) {D D' : Nat → Strategy sigU sigU}
    (h : ∀ k, D k ≤ D' k) : ∀ (e : Nat) (n : TNode M), semNode C W D e n ≤ semNode C W D' e n
  | _, .core _ _ => by simp only [semNode, le_refl]
  | e, .inst t _ => by
    simp only [semNode]
    exact Strategy.comp_mono le_rfl (sem_mono C W h t)
end

/-! ## Congruence -/

omit [CoreModule M] in
/-- Instantiation preserves equal sizes. -/
theorem sameSizes_eval {P P' : Nat → Comp M} (h : ∀ k, SameSizes (P k) (P' k)) :
    ∀ t : Tm M, SameSizes (t.eval P) (t.eval P')
  | .var k => h k
  | .mk _ _ _ => .refl _

/-- **Congruence for refinement**: refining every argument of a context refines the
instantiated context. -/
theorem eval_refines {C : CoreSem M} {P P' : Nat → Comp M} (h : ∀ k, CompRefines C (P k) (P' k))
    (t : Tm M) : CompRefines C (t.eval P) (t.eval P') := by
  have hW : widths P = widths P' := funext fun k => (h k).1.2
  refine ⟨sameSizes_eval (fun k => (h k).1) t, ?_⟩
  rw [denU_eval, denU_eval, hW]
  exact sem_mono C _ (fun k => (h k).2) t

/-- **Congruence**: equivalent arguments give equivalent instantiations of any context.
In particular **the composition of equivalent components is equivalent**. -/
theorem eval_equiv {C : CoreSem M} {P P' : Nat → Comp M} (h : ∀ k, CompEquiv C (P k) (P' k))
    (t : Tm M) : CompEquiv C (t.eval P) (t.eval P') :=
  compEquiv_iff_refines.2 ⟨eval_refines (fun k => (h k).refines) t,
    eval_refines (fun k => (h k).symm.refines) t⟩

/-- Congruence for parametric equivalence. -/
theorem eval_parEquiv {P P' : Nat → Comp M} (h : ∀ k, ParEquiv (P k) (P' k)) (t : Tm M) :
    ParEquiv (t.eval P) (t.eval P') := fun C => eval_equiv (fun k => h k C) t

/-- Congruence for one argument. -/
theorem eval_update_equiv {C : CoreSem M} (P : Nat → Comp M) (k : Nat) {c : Comp M}
    (h : CompEquiv C (P k) c) (t : Tm M) :
    CompEquiv C (t.eval P) (t.eval (Function.update P k c)) := by
  refine eval_equiv (fun j => ?_) t
  by_cases hj : j = k
  · rw [hj, Function.update_self]
    exact h
  · rw [Function.update_of_ne hj]
    exact .refl C (P j)

end Tm

/-! ## Contextual equivalence -/

variable [CoreModule M]

/-- **Contextual equivalence is denotational equivalence.** -/
theorem ctxEquiv_iff {C : CoreSem M} {c c' : Comp M} : CtxEquiv C c c' ↔ CompEquiv C c c' :=
  ⟨fun h => ifaceEquiv_iff.1 (h (.var 0)),
    fun h t => ifaceEquiv_iff.2 (Tm.eval_equiv (fun _ => h) t)⟩

/-- **Contextual refinement is refinement.** -/
theorem ctxRefines_iff {C : CoreSem M} {c c' : Comp M} :
    CtxRefines C c c' ↔ CompRefines C c c' :=
  ⟨fun h => ifaceRefines_iff.1 (h (.var 0)),
    fun h t => ifaceRefines_iff.2 (Tm.eval_refines (fun _ => h) t)⟩

end Silmaril.Wasm.Component.Algebra
