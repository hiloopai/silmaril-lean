module

public import Silmaril.Wasm.Component.Algebra.Wac.Defs
public import Silmaril.Wasm.Component.Algebra.Term.Thms
public import Silmaril.Wasm.Wac.Graph.Thms
public import Silmaril.Wasm.Wac.Seq.Defs
public import Silmaril.Wasm.Wac.Nest.Defs

/-!
# WAC compositions as terms: theorems

## Agreement with the WAC semantics

* `eval_term`: evaluating the term of a graph at the packages `P` is `Graph.build`;
  `eval_term_toComp`: with the packages' own interfaces it is `Graph.toComp`;
* `sem_term`: the algebra's compositional semantics of the term is `Graph.sem`, the
  compositional semantics of WAC; `denU_toComp_alg` re-derives `Wac.denU_toComp` from
  the algebra (`Tm.denU_eval`);
* `docComp_eq`: a document's component is the evaluation of its term.

## Substitution of equivalent components

* `build_refines`, `build_equiv`: with the package interfaces `S` fixed (those the
  document is elaborated against), replacing every package by a refining (equivalent)
  one refines (is equivalent to) the composition; no hypothesis on names or types;
* `toComp_equiv`, `toComp_update_equiv`: the same for `Graph.toComp`, where the
  interfaces are read from the packages, so the replacements must have the same
  interface (`sigOf`);
* `build_nestPkgs`: **nesting is substitution of terms**; `nest_equiv`: replacing a
  nested composition by an equivalent component (or composition) gives an equivalent
  composition;
* `seq_equiv`: the same for plugging (`Graph.seq`);
* `docComp_equiv`: **substituting equivalent packages in a WAC document gives an
  equivalent composition**.
-/

public section

namespace Silmaril.Wasm.Wac

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Algebra

variable {M : Type}

/-! ## Agreement -/

theorem evalNodes_termNodes (S : Nat → PkgSig) (P : Nat → Comp M) (g : Graph) (I : Iface) :
    ∀ (k : Nat) (ns : List Inst),
      Tm.evalNodes P (g.termNodes S I k ns) = g.mkNodes S P I k ns
  | _, [] => by simp only [Graph.termNodes, Tm.evalNodes, Graph.mkNodes]
  | k, n :: ns => by
    simp only [Graph.termNodes, Tm.evalNodes, Tm.evalNode, Tm.eval, Graph.mkNodes,
      evalNodes_termNodes S P g I (k + 1) ns]

/-- **The term of a graph evaluates to the composition.** -/
theorem eval_term (S : Nat → PkgSig) (P : Nat → Comp M) (g : Graph) :
    (g.term S).eval P = g.build S P := by
  simp only [Graph.term, Tm.eval, evalNodes_termNodes, Graph.build]

/-- With the packages' interfaces: `Graph.toComp`. -/
theorem eval_term_toComp (P : Nat → Comp M) (g : Graph) :
    (g.term fun k => sigOf (P k)).eval P = g.toComp P :=
  eval_term _ P g

/-- A document's component is the evaluation of its term. -/
theorem docComp_eq (env : PkgEnv) (S : Nat → PkgSig) (P : Nat → Comp M)
    (d : Syntax.Document) : docComp env S P d = (docTerm env S d).map (Tm.eval P) := by
  simp only [docComp, docTerm]
  cases docGraph env S d with
  | error e => rfl
  | ok g =>
    show Except.ok (g.build S P) = Except.ok ((g.term S).eval P)
    rw [eval_term]

variable [CoreModule M]

theorem envAfter_termNodes (S : Nat → PkgSig) (g : Graph) (I : Iface) :
    ∀ (k e : Nat) (ns : List Inst),
      Tm.envAfter (fun j => (S j).exports.length) e (g.termNodes S I k ns : List (TNode M)) =
        Graph.envFrom S e ns
  | _, _, [] => by simp only [Graph.termNodes, Tm.envAfter, Graph.envFrom]
  | k, e, n :: ns => by
    simp only [Graph.termNodes, Tm.envAfter, Tm.nodeWidth, Tm.width, Graph.envFrom,
      envAfter_termNodes S g I (k + 1) _ ns]

theorem semNodes_termNodes (C : CoreSem M) (S : Nat → PkgSig) (g : Graph) (I : Iface)
    (D : Nat → Strategy sigU sigU) {X : Sig.{0}} :
    ∀ (k e : Nat) (ns : List Inst) (E : Strategy X sigU),
      Tm.semNodes C (fun j => (S j).exports.length) D e (g.termNodes S I k ns : List (TNode M)) E =
        g.semNodes S I D k e ns E
  | _, _, [], _ => by simp only [Graph.termNodes, Tm.semNodes, Graph.semNodes]
  | k, e, n :: ns, E => by
    simp only [Graph.termNodes, Tm.semNodes, Tm.semNode, Tm.sem, Tm.nodeWidth, Tm.width,
      Graph.semNodes, semNodes_termNodes C S g I D (k + 1) _ ns]

/-- **The algebra's semantics of a WAC term is WAC's compositional semantics.** -/
theorem sem_term (C : CoreSem M) (S : Nat → PkgSig) (D : Nat → Strategy sigU sigU) (g : Graph) :
    (g.term S : Tm M).sem C (fun j => (S j).exports.length) D = g.sem S D := by
  simp only [Graph.term, Tm.sem, envAfter_termNodes, semNodes_termNodes, Graph.sem]

/-- `Wac.denU_toComp`, derived from the algebra. -/
theorem denU_toComp_alg (C : CoreSem M) (P : Nat → Comp M) (g : Graph) :
    (g.toComp P).denU C = g.sem (fun k => sigOf (P k)) (fun k => (P k).denU C) := by
  have hW : Tm.widths P = fun j => (sigOf (P j)).exports.length :=
    funext fun j => (length_exports_sigOf (P j)).symm
  rw [← eval_term_toComp, Tm.denU_eval, hW, sem_term]

/-! ## Substitution of equivalent packages -/

/-- **Refining packages refines the composition** (fixed package interfaces). -/
theorem build_refines {C : CoreSem M} (S : Nat → PkgSig) {P P' : Nat → Comp M}
    (h : ∀ k, CompRefines C (P k) (P' k)) (g : Graph) :
    CompRefines C (g.build S P) (g.build S P') := by
  rw [← eval_term, ← eval_term]
  exact Tm.eval_refines h _

/-- **Equivalent packages give an equivalent composition** (fixed package interfaces). -/
theorem build_equiv {C : CoreSem M} (S : Nat → PkgSig) {P P' : Nat → Comp M}
    (h : ∀ k, CompEquiv C (P k) (P' k)) (g : Graph) :
    CompEquiv C (g.build S P) (g.build S P') := by
  rw [← eval_term, ← eval_term]
  exact Tm.eval_equiv h _

omit [CoreModule M] in
/-- Packages with the same interface are the same size. -/
theorem sameSizes_of_sigOf {c c' : Comp M} (h : sigOf c = sigOf c') : SameSizes c c' := by
  have hi : c.imports = c'.imports := congrArg PkgSig.imports h
  have he : (sigOf c).exports.length = (sigOf c').exports.length := by rw [h]
  exact ⟨by rw [hi], by simpa only [length_exports_sigOf] using he⟩

/-- **Equivalent packages with the same interfaces give an equivalent composition.** -/
theorem toComp_equiv {C : CoreSem M} {P P' : Nat → Comp M} (hs : ∀ k, sigOf (P k) = sigOf (P' k))
    (h : ∀ k, (P k).denU C = (P' k).denU C) (g : Graph) :
    CompEquiv C (g.toComp P) (g.toComp P') := by
  have hS : (fun k => sigOf (P k)) = fun k => sigOf (P' k) := funext hs
  have hb := build_equiv (fun k => sigOf (P k)) (fun k => ⟨sameSizes_of_sigOf (hs k), h k⟩) g
  rw [Graph.toComp, Graph.toComp, ← hS]
  exact hb

/-- **Substituting one package by an equivalent component with the same interface.** -/
theorem toComp_update_equiv {C : CoreSem M} (P : Nat → Comp M) (k : Nat) {c : Comp M}
    (hs : sigOf c = sigOf (P k)) (h : (P k).denU C = c.denU C) (g : Graph) :
    CompEquiv C (g.toComp P) (g.toComp (Function.update P k c)) := by
  refine toComp_equiv (fun j => ?_) (fun j => ?_) g
  · by_cases hj : j = k
    · rw [hj, Function.update_self, hs]
    · rw [Function.update_of_ne hj]
  · by_cases hj : j = k
    · rw [hj, Function.update_self, h]
    · rw [Function.update_of_ne hj]

omit [CoreModule M] in
/-- **Nesting is substitution of terms**: a composition `g₂` in which package `k0` is the
composition `g₁` evaluates the term of `g₂` with the term of `g₁` substituted for the
variable `k0`. -/
theorem build_nestPkgs (S₂ : Nat → PkgSig) (P : Nat → Comp M) (k0 : Nat) (g₁ g₂ : Graph) :
    g₂.build S₂ (nestPkgs P k0 g₁) =
      ((g₂.term S₂).subst (Function.update Tm.var k0 (g₁.term fun k => sigOf (P k)))).eval P := by
  rw [Tm.eval_subst, eval_term]
  congr 1
  funext k
  by_cases hk : k = k0
  · rw [hk, Function.update_self, eval_term_toComp]
    simp only [nestPkgs, ↓reduceIte]
  · rw [Function.update_of_ne hk]
    simp only [nestPkgs, hk, ↓reduceIte, Tm.eval]

/-- **Replacing a nested composition by an equivalent component** (fixed interfaces of
the outer composition). -/
theorem nest_equiv {C : CoreSem M} (S₂ : Nat → PkgSig) (P : Nat → Comp M) (k0 : Nat)
    (g₁ g₂ : Graph) {c : Comp M} (h : CompEquiv C (g₁.toComp P) c) :
    CompEquiv C (g₂.build S₂ (nestPkgs P k0 g₁)) (g₂.build S₂ (Function.update P k0 c)) := by
  refine build_equiv S₂ (fun k => ?_) g₂
  by_cases hk : k = k0
  · rw [hk, Function.update_self]
    simpa only [nestPkgs, ↓reduceIte] using h
  · rw [Function.update_of_ne hk]
    simpa only [nestPkgs, hk, ↓reduceIte] using CompEquiv.refl C (P k)

/-- Plugging (`wac plug`) equivalent packages gives equivalent compositions. -/
theorem seq_equiv {C : CoreSem M} (S : Nat → PkgSig) {P P' : Nat → Comp M}
    (h : ∀ k, CompEquiv C (P k) (P' k)) (g₁ g₂ : Graph) :
    CompEquiv C ((g₁.seq S g₂).build S P) ((g₁.seq S g₂).build S P') :=
  build_equiv S h _

/-- **Substituting equivalent packages in a WAC document gives an equivalent
composition.** -/
theorem docComp_equiv {C : CoreSem M} (env : PkgEnv) (S : Nat → PkgSig) {P P' : Nat → Comp M}
    (h : ∀ k, CompEquiv C (P k) (P' k)) (d : Syntax.Document) {c : Comp M}
    (hc : docComp env S P d = .ok c) :
    ∃ c', docComp env S P' d = .ok c' ∧ CompEquiv C c c' := by
  revert hc
  simp only [docComp]
  cases docGraph env S d with
  | error e => exact fun hc => nomatch hc
  | ok g =>
    intro hc
    have hc' : g.build S P = c := by injection hc
    exact ⟨g.build S P', rfl, hc' ▸ build_equiv S h g⟩

end Silmaril.Wasm.Wac
