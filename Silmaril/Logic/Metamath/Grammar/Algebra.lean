module

public import Silmaril.Logic.Metamath.Grammar.Tree

@[expose] public section

/-!
# Syntax trees as an algebra

The syntax rules of a grammar form a many-sorted signature
(`Grammar.signature`). Well-sorted trees in a variable context form an
algebra of it (`treeAlgebra`). A well-sorted tree evaluates in any algebra
under a valuation of its variables (`eval`). Evaluation commutes with algebra
homomorphisms and turns tree substitution into composition of valuations.
Closed trees form the initial algebra (`isInitial_treeAlgebra`), so an algebra
of the signature is exactly an interpretation of the syntax, in the sense of
Carneiro's models (*Models for Metamath*, 2016, §3).
-/

namespace Silmaril.Logic.Metamath

open CategoryTheory CategoryTheory.Limits Silmaril.Logic.Metatheory.TheoryModel

universe u w

variable {C V L : Type u} {G : Grammar L C V} {ctx : V → C → Prop}

namespace Grammar

theorem HasSort.length_eq {l : L} {args : List (Tree L V)} {s : C}
    (h : G.HasSort ctx (.node l args) s) : args.length = (G.rule l).arity :=
  h.node_inv.2.1

/-- The `j`-th child of a well-sorted node has the `j`-th argument sort. -/
theorem HasSort.child {l : L} {args : List (Tree L V)} {s : C}
    (h : G.HasSort ctx (.node l args) s) (j : Fin (G.rule l).arity) :
    G.HasSort ctx (args[j.1]'(j.2.trans_eq h.length_eq.symm)) ((G.rule l).args.get j).1 := by
  obtain ⟨-, hlen, hargs⟩ := h.node_inv
  have hj : j.1 < (args.zip (G.rule l).args).length := by simp [hlen]
  have := hargs _ (List.getElem_mem hj)
  simpa [List.getElem_zip] using this

/-- A node whose children have the argument sorts is well sorted. -/
theorem HasSort.node_ofFn {l : L} (a : Fin (G.rule l).arity → Tree L V)
    (h : ∀ j, G.HasSort ctx (a j) ((G.rule l).args.get j).1) :
    G.HasSort ctx (.node l (List.ofFn a)) (G.rule l).tc := by
  refine .node (by simp) fun p hp => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
  simp only [List.length_zip, List.length_ofFn, le_refl, inf_of_le_left] at hi
  simpa [List.getElem_zip] using h ⟨i, hi⟩

variable (G) in
/-- Well-sorted trees in the context `ctx` form an algebra of the grammar
signature. -/
abbrev treeAlgebra (ctx : V → C → Prop) : Algebra.{u, u, u} G.signature where
  Carrier s := {t : Tree L V // G.HasSort ctx t s}
  op {s} o a := ⟨.node o.1 (List.ofFn fun j => (a j).1), by
    have := HasSort.node_ofFn (G := G) (ctx := ctx) (l := o.1) (fun j => (a j).1) fun j => (a j).2
    rwa [o.2] at this⟩

theorem treeAlgebra_op_val {s : C} (o : G.signature.Op s)
    (a : (j : Fin (G.signature.arity o)) → (treeAlgebra G ctx).Carrier (G.signature.argSort o j)) :
    ((treeAlgebra G ctx).op o a).1 = .node o.1 (List.ofFn fun j => (a j).1) := rfl

section Eval

variable (M : Algebra.{u, u, w} G.signature) (ρ : ∀ v s, ctx v s → M.Carrier s)

/-- Evaluate a well-sorted tree in the algebra `M` under the valuation `ρ`. -/
def eval : (t : Tree L V) → {s : C} → G.HasSort ctx t s → M.Carrier s
  | .var v, s, h => ρ v s (HasSort.var_iff.1 h)
  | .node l args, _, h =>
    M.op ⟨l, h.node_inv.1⟩ fun j => eval (args[j.1]'(j.2.trans_eq h.length_eq.symm)) (h.child j)
termination_by t => t
decreasing_by
  have := List.sizeOf_lt_of_mem (List.getElem_mem (l := args) (j.2.trans_eq h.length_eq.symm))
  simp only [Tree.node.sizeOf_spec]
  omega

variable {M ρ}

theorem eval_var {v : V} {s : C} (h : G.HasSort ctx (.var v) s) :
    eval M ρ (.var v) h = ρ v s (HasSort.var_iff.1 h) := by
  rw [eval]

theorem eval_node {l : L} {args : List (Tree L V)} {s : C}
    (h : G.HasSort ctx (.node l args) s) :
    eval M ρ (.node l args) h =
      M.op ⟨l, h.node_inv.1⟩ fun j =>
        eval M ρ (args[j.1]'(j.2.trans_eq h.length_eq.symm)) (h.child j) := by
  rw [eval]

theorem eval_congr {t t' : Tree L V} (e : t = t') {s : C} (h : G.HasSort ctx t s)
    (h' : G.HasSort ctx t' s) : eval M ρ t h = eval M ρ t' h' := by
  subst e; rfl

/-- Evaluation commutes with homomorphisms. -/
theorem Algebra.Hom.map_eval {N : Algebra.{u, u, w} G.signature} (f : Algebra.Hom M N)
    (t : Tree L V) {s : C} (h : G.HasSort ctx t s) :
    f.map (eval M ρ t h) = eval N (fun v s hv => f.map (ρ v s hv)) t h := by
  induction t using Tree.induction generalizing s with
  | var v => rw [eval_var, eval_var]
  | node l args ih =>
    rw [eval_node, eval_node, f.comm]
    congr 1
    funext j
    exact ih _ (List.getElem_mem _) _

/-- Evaluating a substituted tree evaluates the tree under the substituted
valuation. -/
theorem eval_subst {ctx' : V → C → Prop} {M : Algebra.{u, u, w} G.signature}
    {ρ : ∀ v s, ctx' v s → M.Carrier s} {τ : V → Tree L V}
    (hτ : ∀ v s, ctx v s → G.HasSort ctx' (τ v) s) (t : Tree L V) {s : C}
    (h : G.HasSort ctx t s) :
    eval M ρ (t.subst τ) (h.subst hτ) = eval M (fun v s hv => eval M ρ (τ v) (hτ v s hv)) t h := by
  induction t using Tree.induction generalizing s with
  | var v => rw [eval_var, eval_congr (Tree.subst_var' τ v) _ (hτ v s (HasSort.var_iff.1 h))]
  | node l args ih =>
    have hs : G.HasSort ctx' (.node l (args.map (Tree.subst τ))) s :=
      Tree.subst_node τ l args ▸ h.subst hτ
    rw [eval_congr (Tree.subst_node τ l args) _ hs, eval_node, eval_node]
    congr 1
    funext j
    rw [eval_congr (List.getElem_map ..) _ ((h.child j).subst hτ)]
    exact ih _ (List.getElem_mem _) _

end Eval

/-- The valuation of the tree algebra sending each variable to itself. -/
def treeVal (v : V) (s : C) (hv : ctx v s) : (treeAlgebra G ctx).Carrier s := ⟨.var v, .var hv⟩

/-- A tree evaluates to itself in the tree algebra. -/
theorem eval_treeAlgebra (t : Tree L V) {s : C} (h : G.HasSort ctx t s) :
    eval (treeAlgebra G ctx) treeVal t h = ⟨t, h⟩ := by
  induction t using Tree.induction generalizing s with
  | var v => rw [eval_var]; rfl
  | node l args ih =>
    rw [eval_node]
    apply Subtype.ext
    simp only [Tree.node.injEq, true_and]
    refine List.ext_getElem (by simp [h.length_eq]) fun i h₁ h₂ => ?_
    rw [List.getElem_ofFn]
    exact congrArg Subtype.val (ih _ (List.getElem_mem _) _)

/-- The closed trees. -/
abbrev closedTrees (G : Grammar L C V) : Algebra.{u, u, u} G.signature :=
  treeAlgebra G fun _ _ => False

/-- The evaluation of closed trees in an algebra. -/
def closedEval (M : Algebra.{u, u, u} G.signature) : closedTrees G ⟶ M where
  map t := eval M (fun _ _ hv => hv.elim) t.1 t.2
  comm o a := by
    rw [eval_node]
    congr 1
    funext j
    exact eval_congr (List.getElem_ofFn ..) _ _

/-- A well-sorted node is an operation applied to its children. -/
theorem treeAlgebra_node {l : L} {args : List (Tree L V)} {s : C}
    (h : G.HasSort ctx (.node l args) s) :
    (⟨.node l args, h⟩ : (treeAlgebra G ctx).Carrier s) =
      (treeAlgebra G ctx).op ⟨l, h.node_inv.1⟩
        fun j => ⟨args[j.1]'(j.2.trans_eq h.length_eq.symm), h.child j⟩ := by
  apply Subtype.ext
  change Tree.node l args = Tree.node l (List.ofFn _)
  congr 1
  refine List.ext_getElem (by simp [h.length_eq]) fun i h₁ h₂ => ?_
  rw [List.getElem_ofFn]

/-- Every homomorphism out of the closed trees is evaluation. -/
theorem closedEval_unique {M : Algebra.{u, u, u} G.signature} (g : closedTrees G ⟶ M)
    (t : Tree L V) {s : C} (h : G.HasSort (fun _ _ => False) t s) :
    g.map ⟨t, h⟩ = (closedEval M).map ⟨t, h⟩ := by
  induction t using Tree.induction generalizing s with
  | var v => exact (HasSort.var_iff.1 h).elim
  | node l args ih =>
    change g.map ⟨_, h⟩ = eval M _ _ h
    rw [treeAlgebra_node h, g.comm, eval_node]
    congr 1
    funext j
    exact ih _ (List.getElem_mem _) _

/-- Closed trees form the initial algebra of the grammar signature. -/
def isInitial_closedTrees (G : Grammar L C V) : IsInitial (closedTrees G) :=
  IsInitial.ofUniqueHom closedEval fun _ g =>
    Algebra.Hom.ext fun a => closedEval_unique g a.1 a.2

section String

variable [DecidableEq V]

variable (G) in
/-- Math strings form an algebra of the grammar signature: an operation
substitutes its arguments into the rule body. -/
abbrev stringAlgebra : Algebra.{u, u, u} G.signature where
  Carrier _ := Str C V
  op o a := Str.subst (G.argSubst o.1 (List.ofFn a)) (G.rule o.1).body

/-- Flattening is evaluation in the string algebra. -/
theorem flatten_eq_eval (t : Tree L V) {s : C} (h : G.HasSort ctx t s) :
    G.flatten t = eval (stringAlgebra G) (fun v _ _ => [.var v]) t h := by
  induction t using Tree.induction generalizing s with
  | var v => rw [eval_var, flatten_var]
  | node l args ih =>
    rw [eval_node, flatten_node]
    change _ = Str.subst (G.argSubst l (List.ofFn _)) _
    congr 2
    refine List.ext_getElem (by simp [h.length_eq]) fun i h₁ h₂ => ?_
    rw [List.getElem_ofFn, List.getElem_map]
    exact ih _ (List.getElem_mem _) _

end String

end Grammar

end Silmaril.Logic.Metamath
