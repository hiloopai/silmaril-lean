module

public import Silmaril.Logic.Metamath.Grammar.Algebra
public import Silmaril.Logic.Metamath.Grammar.Derivation

@[expose] public section

/-!
# Models of grammatical Metamath systems

A model of a grammar follows Carneiro, *Models for Metamath* (2016),
Definition 10 (models of tree formal systems):

* an algebra of the grammar signature: a domain for each sort and an
  interpretation `π` of each syntax rule (`Model.toAlgebra`);
* a freshness relation `#` between values of any two sorts. It is symmetric,
  every syntax sort has a value fresh for any finitely many given values
  (Definition 2), and an operation applied to arguments fresh for `a` is fresh
  for `a` (the last clause of Definition 10);
* a truth predicate `IsTrue` on the domain of the syntax sort of each provable
  typecode, the subset `U_c ⊆ U_{Syn(c)}`.

The freshness existence clause implies that every syntax sort has a nonempty
domain (`Model.nonempty`). Variables range over syntax sorts only, so a
valuation of a variable context assigns values to the variables at syntax
sorts (`Grammar.synCtx`).

A tree expression holds under a valuation when its tree has the syntax sort
of its typecode and the value of the tree is true. A valuation satisfies the
disjoint-variable conditions when the values of every declared pair of
distinct variables are fresh for each other. A model satisfies a tree
assertion when every valuation satisfying its disjoint-variable conditions and
its essential hypotheses makes its conclusion hold, and a model of an axiom
set satisfies each of its axioms.

The freshness relation of a model is compositional (`Model.fresh_eval`): a
value fresh for the values of all variables of a tree is fresh for the value
of the tree. Carneiro calls this the freshness substitution law.
-/

namespace Silmaril.Logic.Metamath

open Silmaril.Logic.Metatheory.TheoryModel

universe u w

variable {C V L : Type u}

namespace Grammar

variable {G : Grammar L C V}

/-- The part of a variable context at syntax sorts. -/
def synCtx (G : Grammar L C V) (ctx : V → C → Prop) (v : V) (s : C) : Prop :=
  ctx v s ∧ s ∈ G.sorts

theorem synCtx_le (ctx : V → C → Prop) (v : V) (s : C) (h : G.synCtx ctx v s) : ctx v s := h.1

/-- A tree of a syntax sort only uses variables at syntax sorts. -/
theorem HasSort.synCtx {ctx : V → C → Prop} {t : Tree L V} {s : C} (h : G.HasSort ctx t s)
    (hs : s ∈ G.sorts) : G.HasSort (G.synCtx ctx) t s := by
  induction h with
  | var hv => exact .var ⟨hv, hs⟩
  | @node l args hlen _ ih =>
    exact .node hlen fun p hp => ih p hp (G.rule_args l p.2 (List.of_mem_zip hp).2)

theorem hasSort_synCtx_iff {ctx : V → C → Prop} {t : Tree L V} {s : C} (hs : s ∈ G.sorts) :
    G.HasSort (G.synCtx ctx) t s ↔ G.HasSort ctx t s :=
  ⟨HasSort.mono (synCtx_le ctx), fun h => h.synCtx hs⟩

theorem mem_vars_node {l : L} {args : List (Tree L V)} {v : V} :
    v ∈ (Tree.node l args).vars ↔ ∃ a ∈ args, v ∈ a.vars := by
  simp [Tree.vars_node, List.mem_flatMap]

/-- Sorting only depends on the context at the variables of the tree. -/
theorem HasSort.congr_ctx {ctx ctx' : V → C → Prop} {t : Tree L V} {s : C}
    (h : G.HasSort ctx t s) (hctx : ∀ v ∈ t.vars, ∀ s, ctx v s → ctx' v s) :
    G.HasSort ctx' t s := by
  induction h with
  | var hv => exact .var (hctx _ (by simp) _ hv)
  | @node l args hlen _ ih =>
    refine .node hlen fun p hp => ih p hp fun v hv s' h' => hctx v ?_ s' h'
    exact mem_vars_node.2 ⟨p.1, (List.of_mem_zip hp).1, hv⟩

/-- Evaluation only depends on the valuation at the variables of the tree. -/
theorem eval_agree {ctx₁ ctx₂ : V → C → Prop} (M : Algebra.{u, u, w} G.signature)
    {ρ₁ : ∀ v s, ctx₁ v s → M.Carrier s} {ρ₂ : ∀ v s, ctx₂ v s → M.Carrier s} (t : Tree L V)
    {s : C} (h₁ : G.HasSort ctx₁ t s) (h₂ : G.HasSort ctx₂ t s)
    (hρ : ∀ v ∈ t.vars, ∀ s h₁ h₂, ρ₁ v s h₁ = ρ₂ v s h₂) : eval M ρ₁ t h₁ = eval M ρ₂ t h₂ := by
  induction t using Tree.induction generalizing s with
  | var v => rw [eval_var, eval_var]; exact hρ v (by simp) s _ _
  | node l args ih =>
    rw [eval_node, eval_node]
    congr 1
    funext j
    exact ih _ (List.getElem_mem _) _ _ fun v hv s' h₁' h₂' =>
      hρ v (mem_vars_node.2 ⟨_, List.getElem_mem _, hv⟩) s' h₁' h₂'

end Grammar

/-- A model of a grammar (Carneiro, *Models for Metamath*, Definition 10): an
interpretation of the syntax rules, a compositional symmetric freshness
relation with fresh values at every syntax sort, and the true values of each
provable typecode. -/
structure Model (G : Grammar L C V) extends Algebra.{u, u, w} G.signature where
  /-- The freshness relation `#`, between values of any two sorts. -/
  Fresh : ∀ {s t : C}, Carrier s → Carrier t → Prop
  fresh_symm : ∀ {s t : C} {a : Carrier s} {b : Carrier t}, Fresh a b → Fresh b a
  /-- An operation applied to arguments fresh for `a` is fresh for `a`. -/
  fresh_op : ∀ {s t : C} (a : Carrier s) (o : G.signature.Op t)
    (args : (j : Fin (G.signature.arity o)) → Carrier (G.signature.argSort o j)),
    (∀ j, Fresh a (args j)) → Fresh a (op o args)
  /-- Every syntax sort has a value fresh for finitely many given values. -/
  exists_fresh : ∀ s ∈ G.sorts, ∀ W : List (Σ t, Carrier t),
    ∃ a : Carrier s, ∀ w ∈ W, Fresh a w.2
  /-- The true values of the provable typecode `c`, among the values of its
  syntax sort `s`. -/
  IsTrue : ∀ {c s : C}, G.prov c = some s → Carrier s → Prop

namespace Model

open Grammar

variable {G : Grammar L C V} (M : Model.{u, w} G)

theorem nonempty {s : C} (hs : s ∈ G.sorts) : Nonempty (M.Carrier s) :=
  let ⟨a, _⟩ := M.exists_fresh s hs []
  ⟨a⟩

/-- A valuation of the variables of `ctx` at syntax sorts. -/
abbrev Valuation (ctx : V → C → Prop) : Type (max u w) := ∀ v s, G.synCtx ctx v s → M.Carrier s

/-- The value of a well-sorted tree. -/
abbrev value {ctx : V → C → Prop} (ρ : ∀ v s, ctx v s → M.Carrier s) (t : Tree L V) {s : C}
    (h : G.HasSort ctx t s) : M.Carrier s :=
  eval M.toAlgebra ρ t h

theorem value_var {ctx : V → C → Prop} (ρ : ∀ v s, ctx v s → M.Carrier s) {v : V} {s : C}
    (h : G.HasSort ctx (.var v) s) : M.value ρ (.var v) h = ρ v s (HasSort.var_iff.1 h) :=
  eval_var h

/-- Transport a value along an equality of sorts. -/
def transport {s s' : C} (e : s = s') (x : M.Carrier s) : M.Carrier s' := e ▸ x

@[simp] theorem transport_rfl {s : C} (x : M.Carrier s) : M.transport rfl x = x := rfl

theorem fresh_transport {s' : C} (a : M.Carrier s') {s t : C} (e : s = t) (x : M.Carrier s) :
    M.Fresh a (M.transport e x) ↔ M.Fresh a x := by
  subst e
  rfl

/-- The tree expression `e` holds: its tree has the syntax sort of its typecode
and its value is true. -/
def Holds {ctx : V → C → Prop} (ρ : M.Valuation ctx) (e : TExpr L C V) : Prop :=
  ∃ s, ∃ hs : G.prov e.tc = some s, ∃ h : G.HasSort (G.synCtx ctx) e.tree s,
    M.IsTrue hs (M.value ρ e.tree h)

/-- The valuation `ρ` satisfies the disjoint-variable conditions `dv`. -/
def DVHolds {ctx : V → C → Prop} (ρ : M.Valuation ctx) (dv : List (V × V)) : Prop :=
  ∀ x y, (x, y) ∈ dv → x ≠ y → ∀ s t hx hy, M.Fresh (ρ x s hx) (ρ y t hy)

/-- `M` satisfies the tree assertion `A`. -/
def Satisfies (A : TAssertion L C V) : Prop :=
  ∀ ρ : M.Valuation A.ctx, M.DVHolds ρ A.dv → (∀ e ∈ A.essentials, M.Holds ρ e) →
    M.Holds ρ A.concl

/-- `M` is a model of the axiom set `Γ`. -/
def IsModel (Γ : Set (TAssertion L C V)) : Prop := ∀ B ∈ Γ, M.Satisfies B

theorem IsModel.mono {Γ Δ : Set (TAssertion L C V)} (h : Γ ⊆ Δ) {M : Model.{u, w} G}
    (hM : M.IsModel Δ) : M.IsModel Γ :=
  fun B hB => hM B (h hB)

theorem isModel_union {Γ Δ : Set (TAssertion L C V)} :
    M.IsModel (Γ ∪ Δ) ↔ M.IsModel Γ ∧ M.IsModel Δ :=
  ⟨fun h => ⟨h.mono Set.subset_union_left, h.mono Set.subset_union_right⟩,
    fun ⟨h₁, h₂⟩ B hB => hB.elim (h₁ B) (h₂ B)⟩

theorem isModel_singleton {A : TAssertion L C V} : M.IsModel {A} ↔ M.Satisfies A :=
  ⟨fun h => h A rfl, fun h _ hB => hB ▸ h⟩

/-- Compositionality of freshness (Carneiro's freshness substitution law): a
value fresh for the values of all variables of a tree is fresh for the value
of the tree. -/
theorem fresh_eval {ctx : V → C → Prop} (ρ : ∀ v s, ctx v s → M.Carrier s) {s' : C}
    (a : M.Carrier s') (t : Tree L V) {s : C} (h : G.HasSort ctx t s)
    (ha : ∀ v ∈ t.vars, ∀ s hv, M.Fresh a (ρ v s hv)) : M.Fresh a (M.value ρ t h) := by
  induction t using Tree.induction generalizing s with
  | var v => rw [value, eval_var]; exact ha v (by simp) s _
  | node l args ih =>
    rw [value, eval_node]
    exact M.fresh_op a _ _ fun j => ih _ (List.getElem_mem _) _ fun v hv s' hv' =>
      ha v (mem_vars_node.2 ⟨_, List.getElem_mem _, hv⟩) s' hv'

/-- Freshness between the values of two trees whose variables are pairwise
fresh. -/
theorem fresh_eval_eval {ctx : V → C → Prop} (ρ : ∀ v s, ctx v s → M.Carrier s)
    (t t' : Tree L V) {s s' : C} (h : G.HasSort ctx t s) (h' : G.HasSort ctx t' s')
    (hf : ∀ a ∈ t.vars, ∀ b ∈ t'.vars, ∀ s s' ha hb, M.Fresh (ρ a s ha) (ρ b s' hb)) :
    M.Fresh (M.value ρ t h) (M.value ρ t' h') :=
  M.fresh_eval ρ _ t' h' fun b hb sb hb' => M.fresh_symm <|
    M.fresh_eval ρ _ t h fun a ha sa ha' => M.fresh_symm (hf a ha b hb sa sb ha' hb')

/-- Evaluation only depends on the valuation at the variables of the tree. -/
theorem value_agree {ctx₁ ctx₂ : V → C → Prop} {ρ₁ : ∀ v s, ctx₁ v s → M.Carrier s}
    {ρ₂ : ∀ v s, ctx₂ v s → M.Carrier s} (t : Tree L V) {s : C} (h₁ : G.HasSort ctx₁ t s)
    (h₂ : G.HasSort ctx₂ t s) (hρ : ∀ v ∈ t.vars, ∀ s h₁ h₂, ρ₁ v s h₁ = ρ₂ v s h₂) :
    M.value ρ₁ t h₁ = M.value ρ₂ t h₂ :=
  eval_agree M.toAlgebra t h₁ h₂ hρ

variable {M} in
/-- Truth of an expression only depends on the context and the valuation at
its variables. -/
theorem Holds.congr {ctx₁ ctx₂ : V → C → Prop} {ρ₁ : M.Valuation ctx₁} {ρ₂ : M.Valuation ctx₂}
    {e : TExpr L C V} (hctx : ∀ v ∈ e.tree.vars, ∀ s, ctx₁ v s → ctx₂ v s)
    (hρ : ∀ v ∈ e.tree.vars, ∀ s h₁ h₂, ρ₁ v s h₁ = ρ₂ v s h₂) (h : M.Holds ρ₁ e) :
    M.Holds ρ₂ e := by
  obtain ⟨s, hs, ht, htrue⟩ := h
  have ht' : G.HasSort (G.synCtx ctx₂) e.tree s :=
    ht.congr_ctx fun v hv s' h' => ⟨hctx v hv s' h'.1, h'.2⟩
  exact ⟨s, hs, ht', by rwa [← M.value_agree e.tree ht ht' hρ]⟩

/-- The trivial model: one value in every domain, fresh for itself and true.
It satisfies every assertion, so the existence of a model alone says nothing;
a model is useful when some assertion fails in it. -/
def trivial (G : Grammar L C V) : Model.{u, w} G where
  Carrier _ := PUnit
  op _ _ := PUnit.unit
  Fresh _ _ := True
  fresh_symm _ := True.intro
  fresh_op _ _ _ _ := True.intro
  exists_fresh _ _ _ := ⟨PUnit.unit, fun _ _ => True.intro⟩
  IsTrue _ _ := True

theorem trivial_satisfies (A : TAssertion L C V) (hA : A.concl.WellTyped G A.ctx) :
    (trivial.{u, w} G).Satisfies A := by
  intro ρ _ _
  obtain ⟨s, hs, ht⟩ := hA
  exact ⟨s, hs, ht.synCtx (G.prov_sort hs), True.intro⟩

end Model

end Silmaril.Logic.Metamath
