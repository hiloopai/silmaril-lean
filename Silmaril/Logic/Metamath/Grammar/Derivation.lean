module

public import Silmaril.Logic.Metamath.Grammar.Tree
public import Silmaril.Logic.Metamath.Derivation

@[expose] public section

/-!
# Tree assertions and tree derivations

A tree assertion is an assertion whose essential hypotheses and conclusion are
syntax trees at provable typecodes. Its floating hypotheses give the variable
context. Tree derivations have the shape of string derivations
(`Silmaril.Logic.Metamath.Derivation`), except that the syntax proofs of the
substituted strings are replaced by the requirement that the substituted trees
are well sorted. This is Carneiro's tree formal system (*Models for Metamath*,
2016, §2.4).

Flattening turns tree assertions into string assertions. The string axiom set
of a grammatical system is the set of syntax axioms together with the
flattened logical axioms.
-/

namespace Silmaril.Logic.Metamath

open Cslib.Logic

universe u

variable {C V : Type u}

namespace Grammar

variable {L : Type u}

/-- A tree expression: a typecode and a syntax tree. -/
structure TExpr (L C V : Type u) where
  tc : C
  tree : Tree L V

/-- A hypothesis of a tree assertion. -/
inductive THyp (L C V : Type u) where
  /-- The floating hypothesis `tc v`. -/
  | float (tc : C) (v : V)
  /-- An essential hypothesis. -/
  | ess (e : TExpr L C V)

/-- A tree assertion: disjoint-variable pairs, hypotheses in database order,
and a conclusion. -/
structure TAssertion (L C V : Type u) where
  dv : List (V × V)
  hyps : List (THyp L C V)
  concl : TExpr L C V

namespace TExpr

/-- The variables of a tree expression. -/
def vars (e : TExpr L C V) : List V := e.tree.vars

/-- Substitution into a tree expression preserves its typecode. -/
def subst (τ : V → Tree L V) (e : TExpr L C V) : TExpr L C V := ⟨e.tc, e.tree.subst τ⟩

@[simp] theorem subst_tc (τ : V → Tree L V) (e : TExpr L C V) : (e.subst τ).tc = e.tc := rfl

@[simp] theorem subst_tree (τ : V → Tree L V) (e : TExpr L C V) :
    (e.subst τ).tree = e.tree.subst τ := rfl

@[simp] theorem subst_var (e : TExpr L C V) : e.subst .var = e := by
  cases e; simp [subst]

/-- `e` is at a provable typecode, and its tree has the syntax typecode of it. -/
def WellTyped (G : Grammar L C V) (ctx : V → C → Prop) (e : TExpr L C V) : Prop :=
  ∃ s, G.prov e.tc = some s ∧ G.HasSort ctx e.tree s

theorem WellTyped.mono {G : Grammar L C V} {ctx ctx' : V → C → Prop}
    (hle : ∀ v s, ctx v s → ctx' v s) {e : TExpr L C V} (h : e.WellTyped G ctx) :
    e.WellTyped G ctx' :=
  let ⟨s, hs, ht⟩ := h
  ⟨s, hs, ht.mono hle⟩

variable [DecidableEq V]

/-- The string expression of a tree expression. -/
def flatten (G : Grammar L C V) (e : TExpr L C V) : Expr C V := ⟨e.tc, G.flatten e.tree⟩

@[simp] theorem flatten_tc (G : Grammar L C V) (e : TExpr L C V) :
    (e.flatten G).tc = e.tc := rfl

@[simp] theorem flatten_body (G : Grammar L C V) (e : TExpr L C V) :
    (e.flatten G).body = G.flatten e.tree := rfl

theorem flatten_subst (G : Grammar L C V) (τ : V → Tree L V) (e : TExpr L C V) :
    (e.subst τ).flatten G = (e.flatten G).subst fun v => G.flatten (τ v) := by
  simp [flatten, subst, Expr.subst, Grammar.flatten_subst]

end TExpr

namespace THyp

/-- The variables of a hypothesis. -/
def vars : THyp L C V → List V
  | float _ v => [v]
  | ess e => e.vars

/-- The string hypothesis of a tree hypothesis. -/
def flatten [DecidableEq V] (G : Grammar L C V) : THyp L C V → Hyp C V
  | float tc v => .float tc v
  | ess e => .ess (e.flatten G)

end THyp

namespace TAssertion

/-- The floating hypotheses `(typecode, variable)`, in order. -/
def floats (A : TAssertion L C V) : List (C × V) :=
  A.hyps.filterMap fun
    | .float tc v => some (tc, v)
    | .ess _ => none

/-- The essential hypotheses, in order. -/
def essentials (A : TAssertion L C V) : List (TExpr L C V) :=
  A.hyps.filterMap fun
    | .float _ _ => none
    | .ess e => some e

/-- The variable context given by the floating hypotheses. -/
def ctx (A : TAssertion L C V) (v : V) (s : C) : Prop := THyp.float s v ∈ A.hyps

/-- Every variable mentioned by the assertion. -/
def allVars (A : TAssertion L C V) : List V :=
  A.concl.vars ++ A.hyps.flatMap THyp.vars

/-- The symmetric disjointness relation declared by the assertion. -/
def Disjoint (A : TAssertion L C V) (x y : V) : Prop := (x, y) ∈ A.dv ∨ (y, x) ∈ A.dv

/-- `τ` respects `A`'s disjoint-variable conditions inside a context whose
disjointness relation is `disj`. -/
def DVSafe (A : TAssertion L C V) (τ : V → Tree L V) (disj : V → V → Prop) : Prop :=
  ∀ x y, (x, y) ∈ A.dv → ∀ a ∈ (τ x).vars, ∀ b ∈ (τ y).vars, a ≠ b ∧ disj a b

theorem mem_floats {A : TAssertion L C V} {s : C} {v : V} :
    (s, v) ∈ A.floats ↔ A.ctx v s := by
  simp only [floats, List.mem_filterMap, ctx]
  constructor
  · rintro ⟨h, hh, he⟩
    cases h <;> simp at he
    obtain ⟨rfl, rfl⟩ := he
    exact hh
  · exact fun h => ⟨_, h, rfl⟩

theorem mem_essentials {A : TAssertion L C V} {e : TExpr L C V} :
    e ∈ A.essentials ↔ THyp.ess e ∈ A.hyps := by
  simp only [essentials, List.mem_filterMap]
  constructor
  · rintro ⟨h, hh, he⟩
    cases h <;> simp at he
    exact he ▸ hh
  · exact fun h => ⟨_, h, rfl⟩

/-- A variable with a floating hypothesis is mentioned by the assertion. -/
theorem mem_allVars_of_ctx {A : TAssertion L C V} {v : V} {s : C} (h : A.ctx v s) :
    v ∈ A.allVars := by
  simp only [allVars, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨_, h, by simp [THyp.vars]⟩

/-- A well-formed tree assertion: floating hypotheses at syntax typecodes name
distinct variables, essential hypotheses and the conclusion are well typed at
provable typecodes, and disjoint pairs are distinct variables with floating
hypotheses. -/
structure WellFormed (G : Grammar L C V) (A : TAssertion L C V) : Prop where
  floats_nodup : (A.floats.map Prod.snd).Nodup
  float_sort : ∀ v s, A.ctx v s → s ∈ G.sorts
  ess_wellTyped : ∀ e ∈ A.essentials, e.WellTyped G A.ctx
  concl_wellTyped : A.concl.WellTyped G A.ctx
  dv_irrefl : ∀ x y, (x, y) ∈ A.dv → x ≠ y
  dv_float : ∀ x y, (x, y) ∈ A.dv → (∃ s, A.ctx x s) ∧ ∃ s, A.ctx y s

/-- Distinct floating variables make the context functional. -/
theorem functional_ctx {A : TAssertion L C V} (h : (A.floats.map Prod.snd).Nodup) :
    Functional A.ctx := by
  intro v s s' hs hs'
  rw [← mem_floats] at hs hs'
  exact (Prod.mk.inj (List.inj_on_of_nodup_map h hs hs' rfl)).1

variable [DecidableEq V]

/-- The string assertion of a tree assertion. -/
def flatten (G : Grammar L C V) (A : TAssertion L C V) : Assertion C V where
  dv := A.dv
  hyps := A.hyps.map (THyp.flatten G)
  concl := A.concl.flatten G

variable {G : Grammar L C V} {A : TAssertion L C V}

@[simp] theorem flatten_concl : (A.flatten G).concl = A.concl.flatten G := rfl

@[simp] theorem flatten_dv : (A.flatten G).dv = A.dv := rfl

theorem disjoint_flatten : (A.flatten G).Disjoint = A.Disjoint := rfl

theorem float_mem_flatten {s : C} {v : V} :
    Hyp.float s v ∈ (A.flatten G).hyps ↔ A.ctx v s := by
  simp only [flatten, List.mem_map, ctx]
  constructor
  · rintro ⟨h, hh, he⟩
    cases h <;> simp [THyp.flatten] at he
    obtain ⟨rfl, rfl⟩ := he
    exact hh
  · exact fun h => ⟨_, h, rfl⟩

theorem mem_essentials_flatten {e : Expr C V} :
    e ∈ (A.flatten G).essentials ↔ ∃ e' ∈ A.essentials, e'.flatten G = e := by
  simp only [Assertion.essentials, flatten, List.filterMap_map, List.mem_filterMap,
    mem_essentials]
  constructor
  · rintro ⟨h, hh, he⟩
    cases h <;> simp [THyp.flatten] at he
    exact ⟨_, hh, he⟩
  · rintro ⟨e', he', rfl⟩
    exact ⟨_, he', rfl⟩

/-- The hypothesis expressions of a flattened assertion. -/
theorem mem_hypExprs_flatten {e : Expr C V} :
    e ∈ (A.flatten G).hypExprs ↔
      (∃ s v, A.ctx v s ∧ e = ⟨s, [.var v]⟩) ∨ ∃ e' ∈ A.essentials, e = e'.flatten G := by
  simp only [Assertion.hypExprs, flatten, List.map_map, List.mem_map, Function.comp_apply]
  constructor
  · rintro ⟨h, hh, rfl⟩
    cases h with
    | float s v => exact Or.inl ⟨s, v, hh, rfl⟩
    | ess e' => exact Or.inr ⟨e', mem_essentials.2 hh, rfl⟩
  · rintro (⟨s, v, hh, rfl⟩ | ⟨e', he', rfl⟩)
    · exact ⟨_, hh, rfl⟩
    · exact ⟨_, mem_essentials.1 he', rfl⟩

theorem mem_allVars_of_mem_allVars_flatten {v : V} (h : v ∈ (A.flatten G).allVars) :
    v ∈ A.allVars := by
  simp only [Assertion.allVars, flatten, List.mem_append, List.mem_flatMap, List.mem_map] at h
  simp only [allVars, List.mem_append, List.mem_flatMap]
  rcases h with h | ⟨_, ⟨hh, hmem, rfl⟩, hv⟩
  · exact Or.inl (mem_vars_of_mem_vars_flatten h)
  · refine Or.inr ⟨hh, hmem, ?_⟩
    cases hh with
    | float s w => simpa [THyp.flatten, Hyp.vars, Expr.vars, Str.vars, THyp.vars] using hv
    | ess e => exact mem_vars_of_mem_vars_flatten hv

theorem mem_allVars_flatten (hA : A.WellFormed G) {v : V} (h : v ∈ A.allVars) :
    v ∈ (A.flatten G).allVars := by
  simp only [allVars, List.mem_append, List.mem_flatMap] at h
  simp only [Assertion.allVars, flatten, List.mem_append, List.mem_flatMap, List.mem_map]
  rcases h with h | ⟨hh, hmem, hv⟩
  · obtain ⟨s, -, hs⟩ := hA.concl_wellTyped
    exact Or.inl (hs.mem_vars_flatten.2 h)
  · refine Or.inr ⟨_, ⟨hh, hmem, rfl⟩, ?_⟩
    cases hh with
    | float s w => simpa [THyp.flatten, Hyp.vars, Expr.vars, Str.vars, THyp.vars] using hv
    | ess e =>
      obtain ⟨s, -, hs⟩ := hA.ess_wellTyped e (mem_essentials.2 hmem)
      exact hs.mem_vars_flatten.2 hv

end TAssertion

/-- The dummy variables of a tree proof: fresh floating hypotheses on distinct
variables and extra disjointness conditions, each of which mentions a dummy. -/
structure TDummies (A : TAssertion L C V) where
  floats : List (C × V)
  dv : List (V × V)
  fresh : ∀ p ∈ floats, p.2 ∉ A.allVars
  dv_dummy : ∀ p ∈ dv, p.1 ∈ floats.map Prod.snd ∨ p.2 ∈ floats.map Prod.snd
  nodup : (floats.map Prod.snd).Nodup

namespace TDummies

/-- No dummy variables. -/
def none (A : TAssertion L C V) : TDummies A where
  floats := []
  dv := []
  fresh := by simp
  dv_dummy := by simp
  nodup := by simp

end TDummies

namespace TAssertion

/-- The frame of a tree proof with dummy variables `D`. -/
def extend (A : TAssertion L C V) (D : TDummies A) : TAssertion L C V where
  dv := A.dv ++ D.dv
  hyps := A.hyps ++ D.floats.map fun p => .float p.1 p.2
  concl := A.concl

@[simp] theorem extend_none (A : TAssertion L C V) : A.extend (TDummies.none A) = A := by
  simp [extend, TDummies.none]

theorem ctx_extend {A : TAssertion L C V} {D : TDummies A} {v : V} {s : C} :
    (A.extend D).ctx v s ↔ A.ctx v s ∨ (s, v) ∈ D.floats := by
  simp [ctx, extend]

theorem ctx_le_extend {A : TAssertion L C V} (D : TDummies A) (v : V) (s : C)
    (h : A.ctx v s) : (A.extend D).ctx v s :=
  ctx_extend.2 (Or.inl h)

theorem essentials_extend (A : TAssertion L C V) (D : TDummies A) :
    (A.extend D).essentials = A.essentials := by
  simp [essentials, extend, List.filterMap_append, List.filterMap_map]

/-- The context of a frame with distinct floating variables and dummies is
functional. -/
theorem functional_ctx_extend {A : TAssertion L C V} (hA : (A.floats.map Prod.snd).Nodup)
    (D : TDummies A) : Functional (A.extend D).ctx := by
  have hfresh : ∀ v s, A.ctx v s → ∀ s', (s', v) ∉ D.floats := by
    intro v s hv s' hd
    apply D.fresh _ hd
    simp only [allVars, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨_, hv, by simp [THyp.vars]⟩
  intro v s s' hs hs'
  rw [ctx_extend] at hs hs'
  rcases hs with hs | hs <;> rcases hs' with hs' | hs'
  · exact functional_ctx hA v s s' hs hs'
  · exact absurd hs' (hfresh v s hs s')
  · exact absurd hs (hfresh v s' hs' s)
  · exact (Prod.mk.inj (List.inj_on_of_nodup_map D.nodup hs hs' rfl)).1

end TAssertion

/-- A derivation of `e` from the essential hypotheses of `A` using the tree
assertions of `Γ`. Each step applies `B ∈ Γ` under a substitution `τ` that is
well sorted on `B`'s floating variables in `A`'s context. -/
inductive TDerivation (G : Grammar L C V) (Γ : Set (TAssertion L C V)) (A : TAssertion L C V) :
    TExpr L C V → Type u
  | hyp {e : TExpr L C V} (h : e ∈ A.essentials) : TDerivation G Γ A e
  | app (B : TAssertion L C V) (hB : B ∈ Γ) (τ : V → Tree L V)
      (sorted : ∀ v s, B.ctx v s → G.HasSort A.ctx (τ v) s)
      (premises : ∀ e ∈ B.essentials, TDerivation G Γ A (e.subst τ))
      (dv : B.DVSafe τ A.Disjoint) : TDerivation G Γ A (B.concl.subst τ)

/-- A CSLib tag for the tree inference system generated by `Γ`. -/
structure TSystem (G : Grammar L C V) (Γ : Set (TAssertion L C V)) : Type where

/-- A tree proof: dummy variables and a derivation of the conclusion in the
extended frame. -/
def TProof (G : Grammar L C V) (Γ : Set (TAssertion L C V)) (A : TAssertion L C V) : Type u :=
  Σ D : TDummies A, TDerivation G Γ (A.extend D) A.concl

instance (G : Grammar L C V) (Γ : Set (TAssertion L C V)) :
    InferenceSystem (TSystem G Γ) (TAssertion L C V) where
  derivation A := TProof G Γ A

/-- `A` is a theorem of the tree axiom set `Γ`. -/
def TDerivable (G : Grammar L C V) (Γ : Set (TAssertion L C V)) (A : TAssertion L C V) : Prop :=
  InferenceSystem.DerivableIn (TSystem G Γ) A

variable {G : Grammar L C V}

theorem tderivable_iff {Γ : Set (TAssertion L C V)} {A : TAssertion L C V} :
    TDerivable G Γ A ↔ ∃ D : TDummies A, Nonempty (TDerivation G Γ (A.extend D) A.concl) :=
  ⟨fun ⟨⟨D, d⟩⟩ => ⟨D, ⟨d⟩⟩, fun ⟨D, ⟨d⟩⟩ => ⟨⟨D, d⟩⟩⟩

namespace TDerivation

variable {Γ Δ : Set (TAssertion L C V)} {A : TAssertion L C V}

/-- Tree derivations use axioms monotonically. -/
def mono (h : Γ ⊆ Δ) : {e : TExpr L C V} → TDerivation G Γ A e → TDerivation G Δ A e
  | _, hyp he => hyp he
  | _, app B hB τ sorted premises dv =>
    app B (h hB) τ sorted (fun e he => (premises e he).mono h) dv

end TDerivation

theorem TDerivable.mono {Γ Δ : Set (TAssertion L C V)} (h : Γ ⊆ Δ) {A : TAssertion L C V}
    (hA : TDerivable G Γ A) : TDerivable G Δ A := by
  obtain ⟨⟨D, d⟩⟩ := hA
  exact ⟨⟨D, d.mono h⟩⟩

/-- A well-formed tree assertion of `Γ` is a theorem of `Γ`. -/
theorem TDerivable.of_mem {Γ : Set (TAssertion L C V)} {A : TAssertion L C V} (hA : A ∈ Γ)
    (wf : A.WellFormed G) : TDerivable G Γ A := by
  refine ⟨⟨TDummies.none A, ?_⟩⟩
  rw [TAssertion.extend_none]
  have d := TDerivation.app (G := G) (Γ := Γ) (A := A) A hA Tree.var
    (fun v s h => .var h)
    (fun e he => by rw [TExpr.subst_var]; exact .hyp he)
    (fun x y hxy a ha b hb => by
      simp at ha hb
      subst a b
      exact ⟨wf.dv_irrefl x y hxy, Or.inl hxy⟩)
  simpa using d

variable [DecidableEq V]

/-- The string axioms of a grammatical system: the syntax axioms and the
flattened logical axioms. -/
def axioms (G : Grammar L C V) (Γ : Set (TAssertion L C V)) : Set (Assertion C V) :=
  G.syntaxAxioms ∪ TAssertion.flatten G '' Γ

/-- The string dummies of tree dummies. -/
def TDummies.flatten {A : TAssertion L C V} (D : TDummies A) : Dummies (A.flatten G) where
  floats := D.floats
  dv := D.dv
  fresh p hp h := D.fresh p hp (TAssertion.mem_allVars_of_mem_allVars_flatten h)
  nodup := D.nodup
  dv_dummy := D.dv_dummy

theorem TAssertion.flatten_extend {A : TAssertion L C V} (D : TDummies A) :
    (A.extend D).flatten G = (A.flatten G).extend D.flatten := by
  simp [flatten, extend, Assertion.extend, TDummies.flatten, THyp.flatten, Function.comp_def]

end Grammar

end Silmaril.Logic.Metamath
