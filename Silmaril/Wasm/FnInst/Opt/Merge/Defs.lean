module

public import Silmaril.Wasm.FnInst.Opt.Seg.Defs
public import Silmaril.Logic.Inst.Builders.Core.Defs
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.CategoryTheory.Category.Preorder

@[expose] public section

/-! # wasm-merge as amalgamation: a sketch over named contexts

`wasm-merge` links modules by matching the imports of one with the exports of another. At the
level of signatures this is a pushout: two function contexts `X₁`, `X₂` (sets of function
names) glued along their shared names `X₀`. Here signatures are sets of names ordered by
inclusion (a preorder category, where the pushout of `X₀ ⊆ X₁`, `X₀ ⊆ X₂` is `X₁ ∪ X₂`).
Models of `X` are name-indexed environments that leave every name outside `X` unspecified
(`NModel X`); the reduct along `X ⊆ Y` forgets the names outside `X`.

* `NModel.amalgam`: two models that agree on the shared names glue to a model of the union;
* `NModel.amalgam_reduct_left/right`, `NModel.amalgam_unique` (in `Merge.Thms`): it is the
  unique model with both reducts, when `X₀ = X₁ ∩ X₂` (wasm-merge renames clashing names, so
  the shared names are exactly the matched imports/exports);
* `namedInst`: the observational institution over this signature category
  (`Silmaril.Inst.Plain.ofSat`: sentences are predicates of models, translated by reduct);
* `merge_sat`: generic merge correctness: a sentence of each side satisfied by its model is
  satisfied, translated, by the amalgam.

Not done (a sketch): relating this to a syntactic merge of modules of the fragment. The model
of each side in the merged world answers its imports with the other side's functions; that is
a fixpoint of the two semantics, not given by the amalgam alone.
-/

namespace Silmaril.Wasm.FnInst.Opt.Merge

open Silmaril.Wasm.FnInst.Opt CategoryTheory
open scoped Classical

/-- Name-indexed environments: the abstract semantic function of every function name. -/
def NEnv : Type := String → List Val → (ℕ → Val) → Set Ans

/-- Forget the names outside `X`. -/
noncomputable def NEnv.restrict (X : Set String) (E : NEnv) : NEnv :=
  fun f => if f ∈ X then E f else Env.top 0

/-- Models of a named context `X`: environments unspecified outside `X`. -/
abbrev NModel (X : Set String) : Type := {E : NEnv // ∀ f, f ∉ X → E f = Env.top 0}

/-- The reduct along an inclusion. -/
noncomputable def NModel.reduct {X Y : Set String} (_ : X ⟶ Y) (M : NModel Y) : NModel X :=
  ⟨M.1.restrict X, fun f hf => by
    unfold NEnv.restrict
    rw [ite_eq_right hf]⟩

theorem NModel.reduct_val {X Y : Set String} (h : X ⟶ Y) (M : NModel Y) (f : String) :
    (NModel.reduct h M).1 f = if f ∈ X then M.1 f else Env.top 0 := by
  show (if f ∈ X then M.1 f else Env.top 0) = _
  congr

theorem NModel.reduct_id {X : Set String} (M : NModel X) : NModel.reduct (𝟙 X) M = M := by
  apply Subtype.ext
  funext f
  rw [NModel.reduct_val]
  by_cases hf : f ∈ X
  · rw [ite_eq_left hf]
  · rw [ite_eq_right hf, M.2 f hf]

theorem NModel.reduct_comp {X Y Z : Set String} (σ : X ⟶ Y) (τ : Y ⟶ Z) (M : NModel Z) :
    NModel.reduct (σ ≫ τ) M = NModel.reduct σ (NModel.reduct τ M) := by
  apply Subtype.ext
  funext f
  rw [NModel.reduct_val, NModel.reduct_val, NModel.reduct_val]
  by_cases hf : f ∈ X
  · rw [ite_eq_left hf, ite_eq_left hf, ite_eq_left (leOfHom σ hf)]
  · rw [ite_eq_right hf, ite_eq_right hf]

/-- The named-context institution: sentences are properties of models (an observational
semantics), translated along inclusions by the reduct. -/
noncomputable def namedPlain : Silmaril.Inst.Plain.{0, 0, 0, 0} (Set String) :=
  Silmaril.Inst.Plain.ofSat NModel (fun σ M => NModel.reduct σ M)
    (fun _ M => NModel.reduct_id M) (fun σ τ M => NModel.reduct_comp σ τ M)

/-- **The named-context institution** (`Silmaril.Inst` facade). -/
noncomputable abbrev namedInst : Silmaril.Inst.Institution.{0, 0, 0, 0, 0} := namedPlain.toInst

/-- The amalgam of two models: the left one on its names, the right one elsewhere. -/
noncomputable def NModel.amalgam {X₁ X₂ : Set String} (M₁ : NModel X₁) (M₂ : NModel X₂) :
    NModel (X₁ ∪ X₂) := by
  refine ⟨fun f => if f ∈ X₁ then M₁.1 f else M₂.1 f, fun f hf => ?_⟩
  have h₁ : f ∉ X₁ := fun h => hf (Or.inl h)
  have h₂ : f ∉ X₂ := fun h => hf (Or.inr h)
  show (if f ∈ X₁ then M₁.1 f else M₂.1 f) = _
  rw [ite_eq_right h₁, M₂.2 f h₂]

/-- The inclusions of a pushout square of named contexts. -/
def inl (X₁ X₂ : Set String) : X₁ ⟶ X₁ ∪ X₂ := homOfLE Set.subset_union_left
def inr (X₁ X₂ : Set String) : X₂ ⟶ X₁ ∪ X₂ := homOfLE Set.subset_union_right

end Silmaril.Wasm.FnInst.Opt.Merge
