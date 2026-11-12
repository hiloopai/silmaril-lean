module

public import Silmaril.Raw.SSA.Isotope.Semantics.Model
public import Mathlib.Data.Set.Functor

/-! # Relations and typed primitive relations

Relations compose by existential quantification over an intermediate value.
The powerset comparison uses Mathlib's existing `SetM` monad.
Effects remain a separate signature and are not restricted by this model.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Semantics

structure RelationModel {τ : Type u} (D : τ → Type v) (Φ : Type w) [HasTy Φ τ] where
  eval (f : Φ) : D (instrSrc f) → D (instrTrg f) → Prop

def RelationModel.toSetModel {τ : Type u} {D : τ → Type v} {Φ : Type w}
    [HasTy Φ τ] (R : RelationModel D Φ) : InstructionModel D Φ SetM :=
  ⟨fun f a => {b | R.eval f a b}⟩

/-- Every powerset primitive interpretation also determines a primitive relation. -/
def RelationModel.ofSetModel {τ : Type u} {D : τ → Type v} {Φ : Type w}
    [HasTy Φ τ] (M : InstructionModel D Φ SetM) : RelationModel D Φ :=
  ⟨fun f a b => b ∈ (M.eval f a).run⟩

@[simp] theorem RelationModel.ofSetModel_toSetModel
    {τ : Type u} {D : τ → Type v} {Φ : Type w} [HasTy Φ τ] (R : RelationModel D Φ) :
    ofSetModel R.toSetModel = R := rfl

@[simp] theorem RelationModel.toSetModel_ofSetModel
    {τ : Type u} {D : τ → Type v} {Φ : Type w} [HasTy Φ τ]
    (M : InstructionModel D Φ SetM) : (ofSetModel M).toSetModel = M := rfl

/-- Primitive relations and powerset primitive interpretations contain the same data. -/
def RelationModel.setModelEquiv {τ : Type u} (D : τ → Type v) (Φ : Type w)
    [HasTy Φ τ] : RelationModel D Φ ≃ InstructionModel D Φ SetM where
  toFun := RelationModel.toSetModel
  invFun := RelationModel.ofSetModel
  left_inv := RelationModel.ofSetModel_toSetModel
  right_inv := RelationModel.toSetModel_ofSetModel

namespace Relation

variable {A B C E : Type u}

def id (a b : A) : Prop := b = a

def comp (r : A → B → Prop) (s : B → C → Prop) (a : A) (c : C) : Prop :=
  ∃ b, r a b ∧ s b c

@[simp] theorem id_comp (r : A → B → Prop) : comp id r = r := by
  funext a b
  exact propext (by simp [comp, id])

@[simp] theorem comp_id (r : A → B → Prop) : comp r id = r := by
  funext a b
  exact propext (by simp [comp, id])

theorem comp_assoc (r : A → B → Prop) (s : B → C → Prop) (t : C → E → Prop) :
    comp (comp r s) t = comp r (comp s t) := by
  funext a e
  apply propext
  constructor
  · rintro ⟨c, ⟨b, hab, hbc⟩, hce⟩
    exact ⟨b, hab, c, hbc, hce⟩
  · rintro ⟨b, hab, c, hbc, hce⟩
    exact ⟨c, ⟨b, hab, hbc⟩, hce⟩

/-- Finite successful relational iteration. A right value requests another step;
a left value returns. This relation makes no claim about infinite executions. -/
inductive Iterates (step : A → B ⊕ A → Prop) : A → B → Prop
  | done {a b} : step a (.inl b) → Iterates step a b
  | more {a a' b} : step a (.inr a') → Iterates step a' b → Iterates step a b

theorem Iterates.unfold {step : A → B ⊕ A → Prop} {a : A} {b : B} :
    Iterates step a b ↔ step a (.inl b) ∨ ∃ a', step a (.inr a') ∧ Iterates step a' b := by
  constructor
  · intro h
    cases h with
    | done h => exact .inl h
    | more h tail => exact .inr ⟨_, h, tail⟩
  · rintro (h | ⟨_, h, tail⟩)
    · exact .done h
    · exact .more h tail

theorem Iterates.mono {r s : A → B ⊕ A → Prop}
    (h : ∀ a x, r a x → s a x) {a : A} {b : B} : Iterates r a b → Iterates s a b := by
  intro run
  induction run with
  | done hx => exact .done (h _ _ hx)
  | more hx _ ih => exact .more (h _ _ hx) ih

/-- A relation closed under returns and recursive steps contains every finite run. -/
theorem Iterates.least {step : A → B ⊕ A → Prop} {result : A → B → Prop}
    (done : ∀ a b, step a (.inl b) → result a b)
    (more : ∀ a a' b, step a (.inr a') → result a' b → result a b)
    {a : A} {b : B} : Iterates step a b → result a b := by
  intro run
  induction run with
  | done h => exact done _ _ h
  | more h _ ih => exact more _ _ _ h ih

@[simp] theorem setM_pure_iff {a b : A} : b ∈ (pure a : SetM A).run ↔ b = a := Iff.rfl

theorem setM_bind_iff {s : SetM A} {f : A → SetM B} {b : B} :
    b ∈ (s >>= f).run ↔ ∃ a, a ∈ s.run ∧ b ∈ (f a).run := by
  change b ∈ ⋃ a ∈ s.run, (f a).run ↔ _
  simp only [Set.mem_iUnion, exists_prop]

theorem setM_map_equiv (e : A ≃ B) (s : SetM A) (b : B) :
    b ∈ (s >>= fun a => pure (e a)).run ↔ e.symm b ∈ s.run := by
  rw [setM_bind_iff]
  constructor
  · rintro ⟨a, ha, hb⟩
    rw [setM_pure_iff] at hb
    simpa only [hb, Equiv.symm_apply_apply] using ha
  · intro h
    exact ⟨e.symm b, h, setM_pure_iff.mpr (e.apply_symm_apply b).symm⟩

end Relation
end Silmaril.Isotope.Semantics
