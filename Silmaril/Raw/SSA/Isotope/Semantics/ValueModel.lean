module

public import Silmaril.Raw.SSA.Isotope.Semantics.Model
public import Silmaril.SSA.Isotope.LambdaSSA.Defs
public import Silmaril.Semantics.ElgotMonads.Thms

/-!
# Typed values represented in the operational carrier

Atoms retain their type tag and interpreted value. Products, sums, and unit use
the corresponding runtime constructors. Primitive compatibility records exact
finite outcomes in the state-and-powerset model, independently of effect labels.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Semantics

variable {κ : Type u} (F : κ → Type u)

/-- Canonical representation of a typed value in the shared runtime syntax. -/
def encodeValue : (A : Ty κ) → Ty.denote F A → Value (Sigma F)
  | .base a, x => .atom ⟨a, x⟩
  | .product A B, (a, b) => .pair (encodeValue A a) (encodeValue B b)
  | .unit, _ => .unit
  | .coprod A _, .inl a => .inl (encodeValue A a)
  | .coprod _ B, .inr b => .inr (encodeValue B b)
  | .empty, x => x.elim

/-- Encoding loses no value information at any fixed type. -/
theorem encodeValue_injective (A : Ty κ) : Function.Injective (encodeValue F A) := by
  induction A with
  | base a => intro x y h; cases h; rfl
  | unit => intro x y _; cases x; cases y; rfl
  | empty => intro x; exact x.elim
  | product A B ihA ihB =>
      rintro ⟨a, b⟩ ⟨a', b'⟩ h
      obtain ⟨ha, hb⟩ := Value.pair.inj h
      cases ihA ha
      cases ihB hb
      rfl
  | coprod A B ihA ihB =>
      intro x y h
      cases x <;> cases y
      · exact congrArg Sum.inl (ihA (Value.inl.inj h))
      · cases h
      · cases h
      · exact congrArg Sum.inr (ihB (Value.inr.inj h))

variable {Φ : Type v} [HasTy Φ (Ty κ)] {σ : Type u}

/-- The finite atomic relation induced by an actual typed instruction model. -/
def InstructionModel.operational
    (M : InstructionModel (Ty.denote F) Φ (StateT σ SetM))
    (f : Φ) (input : Value (Sigma F)) (s : σ) (output : Value (Sigma F)) (s' : σ) : Prop :=
  ∃ (a : Ty.denote F (instrSrc f)) (b : Ty.denote F (instrTrg f)),
    input = encodeValue F _ a ∧ output = encodeValue F _ b ∧ (b, s') ∈ (M.eval f a s).run

/-- An externally supplied primitive relation agrees on all well-typed inputs. -/
def InstructionModel.Compatible
    (M : InstructionModel (Ty.denote F) Φ (StateT σ SetM))
    (instr : Φ → Value (Sigma F) → σ → Value (Sigma F) → σ → Prop) : Prop :=
  ∀ f (a : Ty.denote F (instrSrc f)) s output s',
    instr f (encodeValue F _ a) s output s' ↔
      ∃ b, output = encodeValue F _ b ∧ (b, s') ∈ (M.eval f a s).run

theorem InstructionModel.operational_compatible
    (M : InstructionModel (Ty.denote F) Φ (StateT σ SetM)) :
    M.Compatible F (M.operational F) := by
  intro f a s output s'
  constructor
  · rintro ⟨a', b, ha, hb, run⟩
    cases encodeValue_injective F _ ha
    exact ⟨b, hb, run⟩
  · rintro ⟨b, hb, run⟩
    exact ⟨a, b, rfl, hb, run⟩

namespace Stateful

variable {A B : Type u}

/-- Successful membership after stateful bind exposes the intermediate value and state. -/
theorem mem_bind (x : StateT σ SetM A) (f : A → StateT σ SetM B) (s s' : σ) (b : B) :
    (b, s') ∈ ((x >>= f) s).run ↔
      ∃ a s₁, (a, s₁) ∈ (x s).run ∧ (b, s') ∈ (f a s₁).run := by
  change (b, s') ∈ ((x s) >>= fun p => f p.1 p.2).run ↔ _
  rw [Elgot.Nondet.mem_bind_iff]
  constructor
  · rintro ⟨⟨a, s₁⟩, hx, hf⟩
    exact ⟨a, s₁, hx, hf⟩
  · rintro ⟨a, s₁, hx, hf⟩
    exact ⟨(a, s₁), hx, hf⟩

@[simp] theorem mem_pure (a b : A) (s s' : σ) :
    (b, s') ∈ ((pure a : StateT σ SetM A) s).run ↔ b = a ∧ s' = s := by
  change (b, s') = (a, s) ↔ _
  simp only [Prod.mk.injEq]

/-- Finite stateful iterations, exposed from the existing complete Elgot instance. -/
inductive Iterates (f : A → StateT σ SetM (B ⊕ A)) : A → σ → B → σ → Prop where
  | done {a b s s'} : (.inl b, s') ∈ (f a s).run → Iterates f a s b s'
  | more {a a' b s s₁ s₂} : (.inr a', s₁) ∈ (f a s).run →
      Iterates f a' s₁ b s₂ → Iterates f a s b s₂

theorem mem_body_inl (f : A → StateT σ SetM (B ⊕ A)) (a : A) (s : σ) (b : B) (s' : σ) :
    Sum.inl (b, s') ∈ (Elgot.StateT.body f (a, s)).run ↔ (.inl b, s') ∈ (f a s).run := by
  simp only [Elgot.StateT.body, Elgot.Nondet.mem_bind_iff, Function.comp_apply,
    Elgot.Nondet.mem_pure_iff]
  constructor
  · rintro ⟨⟨x, t⟩, h, eq⟩
    cases x with
    | inl x => cases eq; exact h
    | inr x => cases eq
  · intro h
    exact ⟨(.inl b, s'), h, rfl⟩

theorem mem_body_inr (f : A → StateT σ SetM (B ⊕ A)) (a : A) (s : σ) (a' : A) (s' : σ) :
    Sum.inr (a', s') ∈ (Elgot.StateT.body f (a, s)).run ↔ (.inr a', s') ∈ (f a s).run := by
  simp only [Elgot.StateT.body, Elgot.Nondet.mem_bind_iff, Function.comp_apply,
    Elgot.Nondet.mem_pure_iff]
  constructor
  · rintro ⟨⟨x, t⟩, h, eq⟩
    cases x with
    | inl x => cases eq
    | inr x => cases eq; exact h
  · intro h
    exact ⟨(.inr a', s'), h, rfl⟩

theorem Iterates.of_runs {f : A → StateT σ SetM (B ⊕ A)} {a : A × σ} {b : B × σ}
    (h : Elgot.Nondet.Runs (Elgot.StateT.body f) a b) : Iterates f a.1 a.2 b.1 b.2 := by
  induction h with
  | done step => exact .done ((mem_body_inl ..).mp step)
  | more step tail ih => exact .more ((mem_body_inr ..).mp step) ih

theorem Iterates.runs {f : A → StateT σ SetM (B ⊕ A)} {a : A} {b : B} {s s' : σ}
    (h : Iterates f a s b s') : Elgot.Nondet.Runs (Elgot.StateT.body f) (a, s) (b, s') := by
  induction h with
  | done step => exact .done ((mem_body_inl ..).mpr step)
  | more step tail ih => exact .more ((mem_body_inr ..).mpr step) ih

/-- The state transformer retains exactly the successful finite loop paths. -/
theorem mem_iter (f : A → StateT σ SetM (B ⊕ A)) (a : A) (b : B) (s s' : σ) :
    (b, s') ∈ (Elgot.iter f a s).run ↔ Iterates f a s b s' := by
  change Elgot.Nondet.Runs (Elgot.StateT.body f) (a, s) (b, s') ↔ _
  exact ⟨Iterates.of_runs, Iterates.runs⟩

end Stateful
end Silmaril.Isotope.Semantics
