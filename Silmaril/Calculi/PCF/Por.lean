module

public import Silmaril.Calculi.PCF.Denotation

/-! # Parallel and sequential or

Parallel or (`porFun`, defined with the model in `Silmaril.Calculi.PCF.Denotation`)
is `true` as soon as either argument is `true`, even if the other is `⊥`.
The left sequential or `orFun` is the denotation of the PCF term
`Term.seqOr = fun x:bool. fun y:bool. if x then true else y`, which inspects
its first argument first and so is `⊥` whenever that argument is. The two
agree on defined arguments and differ at `(⊥, true)`.

Parallel or is also the curried domain element
`porElem ∈ ⟦bool -> bool -> bool⟧`, the denotation of
`fun x:bool. fun y:bool. por(x, y)` in PCF+`por` (`denote_porLam`). It is
characterized by three entries of its table (`PorSpec`): a monotone function
with `p(true)(⊥) = true`, `p(⊥)(true) = true` and `p(false)(false) = false`
is parallel or (`eq_porFun_of_monotone`, `PorSpec.eq_porElem`). By
`Silmaril.Calculi.PCF.por_undefinable` no PCF term denotes it.

The notes' numbered items on these functions (Definitions 32 and 33,
Exercise 20) are restated in
`Silmaril.Courses.Cambridge.DenotationalSemantics.FullAbstraction`.
-/

@[expose] public section

namespace Silmaril.Calculi.PCF


open OmegaCompletePartialOrder Silmaril.Semantics.Domain TypedLambda Cslib.LambdaCalculus.LocallyNameless.Stlc

/-- The type `bool -> bool -> bool` of binary boolean functions. -/
abbrev Ty.bool₂ : Ty := Ty.bool ⤳ Ty.bool ⤳ Ty.bool

/-- Apply an element of `⟦bool -> bool -> bool⟧` to two arguments
(`Model.app₂` at this type). -/
noncomputable abbrev app₂ {p : Bool} (f : (model p).ty Ty.bool₂) (x y : Part Bool) :
    Part Bool :=
  Model.app₂ (M := model p) (σ := Ty.bool) (σ' := Ty.bool) (τ := Ty.bool) f x y

/-- Two elements of `⟦bool -> bool -> bool⟧` with the same values are equal. -/
theorem ext_app₂ {p : Bool} {f g : (model p).ty Ty.bool₂} (h : ∀ x y, app₂ f x y = app₂ g x y) :
    f = g :=
  Model.ext_app₂ h

/-- On defined arguments parallel or is boolean disjunction. -/
@[simp] theorem porFun_some_some (a b : Bool) :
    porFun (.some a) (.some b) = .some (a || b) := by
  cases a <;> cases b <;> simp

/-- Parallel or as a curried domain element, `por ∈ ⟦bool -> bool -> bool⟧`. -/
noncomputable def porElem {p : Bool} : (model p).ty Ty.bool₂ :=
  curry porHom

/-- `por(x)(y) = por(x, y)`. -/
theorem porElem_app {p : Bool} (x y : Part Bool) :
    app₂ (porElem (p := p)) x y = porFun x y := rfl

section SeqOr

variable {p : Bool} {Γ : Ctx Base}

/-- The PCF term `fun x:bool. fun y:bool. if x then true else y`. -/
def Term.seqOr : Term p Γ Ty.bool₂ :=
  .lam (.lam (Term.ite (.var (.succ .zero)) Term.tt Term.v0))

/-- The left sequential or, `or(x, y) = if(x, true, y)`. -/
noncomputable def orFun (x y : Part Bool) : Part Bool := condFun x (.some true) y

/-- `or` is the denotation of `Term.seqOr`. -/
theorem denote_seqOr (ρ : (model p).Env Γ) (x y : Part Bool) :
    app₂ (denote (Term.seqOr : Term p Γ _) ρ) x y = orFun x y := rfl

/-- `or(true, y) = true`. -/
@[simp] theorem orFun_true_left (y : Part Bool) : orFun (.some true) y = .some true :=
  condFun_true _ _

/-- `or(false, y) = y`. -/
@[simp] theorem orFun_false_left (y : Part Bool) : orFun (.some false) y = y :=
  condFun_false _ _

/-- `or(⊥, y) = ⊥`. -/
@[simp] theorem orFun_none_left (y : Part Bool) : orFun .none y = .none :=
  condFun_none _ _

/-- Both functions are boolean disjunction on defined arguments. -/
theorem orFun_some_some (a b : Bool) : orFun (.some a) (.some b) = porFun (.some a) (.some b) := by
  cases a <;> cases b <;> simp

/-- The two functions differ at `(⊥, true)`: `or(⊥, true) = ⊥` but
`por(⊥, true) = true`. -/
theorem orFun_ne_porFun : orFun .none (.some true) ≠ porFun .none (.some true) := by
  simp only [orFun_none_left, porFun_true_right]
  exact fun h => Part.some_ne_none true h.symm

end SeqOr

section Characterization

/-- A monotone `q : 𝔹⊥ → 𝔹⊥ → 𝔹⊥` with `q(true)(⊥) = true`,
`q(⊥)(true) = true` and `q(false)(false) = false` is parallel or. -/
theorem eq_porFun_of_monotone {q : Part Bool → Part Bool → Part Bool}
    (hq : Monotone q) (hq' : ∀ x, Monotone (q x))
    (htb : q (.some true) .none = .some true) (hbt : q .none (.some true) = .some true)
    (hff : q (.some false) (.some false) = .some false) (x y : Part Bool) :
    q x y = porFun x y := by
  -- Monotonicity in both arguments at once.
  have mono : ∀ {x x' y y'}, x ≤ x' → y ≤ y' → q x y ≤ q x' y' := fun hx hy =>
    (hq hx _).trans (hq' _ hy)
  -- A value below both `true` and `false` is `⊥`.
  have below : ∀ {z : Part Bool}, z ≤ .some true → z ≤ .some false → z = .none := by
    intro z h₁ h₂
    rcases Flat.le_iff_eq_none_or_eq.1 h₁ with h | h
    · exact h
    · rw [h] at h₂
      exact absurd (Flat.eq_of_some_le h₂) (by simp)
  have ht_ : ∀ y, q (.some true) y = .some true := fun y =>
    Flat.eq_of_some_le (htb.symm.le.trans (hq' _ bot_le))
  have h_t : ∀ x, q x (.some true) = .some true := fun x =>
    Flat.eq_of_some_le (hbt.symm.le.trans (hq bot_le _))
  have hf_ : q (.some false) .none = .none :=
    below ((mono le_rfl bot_le).trans (h_t _).le) ((mono le_rfl bot_le).trans hff.le)
  have h_f : q .none (.some false) = .none :=
    below ((mono bot_le le_rfl).trans (ht_ _).le) ((mono bot_le le_rfl).trans hff.le)
  have h__ : q .none .none = .none :=
    below ((mono bot_le bot_le).trans (ht_ (.some true)).le) ((mono bot_le bot_le).trans hff.le)
  rcases part_bool_cases x with rfl | rfl | rfl <;>
    rcases part_bool_cases y with rfl | rfl | rfl <;> simp [*]

/-- The three entries of the table of parallel or that characterize it:
`f(true)(⊥) = true`, `f(⊥)(true) = true` and `f(false)(false) = false`. -/
def PorSpec {p : Bool} (f : (model p).ty Ty.bool₂) : Prop :=
  app₂ f (.some true) .none = .some true ∧ app₂ f .none (.some true) = .some true ∧
    app₂ f (.some false) (.some false) = .some false

/-- Parallel or satisfies its specification. -/
theorem porSpec_porElem {p : Bool} : PorSpec (porElem (p := p)) :=
  ⟨porFun_true_left _, porFun_true_right _, porFun_false_false⟩

/-- An element of `⟦bool -> bool -> bool⟧` satisfying `PorSpec` is parallel
or, since continuous functions are monotone. -/
theorem PorSpec.eq_porElem {p : Bool} {f : (model p).ty Ty.bool₂} (h : PorSpec f) :
    f = porElem :=
  ext_app₂ <| eq_porFun_of_monotone (q := app₂ f)
    (fun _ _ h y => (Model.fn f).monotone h y) (fun x => (Model.fn (Model.app f x)).monotone)
    h.1 h.2.1 h.2.2

/-- `PorSpec f` holds exactly when `f` is parallel or. -/
theorem porSpec_iff {p : Bool} {f : (model p).ty Ty.bool₂} : PorSpec f ↔ f = porElem :=
  ⟨PorSpec.eq_porElem, fun h => h ▸ porSpec_porElem⟩

end Characterization

section PorTerm

variable {Γ : Ctx Base}

/-- The PCF+`por` term `fun x:bool. fun y:bool. por(x, y)`. -/
def Term.porLam : Term true Γ Ty.bool₂ :=
  .lam (.lam (Term.por (.var (.succ .zero)) Term.v0))

/-- `⟦fun x:bool. fun y:bool. por(x, y)⟧ = por`: the curried form of
`⟦por⟧ = por`, so parallel or is definable in PCF+`por`. The uncurried
equation holds by definition (`denote_op_por`). -/
theorem denote_porLam (ρ : (model true).Env Γ) :
    denote (Term.porLam : Term true Γ _) ρ = porElem :=
  ext_app₂ fun _ _ => rfl

end PorTerm

end Silmaril.Calculi.PCF
