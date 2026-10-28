module

public import Mathlib.Algebra.Group.Int.Even
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Int.Defs

/-! # §16 Inference-based program analysis (notes pp. 29–30; slides pp. 105–107)

"An inference system specifies judgements of the form `Γ ⊢ e : φ` where `φ` is a
program property and `Γ` is a set of assumptions about free variables of `e`"
(notes p. 29). The notes' example has properties `φ ::= odd | even | φ → φ′`
and the rules (VAR), (LAM), (APP) over `e ::= x | λx.e | e₁ e₂`. Constants and
operators (`2`, `+`, `×`) are free variables with assumptions in `Γ`.

Conjunctions `φ ∧ φ′`, with introduction and elimination rules, are the
"more elaborate property" the notes ask for (p. 30).

Safety: every derivation of `Γ ⊢ e : φ` denotes, in an environment satisfying
`Γ`, a value with property `φ` (`Derives.sound`). A derivation denotes the
program it types, read at the types its properties erase to (`Prp.Sem`).
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers.InferenceBased

/-- Terms of the λ-calculus. -/
inductive Term where
  | var (x : String)
  | lam (x : String) (e : Term)
  | app (f a : Term)

/-- Properties: `odd`, `even`, `φ → φ′` and `φ ∧ φ′`. -/
inductive Prp where
  | odd | even
  | arrow (a b : Prp)
  | and (a b : Prp)

namespace Prp

/-- The type of values a property is about: integers for `odd`/`even`,
functions for `→`, pairs for `∧`. -/
def Sem : Prp → Type
  | odd | even => ℤ
  | arrow a b => a.Sem → b.Sem
  | and a b => a.Sem × b.Sem

/-- When a value has a property. -/
def Holds : (φ : Prp) → φ.Sem → Prop
  | odd, n => @Odd ℤ _ n
  | even, n => @Even ℤ _ n
  | arrow a b, f => ∀ v, a.Holds v → b.Holds (f v)
  | and a b, p => a.Holds p.1 ∧ b.Holds p.2

end Prp

/-- Assumptions `x : φ`, most recent first; `Γ[x : φ]` is `(x, φ) :: Γ`. -/
abbrev Ctx := List (String × Prp)

/-- `x : φ` is the first assumption about `x` in `Γ`. -/
inductive Lookup : Ctx → String → Prp → Type where
  | here {Γ x φ} : Lookup ((x, φ) :: Γ) x φ
  | there {Γ x y φ ψ} : x ≠ y → Lookup Γ x φ → Lookup ((y, ψ) :: Γ) x φ

/-- Environments: a value for each assumption. -/
inductive Env : Ctx → Type where
  | nil : Env []
  | cons {Γ x φ} : φ.Sem → Env Γ → Env ((x, φ) :: Γ)

/-- Every value in the environment has its assumed property. -/
def Env.Holds : {Γ : Ctx} → Env Γ → Prop
  | [], .nil => True
  | (_, φ) :: _, .cons v ρ => φ.Holds v ∧ ρ.Holds

/-- Look up a variable. -/
def Lookup.get : {Γ : Ctx} → {x : String} → {φ : Prp} → Lookup Γ x φ → Env Γ → φ.Sem
  | _, _, _, .here, .cons v _ => v
  | _, _, _, .there _ h, .cons _ ρ => h.get ρ

/-- The rules (VAR), (LAM), (APP) of notes p. 29, and conjunction. -/
inductive Derives : Ctx → Term → Prp → Type where
  | var {Γ x φ} : Lookup Γ x φ → Derives Γ (.var x) φ
  | lam {Γ x e φ ψ} : Derives ((x, φ) :: Γ) e ψ → Derives Γ (.lam x e) (.arrow φ ψ)
  | app {Γ f a φ ψ} : Derives Γ f (.arrow φ ψ) → Derives Γ a φ → Derives Γ (.app f a) ψ
  | andI {Γ e φ ψ} : Derives Γ e φ → Derives Γ e ψ → Derives Γ e (.and φ ψ)
  | andL {Γ e φ ψ} : Derives Γ e (.and φ ψ) → Derives Γ e φ
  | andR {Γ e φ ψ} : Derives Γ e (.and φ ψ) → Derives Γ e ψ

/-- The value a derivation denotes. -/
def Derives.denote : {Γ : Ctx} → {e : Term} → {φ : Prp} → Derives Γ e φ → Env Γ → φ.Sem
  | _, _, _, .var h, ρ => h.get ρ
  | _, _, _, .lam d, ρ => fun v => d.denote (.cons v ρ)
  | _, _, _, .app d₁ d₂, ρ => d₁.denote ρ (d₂.denote ρ)
  | _, _, _, .andI d₁ d₂, ρ => (d₁.denote ρ, d₂.denote ρ)
  | _, _, _, .andL d, ρ => (d.denote ρ).1
  | _, _, _, .andR d, ρ => (d.denote ρ).2

/-- Safety: `(Γ ⊢ e : φ) ⇒ ⟦e⟧ ∈ ⟦φ⟧` (notes p. 29). -/
theorem Lookup.sound : {Γ : Ctx} → {x : String} → {φ : Prp} → (h : Lookup Γ x φ) →
    (ρ : Env Γ) → ρ.Holds → φ.Holds (h.get ρ)
  | _, _, _, .here, .cons _ _, hρ => hρ.1
  | _, _, _, .there _ h, .cons _ ρ, hρ => h.sound ρ hρ.2

theorem Derives.sound {Γ : Ctx} {e : Term} {φ : Prp} (d : Derives Γ e φ) {ρ : Env Γ}
    (hρ : ρ.Holds) : φ.Holds (d.denote ρ) := by
  induction d with
  | var h => exact h.sound ρ hρ
  | lam d ih => intro v hv; exact ih (ρ := .cons v ρ) ⟨hv, hρ⟩
  | app d₁ d₂ ih₁ ih₂ => exact ih₁ hρ _ (ih₂ hρ)
  | andI d₁ d₂ ih₁ ih₂ => exact ⟨ih₁ hρ, ih₂ hρ⟩
  | andL d ih => exact (ih hρ).1
  | andR d ih => exact (ih hρ).2

/-! ## A syntactic characterisation of derivability

Used to refute derivations: `Ok Γ e χ` says the non-conjunctive property `χ` is
derivable by the structural rules, and every property derivable for `e` is a
conjunction of such leaves (`Derives.ok`). -/

/-- The first assumption about `x`. -/
def find : Ctx → String → Option Prp
  | [], _ => none
  | (y, φ) :: Γ, x => if x = y then some φ else find Γ x

/-- `χ` is a leaf of the conjunction tree `φ`. -/
def Leaf (χ : Prp) : Prp → Prop
  | .odd => χ = .odd
  | .even => χ = .even
  | .arrow a b => χ = .arrow a b
  | .and a b => Leaf χ a ∨ Leaf χ b

theorem exists_leaf : ∀ φ : Prp, ∃ χ, Leaf χ φ
  | .odd => ⟨.odd, rfl⟩
  | .even => ⟨.even, rfl⟩
  | .arrow a b => ⟨.arrow a b, rfl⟩
  | .and a _ => let ⟨χ, h⟩ := exists_leaf a; ⟨χ, Or.inl h⟩

/-- Structural derivability of a leaf property. -/
def Ok : Ctx → Term → Prp → Prop
  | Γ, .var x, χ => ∃ φ, find Γ x = some φ ∧ Leaf χ φ
  | Γ, .lam x e, χ => ∃ φ ψ, χ = .arrow φ ψ ∧ ∀ χ', Leaf χ' ψ → Ok ((x, φ) :: Γ) e χ'
  | Γ, .app f a, χ => ∃ φ ψ, Ok Γ f (.arrow φ ψ) ∧ (∀ χ', Leaf χ' φ → Ok Γ a χ') ∧ Leaf χ ψ

theorem Lookup.find_eq : {Γ : Ctx} → {x : String} → {φ : Prp} → Lookup Γ x φ →
    find Γ x = some φ
  | _, _, _, .here => by simp [find]
  | _, _, _, .there hne h => by simp [find, hne, h.find_eq]

theorem Derives.ok {Γ : Ctx} {e : Term} {φ : Prp} (d : Derives Γ e φ) :
    ∀ χ, Leaf χ φ → Ok Γ e χ := by
  induction d with
  | var h => intro χ hχ; exact ⟨_, h.find_eq, hχ⟩
  | lam d ih => intro χ hχ; exact ⟨_, _, hχ, ih⟩
  | app d₁ d₂ ih₁ ih₂ => intro χ hχ; exact ⟨_, _, ih₁ (.arrow _ _) rfl, ih₂, hχ⟩
  | andI d₁ d₂ ih₁ ih₂ => intro χ hχ; exact hχ.elim (ih₁ χ) (ih₂ χ)
  | andL d ih => intro χ hχ; exact ih χ (Or.inl hχ)
  | andR d ih => intro χ hχ; exact ih χ (Or.inr hχ)

/-! ## The notes' examples (p. 30) -/

/-- `e₁ + e₂` and `e₁ × e₂`, with `+` and `×` as curried free variables. -/
def plus (a b : Term) : Term := .app (.app (.var "+") a) b
def times (a b : Term) : Term := .app (.app (.var "×") a) b

/-- `Γ = {2 : even, + : even → even → even, × : even → odd → even}`. -/
def Γ₀ : Ctx :=
  [("2", .even), ("+", .arrow .even (.arrow .even .even)), ("×", .arrow .even (.arrow .odd .even))]

/-- `Γ ⊢ λx.λy.2 × x + y : odd → even → even`. -/
theorem example₁ :
    Nonempty (Derives Γ₀ (.lam "x" (.lam "y" (plus (times (.var "2") (.var "x")) (.var "y"))))
      (.arrow .odd (.arrow .even .even))) :=
  ⟨.lam (.lam (.app
    (.app (.var (.there (by simp) (.there (by simp) (.there (by simp) .here))))
      (.app (.app (.var (.there (by simp) (.there (by simp) (.there (by simp)
          (.there (by simp) .here)))))
        (.var (.there (by simp) (.there (by simp) .here))))
        (.var (.there (by simp) .here))))
    (.var .here)))⟩

/-- `λx.λy.2 × x + 3 × y : even → even → even` is not derivable from `Γ` extended
with `3 : odd` alone: `×` would need a second assumption (notes p. 30). -/
theorem example₂_not_derivable :
    IsEmpty (Derives (("3", .odd) :: Γ₀)
      (.lam "x" (.lam "y" (plus (times (.var "2") (.var "x")) (times (.var "3") (.var "y")))))
      (.arrow .even (.arrow .even .even))) := by
  refine ⟨fun d => ?_⟩
  obtain ⟨φ₁, ψ₁, h₁, h⟩ := d.ok (.arrow .even (.arrow .even .even)) rfl
  cases h₁
  obtain ⟨φ₂, ψ₂, h₂, h⟩ := h (.arrow .even .even) rfl
  cases h₂
  obtain ⟨φ₃, ψ₃, -, hB, -⟩ := h .even rfl
  obtain ⟨χ, hχ⟩ := exists_leaf φ₃
  obtain ⟨φ₄, ψ₄, hf, -, -⟩ := hB χ hχ
  obtain ⟨φ₅, ψ₅, hx, h3, -⟩ := hf
  obtain ⟨p, hp, hlp⟩ := hx
  simp [find, Γ₀] at hp
  subst hp
  cases hlp
  obtain ⟨q, hq, hlq⟩ := h3 .even rfl
  simp [find] at hq
  subst hq
  cases hlq

/-- The conjunctive assumption for `×` of notes p. 30. -/
def timesConj : Prp :=
  .and (.and (.arrow .even (.arrow .even .even)) (.arrow .even (.arrow .odd .even)))
    (.and (.arrow .odd (.arrow .even .even)) (.arrow .odd (.arrow .odd .odd)))

/-- With the conjunctive assumption, the second example is derivable. -/
theorem example₂_derivable :
    Nonempty (Derives [("2", .even), ("3", .odd), ("+", .arrow .even (.arrow .even .even)),
        ("×", timesConj)]
      (.lam "x" (.lam "y" (plus (times (.var "2") (.var "x")) (times (.var "3") (.var "y")))))
      (.arrow .even (.arrow .even .even))) :=
  ⟨.lam (.lam (.app
    (.app (.var (.there (by simp) (.there (by simp) (.there (by simp) (.there (by simp) .here)))))
      (.app (.app (.andL (.andL (.var (.there (by simp) (.there (by simp) (.there (by simp)
          (.there (by simp) (.there (by simp) .here))))))))
        (.var (.there (by simp) (.there (by simp) .here))))
        (.var (.there (by simp) .here))))
    (.app (.app (.andL (.andR (.var (.there (by simp) (.there (by simp) (.there (by simp)
          (.there (by simp) (.there (by simp) .here))))))))
        (.var (.there (by simp) (.there (by simp) (.there (by simp) .here)))))
      (.var .here))))⟩

end Silmaril.Courses.Cambridge.OptimisingCompilers.InferenceBased
