module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Int.Basic

/-! # Exercise sheet 4, question 4 (matrix-size inference)

Source: `cam-optcomp-2025-exercise-sheet-4` in `references.bib`, question 4.


Answer: `Derives`. `+` and `−` need equal sizes; `×` needs the inner sizes to
agree, `Γ ⊢ e₁ : m × n` and `Γ ⊢ e₂ : n × p` give `Γ ⊢ e₁ × e₂ : m × p`; and
transposition swaps the sizes. Sizes are unique (`Derives.unique`), and the
analysis is safe: a derivable expression evaluates, without a size mismatch, to a
matrix of the derived size (`Derives.eval_isSome`).
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers.Exercises.S4Q4

/-- Matrix expressions. -/
inductive MExpr where
  | var (A : String)
  | add (a b : MExpr)
  | sub (a b : MExpr)
  | mul (a b : MExpr)
  | transpose (a : MExpr)

/-- Contexts: the size of each matrix variable. -/
abbrev Ctx := String → Option (ℕ × ℕ)

/-- The size-inference rules. -/
inductive Derives (Γ : Ctx) : MExpr → ℕ × ℕ → Prop where
  | var {A s} : Γ A = some s → Derives Γ (.var A) s
  | add {a b s} : Derives Γ a s → Derives Γ b s → Derives Γ (.add a b) s
  | sub {a b s} : Derives Γ a s → Derives Γ b s → Derives Γ (.sub a b) s
  | mul {a b m n p} : Derives Γ a (m, n) → Derives Γ b (n, p) → Derives Γ (.mul a b) (m, p)
  | transpose {a m n} : Derives Γ a (m, n) → Derives Γ (.transpose a) (n, m)

/-- Sizes are unique. -/
theorem Derives.unique {Γ : Ctx} {e : MExpr} {s s' : ℕ × ℕ} (h : Derives Γ e s)
    (h' : Derives Γ e s') : s = s' := by
  induction h generalizing s' with
  | var hA => cases h' with | var hA' => rw [hA] at hA'; exact Option.some.inj hA'
  | add _ _ iha _ => cases h' with | add ha' _ => exact iha ha'
  | sub _ _ iha _ => cases h' with | sub ha' _ => exact iha ha'
  | mul _ _ iha ihb =>
    cases h' with
    | mul ha' hb' =>
      have h₁ := iha ha'
      have h₂ := ihb hb'
      simp only [Prod.mk.injEq] at h₁ h₂ ⊢
      exact ⟨h₁.1, h₂.2⟩
  | transpose _ iha =>
    cases h' with
    | transpose ha' =>
      have h₁ := iha ha'
      simp only [Prod.mk.injEq] at h₁ ⊢
      exact ⟨h₁.2, h₁.1⟩

/-- A sized matrix value. -/
abbrev SMat := Σ mn : ℕ × ℕ, Matrix (Fin mn.1) (Fin mn.2) ℤ

/-- Evaluation, failing on a size mismatch. -/
def eval (ρ : String → Option SMat) : MExpr → Option SMat
  | .var A => ρ A
  | .add a b => do
    let ⟨s, x⟩ ← eval ρ a
    let ⟨s', y⟩ ← eval ρ b
    if h : s' = s then pure ⟨s, x + h ▸ y⟩ else none
  | .sub a b => do
    let ⟨s, x⟩ ← eval ρ a
    let ⟨s', y⟩ ← eval ρ b
    if h : s' = s then pure ⟨s, x - h ▸ y⟩ else none
  | .mul a b => do
    let ⟨(m, n), x⟩ ← eval ρ a
    let ⟨(n', p), y⟩ ← eval ρ b
    if h : n' = n then pure ⟨(m, p), x * (h ▸ y : Matrix (Fin n) (Fin p) ℤ)⟩ else none
  | .transpose a => do
    let ⟨(m, n), x⟩ ← eval ρ a
    pure ⟨(n, m), x.transpose⟩

/-- Safety: in an environment matching `Γ`, a derivable expression evaluates to
a matrix of the derived size. -/
theorem Derives.eval_isSome {Γ : Ctx} {ρ : String → Option SMat}
    (hρ : ∀ A s, Γ A = some s → ∃ x, ρ A = some ⟨s, x⟩) {e : MExpr} {s : ℕ × ℕ}
    (h : Derives Γ e s) : ∃ x, eval ρ e = some ⟨s, x⟩ := by
  induction h with
  | var hA => obtain ⟨x, hx⟩ := hρ _ _ hA; exact ⟨x, hx⟩
  | add _ _ iha ihb =>
    obtain ⟨x, hx⟩ := iha
    obtain ⟨y, hy⟩ := ihb
    simp [eval, hx, hy]
  | sub _ _ iha ihb =>
    obtain ⟨x, hx⟩ := iha
    obtain ⟨y, hy⟩ := ihb
    simp [eval, hx, hy]
  | mul _ _ iha ihb =>
    obtain ⟨x, hx⟩ := iha
    obtain ⟨y, hy⟩ := ihb
    simp [eval, hx, hy]
  | transpose _ iha =>
    obtain ⟨x, hx⟩ := iha
    simp [eval, hx]

/-- The sheet's context `A : 4 × 2, B : 2 × 3`. -/
def Γ₀ : Ctx := fun x => if x = "A" then some (4, 2) else if x = "B" then some (2, 3) else none

/-- `A : 4 × 2, B : 2 × 3 ⊢ A × B : 4 × 3`. -/
theorem example_mul : Derives Γ₀ (.mul (.var "A") (.var "B")) (4, 3) :=
  .mul (n := 2) (.var (by simp [Γ₀])) (.var (by simp [Γ₀]))

/-- `A + B` is invalid. -/
theorem example_add : ∀ s, ¬ Derives Γ₀ (.add (.var "A") (.var "B")) s := by
  intro s h
  cases h with
  | add ha hb =>
    cases ha with
    | var hA =>
      cases hb with
      | var hB =>
        have := hA.trans hB.symm
        simp [Γ₀] at this

end Silmaril.Courses.Cambridge.OptimisingCompilers.Exercises.S4Q4
