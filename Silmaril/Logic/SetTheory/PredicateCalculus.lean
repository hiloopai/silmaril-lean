module

public import Silmaril.Logic.SetTheory.Formula

@[expose] public section

/-!
# The predicate calculus of set.mm is sound for semantic formulas

set.mm's logical axioms `ax-1` to `ax-13` and its rules `ax-mp` and `ax-gen`
are transcribed as semantic formulas, like the set-theoretic axioms in
`Silmaril.Logic.SetTheory.Axioms`. Every instance is valid in every membership
structure, for arbitrary predicates as wff metavariables and arbitrary, not
necessarily distinct, set variables. The only disjoint-variable condition,
`$d x ph` of `ax-5`, becomes `Wff.NotFree x φ`. Both rules preserve validity,
and `df-ex` holds for the primitive existential quantifier `Wff.ex`.
-/

namespace Silmaril.Logic.SetTheory

universe u v

namespace Axioms

open Wff

variable {M : Type u} {V : Type v}

/-- `ax-1`: `|- ( ph -> ( ps -> ph ) )`. -/
def ax1 (φ ψ : Wff M V) : Wff M V := imp φ (imp ψ φ)

/-- `ax-2`: `|- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) )`. -/
def ax2 (φ ψ χ : Wff M V) : Wff M V := imp (imp φ (imp ψ χ)) (imp (imp φ ψ) (imp φ χ))

/-- `ax-3`: `|- ( ( -. ph -> -. ps ) -> ( ps -> ph ) )`. -/
def ax3 (φ ψ : Wff M V) : Wff M V := imp (imp (Wff.not φ) (Wff.not ψ)) (imp ψ φ)

/-- `ax-7`: `|- ( x = y -> ( x = z -> y = z ) )`. -/
def ax7 (x y z : V) : Wff M V := imp (eq x y) (imp (eq x z) (eq y z))

section Mem

variable [Membership M M]

/-- `ax-8`: `|- ( x = y -> ( x e. z -> y e. z ) )`. -/
def ax8 (x y z : V) : Wff M V := imp (eq x y) (imp (mem x z) (mem y z))

/-- `ax-9`: `|- ( x = y -> ( z e. x -> z e. y ) )`. -/
def ax9 (x y z : V) : Wff M V := imp (eq x y) (imp (mem z x) (mem z y))

end Mem

variable [DecidableEq V]

/-- `ax-4`: `|- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) )`. -/
def ax4 (x : V) (φ ψ : Wff M V) : Wff M V := imp (all x (imp φ ψ)) (imp (all x φ) (all x ψ))

/-- `ax-5`: `|- ( ph -> A. x ph )`, with `$d x ph`. -/
def ax5 (x : V) (φ : Wff M V) : Wff M V := imp φ (all x φ)

/-- `ax-6`: `|- -. A. x -. x = y`. -/
def ax6 (x y : V) : Wff M V := Wff.not (all x (Wff.not (eq x y)))

/-- `ax-10`: `|- ( -. A. x ph -> A. x -. A. x ph )`. -/
def ax10 (x : V) (φ : Wff M V) : Wff M V :=
  imp (Wff.not (all x φ)) (all x (Wff.not (all x φ)))

/-- `ax-11`: `|- ( A. x A. y ph -> A. y A. x ph )`. -/
def ax11 (x y : V) (φ : Wff M V) : Wff M V := imp (all x (all y φ)) (all y (all x φ))

/-- `ax-12`: `|- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) )`. -/
def ax12 (x y : V) (φ : Wff M V) : Wff M V :=
  imp (eq x y) (imp (all y φ) (all x (imp (eq x y) φ)))

/-- `ax-13`: `|- ( -. x = y -> ( y = z -> A. x y = z ) )`. -/
def ax13 (x y z : V) : Wff M V := imp (Wff.not (eq x y)) (imp (eq y z) (all x (eq y z)))

/-- `df-ex`: `|- ( E. x ph <-> -. A. x -. ph )`. -/
def dfEx (x : V) (φ : Wff M V) : Wff M V := iff (ex x φ) (Wff.not (all x (Wff.not φ)))

end Axioms

namespace PredicateCalculus

open Wff Axioms Function

variable {M : Type u} {V : Type v}

/-- `ax-mp` preserves validity. -/
theorem valid_mp {φ ψ : Wff M V} (h₁ : Valid φ) (h₂ : Valid (imp φ ψ)) : Valid ψ :=
  fun ρ => h₂ ρ (h₁ ρ)

theorem valid_ax1 (φ ψ : Wff M V) : Valid (ax1 φ ψ) := fun _ h _ => h

theorem valid_ax2 (φ ψ χ : Wff M V) : Valid (ax2 φ ψ χ) := fun _ h₁ h₂ h₃ => h₁ h₃ (h₂ h₃)

theorem valid_ax3 (φ ψ : Wff M V) : Valid (ax3 φ ψ) := fun _ h hψ =>
  Classical.byContradiction fun hφ => h hφ hψ

theorem valid_ax7 (x y z : V) : Valid (ax7 (M := M) x y z) :=
  fun ρ (h₁ : ρ x = ρ y) (h₂ : ρ x = ρ z) => show ρ y = ρ z from h₁ ▸ h₂

theorem valid_ax8 [Membership M M] (x y z : V) : Valid (ax8 (M := M) x y z) :=
  fun ρ (h₁ : ρ x = ρ y) (h₂ : ρ x ∈ ρ z) => show ρ y ∈ ρ z from h₁ ▸ h₂

theorem valid_ax9 [Membership M M] (x y z : V) : Valid (ax9 (M := M) x y z) :=
  fun ρ (h₁ : ρ x = ρ y) (h₂ : ρ z ∈ ρ x) => show ρ z ∈ ρ y from h₁ ▸ h₂

variable [DecidableEq V]

/-- `ax-gen` preserves validity. -/
theorem valid_gen {φ : Wff M V} (x : V) (h : Valid φ) : Valid (all x φ) :=
  fun _ _ => h _

theorem valid_ax4 (x : V) (φ ψ : Wff M V) : Valid (ax4 x φ ψ) := fun _ h₁ h₂ a =>
  h₁ a (h₂ a)

theorem valid_ax5 {x : V} {φ : Wff M V} (hφ : NotFree x φ) : Valid (ax5 x φ) := fun ρ h a =>
  (hφ ρ a).2 h

theorem valid_ax6 (x y : V) : Valid (ax6 (M := M) x y) := by
  intro ρ h
  by_cases hxy : x = y
  · subst hxy
    exact h (ρ x) (by simp [eq])
  · exact h (ρ y) (by simp [eq, Ne.symm hxy])

theorem valid_ax10 (x : V) (φ : Wff M V) : Valid (ax10 x φ) := fun ρ h a =>
  (notFree_all x φ ρ a).not.2 h

theorem valid_ax11 (x y : V) (φ : Wff M V) : Valid (ax11 x y φ) := by
  intro ρ h b a
  by_cases hxy : x = y
  · subst hxy
    simpa using h b a
  · simpa [update_comm hxy] using h a b

theorem valid_ax12 (x y : V) (φ : Wff M V) : Valid (ax12 x y φ) := by
  intro ρ hxy h a ha
  change ρ x = ρ y at hxy
  change update ρ x a x = update ρ x a y at ha
  by_cases hv : x = y
  · subst hv
    simpa using h a
  · rw [update_self, update_of_ne (Ne.symm hv)] at ha
    have hρ : update ρ x a = ρ := by
      rw [ha, ← hxy, update_eq_self]
    rw [hρ]
    simpa using h (ρ y)

theorem valid_ax13 (x y z : V) : Valid (ax13 (M := M) x y z) := by
  intro ρ hxy hyz a
  change ¬ ρ x = ρ y at hxy
  change ρ y = ρ z at hyz
  change update ρ x a y = update ρ x a z
  by_cases hx : x = y
  · exact absurd (hx ▸ rfl) hxy
  by_cases hx' : x = z
  · exact absurd (hx' ▸ hyz.symm) hxy
  rw [update_of_ne (Ne.symm hx), update_of_ne (Ne.symm hx'), hyz]

theorem valid_dfEx (x : V) (φ : Wff M V) : Valid (dfEx x φ) := fun _ => by
  simp [dfEx, iff, ex, Wff.not, all]

end PredicateCalculus

end Silmaril.Logic.SetTheory
