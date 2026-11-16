module

public import Mathlib.Algebra.Group.Defs

/-!
# Signed formulas and negation of lists

* `Signed A`: an atom with a sign, `pos a` or `neg a`. Negation flips the sign, and it is an
  instance of Mathlib's `InvolutiveNeg` (`- -x = x`), so lemmas stated for any involutive
  negation apply to it.
* `negateEach l`: negate every member of a list, for any `Neg`. It is how formulas move across
  the turnstile (`Γ ⊢ Δ` against `Γ ++ negateEach Δ` being refutable). Those conversions belong
  to the structural modules.
* `SignedCarrier C D A`: explicit maps from antecedent formulas `C` and succedent formulas `D`
  into one carrier `A` with an involutive negation. When `C` and `D` differ, side-moving
  happens only through such a carrier. It records maps and nothing else: no injectivity, and
  no claim that `A` splits into positive and negative parts.

An involutive negation does **not** identify "positive" elements, since a negation may have
fixed points. Positive parts are therefore always taken along an explicit embedding
(`MultiSystem.posPartAlong`). `Signed.pos` is such an embedding for `Signed A`, and `Signed`
genuinely decomposes (`Signed.isPos`, `Signed.atom`).
-/

@[expose] public section

namespace Silmaril.Consequence

universe u v w

/-- An atom with a sign. -/
inductive Signed (A : Type u) where
  /-- The atom, positively. -/
  | pos (a : A)
  /-- The atom, negated. -/
  | neg (a : A)
  deriving DecidableEq, Repr

namespace Signed

variable {A : Type u}

/-- Flip the sign. -/
def flip : Signed A → Signed A
  | pos a => neg a
  | neg a => pos a

instance : InvolutiveNeg (Signed A) where
  neg := flip
  neg_neg x := by cases x <;> rfl

/-- Whether the sign is positive. -/
def isPos : Signed A → Bool
  | pos _ => true
  | neg _ => false

/-- The underlying atom. -/
def atom : Signed A → A
  | pos a => a
  | neg a => a

end Signed

/-- Negate every member of a list. -/
def negateEach {α : Type u} [Neg α] (l : List α) : List α := l.map (-·)

/-- Explicit maps from antecedent formulas `C` and succedent formulas `D` into a common carrier
with an involutive negation. No law is assumed beyond `InvolutiveNeg A`. -/
structure SignedCarrier (C : Type u) (D : Type v) (A : Type w) [InvolutiveNeg A] where
  /-- Antecedent formulas in the carrier. -/
  ofC : C → A
  /-- Succedent formulas in the carrier. -/
  ofD : D → A

end Silmaril.Consequence
