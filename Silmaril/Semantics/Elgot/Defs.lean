module

public import Mathlib.Data.Part

/-!
# Elgot

Source: the thesis [imbrem/thesis](https://github.com/imbrem/thesis) at `69a8126`, Denotational Semantics,
§Freyd–Elgot Categories: Conway iteration, uniformity and strong Elgot structure.
The mapping to the thesis is by content; the source modules do not cite it.
-/

@[expose] public section

section

/-!
## Complete Elgot monads on types

We use the convention that `Sum.inl` is a returned value and `Sum.inr` is a
recursive call.  Thus `iter f` is the dagger of the Kleisli arrow
`f : A → m (B ⊕ A)`.

Uniformity is deliberately restricted to maps `h : A → C` in **Type**, embedded
in the Kleisli category by `pure`.  It is not asserted for arbitrary effectful
Kleisli arrows.

As with Lean's `Monad`, result values and computation carriers may inhabit
different universes. This accommodates large representations of computations
over small values without inserting lifts into the values themselves.
-/

namespace Silmaril.Elgot

universe u v

/-- An iteration operator on a monad. -/
class Iterate (m : Type u → Type v) where
  iter {A B : Type u} : (A → m (B ⊕ A)) → A → m B

export Iterate (iter)

/-- Embed an ordinary function as a pure Kleisli arrow. -/
def liftPure {m : Type u → Type v} [Monad m] {A B : Type u} (f : A → B) : A → m B :=
  pure ∘ f

/-- Act on the returned (left) summand of an iteration body. -/
def mapReturn {m : Type u → Type v} [Monad m] {A B C : Type u}
    (f : A → m (B ⊕ A)) (g : B → m C) : A → m (C ⊕ A) :=
  fun a ↦ f a >>= Sum.elim (fun b ↦ g b >>= pure ∘ Sum.inl) (pure ∘ Sum.inr)

/-- Merge two successive recursive summands. -/
def flatten {A B : Type u} : (B ⊕ A) ⊕ A → B ⊕ A :=
  Sum.elim id Sum.inr

/-- Apply `flatten` to the result of an effectful iteration body. -/
def flattenBody {m : Type u → Type v} [Monad m] {A B : Type u}
    (f : A → m ((B ⊕ A) ⊕ A)) : A → m (B ⊕ A) :=
  f >=> liftPure flatten

/-- The Conway/complete-Elgot equations, with pure uniformity. -/
class LawfulElgotMonad (m : Type u → Type v) [Monad m] [LawfulMonad m] [Iterate m] : Prop where
  fixpoint {A B : Type u} (f : A → m (B ⊕ A)) :
    iter f = fun a ↦ f a >>= Sum.elim pure (iter f)
  naturality {A B C : Type u} (f : A → m (B ⊕ A)) (g : B → m C) :
    (iter f >=> g) = iter (mapReturn f g)
  codiagonal {A B : Type u} (f : A → m ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f)
  uniformity {A B C : Type u} (f : A → m (B ⊕ A)) (g : C → m (B ⊕ C))
      (h : A → C)
      (comm : (f >=> liftPure (Sum.map id h)) = (liftPure h >=> g)) :
    iter f = (liftPure h >=> iter g)

namespace Part

variable {A B C : Type u}

/-- A finite successful execution of an iteration body. -/
inductive Runs {A B : Type u} (f : A → _root_.Part (B ⊕ A)) : A → B → Prop
  | done {a b} : Sum.inl b ∈ f a → Runs f a b
  | more {a a' b} : Sum.inr a' ∈ f a → Runs f a' b → Runs f a b

/-- The partial value returned by the unique finite successful run, if one exists. -/
noncomputable def run {A B : Type u} (f : A → _root_.Part (B ⊕ A)) (a : A) : _root_.Part B where
  Dom := ∃ b, Runs f a b
  get h := Classical.choose h

noncomputable instance : Iterate _root_.Part where
  iter := run

section Examples

end Examples

end Part

end Silmaril.Elgot

end

section

/-! Sequential composition as iteration through two phases. -/

namespace Silmaril.Elgot

universe u v

variable {m : Type u → Type v} [Monad m]

variable {A B : Type u}

/-- First run `x`, then pass its result to `f` and return. -/
def bindBody (x : m A) (f : A → m B) :
    PUnit.{u + 1} ⊕ A → m (B ⊕ (PUnit.{u + 1} ⊕ A))
  | .inl _ => x >>= fun a => pure (.inr (.inr a))
  | .inr a => f a >>= fun b => pure (.inl b)

variable [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

end Silmaril.Elgot

end

section

/-!
## Transport of Elgot laws

A faithful interpretation of computations transports the Elgot equations when
it preserves pure computations, sequencing, and the chosen iteration operator.
-/

namespace Silmaril.Elgot

universe u

variable {m n : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m]
  [Monad n] [LawfulMonad n] [Iterate n]

/-- An injective monad interpretation that preserves the chosen iterations. -/
structure Embedding (m n : Type u → Type u) [Monad m] [Iterate m] [Monad n] [Iterate n] where
  map {A : Type u} : m A → n A
  injective {A : Type u} : Function.Injective (map (A := A))
  map_pure {A : Type u} (a : A) : map (pure a) = pure a
  map_bind {A B : Type u} (x : m A) (f : A → m B) :
    map (x >>= f) = map x >>= fun a => map (f a)
  map_iter {A B : Type u} (f : A → m (B ⊕ A)) (a : A) :
    map (iter f a) = iter (fun a => map (f a)) a

namespace Embedding

variable (e : Embedding m n)

end Embedding

end Silmaril.Elgot

end
