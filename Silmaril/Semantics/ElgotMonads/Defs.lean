module

public import Mathlib.Control.Monad.Basic
public import Mathlib.Data.Set.Functor
public import Mathlib.Control.Monad.Writer
public import Silmaril.Semantics.Elgot.Thms

/-!
# ElgotMonads

Source: the thesis [imbrem/thesis](https://github.com/imbrem/thesis) at `69a8126`, Concrete Models,
§Monads and Monad Transformers (mapped by content).
-/

@[expose] public section

section

/-!
## Partiality and finite approximations

The complete Elgot instance on `Part` is characterized by finite successful
runs. Fuel bounds approximate this same iteration; failure to finish within a
particular bound is not identified with semantic divergence.
-/

universe u

namespace Silmaril.Elgot.Part

variable {A B : Type u}

/-- Explore at most `fuel` calls of the loop body. -/
def runFor (f : A → _root_.Part (B ⊕ A)) : Nat → A → _root_.Part B
  | 0, _ => .none
  | fuel + 1, a => f a >>= Sum.elim _root_.Part.some (runFor f fuel)

end Silmaril.Elgot.Part

end

section

/-!
## Complete Elgot iteration with errors

An error ends the loop and remains distinguishable from divergence in the base
monad. Only a successful right summand requests another iteration.
-/

namespace Silmaril.Elgot.ExceptT

universe u

variable {m : Type u → Type u} [Monad m] {ε A B C : Type u}

def distribute : Except ε (B ⊕ A) → (Except ε B) ⊕ A
  | .error e => .inl (.error e)
  | .ok (.inl b) => .inl (.ok b)
  | .ok (.inr a) => .inr a

def body (f : A → _root_.ExceptT ε m (B ⊕ A)) : A → m ((Except ε B) ⊕ A) :=
  fun a => (f a).run >>= pure ∘ distribute

instance [Iterate m] : Iterate (_root_.ExceptT ε m) where
  iter f a := _root_.ExceptT.mk (iter (body f) a)

/-- Extend a continuation by propagating errors unchanged. -/
def extend (g : B → _root_.ExceptT ε m C) : Except ε B → m (Except ε C)
  | .error e => pure (.error e)
  | .ok b => (g b).run

variable [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

end Silmaril.Elgot.ExceptT

end

section

/-!
## Complete Elgot iteration with optional failure

Failure ends the loop; only a successful right summand continues it. The four
Elgot laws follow through the faithful interpretation into single-error `ExceptT`.
Failure remains distinct from divergence in the underlying monad.
-/

namespace Silmaril.Elgot.OptionT

universe u

variable {m : Type u → Type u} [Monad m] {A B : Type u}

def distribute : Option (B ⊕ A) → Option B ⊕ A
  | none => .inl none
  | some (.inl b) => .inl (some b)
  | some (.inr a) => .inr a

def body (f : A → _root_.OptionT m (B ⊕ A)) : A → m (Option B ⊕ A) :=
  fun a => (f a).run >>= pure ∘ distribute

instance [Iterate m] : Iterate (_root_.OptionT m) where
  iter f a := _root_.OptionT.mk (iter (body f) a)

@[simp] theorem run_iter [Iterate m] (f : A → _root_.OptionT m (B ⊕ A)) (a : A) :
    (iter f a).run = iter (body f) a := rfl

def toExceptValue : Option A → Except PUnit A
  | none => .error ⟨⟩
  | some a => .ok a

def fromExceptValue : Except PUnit A → Option A
  | .error _ => none
  | .ok a => some a

@[simp] theorem from_toExceptValue (x : Option A) :
    fromExceptValue (toExceptValue x) = x := by cases x <;> rfl

@[simp] theorem to_fromExceptValue (x : Except PUnit A) :
    toExceptValue (fromExceptValue x) = x := by
  cases x with
  | error e => cases e; rfl
  | ok a => rfl

/-- Interpret optional failure as the unique error. -/
def toExcept (x : _root_.OptionT m A) : _root_.ExceptT PUnit m A :=
  _root_.ExceptT.mk (x.run >>= pure ∘ toExceptValue)

variable [LawfulMonad m]

theorem toExcept_injective : Function.Injective (toExcept (m := m) (A := A)) := by
  intro x y h
  have h' := congrArg (fun z : _root_.ExceptT PUnit m A =>
    z.run >>= pure ∘ fromExceptValue) h
  apply _root_.OptionT.ext
  simpa only [toExcept, _root_.ExceptT.run_mk, bind_assoc, Function.comp_apply,
    pure_bind, from_toExceptValue, bind_pure] using h'

@[simp] theorem toExcept_pure (a : A) : toExcept (pure a : _root_.OptionT m A) = pure a := by
  apply _root_.ExceptT.ext
  simp [toExcept, toExceptValue]

@[simp] theorem toExcept_bind (x : _root_.OptionT m A) (f : A → _root_.OptionT m B) :
    toExcept (x >>= f) = toExcept x >>= fun a => toExcept (f a) := by
  apply _root_.ExceptT.ext
  simp only [toExcept, _root_.ExceptT.run_mk, _root_.ExceptT.run_bind,
    _root_.OptionT.run_bind, Option.elimM, bind_assoc, Function.comp_apply, pure_bind]
  apply bind_congr
  intro o
  cases o <;> simp [toExceptValue]

theorem body_toExcept (f : A → _root_.OptionT m (B ⊕ A)) :
    ExceptT.body (fun a => toExcept (f a)) = mapReturn (body f) (pure ∘ toExceptValue) := by
  funext a
  simp only [ExceptT.body, toExcept, _root_.ExceptT.run_mk, mapReturn, body,
    bind_assoc, Function.comp_apply, pure_bind]
  apply bind_congr
  intro o
  cases o with
  | none => simp [toExceptValue, distribute, ExceptT.distribute]
  | some s => cases s <;> simp [toExceptValue, distribute, ExceptT.distribute]

variable [Iterate m] [LawfulElgotMonad m]

@[simp] theorem toExcept_iter (f : A → _root_.OptionT m (B ⊕ A)) (a : A) :
    toExcept (iter f a) = iter (fun a => toExcept (f a)) a := by
  apply _root_.ExceptT.ext
  change (iter (body f) a >>= pure ∘ toExceptValue) =
    iter (ExceptT.body (fun a => toExcept (f a))) a
  rw [body_toExcept]
  exact congrFun (LawfulElgotMonad.naturality (body f) (pure ∘ toExceptValue)) a

def embedding : Embedding (_root_.OptionT m) (_root_.ExceptT PUnit m) where
  map := toExcept
  injective := fun h => toExcept_injective h
  map_pure := toExcept_pure
  map_bind := toExcept_bind
  map_iter := toExcept_iter

end Silmaril.Elgot.OptionT

end

section

/-! ## Complete Elgot iteration with a fixed reader environment -/

namespace Silmaril.Elgot.ReaderT

universe u

variable {m : Type u → Type u} [Monad m] {ρ A B C : Type u}

instance [Iterate m] : Iterate (_root_.ReaderT ρ m) where
  iter f a r := iter (fun a => (f a).run r) a

variable [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

end Silmaril.Elgot.ReaderT

end

section

/-!
## Nondeterministic complete Elgot iteration

The powerset monad records all finite successful outcomes. Iteration is its
least fixed point, so divergence and failure both contribute no returned value.
This is a may-outcome semantics, without a fairness or must-termination claim.
-/

universe u

namespace Silmaril.Elgot.Nondet

scoped notation:50 a:50 " ∈ₘ " s:50 => a ∈ _root_.SetM.run s

variable {A B C : Type u}

/-- A finite successful execution of an iteration body. -/
inductive Runs {A B : Type u} (f : A → _root_.SetM (B ⊕ A)) : A → B → Prop
  | done {a b} : Sum.inl b ∈ₘ f a → Runs f a b
  | more {a a' b} : Sum.inr a' ∈ₘ f a → Runs f a' b → Runs f a b

instance : Iterate _root_.SetM where
  iter f a := { b | Runs f a b }

end Silmaril.Elgot.Nondet

end

section

/-!
## Complete Elgot iteration through mutable state

Iteration carries the current state with each recursive call and returns the
final state with the result. All four Elgot laws are inherited from the base
monad; state changes are neither reset nor discarded between iterations.
-/

namespace Silmaril.Elgot.StateT

universe u v

variable {m : Type u → Type v} [Monad m] {σ A B C : Type u}

/-- Move the current state into whichever branch the loop selects. -/
def distribute : (B ⊕ A) × σ → (B × σ) ⊕ (A × σ)
  | (.inl b, s) => .inl (b, s)
  | (.inr a, s) => .inr (a, s)

/-- Regard both the loop argument and its mutable state as the recursive input. -/
def body (f : A → _root_.StateT σ m (B ⊕ A)) : A × σ → m ((B × σ) ⊕ (A × σ)) :=
  fun p => (f p.1).run p.2 >>= pure ∘ distribute

instance [Iterate m] : Iterate (_root_.StateT σ m) where
  iter f a s := iter (body f) (a, s)

variable [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

end Silmaril.Elgot.StateT

end

section

/-!
## Writer iteration over an Elgot monad

Iteration accumulates the monoid output in the base loop's recursive state.
The log has the same termination behavior as the base monad: in particular,
ordinary `WriterT W Part` does not expose output from a nonterminating loop.
-/

namespace Silmaril.Elgot.WriterT

universe u

variable {m : Type u → Type u} [Monad m] [LawfulMonad m]
  {W A B : Type u} [Monoid W]

/-- A writer computation acts on an existing output prefix by right appending. -/
def toState (x : _root_.WriterT W m A) : _root_.StateT W m A :=
  fun w => x.run >>= fun p => pure (p.1, w * p.2)

theorem toState_injective : Function.Injective (toState (m := m) (W := W) (A := A)) := by
  intro x y h
  have h1 := congrFun h 1
  apply _root_.WriterT.ext
  simpa [toState] using h1

@[simp] theorem toState_pure (a : A) : toState (pure a : _root_.WriterT W m A) = pure a := by
  funext w
  simp [toState]
  rfl

@[simp] theorem toState_bind (x : _root_.WriterT W m A) (f : A → _root_.WriterT W m B) :
    toState (x >>= f) = toState x >>= fun a => toState (f a) := by
  apply _root_.StateT.ext
  intro w
  rw [_root_.StateT.run_bind]
  simp [toState, _root_.StateT.run, ← bind_pure_comp, mul_assoc]

/-- The base loop remembers both the recursive argument and the accumulated output. -/
def body (f : A → _root_.WriterT W m (B ⊕ A)) : A × W → m ((B × W) ⊕ (A × W)) :=
  StateT.body (fun a => toState (f a))

instance [Iterate m] : Iterate (_root_.WriterT W m) where
  iter f a := _root_.WriterT.mk (iter (body f) (a, 1))

variable [Iterate m] [LawfulElgotMonad m]

/-- An initial output prefix can be moved outside iteration. -/
theorem iter_prefix (f : A → _root_.WriterT W m (B ⊕ A)) (w s : W) (a : A) :
    iter (body f) (a, w * s) =
      iter (body f) (a, s) >>= fun p => pure (p.1, w * p.2) := by
  let h : A × W → A × W := fun p => (p.1, w * p.2)
  let k : B × W → m (B × W) := fun p => pure (p.1, w * p.2)
  have square : (mapReturn (body f) k >=> liftPure (Sum.map id h)) =
      (liftPure h >=> body f) := by
    funext p
    simp only [Bind.kleisliRight, mapReturn, liftPure, Function.comp_apply, body, StateT.body,
      toState, bind_assoc, pure_bind, _root_.StateT.run]
    apply bind_congr
    rintro ⟨x, t⟩
    cases x <;> simp [StateT.distribute, h, k, mul_assoc]
  have hu := congrFun (LawfulElgotMonad.uniformity (mapReturn (body f) k) (body f) h square) (a, s)
  have hn := congrFun (LawfulElgotMonad.naturality (body f) k) (a, s)
  simpa only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind, h, k] using hu.symm.trans hn.symm

@[simp] theorem toState_iter (f : A → _root_.WriterT W m (B ⊕ A)) (a : A) :
    toState (iter f a) = iter (fun a => toState (f a)) a := by
  funext w
  change (iter (body f) (a, 1) >>= fun p => pure (p.1, w * p.2)) = iter (body f) (a, w)
  simpa only [mul_one] using (iter_prefix f w 1 a).symm

/-- Writer computations embed into state computations without losing their log. -/
def stateEmbedding : Embedding (_root_.WriterT W m) (_root_.StateT W m) where
  map := toState
  injective := fun {_} {_ _} h => toState_injective h
  map_pure := toState_pure
  map_bind := toState_bind
  map_iter := toState_iter

section Examples

/-- A two-step computation emits its logs in execution order. -/
def twoSteps {W : Type} (first second : W) : Bool → _root_.WriterT W _root_.Part (PUnit ⊕ Bool)
  | false => _root_.WriterT.mk (_root_.Part.some (.inr true, first))
  | true => _root_.WriterT.mk (_root_.Part.some (.inl ⟨⟩, second))

end Examples

end Silmaril.Elgot.WriterT

end
