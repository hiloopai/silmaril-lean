module

public import Silmaril.Semantics.ITreeInterpret.Defs
import Silmaril.Proofs.Semantics.ITreeInterpret.Reify
import Silmaril.Proofs.Semantics.ITreeInterpret.Interpret.Hom
import Silmaril.Proofs.Semantics.ITreeInterpret.Interpret.Partial
import Silmaril.Proofs.Semantics.ITreeInterpret.Interpret.Step
import Silmaril.Proofs.Semantics.ITreeInterpret.Interpret.Initial

/-!
# ITreeInterpret

Source: interpretation of interaction trees into complete Elgot monads, after
Concrete Models, §Trace Models of the thesis [imbrem/thesis](https://github.com/imbrem/thesis) at `69a8126`.


Theorems about `Silmaril.Semantics.ITreeInterpret.Defs`. Proofs longer than a few lines live
under `Silmaril.Proofs.Semantics.ITreeInterpret` and are only pointed at from here.
-/

public section

section

/-! ## Reify -/

namespace Silmaril.Elgot.ITree.Interpret

universe u

variable {E : Type u → Type u} {A : Type u} [Small.{u} (Tree E A)]

@[simp] theorem fold_self_diverge :
    fold (E := E) (m := Tree E) trigger (diverge : Tree E A) = diverge :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Interpret.fold_self_diverge

/-- Interpreting each visible event by the corresponding visible tree is the
identity on all weak trees, not only the finite free-effect fragment. -/
@[simp] theorem fold_self (t : Tree E A) :
    fold (E := E) (m := Tree E) trigger t = t :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Interpret.fold_self t

end Silmaril.Elgot.ITree.Interpret

end

section

/-! ## Interpret.Hom -/

namespace Silmaril.Elgot.ITree.Interpret

universe u v

variable {E : Type u → Type u} {m : Type u → Type v} [Monad m] [Iterate m]

namespace Hom

variable {handler : Handler E m} (f : Hom (E := E) (m := m) handler)

theorem map_stepTree {A : Type u} [Small.{u} (Tree E A)] (t : Tree E A) :
    f.map (stepTree (E := E) (m := Tree E) trigger t) =
      stepTree (E := E) (m := m) handler t :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Interpret.Hom.map_stepTree f t

theorem map_step {A : Type u} [Small.{u} (Tree E A)] (state : Shrink.{u} (Tree E A)) :
    f.map (step (E := E) (m := Tree E) trigger state) =
      step (E := E) (m := m) handler state :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Interpret.Hom.map_step f state

/-- Any candidate preserving the stated structure is forced to be the fold on
all trees, including trees with infinite visible behavior. -/
theorem unique {A : Type u} [Small.{u} (Tree E A)] (t : Tree E A) :
    f.map t = fold (E := E) (m := m) handler t :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Interpret.Hom.unique f t

@[ext] theorem ext {f g : Hom (E := E) (m := m) handler}
    (h : ∀ {A : Type u} (t : Tree E A), f.map t = g.map t) : f = g :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Interpret.Hom.ext h

/-- There is at most one complete-iteration-preserving interpretation of a
small event tree for a fixed handler. This states uniqueness, not existence. -/
theorem subsingleton [∀ A : Type u, Small.{u} (Tree E A)] :
    Subsingleton (Hom (E := E) (m := m) handler) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Interpret.Hom.subsingleton

end Hom

end Silmaril.Elgot.ITree.Interpret

end

section

/-! ## Interpret.Partial -/

namespace Silmaril.Elgot.ITree.Interpret

universe u v

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

theorem liftPart_bind {A B : Type u} (x : _root_.Part A) (k : A → _root_.Part B) :
    liftPart (m := m) (x >>= k) = (liftPart (m := m) x >>= fun a => liftPart (m := m) (k a)) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Interpret.liftPart_bind x k

end Silmaril.Elgot.ITree.Interpret

end

section

/-! ## Interpret.Step -/

namespace Silmaril.Elgot.ITree.Interpret

universe u v

variable {E : Type u → Type u} {m : Type u → Type v}
  [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

omit [LawfulMonad m] [LawfulElgotMonad m] in
@[simp] theorem partialStep_shrink {A : Type u} [Small.{u} (Tree E A)]
    (handler : Handler E m) (t : Tree E A) :
    partialStep (E := E) (m := m) handler (equivShrink _ t) =
      partialStepTree (E := E) (m := m) handler t := by simp [partialStep]

@[simp] theorem fold_diverge {A : Type u} [Small.{u} (Tree E A)]
    (handler : Handler E m) : fold (E := E) (m := m) handler (diverge : Tree E A) = bottom :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Interpret.fold_diverge handler

end Silmaril.Elgot.ITree.Interpret

end

section

/-! ## Interpret.Initial -/

namespace Silmaril.Elgot.ITree.Interpret

universe u v

variable {E : Type u → Type u} [∀ A : Type u, Small.{u} (Tree E A)]
  {m : Type u → Type v} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

/-- The free event model includes unbounded visible behavior and silent
divergence, and is initial for interpretations preserving complete iteration. -/
theorem initial (handler : Handler E m) : ∃! _f : Hom (E := E) (m := m) handler, True :=
  Silmaril.Proofs.Semantics.Elgot.ITree.Interpret.initial handler

end Silmaril.Elgot.ITree.Interpret

end
