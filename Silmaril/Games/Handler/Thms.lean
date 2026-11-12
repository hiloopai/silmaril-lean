module

public import Silmaril.Games.Handler.Defs
public import Silmaril.Games.Composition.Thms
public import Silmaril.Games.LTS.Thms
import Silmaril.Proofs.Games.Handler.Comp
import Silmaril.Proofs.Games.Handler.Id

/-!
# Strategies of handlers: theorems

* `Strategy.mem_ofHandler`: the plays of `ofHandler h` are exactly the traces
  of its reduction semantics (handlers accept every question and answer).
* `Strategy.ofHandler_comp`: handler composition (interpretation) is strategy
  composition — `ofHandler` is a functor from handlers to strategies.
* `Strategy.ofHandler_id`: the forwarding handler denotes copycat.
* Consequences for restriction along renamings: `Strategy.restrict_id`,
  `Strategy.restrict_comp`, `Strategy.restrict_mono`.

Proofs are in `Silmaril.Proofs.Games.Handler.Comp` and
`Silmaril.Proofs.Games.Handler.Id`.
-/

public section

namespace Silmaril.Games

universe u

variable {E F G : Sig.{u}}

namespace Strategy

/-- The plays of the strategy of a handler are the traces of its reduction
semantics. -/
theorem mem_ofHandler {h : Handler E F} {p : List (Move E F)} :
    p ∈ ofHandler h ↔ p ∈ h.toReduction.toLTS.Traces :=
  Silmaril.Proofs.Games.Handler.mem_ofHandler

/-- The transition system of a handler denotes its strategy. -/
theorem _root_.Silmaril.Games.Handler.denotes_toLTS (h : Handler E F) :
    h.toReduction.toLTS.Denotes (ofHandler h) := fun _ => mem_ofHandler.symm

/-- `ofHandler` maps handler composition to strategy composition. -/
theorem ofHandler_comp (h₁ : Handler E F) (h₂ : Handler F G) :
    ofHandler (h₁.comp h₂) = (ofHandler h₁).comp (ofHandler h₂) :=
  Silmaril.Proofs.Games.Handler.ofHandler_comp h₁ h₂

/-- The forwarding handler denotes copycat. -/
theorem ofHandler_id (E : Sig.{u}) : ofHandler (Handler.id E) = Strategy.id E := by
  ext p
  rw [mem_ofHandler, mem_id]
  exact Silmaril.Proofs.Games.Handler.mem_ofHandler_id

/-- Restricting along the identity renaming does nothing. -/
theorem restrict_id {X : Sig.{u}} (σ : Strategy X F) : σ.restrict (Sig.Hom.id F) = σ := by
  rw [restrict, show Handler.ofHom (Sig.Hom.id F) = Handler.id F from rfl, ofHandler_id,
    comp_id]

/-- Restriction along a composite renaming is iterated restriction. -/
theorem restrict_comp {X : Sig.{u}} (σ : Strategy X G) (f : Sig.Hom E F) (g : Sig.Hom F G) :
    σ.restrict (f.comp g) = (σ.restrict g).restrict f := by
  rw [restrict, restrict, restrict, comp_assoc, ← ofHandler_comp]
  rfl

/-- Restriction is monotone. -/
theorem restrict_mono {X : Sig.{u}} {σ τ : Strategy X F} (h : σ ≤ τ) (ρ : Sig.Hom E F) :
    σ.restrict ρ ≤ τ.restrict ρ :=
  comp_mono_left h _

end Strategy

end Silmaril.Games
