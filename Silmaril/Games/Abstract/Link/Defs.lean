module

public import Silmaril.Games.Abstract.Hiding.Defs
public import Silmaril.Games.Abstract.Machine.Defs

/-!
# Linking with hiding, for trace models and for machines

A *linking situation* `Λ : LinkSpec G₁ G₂ G` fixes the following:

* a joint game `Λ.L` whose moves are every event of the linked system: moves
  of the first component, of the second, internal calls between them, and
  external moves;
* the view of each component, `Λ.π₁ : L.PHom G₁` and `Λ.π₂ : L.PHom G₂`. A
  joint move is seen by one component (a private move), by both (an internal
  interaction, synchronised), or by neither;
* the external view `Λ.ext : L.PHom G`, which hides internal interactions.

The legal plays of `L` say which interleavings the linked system allows:
which component has control, whether reentrant calls are allowed, how
asynchronous events may interleave, and what startup ordering is required.
Plays that would need incompatible choices are not legal in `L`, or are not
accepted by one of the components; synchronisation is intersection.

* Trace models: `TraceModel.link Λ T₁ T₂ = hide Λ.ext (pull Λ.π₁ T₁ ⊓ pull Λ.π₂ T₂)`.
  These are the joint plays both components accept, with internal moves
  hidden.
* Machines: `Machine.link Λ M₁ M₂` runs both machines side by side with a
  monitor of the joint history. Each component takes silent steps on its own.
  A joint move `l` is taken when the history stays legal and every component
  that sees `l` takes it. The step is visible as `Λ.ext.map l`, or silent when
  that move is hidden.

`Silmaril.Games.Abstract.Link.Thms` proves that state erasure commutes with
linking for receptive components, and that the machine composite is always
below the trace composite.
-/

@[expose] public section

namespace Silmaril.Games.Abstract

universe u

/-- A linking situation: the joint game, the views of the two components and
the external view. -/
structure LinkSpec (G₁ G₂ G : Game.{u}) : Type (u + 1) where
  /-- The joint game. -/
  L : Game.{u}
  /-- What the first component sees. -/
  π₁ : L.PHom G₁
  /-- What the second component sees. -/
  π₂ : L.PHom G₂
  /-- What the environment of the linked system sees. -/
  ext : L.PHom G

variable {G₁ G₂ G : Game.{u}}

namespace TraceModel

/-- Linking of trace models: synchronise on the joint game, then hide. -/
def link (Λ : LinkSpec G₁ G₂ G) (T₁ : TraceModel G₁) (T₂ : TraceModel G₂) : TraceModel G :=
  hide Λ.ext (pull Λ.π₁ T₁ ⊓ pull Λ.π₂ T₂)

end TraceModel

namespace Machine

/-- `M` takes the optional move `o` from `x` to `x'`: stays put on `none`. -/
def Moves {H : Game.{u}} (M : Machine H) : Option H.Move → M.State → M.State → Prop
  | none, x, x' => x' = x
  | some m, x, x' => M.step x (some m) x'

/-- Steps of the linked machine. -/
inductive LinkStep (Λ : LinkSpec G₁ G₂ G) (M₁ : Machine G₁) (M₂ : Machine G₂) :
    M₁.State × M₂.State × List Λ.L.Move → Option G.Move →
      M₁.State × M₂.State × List Λ.L.Move → Prop
  /-- A silent step of the first component. -/
  | tau₁ {x x' : M₁.State} {y : M₂.State} {h : List Λ.L.Move} :
      M₁.step x none x' → LinkStep Λ M₁ M₂ (x, y, h) none (x', y, h)
  /-- A silent step of the second component. -/
  | tau₂ {x : M₁.State} {y y' : M₂.State} {h : List Λ.L.Move} :
      M₂.step y none y' → LinkStep Λ M₁ M₂ (x, y, h) none (x, y', h)
  /-- A joint move, taken by every component that sees it. -/
  | move {x x' : M₁.State} {y y' : M₂.State} {h : List Λ.L.Move} (l : Λ.L.Move) :
      h ++ [l] ∈ Λ.L.Legal → M₁.Moves (Λ.π₁.map l) x x' → M₂.Moves (Λ.π₂.map l) y y' →
      LinkStep Λ M₁ M₂ (x, y, h) (Λ.ext.map l) (x', y', h ++ [l])

/-- The linked machine. -/
abbrev link (Λ : LinkSpec G₁ G₂ G) (M₁ : Machine G₁) (M₂ : Machine G₂) : Machine G where
  State := M₁.State × M₂.State × List Λ.L.Move
  init := (M₁.init, M₂.init, [])
  step := LinkStep Λ M₁ M₂

end Machine

end Silmaril.Games.Abstract
