module

public import Silmaril.Games.Abstract.Game.Defs

/-!
# Interleaved tasks: the asynchronous extension of a game

`G.interleave ι` runs one copy of `G` per task `i : ι`, interleaved. A move is
a task with a move of `G`, and a play is legal when every task's projection
is legal in `G`. This is the shape of asynchronous calls in the component
model: each export call is a task with its own sequential protocol, and calls
may overlap. Streams and futures add further events to each task's game and
are a later stage.

The *synchronous submodel* is a single task: `Game.Hom.single i` sends each
move of `G` to task `i`. It is injective on moves and reflects Opponent
polarity. By `Silmaril.Games.Abstract.Interleave.Thms`, pushing a model of `G`
forward along it is an order embedding of `TraceModel G` into
`TraceModel (G.interleave ι)`, with `comap` as retraction. The synchronous
model is a submodel of the asynchronous one, not a replacement for it, and
with two tasks the inclusion is strict.
-/

@[expose] public section

namespace Silmaril.Games.Abstract

universe u v

namespace Game

variable (G : Game.{u}) (ι : Type u) [DecidableEq ι]

/-- The move of task `i`, if the move belongs to it. -/
def taskProj {G : Game.{u}} {ι : Type u} [DecidableEq ι] (i : ι) (x : ι × G.Move) :
    Option G.Move :=
  if x.1 = i then some x.2 else none

/-- Interleaved tasks, each playing `G`. -/
abbrev interleave : Game.{u} where
  Move := ι × G.Move
  IsO x := G.IsO x.2
  Legal := {s | ∀ i, s.filterMap (taskProj i) ∈ G.Legal}
  nil_legal _ := G.nil_legal
  legal_of_prefix ht h i := G.legal_of_prefix (ht i) (h.filterMap _)

variable {G ι}

theorem filterMap_taskProj_self (i : ι) (s : List G.Move) :
    (s.map (fun m => (i, m))).filterMap (taskProj i) = s := by
  induction s with
  | nil => rfl
  | cons m s ih =>
    simp only [List.map_cons, List.filterMap_cons, taskProj, ↓reduceIte]
    exact congrArg _ ih

theorem filterMap_taskProj_ne {i j : ι} (hj : i ≠ j) (s : List G.Move) :
    (s.map (fun m => (i, m))).filterMap (taskProj j) = [] := by
  induction s with
  | nil => rfl
  | cons m s ih =>
    simp only [List.map_cons, List.filterMap_cons, taskProj, hj, ↓reduceIte]
    exact ih

/-- The synchronous submodel: everything happens in task `i`. -/
def Hom.single (i : ι) : G.Hom (G.interleave ι) where
  map m := (i, m)
  legal {s} h j := by
    by_cases hj : i = j
    · subst hj
      exact (filterMap_taskProj_self i s).symm ▸ h
    · exact (filterMap_taskProj_ne hj s).symm ▸ G.nil_legal
  isO h := h

end Game

end Silmaril.Games.Abstract
