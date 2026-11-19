module

public import Silmaril.Cerberus.TV.Explore.Defs
import Silmaril.Proofs.Cerberus.TV.Explore

/-!
# What an exploration establishes

Soundness holds for every exploration; completeness, termination and progress need an exhaustive
one (`limited = false`). See `Silmaril.Cerberus.TV.Explore.Defs`.
-/

@[expose] public section

namespace Silmaril.Cerberus.TV

open Silmaril.Cerberus.Core.Dynamics

/-- **Soundness**: every collected ending is an ending of the program. -/
theorem Closed.explore_sound (P : Closed) (bounds : Bounds) (e : Outcome × String)
    (h : e ∈ (P.explore bounds).ends) : P.Ends e.1 e.2 :=
  Proofs.Cerberus.TV.Closed.explore_sound P bounds e h

/-- **Completeness**: an exhaustive exploration collects every ending. -/
theorem Closed.explore_complete (P : Closed) (bounds : Bounds)
    (hl : (P.explore bounds).limited = false) (o : Outcome) (out : String)
    (h : P.Ends o out) : (o, out) ∈ (P.explore bounds).ends :=
  Proofs.Cerberus.TV.Closed.explore_complete P bounds hl o out h

/-- **Termination**: a program with an exhaustive exploration has no infinite run. -/
theorem Closed.explore_terminates (P : Closed) (bounds : Bounds)
    (hl : (P.explore bounds).limited = false) : ¬ P.Diverges :=
  Proofs.Cerberus.TV.Closed.explore_terminates P bounds hl

/-- **Progress**: an exhaustive exploration that met no stuck state proves there is none. -/
theorem Closed.explore_noStuck (P : Closed) (bounds : Bounds)
    (hl : (P.explore bounds).limited = false) (hs : (P.explore bounds).stuck = false) :
    ¬ P.Stuck :=
  Proofs.Cerberus.TV.Closed.explore_noStuck P bounds hl hs

end Silmaril.Cerberus.TV
