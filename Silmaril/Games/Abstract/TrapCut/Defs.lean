module

public import Silmaril.Games.Abstract.Outcome.Defs
public import Mathlib.Data.Nat.Find

/-!
# Trap ≈ divergence when a trap is a move

In the Wasm game an export call that traps is answered by a visible
Proponent move (`Answer.trap`), and the instance stays callable. A divergence
is the absence of any answer. To identify the two, a trap move must be read as
the end of observation: everything after it is dropped, and the prefix before
it is tagged `abort`, exactly like a divergence there.

`Obs.cut T` does this for a predicate `T` on moves (the trap moves):

* a finite observation whose trace contains a `T` move becomes the prefix
  before the first one, tagged `abort`;
* otherwise trap and divergence tags are merged as in `Obs.collapse`;
* an infinite run containing a `T` move becomes its prefix before the first
  one, tagged `abort`.

`CutEquiv T M N` is equality of these observations: the **trap ≈ divergence**
equivalence for games where traps are moves. `TagEquiv` (equal tagged
observations) is the **sensitive** one. With no trap moves, `Obs.cut` is
`Obs.collapse` (`Silmaril.Games.Abstract.TrapCut.Thms`).

What is dropped after a trap move is deliberate: a context that sees a trap
and then calls again can observe more than one that saw a divergence, which
never returns. So `CutEquiv` is the right coarse notion only for contexts that
stop at a trap. Contexts that continue after a trap need `TagEquiv`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract

universe u

open Classical in
/-- The prefix before the first `T` move, if there is one. -/
noncomputable def firstCut {M : Type u} (T : M → Prop) : List M → Option (List M)
  | [] => none
  | m :: s => if T m then some [] else (firstCut T s).map (m :: ·)

open Classical in
/-- Trap ≈ divergence with trap moves: cut at the first trap move. -/
noncomputable def Obs.cut {G : Game.{u}} {R : Type u} (T : G.Move → Prop) :
    Obs G R → CObs G R
  | .fin s t =>
    match firstCut T s with
    | some p => .fin p .abort
    | none => .fin s t.collapse
  | .inf ω => if h : ∃ n, T (ω n) then .fin ((List.range (Nat.find h)).map ω) .abort else .inf ω

namespace OMachine

variable {G : Game.{u}} {R : Type u}

/-- The cut observations. -/
noncomputable def cobsCut (T : G.Move → Prop) (M : OMachine G R) : Set (CObs G R) :=
  Obs.cut T '' M.obs

/-- Trap ≈ divergence equivalence when traps are the moves `T`. -/
def CutEquiv (T : G.Move → Prop) (M N : OMachine G R) : Prop := M.cobsCut T = N.cobsCut T

end OMachine

end Silmaril.Games.Abstract
