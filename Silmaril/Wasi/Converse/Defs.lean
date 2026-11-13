module

public import Silmaril.Wasi.Host.Defs

@[expose] public section

/-!
# The converse of WASI linking: the host half of a component play

`Silmaril.Wasi.Host.Thms.link_sat` says that a component satisfying the assume–guarantee sentence
`ag (A ∘ hostView) (G ∘ expView)` is correct over every host satisfying `A`. The converse goes
through the **loose** host `ofPred A`: every play of the component whose import answers satisfy
`A` is matched by a play of the loose host. The matching host play is the component's own import
traffic, read from the host's side.

* `hmove`, `hplay t`: the import moves of a component play `t`, as moves of the host's upper
  interface (the component's import calls are the host's Opponent questions, the import answers
  its Proponent answers). Export moves are dropped; the host makes no lower calls.
* `xmove`, `xplay t`: the export moves of `t`, as moves of the linked system.
* `hpos`: the host position of a component position: idle while the component is idle or
  running, answering `m` while the component waits for `m`.

`Thms` shows that `hplay t` and `t` interact to `xplay t` (`zip_split`), that `hplay t` is legal
(`legal_hplay`), hence the converse `ag_of_link_loose` and the characterisations
`link_loose_iff`, `every_host_iff`.

A Silmaril addition.
-/

namespace Silmaril.Wasi

open Silmaril.Games

variable {Y : Sig.{0}} {I X : Set FnName}

/-- An import move of a component, seen from the host; export moves have no host image. -/
def hmove : Move (nsig I) (nsig X) → Option (Move Y (nsig I))
  | .inl e => some (.inr e)
  | .inr _ => none

/-- **The host half of a component play**: its import moves, as a play of the host. -/
def hplay (t : List (Move (nsig I) (nsig X))) : List (Move Y (nsig I)) := t.filterMap hmove

/-- An export move of a component, as a move of the linked system. -/
def xmove : Move (nsig I) (nsig X) → Option (Move Y (nsig X))
  | .inr e => some (.inr e)
  | .inl _ => none

/-- The visible part of a component play once its imports are linked: its export moves. -/
def xplay (t : List (Move (nsig I) (nsig X))) : List (Move Y (nsig X)) := t.filterMap xmove

/-- The host's position while the component is at `x`. -/
def hpos : Pos (nsig I) (nsig X) → Pos Y (nsig I)
  | .idle => .idle
  | .run _ => .idle
  | .wait _ m => .run m

end Silmaril.Wasi
