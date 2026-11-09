module

public import Silmaril.X86.Sep.Defs

/-!
# Extra separation-logic connectives: disjunction and `True`

Two connectives that `Sep/Defs.lean` does not provide, used by the allocator interface
(`Sep/Alloc`). Packages that need them import this header and do not redefine them.

* `sor P Q`: disjunction, pointwise on fragments.
* `strue`: the assertion that holds of every fragment ("garbage"). The logic of
  `Sep/Spec` is linear (`toFrag` is total, so a postcondition accounts for every location its
  precondition owned); a leaking function says `∗ strue` in its postcondition.

The laws are in `Sep/Extra/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.X86.Sep

/-- Disjunction. -/
def sor (P Q : SProp) : SProp := fun h => P h ∨ Q h

/-- The assertion that holds of every fragment: owned locations that are dropped. -/
def strue : SProp := fun _ => True

end Silmaril.X86.Sep
