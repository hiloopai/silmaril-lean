module

public import Silmaril.Machine.X86.Sep.Defs
public import Silmaril.Machine.X86.Open.Defs

/-!
# Total triples over the open machine, with the frame built in

`Triple P Q` is Myreen's `SPEC` with the frame quantified inside: for **every** frame
assertion `F` and every machine state whose total fragment splits as `P ∗ F`, the open machine
(`Silmaril.Machine.X86.Open.step`, where `ret` is an ordinary pop and jump) reaches a state whose
total fragment splits as `Q ∗ F`. Because `F` is arbitrary (it may pin every location it owns
to its current value), a triple promises that every location outside `P`'s fragment is
unchanged. It is a total-correctness statement: the run is finite. It is over the same
`Silmaril.Machine.Execution.Reaches` that `SegVC.sound` concludes and that
`Silmaril.Machine.X86.FnContract` uses.

`SPEC C P Q` is `Triple (C ∗ P) (C ∗ Q)`: the code assertion `C` (normally `codePt`) is
owned by the triple and returned unchanged, as Myreen's code pool. Self-modifying code is
excluded because `C` is precise and is in both the pre- and postcondition.

The FS base is not a location, so triples say nothing about it.
-/

@[expose] public section

namespace Silmaril.Machine.X86.Sep

open Silmaril.X86 (MState)
open Silmaril.Machine.Execution (Reaches)

/-- **A total triple** on the open machine, frame built in. -/
def Triple (P Q : SProp) : Prop :=
  ∀ (F : SProp) (m : MState), (P ∗ F) (toFrag m) →
    ∃ m', Reaches Silmaril.Machine.X86.Open.step m m' ∧ (Q ∗ F) (toFrag m')

/-- **Myreen's `SPEC`**: a triple for code `C`, which it returns unchanged. -/
def SPEC (C P Q : SProp) : Prop := Triple (C ∗ P) (C ∗ Q)

end Silmaril.Machine.X86.Sep
