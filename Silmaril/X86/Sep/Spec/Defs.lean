module

public import Silmaril.X86.Sep.Defs
public import Silmaril.X86.SegVC

/-!
# Total triples over any segment-VC machine, with the frame built in

`Triple I P Q` is Myreen's `SPEC` with the frame quantified inside, over a machine
`I : SegVC.Isa σ` (`Open.isa`, `Open9.isa`, `Str9.isa`, or a machine with more state): for
**every** frame assertion `F` and every live state whose fragment `frag I s` splits as
`P ∗ F`, the machine reaches a state whose fragment splits as `Q ∗ F`. Because `F` is
arbitrary (it may pin every location it owns to its current value), a triple promises that
every location outside `P`'s fragment is unchanged. It is a total-correctness statement: the
run is finite. It is over the same `Silmaril.Machine.Execution.Reaches` that `SegVC.sound`
concludes and that `Silmaril.X86.FnContract` uses. Like `FnContract.Spec.Total` it is
angelic: it promises some reachable state, not the first one.

* `frag I s`: the fragment of a state, `toFrag` of its core and memory. A machine with more
  state than core and memory (an XMM file, for instance) keeps the rest out of the logic: a
  triple says nothing about it.
* `SPEC I C P Q` is `Triple I (C ∗ P) (C ∗ Q)`: the code assertion `C` (normally `codePt`)
  is owned by the triple and returned unchanged, as Myreen's code pool. Self-modifying code
  is excluded because `C` is precise and is in both the pre- and postcondition.
* `Flat I`: the state of `I` is exactly its core and memory (`upd` with a state's own core
  and memory gives that state). True of `Open.isa`, `Open9.isa` and `Str9.isa`; needed only
  to turn triples into `FnContract`s, whose result states must be `silent`.

The FS base is not a location, so triples say nothing about it. The rules, and the transfer
`Triple.lift` along a machine extension (`SegVC.Isa.Extends`), are in `Sep/Spec/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.X86.Sep

open Silmaril.X86 (MState)
open Silmaril.X86.SegVC (Isa)
open Silmaril.Machine.Execution (Reaches)

variable {σ : Type}

/-- The fragment of a state of the machine `I`: the total fragment of its core and memory. -/
def frag (I : Isa σ) (s : σ) : Frag := toFrag ⟨I.core s, I.mem s⟩

/-- **A total triple** on the machine `I`, frame built in. -/
def Triple (I : Isa σ) (P Q : SProp) : Prop :=
  ∀ (F : SProp) (s : σ), I.live s → (P ∗ F) (frag I s) →
    ∃ t, Reaches I.step s t ∧ (Q ∗ F) (frag I t)

/-- **Myreen's `SPEC`**: a triple for code `C`, which it returns unchanged. -/
def SPEC (I : Isa σ) (C P Q : SProp) : Prop := Triple I (C ∗ P) (C ∗ Q)

/-- The state of `I` is exactly its core and memory. -/
def Flat (I : Isa σ) : Prop := ∀ s t, I.upd s (I.core t) (I.mem t) = t

end Silmaril.X86.Sep
