module

public import Silmaril.Compiler.C.Sem.RenameDefs.Defs
@[expose] public section

/-!
# The renamer targets (frozen)

`Targets.renumber_certified` (every numbering of `renumber` has a liveness certificate) is
false: a function whose entry label names no block can have two parameters with one new number
(`Compile/Target/RenameCounterexample.lean`). It is replaced by two statements:

* `renumber_checked_refines`: the checked stage `renumberChecked k` (renumber when ccomp's
  checker `checkCert` accepts, otherwise leave the program unchanged) refines the program it
  renumbers, at the identity observation, from start states of the same call;
* `renumber_certified_wf`: every numbering of `renumber` has a liveness certificate on programs
  whose every function's entry label names a block.

`renumberCheckedStats` (`RenameDefs.lean`) counts, over ccomp's Lir for a corpus program, the
functions the checker accepts: `renumber_checked_refines` says nothing about `renumber` on the
functions it rejects.
-/

namespace Silmaril.Compile.Targets

open Silmaril.Machine Silmaril.Machine.Lir Silmaril.Compile.Target.RegAlloc

open Silmaril.Machine.Behaviour (Refines Mode Obs) in
/-- **The checked renumbering refines the program it renumbers**, for every `k`. -/
def renumber_checked_refines : Prop :=
  ∀ (k : Nat) (p : Prog Nat),
    Refines Mode.strict (sem (renumberChecked k p)) (sem p)
      (fun t s => ∃ f args mem, p.start f args mem = some s ∧
        (renumberChecked k p).start f args mem = some t)
      (fun _ _ => Obs.id)

/-- **Every numbering of `renumber` has a liveness certificate** on programs whose functions'
entry labels name blocks. -/
def renumber_certified_wf : Prop :=
  ∀ (k : Nat) (p : Prog Nat), (∀ fn ∈ p.funcs, fn.entry < fn.blocks.length) →
    ∃ live, LiveCert p (renumberσ k p) live

end Silmaril.Compile.Targets
