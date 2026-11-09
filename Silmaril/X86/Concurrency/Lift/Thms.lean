module

public import Silmaril.X86.Concurrency.Lift.Defs
public import Silmaril.X86.Concurrency.Cir.Seq.Thms
import Silmaril.Proofs.X86.Concurrency.Lift
import Silmaril.Proofs.X86.Concurrency.Lift.Flat

/-!
# The single-threaded lift for sequential machines and function contracts: what is proved

Proofs in `Silmaril/Proofs/X86/Concurrency/Lift.lean`.

PROVED (standard axioms):

* `runUnder_of_reaches`: every run of a flat-evented machine (`FlatStep`) **reads the same under
  every `SC ⊑ M ⊑ XL`**: its event trace, as one thread under `M`, has the run's final memory as
  its only behaviour (from `Cir.Seq.oneSem_iff`, step by step);
* `totalUnder_of`: a total function contract on a flat-evented machine is **total under every
  `SC ⊑ M ⊑ XL`** (`Spec.TotalUnder`).

* **`openFlatStep : Task.openFlatStep`** and **`open9FlatStep : Task.open9FlatStep`** (proofs
  in `Silmaril/Proofs/X86/Concurrency/Lift/Flat.lean`): the memory-event glue. Every `Open` /
  `Open9` step has `ActOk` actions with exactly the access list of its instruction, replaying
  sequentially from the flat pre-memory to the flat post-memory. Generic in the access list:
  `Patched` (`MemEvent.open_step_sc`) plus the fact that every access list of these
  machines reads before it writes (`Flat.ext9_good`).

So every total contract on `Open.isa` or `Open9.isa` is total under every `SC ⊑ M ⊑ XL`
(`totalUnder_of` with `openFlatStep` or `open9FlatStep`).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Lift

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Seq
open Silmaril.X86.MemoryModel.Litmus (XAct)
open Silmaril.X86.MemoryModel.Axiomatic (Exec)


variable {σ : Type} {step : σ → Option σ} {mem : σ → Cir.Mem} {P : σ → List XAct → Prop}

/-- A run of a flat-evented machine has an event trace. -/
theorem evRun_of_reaches (hF : FlatStep step mem P) {s t : σ}
    (h : Silmaril.Machine.Execution.Reaches step s t) : ∃ acts, EvRun step mem P s t acts :=
  Silmaril.Proofs.X86.Concurrency.Lift.evRun_of_reaches hF h

/-- The event trace of a run replays sequentially from its first memory to its last. -/
theorem evRun_replay {s t : σ} {acts : List XAct} (h : EvRun step mem P s t acts) :
    (∀ a ∈ acts, ActOk a) ∧ actsReplay (mem s) acts = some (mem t) :=
  Silmaril.Proofs.X86.Concurrency.Lift.evRun_replay h

/-- **A run of a flat-evented machine reads the same under every `SC ⊑ M ⊑ XL`.** -/
theorem runUnder_of_reaches (hF : FlatStep step mem P) {M : Exec → Prop} (hsc : Exec.Sc ⊑ M)
    (hxl : M ⊑ Exec.Xl) {s t : σ} (h : Silmaril.Machine.Execution.Reaches step s t) :
    RunUnder M step mem P s t :=
  Silmaril.Proofs.X86.Concurrency.Lift.runUnder_of_reaches hF hsc hxl h

/-- **A total contract on a flat-evented machine is total under every `SC ⊑ M ⊑ XL`.** -/
theorem totalUnder_of {I : Silmaril.X86.SegVC.Isa σ} {S : Silmaril.X86.FnContract.Spec σ}
    (hF : FlatStep I.step (fun s => flat (I.mem s)) P) (hT : S.Total I) {M : Exec → Prop}
    (hsc : Exec.Sc ⊑ M) (hxl : M ⊑ Exec.Xl) : S.TotalUnder I P M :=
  Silmaril.Proofs.X86.Concurrency.Lift.totalUnder_of hF hT hsc hxl

/-- **Memory-event glue for `Open`** (PROVED): every `Open.step` has `ActOk` actions with exactly the
access list of its instruction, replaying sequentially to the step's memory. -/
theorem openFlatStep : Task.openFlatStep :=
  Silmaril.Proofs.X86.Concurrency.Lift.Flat.openFlatStep

/-- **Memory-event glue for `Open9`** (PROVED). -/
theorem open9FlatStep : Task.open9FlatStep :=
  Silmaril.Proofs.X86.Concurrency.Lift.Flat.open9FlatStep

end Silmaril.X86.Concurrency.Lift
