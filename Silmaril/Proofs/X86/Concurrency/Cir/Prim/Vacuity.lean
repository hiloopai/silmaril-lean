module

public import Silmaril.X86.Concurrency.Cir.Prim.Mutants.Defs

/-!
# The explorer results are not vacuous: the Boolean checks

The final-state statements of `Prim/Thms.lean` quantify over
finished, drained TSO configurations within loop bound `2`; they would hold trivially if no run
finished. These checks (kernel `decide`) list finished witnesses:

* each lock client has a finished state (with the counter `2`);
* the seqlock reader can return the written pair `(1, 1)`, and also the initial `(0, 0)`;
* the SPSC consumer can pop both `1` and `2`;
* the test-then-set mutant of the spinlock loses an increment (counter `1`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Prim

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Prim
open Silmaril.X86.Concurrency.Cir.Prim.Clients
open Silmaril.X86.Concurrency.Cir.Robust

set_option maxRecDepth 100000

/-- Each lock client has a finished, drained state with the counter `2`. -/
theorem spin_fin :
    (tsoStates 2 fuel spinC).any (fun c => c.doneB 2 && c.drainedB && countIs2 c) = true := by
  decide +kernel
theorem tick_fin :
    (tsoStates 2 fuel tickC).any (fun c => c.doneB 2 && c.drainedB && countIs2 c) = true := by
  decide +kernel
/-- The seqlock reader can return the written pair. -/
theorem seq_fin_new :
    (tsoStates 2 fuel seqC).any (fun c => c.doneB 2 && c.drainedB &&
      (memOf c.mem 0x200 == some 1 && memOf c.mem 0x204 == some 1)) = true := by
  decide +kernel
/-- The seqlock reader can return the initial pair. -/
theorem seq_fin_old :
    (tsoStates 2 fuel seqC).any (fun c => c.doneB 2 && c.drainedB &&
      (memOf c.mem 0x200 == some 0 && memOf c.mem 0x204 == some 0)) = true := by
  decide +kernel
/-- The ring can pop `1` and then `2`. -/
theorem spsc_fin_both :
    (tsoStates 2 fuel spscC).any (fun c => c.doneB 2 && c.drainedB &&
      (memOf c.mem 0x200 == some 1 && memOf c.mem 0x204 == some 2)) = true := by
  decide +kernel
/-- The test-then-set mutant loses an increment. -/
theorem tts_lost :
    (tsoStates 2 fuel Mutants.ttsC).any (fun c => c.doneB 2 && c.drainedB &&
      memOf c.mem 0x200 == some 1) = true := by
  decide +kernel

end Silmaril.Proofs.X86.Concurrency.Cir.Prim
