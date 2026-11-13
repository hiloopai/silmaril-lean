module

public import Silmaril.X86.Concurrency.Cir.Chan.Defs

/-!
# Channels on CIR: the kernel checks

One `decide +kernel` per Boolean check:

* `mailbox_safe`, `ring_safe`: the forced-cycle safety check (`Cir.Refute.safeCheck`) of
  "received `1, 2, 3` in order" for the spin bound `0` (about 20 s and 2 min);
* `*_good`, `*_stale`: explicit SC witnesses for the good outcome (non-vacuity) and, for the
  swapped mutants, for the stale first message;
* `*_uniform`, `*_modes`: the programs are uniform (aligned whole-cell write-back accesses) and
  the payload accesses are `na`, the control accesses `acq`/`rel`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Chan

open Silmaril.X86.Concurrency.Cir Silmaril.X86.Concurrency.Cir.Refute
open Silmaril.X86.Concurrency.Cir.Chan

set_option maxHeartbeats 4000000 in
theorem mailbox_safe :
    safeCheck (Mailbox.prog 0).memTest ((Mailbox.prog 0).traces dom) (inOrder r1 r2 r3) = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem ring_safe :
    safeCheck (Ring.prog 0).memTest ((Ring.prog 0).traces dom)
      (inOrder Ring.q1 Ring.q2 Ring.q3) = true := by
  decide +kernel

theorem mailbox_good :
    witnessAuto (Mailbox.prog 0).memTest ((Mailbox.prog 0).traces dom) [0, 27]
      (inOrder r1 r2 r3) = true := by
  decide +kernel

theorem mailbox_stale :
    witnessAuto (Mailbox.prog 0 true).memTest ((Mailbox.prog 0 true).traces dom) [0, 6]
      (staleFirst r1) = true := by
  decide +kernel

theorem ring_good :
    witnessAuto (Ring.prog 0).memTest ((Ring.prog 0).traces dom) [0, 43]
      (inOrder Ring.q1 Ring.q2 Ring.q3) = true := by
  decide +kernel

theorem ring_stale :
    witnessAuto (Ring.prog 0 true).memTest ((Ring.prog 0 true).traces dom) [0, 1]
      (staleFirst Ring.q1) = true := by
  decide +kernel

theorem mailbox_uniform : (Mailbox.prog 0).uniformB = true ∧ (Mailbox.prog 0 true).uniformB = true := by
  decide +kernel

theorem ring_uniform : (Ring.prog 0).uniformB = true ∧ (Ring.prog 0 true).uniformB = true := by
  decide +kernel

theorem mailbox_modes : modesOk (Mailbox.prog 0) [Mailbox.data] [Mailbox.seq, Mailbox.ack] = true := by
  decide +kernel

theorem ring_modes : modesOk (Ring.prog 0) [Ring.s0, Ring.s1] [Ring.tail, Ring.head] = true := by
  decide +kernel

/-- The checker does not refute SB's weak outcome (it is XL- and TSO-allowed). -/
theorem sb_unrefuted :
    safeCheck Checks.sb.memTest (Checks.sb.traces [0, 1]) Checks.sbSc = false := by
  decide +kernel

/-- The checker refutes MP's weak outcome. -/
theorem mp_safe : safeCheck Checks.mp.memTest (Checks.mp.traces [0, 1]) Checks.mpOk = true := by
  decide +kernel

end Silmaril.Proofs.X86.Concurrency.Cir.Chan
