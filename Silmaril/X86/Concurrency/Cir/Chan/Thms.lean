module

public import Silmaril.X86.Concurrency.Cir.Chan.Defs
public import Silmaril.X86.Concurrency.Cir.Refute.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.Chan
import Silmaril.Proofs.X86.Concurrency.Cir.Chan.Spin

/-!
# Channels on CIR: what is proved

PROVED (standard axioms only; the kernel checks are in
`Silmaril/Proofs/X86/Concurrency/Cir/Chan.lean`), for spin bound `0` and the domain
`[0, 1, 2, 3]`, under each of SC, TSO and XL:

* `mailbox_in_order`, `ring_in_order`: **every behaviour** of the mailbox and of the ring
  ends with the consumer's results `r1, r2, r3 = 1, 2, 3`: exactly the sent values, in order,
  no stale or future payload;
* `mailbox_some`, `ring_some`: some behaviour exists (it is that one), so the safety statements
  are not vacuous;
* `mailbox_swapped_stale`, `ring_swapped_stale`: with the producer's payload and control stores
  **swapped**, the consumer can receive the initial payload `0` as its first message;
* `mailbox_uniform`, `ring_uniform`: the programs are uniform (no tearing), and
  `mailbox_modes`, `ring_modes`: the payload accesses are `na` and the control accesses
  `acq`/`rel`.

PROVED (`Silmaril/Proofs/X86/Concurrency/Cir/Chan/Spin.lean`): `spinRetry_holds`,
spin retries add no behaviour (`Task.spinRetry`: in a uniform program whose loops are spins,
every behaviour with spin bound `n` is one with bound `0`, under SC, TSO and XL). Hence
`mailbox_in_order_all`, `ring_in_order_all`: the same in-order delivery **for every spin bound
`n`**, unconditionally.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Chan

open Silmaril.X86.Concurrency.Cir.Refute
open Silmaril.X86.MemoryModel.Litmus (Model Final)
open Silmaril.Proofs.X86.Concurrency.Cir.Chan in
/-- **The mailbox delivers `1, 2, 3` in order**, under SC, TSO and XL (spin bound `0`). -/
theorem mailbox_in_order (M : Model) {f : Final} (hf : BehavIn (Mailbox.prog 0) dom M.Holds f) :
    (inOrder r1 r2 r3).eval f = true :=
  behavIn_safe mailbox_safe M hf

open Silmaril.Proofs.X86.Concurrency.Cir.Chan in
/-- **The ring delivers `1, 2, 3` in order**, under SC, TSO and XL (spin bound `0`). -/
theorem ring_in_order (M : Model) {f : Final} (hf : BehavIn (Ring.prog 0) dom M.Holds f) :
    (inOrder Ring.q1 Ring.q2 Ring.q3).eval f = true :=
  behavIn_safe ring_safe M hf

open Silmaril.Proofs.X86.Concurrency.Cir.Chan in
/-- The mailbox has a behaviour under every model. -/
theorem mailbox_some (M : Model) :
    ∃ f, BehavIn (Mailbox.prog 0) dom M.Holds f ∧ (inOrder r1 r2 r3).eval f = true :=
  witnessAuto_model mailbox_good M

open Silmaril.Proofs.X86.Concurrency.Cir.Chan in
/-- The ring has a behaviour under every model. -/
theorem ring_some (M : Model) :
    ∃ f, BehavIn (Ring.prog 0) dom M.Holds f ∧ (inOrder Ring.q1 Ring.q2 Ring.q3).eval f = true :=
  witnessAuto_model ring_good M

open Silmaril.Proofs.X86.Concurrency.Cir.Chan in
/-- **Mutant**: with the payload and `seq` stores swapped, the first message can be stale. -/
theorem mailbox_swapped_stale (M : Model) :
    ∃ f, BehavIn (Mailbox.prog 0 true) dom M.Holds f ∧ (staleFirst r1).eval f = true :=
  witnessAuto_model mailbox_stale M

open Silmaril.Proofs.X86.Concurrency.Cir.Chan in
/-- **Mutant**: with the slot and `tail` stores swapped, the first message can be stale. -/
theorem ring_swapped_stale (M : Model) :
    ∃ f, BehavIn (Ring.prog 0 true) dom M.Holds f ∧ (staleFirst Ring.q1).eval f = true :=
  witnessAuto_model ring_stale M

open Silmaril.Proofs.X86.Concurrency.Cir.Chan in
theorem mailbox_uniform : (Mailbox.prog 0).uniformB = true ∧ (Mailbox.prog 0 true).uniformB = true :=
  Silmaril.Proofs.X86.Concurrency.Cir.Chan.mailbox_uniform

theorem ring_uniform : (Ring.prog 0).uniformB = true ∧ (Ring.prog 0 true).uniformB = true :=
  Silmaril.Proofs.X86.Concurrency.Cir.Chan.ring_uniform

theorem mailbox_modes : modesOk (Mailbox.prog 0) [Mailbox.data] [Mailbox.seq, Mailbox.ack] = true :=
  Silmaril.Proofs.X86.Concurrency.Cir.Chan.mailbox_modes

theorem ring_modes : modesOk (Ring.prog 0) [Ring.s0, Ring.s1] [Ring.tail, Ring.head] = true :=
  Silmaril.Proofs.X86.Concurrency.Cir.Chan.ring_modes

open Silmaril.Proofs.X86.Concurrency.Cir.Chan in
/-- **Checker regression**: `safeCheck` proves MP's TSO/XL-forbidden outcome absent,
so under every model MP's reader never sees the flag without the data. -/
theorem mp_safe (M : Model) {f : Final} (hf : BehavIn Checks.mp [0, 1] M.Holds f) :
    Checks.mpOk.eval f = true :=
  behavIn_safe Silmaril.Proofs.X86.Concurrency.Cir.Chan.mp_safe M hf

/-- **Checker regression**: `safeCheck` does not claim SB's weak outcome absent; it is
allowed under TSO and XL, so a checker that refuted it would be unsound. -/
theorem sb_unrefuted :
    safeCheck Checks.sb.memTest (Checks.sb.traces [0, 1]) Checks.sbSc = false :=
  Silmaril.Proofs.X86.Concurrency.Cir.Chan.sb_unrefuted

/-- The mailbox with bound `n` is the bound-`0` mailbox with every loop bound set to `n`. -/
theorem mailbox_withBound (n : Nat) (sw : Bool) : Mailbox.prog n sw = boundProg (Mailbox.prog 0 sw) n := by
  cases sw <;> rfl

/-- The ring with bound `n` is the bound-`0` ring with every loop bound set to `n`. -/
theorem ring_withBound (n : Nat) (sw : Bool) : Ring.prog n sw = boundProg (Ring.prog 0 sw) n := by
  cases sw <;> rfl

theorem mailbox_spins : ((Mailbox.prog 0).threads.all fun th => spinsOnly th.body) = true := by
  decide

theorem ring_spins : ((Ring.prog 0).threads.all fun th => spinsOnly th.body) = true := by
  decide

/-- **Spin retries add no behaviour**: the failed reads of a spin are plain loads
with a kept twin (its last read), and dropping them keeps every SC/TSO/XL candidate execution
(`Proofs.Machine.Concurrency.Cir.Chan.Spin.spinRetry`). -/
theorem spinRetry_holds : Task.spinRetry := Silmaril.Proofs.X86.Concurrency.Cir.Chan.Spin.spinRetry

/-- **Every spin bound**: the mailbox delivers `1, 2, 3`, under SC, TSO and XL. -/
theorem mailbox_in_order_all (n : Nat) (M : Model) {f : Final}
    (hf : BehavIn (Mailbox.prog n) dom M.Holds f) : (inOrder r1 r2 r3).eval f = true := by
  rw [mailbox_withBound n false] at hf
  have h0 : boundProg (Mailbox.prog 0) 0 = Mailbox.prog 0 := (mailbox_withBound 0 false).symm
  exact mailbox_in_order M (h0 ▸ spinRetry_holds _ mailbox_uniform.1 mailbox_spins n dom M f hf)

/-- **Every spin bound**: the ring delivers `1, 2, 3`, under SC, TSO and XL. -/
theorem ring_in_order_all (n : Nat) (M : Model) {f : Final}
    (hf : BehavIn (Ring.prog n) dom M.Holds f) : (inOrder Ring.q1 Ring.q2 Ring.q3).eval f = true := by
  rw [ring_withBound n false] at hf
  have h0 : boundProg (Ring.prog 0) 0 = Ring.prog 0 := (ring_withBound 0 false).symm
  exact ring_in_order M (h0 ▸ spinRetry_holds _ ring_uniform.1 ring_spins n dom M f hf)

end Silmaril.X86.Concurrency.Cir.Chan
