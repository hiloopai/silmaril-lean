module

public import Silmaril.X86.Concurrency.Cir.Prim.Clients.Defs

/-!
# The primitives: the Boolean checks, by kernel evaluation

One `decide +kernel` per fact:

* the eight translation-validation certificates check against the pinned bytes;
* the explorer's checks on the five clients.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Prim

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Prim
open Silmaril.X86.Concurrency.Cir.Prim.Clients
open Silmaril.X86.Concurrency.Cir.Robust
open Silmaril.X86.Concurrency.Cir.TvCfg (tvCfg)

/-! ## Translation validation -/

theorem tv_spinLock : tvCfg (thr Code.spinLock) SpinLock.cert = true := by decide +kernel
theorem tv_spinUnlock : tvCfg (thr Code.spinUnlock) SpinUnlock.cert = true := by decide +kernel
theorem tv_ticketLock : tvCfg (thr Code.ticketLock) TicketLock.cert = true := by decide +kernel
theorem tv_ticketUnlock : tvCfg (thr Code.ticketUnlock) TicketUnlock.cert = true := by
  decide +kernel
theorem tv_seqWrite : tvCfg (thr Code.seqWrite) SeqWrite.cert = true := by decide +kernel
theorem tv_seqRead : tvCfg (thr Code.seqRead) SeqRead.cert = true := by decide +kernel
theorem tv_spscPush : tvCfg (thr Code.spscPush) SpscPush.cert = true := by decide +kernel
theorem tv_spscPop : tvCfg (thr Code.spscPop) SpscPop.cert = true := by decide +kernel

/-! ## The explorer on the clients -/

set_option maxRecDepth 100000

theorem spin_count : tsoCheck 2 fuel spinC countIs2 = true := by decide +kernel
theorem spin_robust : robustB 2 fuel fuel spinC = true := by decide +kernel
theorem tick_count : tsoCheck 2 fuel tickC countIs2 = true := by decide +kernel
theorem tick_robust : robustB 2 fuel fuel tickC = true := by decide +kernel
theorem seq_snapshot : tsoCheck 2 fuel seqC snapshotOk = true := by decide +kernel
theorem seq_robust : robustB 2 fuel fuel seqC = true := by decide +kernel
theorem torn_witness :
    ((tsoStates 2 fuel tornC).any fun c => c.doneB 2 && c.drainedB && !snapshotOk c) = true := by
  decide +kernel
theorem spsc_fifo : tsoCheck 2 fuel spscC fifoOk = true := by decide +kernel
theorem spsc_sc : scCheck 2 fuel spscC (fun c => !sbOutcome c) = true := by decide +kernel
theorem spsc_witness :
    ((tsoStates 2 fuel spscC).any fun c => c.doneB 2 && c.drainedB && sbOutcome c) = true := by
  decide +kernel
theorem spsc_not_robust : robustB 2 fuel fuel spscC = false := by decide +kernel

end Silmaril.Proofs.X86.Concurrency.Cir.Prim
