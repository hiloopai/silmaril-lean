module

public import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.Ghost
public import Silmaril.Proofs.X86.Concurrency.Cir.Mutex.Inst

/-!
# Proofs: the ticket-lock instance of `Even` finishes

`Inst.ticketC` is `Even.client` linked with `ticketMutexG` at loop bound 2 (`ticketC_cfg`), and
the explorer finds a finished, drained TSO state of it (`ticket_fin`). With `even_ticket` this
shows that the hypotheses of `even_ticket` (and so of `Task.ticketIface` for `Even`) are met by a
real run (`Mutex.even_ticket_finishes`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Mutex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Mutex
open Silmaril.X86.Concurrency.Cir.Robust

set_option maxRecDepth 100000 in
theorem ticket_fin : (tsoStates 2 Prim.Clients.fuel Inst.ticketC).any
    (fun c => c.doneB 2 && c.drainedB && Inst.evenOuts c) = true := by decide +kernel

theorem ticketC_cfg : Inst.ticketC.cfg = Even.client.linkG ticketMutexG Inst.L := by
  simp only [CSt.cfg, Inst.ticketC, Client.linkG, Client.startWith]
  congr 1
  · rw [start_th]; rfl
  · funext a; exact mem5 a

end Silmaril.Proofs.X86.Concurrency.Cir.Mutex
