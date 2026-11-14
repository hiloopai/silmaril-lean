module

public import Silmaril.X86.Concurrency.Story.Pipe.Defs
public import Silmaril.X86.Concurrency.Cir.Robust.Thms
public import Silmaril.X86.Concurrency.Cir.Mutex.Thms
public import Silmaril.X86.Concurrency.Cir.Mutex.Futex.Thms

/-!
# Proofs: the pipeline instance finishes (non-vacuity)

`pipeC` is the pipeline for `vs = [5]` (spin bound 2) linked with the ticket lock (loop bound
2) as a configuration of the explorer (`pipeC_cfg`). The explorer finds a finished, drained TSO
state with `out 0 = 5` and `acc = 6` (`pipe_fin`), so the hypotheses of `Pipe.pipe_ticket` are
met by a real run. One kernel evaluation, about 17 s.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Story.Pipe

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Robust
open Silmaril.X86.Concurrency.Cir.Mutex
open Silmaril.X86.Concurrency.Story.Pipe

/-- The ticket lock's derived ops at loop bound 2. -/
def tlk : Expr → Stmt := Inst.call (Prim.TicketLock.cert.body 2)
/-- The ticket unlock's derived op at loop bound 2. -/
def tul : Expr → Stmt := Inst.call (Prim.TicketUnlock.cert.body 2)

/-- The cells of the instance: the client's and the ticket lock's two words. -/
def wcells : List (Nat × Nat) :=
  [(cseq, 0), (cack, 0), (cdat, 0), (acc, 0), (r0, 0), (r1, 0), (pP, 0), (pC, 0), (sm, 0),
   (out 0, 0), (m, 0), (m + 4, 0)]

/-- **The pipeline for `[5]` linked with the ticket lock**, as an explorer configuration. -/
def pipeC : CSt :=
  start [(body [5] 2 tlk tul 0, Regs.zero), (body [5] 2 tlk tul 1, Regs.zero)] wcells

/-- The expected outputs: `acc = 1 + 5`, `out 0 = 5`. -/
def outsOk (c : CSt) : Bool := memOf c.mem acc == some 6 && memOf c.mem (out 0) == some 5

set_option maxRecDepth 100000 in
theorem pipe_fin : (tsoStates 2 Prim.Clients.fuel pipeC).any
    (fun c => c.doneB 2 && c.drainedB && outsOk c) = true := by decide +kernel

theorem rget_rlist (rs : Regs) : rget (rlist rs) = rs := by
  funext r; cases r <;> rfl

theorem memOf_cons (p : Nat × Nat) (l : List (Nat × Nat)) (a : Nat) :
    memOf (p :: l) a = if p.1 = a then some p.2 else memOf l a := by
  simp only [memOf, List.find?_cons]
  split <;> simp_all

theorem memOf_nil (a : Nat) : memOf [] a = none := rfl

theorem pipeC_mem (a : Nat) :
    memOf wcells a =
      Heap.union (mem [5].length) (Heap.union (ticketMutexG.init m) Heap.empty) a := by
  by_cases hS : a = cseq ∨ a = cack ∨ a = cdat ∨ a = acc ∨ a = r0 ∨ a = r1 ∨ a = pP ∨ a = pC ∨
      a = sm ∨ a = out 0 ∨ a = m ∨ a = m + 4
  · rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [not_or] at hS
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hS
    have e1 : memOf wcells a = none := by
      simp [wcells, memOf_cons, memOf_nil, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4,
        Ne.symm h5, Ne.symm h6, Ne.symm h7, Ne.symm h8, Ne.symm h9, Ne.symm h10, Ne.symm h11,
        Ne.symm h12]
    rw [e1]
    have hT : ¬ (a = cseq ∨ a = cack ∨ a = cdat ∨ a = acc ∨ a = r0 ∨ a = r1 ∨ a = pP ∨ a = pC ∨
        a = sm ∨ isOut [5].length a) := by
      simp only [isOut, out, ob, List.length_singleton] at h10 ⊢; omega
    show none = Heap.union (mem [5].length)
      (Heap.union (Heap.union (Heap.single m 0) (Heap.single (m + 4) 0)) Heap.empty) a
    simp only [Heap.union, Silmaril.X86.Sep.BI.SepAlg.pmapUnion, mem, hT, ite_false,
      Heap.single, h11, h12, Heap.empty]

theorem pipeC_th : pipeC.th = fun t =>
    (if t < 2 then body [5] 2 (ticketMutexG.lock 2) (ticketMutexG.unlock 2) t else .skip,
      Regs.zero) := by
  funext t
  rcases t with _ | _ | t <;> simp [CSt.th, start, pipeC, rget_rlist] <;> rfl

/-- **The explorer instance is the linked pipeline.** -/
theorem pipeC_cfg : pipeC.cfg = (client [5] 2).linkG ticketMutexG 2 := by
  simp only [CSt.cfg, Client.linkG, Client.startWith]
  congr 1
  · rw [pipeC_th]; rfl
  · funext a; exact pipeC_mem a

/-! ## Two messages

The same for `vs = [3, 4]`: two messages through the channel, so the run exercises the
stop-and-wait handshake (the second send waits for the first acknowledgement) and the ordering
of `out 0`, `out 1`. One kernel evaluation, about 20 s. -/

/-- The cells of the two-message instance. -/
def wcells2 : List (Nat × Nat) :=
  [(cseq, 0), (cack, 0), (cdat, 0), (acc, 0), (r0, 0), (r1, 0), (pP, 0), (pC, 0), (sm, 0),
   (out 0, 0), (out 1, 0), (m, 0), (m + 4, 0)]

/-- **The pipeline for `[3, 4]` linked with the ticket lock**, as an explorer configuration. -/
def pipeC2 : CSt :=
  start [(body [3, 4] 2 tlk tul 0, Regs.zero), (body [3, 4] 2 tlk tul 1, Regs.zero)] wcells2

/-- The expected outputs: `acc = 2 + 3 + 4`, `out 0 = 3`, `out 1 = 4`. -/
def outsOk2 (c : CSt) : Bool :=
  memOf c.mem acc == some 9 && memOf c.mem (out 0) == some 3 && memOf c.mem (out 1) == some 4

set_option maxRecDepth 100000 in
theorem pipe_fin2 : (tsoStates 2 Prim.Clients.fuel pipeC2).any
    (fun c => c.doneB 2 && c.drainedB && outsOk2 c) = true := by decide +kernel

theorem pipeC2_mem (a : Nat) :
    memOf wcells2 a =
      Heap.union (mem [3, 4].length) (Heap.union (ticketMutexG.init m) Heap.empty) a := by
  by_cases hS : a = cseq ∨ a = cack ∨ a = cdat ∨ a = acc ∨ a = r0 ∨ a = r1 ∨ a = pP ∨ a = pC ∨
      a = sm ∨ a = out 0 ∨ a = out 1 ∨ a = m ∨ a = m + 4
  · rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  · simp only [not_or] at hS
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h10', h11, h12⟩ := hS
    have e1 : memOf wcells2 a = none := by
      simp [wcells2, memOf_cons, memOf_nil, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4,
        Ne.symm h5, Ne.symm h6, Ne.symm h7, Ne.symm h8, Ne.symm h9, Ne.symm h10, Ne.symm h10',
        Ne.symm h11, Ne.symm h12]
    rw [e1]
    have hT : ¬ (a = cseq ∨ a = cack ∨ a = cdat ∨ a = acc ∨ a = r0 ∨ a = r1 ∨ a = pP ∨ a = pC ∨
        a = sm ∨ isOut [3, 4].length a) := by
      simp only [isOut, out, ob, List.length_cons, List.length_nil] at h10 h10' ⊢; omega
    show none = Heap.union (mem [3, 4].length)
      (Heap.union (Heap.union (Heap.single m 0) (Heap.single (m + 4) 0)) Heap.empty) a
    simp only [Heap.union, Silmaril.X86.Sep.BI.SepAlg.pmapUnion, mem, hT, ite_false,
      Heap.single, h11, h12, Heap.empty]

theorem pipeC2_th : pipeC2.th = fun t =>
    (if t < 2 then body [3, 4] 2 (ticketMutexG.lock 2) (ticketMutexG.unlock 2) t else .skip,
      Regs.zero) := by
  funext t
  rcases t with _ | _ | t <;> simp [CSt.th, start, pipeC2, rget_rlist] <;> rfl

/-- **The two-message explorer instance is the linked pipeline.** -/
theorem pipeC2_cfg : pipeC2.cfg = (client [3, 4] 2).linkG ticketMutexG 2 := by
  simp only [CSt.cfg, Client.linkG, Client.startWith]
  congr 1
  · rw [pipeC2_th]; rfl
  · funext a; exact pipeC2_mem a

end Silmaril.Proofs.X86.Concurrency.Story.Pipe
