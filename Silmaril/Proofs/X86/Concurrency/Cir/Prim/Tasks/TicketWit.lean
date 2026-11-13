module

public import Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.Ticket
public import Silmaril.X86.Concurrency.Cir.Robust.Thms

/-!
# Non-vacuity of `Task.ticketMutexTso`

`ticketMutexTso_nonvacuous`: with two threads, an empty critical section, the lock at `0x100`
and loop bound 2, the start of `Task.ticketMutexTso` reaches a finished, drained TSO state (the
explorer, `tkNv_fin`), so the theorem's hypotheses are met by a real run, and there
`next = serving = 2` (by `ticketMutexTso_holds`).

The explorer's start leaves the idle threads `t ≥ 2` as `(skip, 0)`, while `lockCfg` gives them
`rdi = l`; `oreach_trunc` moves a run between the two (idle threads never step).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Robust
open Silmaril.X86.Concurrency.Cir.Prim.Clients

theorem rget_rlist' (rs : Regs) : rget (rlist rs) = rs := by
  funext r; cases r <;> rfl


/-- Replace the idle threads `t ≥ N` by `X`. -/
def idleTrunc (N : Nat) (X : Nat → Stmt × Regs) (C : OCfg) : OCfg :=
  { C with ts := fun t => if t < N then C.ts t else X t }

theorem idleTrunc_upd {N t : Nat} (ht : t < N) (X : Nat → Stmt × Regs) (f : Nat → Stmt × Regs) (x) :
    (fun u => if u < N then upd f t x u else X u) =
      upd (fun u => if u < N then f u else X u) t x := by
  funext u; by_cases h : u = t
  · subst h; simp [upd, ht]
  · simp [upd, h]

theorem ostep_trunc {M : OModel} {N : Nat} (X : Nat → Stmt × Regs) {C C' : OCfg}
    (h : OStep M N C C') : OStep M N (idleTrunc N X C) (idleTrunc N X C') := by
  cases h with
  | tau ht hs =>
    have := OStep.tau (M := M) (C := idleTrunc N X C) ht (by simpa [idleTrunc, ht] using hs)
    simpa [idleTrunc, idleTrunc_upd ht] using this
  | buffered ht hs hm hd hc hok =>
    have := OStep.buffered (M := M) (C := idleTrunc N X C) ht (by simpa [idleTrunc, ht] using hs) hm hd
      hc hok
    simpa [idleTrunc, idleTrunc_upd ht] using this
  | drained ht hs hm hd he hc hok =>
    have := OStep.drained (M := M) (C := idleTrunc N X C) ht (by simpa [idleTrunc, ht] using hs) hm hd
      he hc hok
    simpa [idleTrunc, idleTrunc_upd ht] using this
  | flush ht hb hp hmod =>
    exact OStep.flush (C := idleTrunc N X C) ht hb hp hmod

theorem oreach_trunc {M : OModel} {N : Nat} (X : Nat → Stmt × Regs) {C C' : OCfg}
    (h : OReach M N C C') : OReach M N (idleTrunc N X C) (idleTrunc N X C') := by
  induction h with
  | refl => exact Star.refl
  | step h1 _ ih => exact Star.step (ostep_trunc X h1) ih

/-- Two threads, each `ticket_lock; skip; ticket_unlock` on the lock at `0x100`. -/
def tkNvC : CSt :=
  start [(Tv.chain [Prim.TicketLock.cert.body 2, .skip, Prim.TicketUnlock.cert.body 2], regs [(.rdi, 0x100)]),
      (Tv.chain [Prim.TicketLock.cert.body 2, .skip, Prim.TicketUnlock.cert.body 2], regs [(.rdi, 0x100)])]
    [(0x100, 0), (0x104, 0)]

set_option maxRecDepth 100000 in
theorem tkNv_fin : (tsoStates 2 fuel tkNvC).any
    (fun c => c.doneB 2 && c.drainedB) = true := by decide +kernel

theorem tkNvC_cfg : idleTrunc 2 (fun _ => (.skip, regs [(.rdi, 0x100)])) tkNvC.cfg.toO =
    (lockCfg (Prim.TicketLock.cert.body 2) (Prim.TicketUnlock.cert.body 2) 2 0x100 (fun _ => .skip)
      (heapOf [(0x100, 0), (0x104, 0)] Heap.empty)).toO := by
  simp only [idleTrunc, Cfg.toO, CSt.cfg, lockCfg, OCfg.mk.injEq, and_true]
  constructor
  · funext t
    rcases t with _ | _ | t
    · simp [CSt.th, tkNvC, start, rget_rlist']
    · simp [CSt.th, tkNvC, start, rget_rlist']
    · simp [show ¬ (t + 1 + 1 < 2) by omega]
  · funext a
    simp [memOf, heapOf, Heap.empty, tkNvC, start]

/-- **Non-vacuity of `Task.ticketMutexTso`**: with two threads, an empty critical section and
loop bound 2, the start reaches a finished, drained TSO state, where `next = serving = 2`. -/
theorem ticketMutexTso_nonvacuous : ∃ C : OCfg, OReach .tso 2
      (lockCfg (Prim.TicketLock.cert.body 2) (Prim.TicketUnlock.cert.body 2) 2 0x100 (fun _ => .skip)
        (heapOf [(0x100, 0), (0x104, 0)] Heap.empty)).toO C ∧
    C.Drained ∧ (∀ t < 2, (C.ts t).1 = .skip) ∧ C.mem 0x100 = some 2 ∧ C.mem 0x104 = some 2 := by
  obtain ⟨d, hr, hd, hf, -⟩ := Robust.witness_of_any (N := 2) (c0 := tkNvC) rfl rfl
    (P := fun _ => true) (by simpa using tkNv_fin)
  have hr' := oreach_trunc (fun _ => (.skip, regs [(.rdi, 0x100)])) hr
  rw [tkNvC_cfg] at hr'
  have hd' : (idleTrunc 2 (fun _ => (.skip, regs [(.rdi, 0x100)])) d.ocfg).Drained := hd
  have hf' : ∀ t < 2, ((idleTrunc 2 (fun _ => (.skip, regs [(.rdi, 0x100)])) d.ocfg).ts t).1 = .skip :=
    fun t ht => by simpa [idleTrunc, ht] using hf t ht
  obtain ⟨h1, h2, -⟩ := ticketMutexTso_holds 2 2 0x100 (fun h => h = Heap.empty) Heap.empty
    (fun _ => .skip) (by decide) (by decide) rfl rfl rfl (fun _ => by decide)
    (fun _ _ _ e => by subst e; exact Csl.safe_skip rfl) _ hr' hd' hf'
  exact ⟨_, hr', hd', hf', h1, h2⟩

end Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks
