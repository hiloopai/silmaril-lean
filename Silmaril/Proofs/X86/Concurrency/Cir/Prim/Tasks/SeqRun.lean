module

public import Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.SpscCex

/-!
# The seqlock client of `Task.seqlockTso` has finished runs (non-vacuity)

For `L = 2`, `s = 0x100`, one write `(1, 1)` and one reader writing to `0x200`: a TSO run from
the Task's start finishes, drains, and the reader returns `(1, 1)`. A schedule of the
enumerated TSO steps (`SpscCex.walk2`), checked by kernel `decide`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.SeqRun

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Prim
open Silmaril.X86.Concurrency.Cir.Prim.Clients
open Silmaril.X86.Concurrency.Cir.Robust
open Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.SpscCex

/-- The writer of `Task.seqlockTso` for `ws = [(1, 1)]`. -/
def wS : Stmt := Tv.chain ([((1 : Nat), (1 : Nat))].map fun p => Tv.chain [.assign .rsi (.lit p.1),
  .assign .rdx (.lit p.2), SeqWrite.cert.body 2])

/-- The cells. -/
def memS : List (Nat × Nat) :=
  [(0x100, 0), (0x100 + 4, 0), (0x100 + 8, 0)] ++ [0x200].flatMap fun o => [(o, 0), (o + 4, 0)]

/-- The concrete start. -/
def cS : CSt := start [(wS, regs [(.rdi, 0x100)]),
  (SeqRead.cert.body 2, regs [(.rdi, 0x100), (.rsi, 0x200)])] memS

/-- The final configuration: the writer runs and flushes, then the reader. -/
def cSF : CSt := walk2 2 cS (eager 0 40 ++ eager 1 60)

set_option maxRecDepth 100000 in
theorem cSF_check : (cSF.doneB 2 && cSF.drainedB && memOf cSF.mem 0x200 == some 1 &&
    memOf cSF.mem 0x204 == some 1) = true := by
  decide +kernel

/-- **A finished run of the seqlock client**: the reader returns the written pair `(1, 1)`. -/
theorem seqlock_finishes : ∃ C : OCfg, OReach .tso 2 (⟨fun t =>
      if t = 0 then (wS, regs [(.rdi, 0x100)])
      else if t < 2 then (SeqRead.cert.body 2, regs [(.rdi, 0x100), (.rsi, [0x200].getD (t - 1) 0)])
      else (.skip, Regs.zero), heapOf memS Heap.empty⟩ : Cfg).toO C ∧ C.Drained ∧
    (∀ t < 2, (C.ts t).1 = .skip) ∧ C.mem 0x200 = some 1 ∧ C.mem 0x204 = some 1 := by
  have hc := cSF_check
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨hdone, hdr⟩, h0⟩, h1⟩ := hc
  have hstart : cS.cfg.toO = cS.ocfg := start_toO (by decide)
  have hth : cS.th = fun t =>
      if t = 0 then (wS, regs [(.rdi, 0x100)])
      else if t < 2 then (SeqRead.cert.body 2, regs [(.rdi, 0x100), (.rsi, [0x200].getD (t - 1) 0)])
      else (.skip, Regs.zero) := by
    funext t
    rcases t with _ | _ | t <;>
      simp only [CSt.th, cS, start, List.map_cons, List.map_nil, List.getElem?_cons_zero,
        List.getElem?_cons_succ, List.getElem?_nil, rget_rlist] <;> simp
  have hmem : memOf cS.mem = heapOf memS Heap.empty := by
    funext a
    simp only [memOf, heapOf, cS, start, Heap.empty, Option.or_none]
  have hcfg : cS.cfg = ⟨fun t =>
      if t = 0 then (wS, regs [(.rdi, 0x100)])
      else if t < 2 then (SeqRead.cert.body 2, regs [(.rdi, 0x100), (.rsi, [0x200].getD (t - 1) 0)])
      else (.skip, Regs.zero), heapOf memS Heap.empty⟩ := by
    show (⟨cS.th, memOf cS.mem⟩ : Cfg) = _
    rw [hth, hmem]
  have hr : OReach .tso 2 cS.cfg.toO cSF.ocfg := by rw [hstart]; exact walk2_reach _ cS
  rw [hcfg] at hr
  have e : cSF.ocfg.mem = memOf cSF.mem := ocfg_mem cSF
  refine ⟨cSF.ocfg, hr, fun t => ?_, fun t ht => ?_, ?_⟩
  rotate_left 2
  · rw [e]; exact ⟨h0, h1⟩
  · simp only [CSt.drainedB, List.all_eq_true] at hdr
    simp only [CSt.ocfg, List.getD_eq_getElem?_getD]
    cases ht : cSF.buf[t]? with
    | none => rfl
    | some b => simpa using hdr b (List.mem_of_getElem? ht)
  · simp only [CSt.doneB, List.all_eq_true, List.mem_range] at hdone
    exact TvCfg.sbeq_eq (hdone t ht)

end Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.SeqRun
