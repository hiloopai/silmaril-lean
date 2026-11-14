module

public import Silmaril.X86.Concurrency.Cir.Prim.Tasks.Defs
public import Silmaril.X86.Concurrency.Cir.Robust.Thms
public import Silmaril.X86.Concurrency.Cir.TvCfg.Thms

/-!
# The SPSC goal is false (`spscFifoTsoPrim`)

`spsc_push` drops its value when the ring is full, so the successfully pushed values are a
subsequence of the pushed list, not a prefix. With `vs = [1, 2, 3, 4]` and `k = 3` pops, the
schedule "producer pushes `1`, `2` and fails on `3`; consumer pops `1`; producer pushes `4`;
consumer pops `2` and `4`", with every store flushed at once (so the run is even sequentially
consistent), ends with the outputs `[1, 2, 4]`. The run is a schedule of the enumerated TSO
steps (`walk2`, sound by `Robust.tsoStepT_sound`), checked by kernel `decide`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.SpscCex

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Prim
open Silmaril.X86.Concurrency.Cir.Prim.Clients
open Silmaril.X86.Concurrency.Cir.Robust

/-- The pushed values. -/
def vsX : List Nat := [1, 2, 3, 4]

/-- The producer of `spscFifoTsoPrim` for `vsX`, loop bound `2`. -/
def prodX : Stmt :=
  Tv.chain (vsX.map fun v => Tv.chain [.assign .rsi (.lit v), SpscPush.cert.body 2])

/-- The consumer: three pops into `0x200`, `0x204`, `0x208`. -/
def consX : Stmt := Tv.chain ((List.range 3).map fun i =>
  Tv.chain [.assign .rsi (.lit (0x200 + 4 * i)), SpscPop.cert.body 2])

/-- The cells: the ring at `0x100` and the outputs. -/
def memX : List (Nat × Nat) :=
  [(0x100, 0), (0x104, 0), (0x108, 0), (0x10c, 0)] ++ (List.range 3).map fun i => (0x200 + 4 * i, 0)

/-- The concrete start. -/
def cX : CSt := start [(prodX, regs [(.rdi, 0x100)]), (consX, regs [(.rdi, 0x100)])] memX

/-- One scheduled step: `(t, false)` takes thread `t`'s first enumerated TSO successor (a thread
step when it has one), `(t, true)` flushes `t`'s oldest store (if any). -/
def wstep (N : Nat) (c : CSt) (p : Nat × Bool) : CSt :=
  if p.1 < N ∧ p.1 < c.buf.length then
    if p.2 then (if (c.bufT p.1).isEmpty then c else (tsoStepT c p.1).getLast?.getD c)
    else (tsoStepT c p.1).head?.getD c
  else c

/-- Follow a schedule. -/
def walk2 (N : Nat) (c : CSt) : List (Nat × Bool) → CSt
  | [] => c
  | p :: ps => walk2 N (wstep N c p) ps

/-- `n` steps of thread `t`, each followed by a flush. -/
def eager (t n : Nat) : List (Nat × Bool) := (List.replicate n [(t, false), (t, true)]).flatten

/-- The schedule of the counterexample. -/
def schedX : List (Nat × Bool) := eager 0 80 ++ eager 1 30 ++ eager 0 200 ++ eager 1 200

/-- The final configuration. -/
def cF : CSt := walk2 2 cX schedX

theorem wstep_reach {N : Nat} (c : CSt) (p : Nat × Bool) :
    OReach .tso N c.ocfg (wstep N c p).ocfg := by
  simp only [wstep]
  split
  · rename_i h
    split
    · split
      · exact .refl
      · cases hc : (tsoStepT c p.1).getLast? with
        | none => exact .refl
        | some e => exact .step (tsoStepT_sound h.1 h.2 (List.mem_of_getLast? hc)) .refl
    · cases hc : (tsoStepT c p.1).head? with
      | none => exact .refl
      | some e => exact .step (tsoStepT_sound h.1 h.2 (List.mem_of_mem_head? hc)) .refl
  · exact .refl

theorem star_trans {α : Type} {r : α → α → Prop} {a b c : α} (h₁ : Star r a b)
    (h₂ : Star r b c) : Star r a c := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)

theorem walk2_reach {N : Nat} : ∀ (l : List (Nat × Bool)) (c : CSt),
    OReach .tso N c.ocfg (walk2 N c l).ocfg
  | [], _ => .refl
  | p :: ps, c => star_trans (wstep_reach c p) (walk2_reach ps _)

set_option maxRecDepth 100000 in
/-- The run finishes, drains, and outputs `[1, 2, 4]`. -/
theorem cF_check : (cF.doneB 2 && cF.drainedB && memOf cF.mem 0x200 == some 1 &&
    memOf cF.mem 0x204 == some 2 && memOf cF.mem 0x208 == some 4 && cF.buf.length == 2) = true := by
  decide +kernel

theorem rget_rlist (rs : Regs) : rget (rlist rs) = rs := by
  funext r; cases r <;> rfl

/-- **The statement of the SPSC goal is false.** -/
theorem spscFifoTsoPrim_false : ¬ spscFifoTsoPrim := by
  intro H
  have hc := cF_check
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨hdone, hdr⟩, h0⟩, h1⟩, h2⟩, _⟩ := hc
  have hstart : cX.cfg.toO = cX.ocfg := start_toO (by decide)
  have hr : OReach .tso 2 cX.cfg.toO cF.ocfg := by rw [hstart]; exact walk2_reach schedX cX
  have hth : cX.th = fun t =>
      if t = 0 then (prodX, regs [(.rdi, 0x100)]) else if t = 1 then (consX, regs [(.rdi, 0x100)])
      else (.skip, Regs.zero) := by
    funext t
    rcases t with _ | _ | t <;>
      simp only [CSt.th, cX, start, List.map_cons, List.map_nil, List.getElem?_cons_zero,
        List.getElem?_cons_succ, List.getElem?_nil, rget_rlist] <;> simp
  have hmem : memOf cX.mem = heapOf ([(0x100, 0), (0x104, 0), (0x108, 0), (0x10c, 0)] ++
        (List.range 3).map fun i => (0x200 + 4 * i, 0)) Heap.empty := by
    funext a
    simp only [memOf, heapOf, cX, start, memX, Heap.empty, Option.or_none]
  have hcfg : cX.cfg = ⟨fun t =>
      if t = 0 then (prodX, regs [(.rdi, 0x100)]) else if t = 1 then (consX, regs [(.rdi, 0x100)])
      else (.skip, Regs.zero),
      heapOf ([(0x100, 0), (0x104, 0), (0x108, 0), (0x10c, 0)] ++
        (List.range 3).map fun i => (0x200 + 4 * i, 0)) Heap.empty⟩ := by
    show (⟨cX.th, memOf cX.mem⟩ : Cfg) = _
    rw [hth, hmem]
  rw [hcfg] at hr
  have hd : cF.ocfg.Drained := by
    intro t
    simp only [CSt.drainedB, List.all_eq_true] at hdr
    simp only [CSt.ocfg, List.getD_eq_getElem?_getD]
    cases ht : cF.buf[t]? with
    | none => rfl
    | some b => simpa using hdr b (List.mem_of_getElem? ht)
  have hfin : ∀ t < 2, (cF.ocfg.ts t).1 = .skip := by
    intro t ht
    simp only [CSt.doneB, List.all_eq_true, List.mem_range] at hdone
    have := hdone t ht
    simp only [CSt.ocfg]
    exact TvCfg.sbeq_eq this
  have := H 2 0x100 0x200 3 vsX (by decide) (by decide) (by decide) (by decide) cF.ocfg hr hd hfin
  simp only [CSt.ocfg] at this
  rw [show (List.range 3) = [0, 1, 2] from rfl] at this
  simp only [List.map_cons, List.map_nil, Nat.mul_zero, Nat.add_zero, Nat.mul_one] at this
  rw [h0, h1, show 0x200 + 4 * 2 = 0x208 from rfl, h2] at this
  simp [vsX] at this

/-! ## The restated client has finished runs (non-vacuity of `Task.spscFifoTso`)

The same values with the producer recording its results at `0x300 + 4j`: a TSO run finishes
with the outputs `[1, 2, 4]` and the result of the third push `0` (dropped). -/

/-- The recording producer of `Task.spscFifoTso` for `vsX`, results at `0x300`. -/
def prodR : Stmt := Tv.chain ((List.range vsX.length).map fun j =>
  Tv.chain [.assign .rsi (.lit (vsX.getD j 0)), SpscPush.cert.body 2,
    .store .na 4 .wb (.lit (0x300 + 4 * j)) (.reg .rax)])

/-- The cells of the recording client. -/
def memR : List (Nat × Nat) :=
  [(0x100, 0), (0x104, 0), (0x108, 0), (0x10c, 0)] ++
    ((List.range 3).map fun i => (0x200 + 4 * i, 0)) ++
    (List.range vsX.length).map fun j => (0x300 + 4 * j, 0)

/-- The concrete start of the recording client. -/
def cR : CSt := start [(prodR, regs [(.rdi, 0x100)]), (consX, regs [(.rdi, 0x100)])] memR

/-- The final configuration of the recording run. -/
def cRF : CSt := walk2 2 cR (eager 0 86 ++ eager 1 30 ++ eager 0 200 ++ eager 1 200)

theorem ocfg_mem (c : CSt) : c.ocfg.mem = memOf c.mem := rfl

set_option maxRecDepth 100000 in
theorem cRF_check : (cRF.doneB 2 && cRF.drainedB && memOf cRF.mem 0x200 == some 1 &&
    memOf cRF.mem 0x204 == some 2 && memOf cRF.mem 0x208 == some 4 &&
    memOf cRF.mem 0x308 == some 0 && memOf cRF.mem 0x30c == some 1) = true := by
  decide +kernel

/-- **A finished run of the restated SPSC client** (from `Task.spscFifoTso`'s start, with
`L = 2`, `q = 0x100`, `out = 0x200`, `res = 0x300`, `k = 3`, `vs = [1, 2, 3, 4]`): it pops
`[1, 2, 4]`, and the third push reports a full ring. -/
theorem spscRec_finishes : ∃ C : OCfg, OReach .tso 2 (⟨fun t =>
      if t = 0 then (prodR, regs [(.rdi, 0x100)]) else if t = 1 then (consX, regs [(.rdi, 0x100)])
      else (.skip, Regs.zero), heapOf memR Heap.empty⟩ : Cfg).toO C ∧ C.Drained ∧
    (∀ t < 2, (C.ts t).1 = .skip) ∧ C.mem 0x200 = some 1 ∧ C.mem 0x204 = some 2 ∧
    C.mem 0x208 = some 4 ∧ C.mem 0x308 = some 0 ∧ C.mem 0x30c = some 1 := by
  have hc := cRF_check
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨hdone, hdr⟩, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩ := hc
  have hstart : cR.cfg.toO = cR.ocfg := start_toO (by decide)
  have hth : cR.th = fun t =>
      if t = 0 then (prodR, regs [(.rdi, 0x100)]) else if t = 1 then (consX, regs [(.rdi, 0x100)])
      else (.skip, Regs.zero) := by
    funext t
    rcases t with _ | _ | t <;>
      simp only [CSt.th, cR, start, List.map_cons, List.map_nil, List.getElem?_cons_zero,
        List.getElem?_cons_succ, List.getElem?_nil, rget_rlist] <;> simp
  have hmem : memOf cR.mem = heapOf memR Heap.empty := by
    funext a
    simp only [memOf, heapOf, cR, start, Heap.empty, Option.or_none]
  have hcfg : cR.cfg = ⟨fun t =>
      if t = 0 then (prodR, regs [(.rdi, 0x100)]) else if t = 1 then (consX, regs [(.rdi, 0x100)])
      else (.skip, Regs.zero), heapOf memR Heap.empty⟩ := by
    show (⟨cR.th, memOf cR.mem⟩ : Cfg) = _
    rw [hth, hmem]
  have hr : OReach .tso 2 cR.cfg.toO cRF.ocfg := by rw [hstart]; exact walk2_reach _ cR
  rw [hcfg] at hr
  have e : cRF.ocfg.mem = memOf cRF.mem := ocfg_mem cRF
  refine ⟨cRF.ocfg, hr, fun t => ?_, fun t ht => ?_, ?_⟩
  rotate_left 2
  · rw [e]; exact ⟨h0, h1, h2, h3, h4⟩
  · simp only [CSt.drainedB, List.all_eq_true] at hdr
    simp only [CSt.ocfg, List.getD_eq_getElem?_getD]
    cases ht : cRF.buf[t]? with
    | none => rfl
    | some b => simpa using hdr b (List.mem_of_getElem? ht)
  · simp only [CSt.doneB, List.all_eq_true, List.mem_range] at hdone
    exact TvCfg.sbeq_eq (hdone t ht)

end Silmaril.Proofs.X86.Concurrency.Cir.Prim.Tasks.SpscCex
