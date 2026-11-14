module

public import Silmaril.Proofs.X86.Concurrency.Cir.Fj.Units
public import Silmaril.Proofs.X86.Concurrency.Cir.Fj.Mem
public import Mathlib.Data.List.Forall2

/-!
# Fork-join CIR: the traces of a fork-join program

A choice of one trace per thread of `Par.prog` (`Shape`): the main
thread's actions are the spawn events, the join events and the combine block's loads and
stores; worker `k`'s are its start event, its job block's loads and stores and its end event.
The block's values fit their cells and its outputs are `fn` of its inputs (`shape_of`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Fj

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Fj
open Silmaril.X86.MemoryModel.Litmus (Byte XAct XTrace seqL)

/-! ## Runs -/

theorem run_seqs {dom : List Nat} (S : Nat → Stmt) (L : Nat → Lab)
    (hS : ∀ k rs, run dom (S k) rs = [([L k], rs)]) (rs : Regs) :
    ∀ l : List Nat, run dom (seqs (l.map S)) rs = [(l.map L, rs)]
  | [] => rfl
  | k :: l => by
    simp only [List.map_cons, seqs, run, hS, Res.bind, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    rw [run_seqs S L hS rs l]
    simp

theorem mem_seqL_map {α β : Type} (g : β → List α) :
    ∀ (l : List β) (v : List α), v ∈ seqL (l.map g) ↔ List.Forall₂ (fun a c => a ∈ g c) v l
  | [], v => by simp [seqL]
  | c :: l, v => by
    simp only [List.map_cons, seqL, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨a, ha, w, hw, rfl⟩
      exact List.Forall₂.cons ha ((mem_seqL_map g l w).mp hw)
    · intro h
      cases h with
      | cons ha hw => exact ⟨_, ha, _, (mem_seqL_map g l _).mpr hw, rfl⟩

/-- Values chosen from `pick` fit their cells. -/
def Fits (dom : List Nat) (vs : List Nat) (cs : List (Nat × Nat)) : Prop :=
  List.Forall₂ (fun v c => v ∈ pick dom c.2) vs cs

theorem mem_runBlock {dom : List Nat} {j : Job} {rs : Regs} {p : List Lab × Regs}
    (h : p ∈ runBlock dom j.block rs) :
    ∃ ivs ovs, Fits dom ivs j.ins ∧ Fits dom ovs j.outs ∧ ovs = j.fn ivs ∧
      p = ([.blk j.name (cellVals j.ins ivs) (cellVals j.outs ovs) []], rs) := by
  simp only [runBlock, Job.block, List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨ivs, hivs, rvs, hrvs, ovs, hovs, hp⟩ := h
  simp only [List.map_nil, seqL, List.mem_singleton] at hrvs
  subst hrvs
  split at hp
  · rename_i hd
    simp only [Option.some.injEq] at hp
    subst hp
    simp only [List.map_nil, List.nil_append, decide_eq_true_eq] at hd
    exact ⟨ivs, ovs, (mem_seqL_map _ _ _).mp hivs, (mem_seqL_map _ _ _).mp hovs, hd, rfl⟩
  · simp at hp

/-! ## Actions -/

/-- The actions of a job block with inputs `ivs` and outputs `ovs`. -/
def blkActs (j : Job) (ivs ovs : List Nat) : List XAct :=
  (cellVals j.ins ivs).map (fun c => ldAct .wb c.1 c.2.1 c.2.2) ++
    (cellVals j.outs ovs).map fun c => stAct .wb c.1 c.2.1 c.2.2

/-- The spawn events of the main thread. -/
def spawnActs (N : Nat) : List XAct := (List.range N).map fun k => ctlAct (k + 1) 0 1

/-- The join events of the main thread. -/
def joinActs (N : Nat) : List XAct := (List.range N).map fun k => endAct (k + 1) 1 2

/-- **A choice of traces of a fork-join program**: per thread, its actions and block values. -/
structure Shape (F : Par) (dom : List Nat) (trs : List XTrace) : Prop where
  len : trs.length = F.jobs.length + 1
  main : ∃ tr ivs ovs, trs[0]? = some tr ∧ Fits dom ivs F.comb.ins ∧ Fits dom ovs F.comb.outs ∧
    ovs = F.comb.fn ivs ∧
    tr.acts = (spawnActs F.jobs.length ++ joinActs F.jobs.length) ++ blkActs F.comb ivs ovs
  worker : ∀ k (hk : k < F.jobs.length), ∃ tr ivs ovs, trs[k + 1]? = some tr ∧
    Fits dom ivs F.jobs[k].ins ∧ Fits dom ovs F.jobs[k].outs ∧ ovs = F.jobs[k].fn ivs ∧
    tr.acts = ([ctlAct (k + 1) 1 2] ++ blkActs F.jobs[k] ivs ovs) ++ [endAct (k + 1) 0 1]

theorem xtrace_acts (th : Thread) (i : Nat) (p : List Lab × Regs) :
    (th.xtrace i p).acts = th.acts i p.1 := by
  simp [Thread.xtrace, Silmaril.X86.Litmus.Trace.acts]

theorem blk_acts (j : Job) (ivs ovs : List Nat) :
    (Lab.blk j.name (cellVals j.ins ivs) (cellVals j.outs ovs) []).acts = blkActs j ivs ovs := rfl

theorem flatMap_spawn (N : Nat) :
    ((List.range N).map fun k => Lab.spawn (k + 1)).flatMap Lab.acts = spawnActs N := by
  simp only [spawnActs, List.flatMap_map, Lab.acts]
  induction List.range N <;> simp_all

theorem flatMap_join (N : Nat) :
    ((List.range N).map fun k => Lab.join (k + 1)).flatMap Lab.acts = joinActs N := by
  simp only [joinActs, List.flatMap_map, Lab.acts]
  induction List.range N <;> simp_all

theorem run_main {dom : List Nat} (F : Par) (rs : Regs) :
    run dom F.main rs = (runBlock dom F.comb.block rs).map fun q =>
      (((List.range F.jobs.length).map fun k => Lab.spawn (k + 1)) ++
        (((List.range F.jobs.length).map fun k => Lab.join (k + 1)) ++ q.1), q.2) := by
  simp only [Par.main, run,
      run_seqs (dom := dom) (fun k => .spawn (k + 1)) (fun k => .spawn (k + 1))
      (fun _ _ => rfl), run_seqs (dom := dom) (fun k => .join (k + 1)) (fun k => .join (k + 1))
      (fun _ _ => rfl), Res.bind]
  simp

/-- **Every choice of traces has the fork-join shape.** -/
theorem shape_of {F : Par} {dom : List Nat} {trs : List XTrace}
    (h : List.Forall₂ (· ∈ ·) trs (F.prog.traces dom)) : Shape F dom trs := by
  obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.mp h
  have hlen' : trs.length = F.jobs.length + 1 := by
    rw [hlen]; simp [Prog.traces, Par.prog]
  refine ⟨hlen', ?_, ?_⟩
  · have h0 := hget 0 (by omega) (by rw [← hlen]; omega)
    simp only [List.get_eq_getElem, Prog.traces, Par.prog, List.getElem_mapIdx,
      List.getElem_cons_zero, List.mem_map] at h0
    obtain ⟨p, hp, hpe⟩ := h0
    rw [run_main, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨ivs, ovs, hi, ho, hf, rfl⟩ := mem_runBlock hq
    refine ⟨trs[0], ivs, ovs, by simp, hi, ho, hf, ?_⟩
    rw [← hpe, xtrace_acts]
    simp [Thread.acts, List.flatMap_append, flatMap_spawn, flatMap_join, blk_acts]
  · intro k hk
    have hk' := hget (k + 1) (by omega) (by rw [← hlen]; omega)
    simp only [List.get_eq_getElem, Prog.traces, Par.prog, List.getElem_mapIdx,
      List.getElem_cons_succ, List.getElem_map, List.mem_map] at hk'
    obtain ⟨p, hp, hpe⟩ := hk'
    simp only [run] at hp
    obtain ⟨ivs, ovs, hi, ho, hf, rfl⟩ := mem_runBlock hp
    refine ⟨trs[k + 1], ivs, ovs, by simp, hi, ho, hf, ?_⟩
    rw [← hpe, xtrace_acts]
    simp [Thread.acts, blk_acts]

/-! ## Footprints of the actions -/

/-- The footprint of an action. -/
def Act.has (a : XAct) (y : Nat) : Prop := a.ev.addr ≤ y ∧ y < a.ev.addr + a.ev.size

theorem ctl_has {t o n y : Nat} (h : Act.has (ctlAct t o n) y) : y = ctlAddr t := by
  simp [Act.has, ctlAct, rmwAct] at h; omega

theorem end_has {t o n y : Nat} (h : Act.has (endAct t o n) y) : y = endAddr t := by
  simp [Act.has, endAct, rmwAct] at h; omega

theorem dataTop_le_ctl (t : Nat) : dataTop ≤ ctlAddr t := by simp [dataTop, ctlAddr]

theorem dataTop_le_end (t : Nat) : dataTop ≤ endAddr t := by simp [dataTop, endAddr, ctlAddr]; omega

theorem mem_spawnActs {N : Nat} {a : XAct} (h : a ∈ spawnActs N) :
    ∃ k < N, a = ctlAct (k + 1) 0 1 := by
  simp only [spawnActs, List.mem_map, List.mem_range] at h
  obtain ⟨k, hk, rfl⟩ := h; exact ⟨k, hk, rfl⟩

theorem mem_joinActs {N : Nat} {a : XAct} (h : a ∈ joinActs N) :
    ∃ k < N, a = endAct (k + 1) 1 2 := by
  simp only [joinActs, List.mem_map, List.mem_range] at h
  obtain ⟨k, hk, rfl⟩ := h; exact ⟨k, hk, rfl⟩

/-- A block action: a load of an input cell or a store of an output cell. -/
theorem mem_blkActs {j : Job} {ivs ovs : List Nat} {a : XAct} (h : a ∈ blkActs j ivs ovs) :
    (∃ c ∈ cellVals j.ins ivs, a = ldAct .wb c.1 c.2.1 c.2.2) ∨
      (∃ c ∈ cellVals j.outs ovs, a = stAct .wb c.1 c.2.1 c.2.2) := by
  simp only [blkActs, List.mem_append, List.mem_map] at h
  rcases h with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
  · exact .inl ⟨c, hc, rfl⟩
  · exact .inr ⟨c, hc, rfl⟩

theorem ld_has {a sz v y : Nat} : Act.has (ldAct .wb a sz v) y ↔ Cell.has (a, sz) y := by
  simp [Act.has, ldAct, Cell.has]

theorem st_has {a sz v y : Nat} : Act.has (stAct .wb a sz v) y ↔ Cell.has (a, sz) y := by
  simp [Act.has, stAct, Cell.has]

/-- Cells of a job lie in the data region. -/
theorem cell_low {c : Nat × Nat} (hc : c.1 + c.2 ≤ dataTop) {y : Nat} (hy : Cell.has c y) :
    y < dataTop := by
  simp only [Cell.has] at hy; omega

end Silmaril.Proofs.X86.Concurrency.Cir.Fj
