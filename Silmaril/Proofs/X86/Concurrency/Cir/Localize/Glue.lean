module

public import Silmaril.Proofs.X86.Concurrency.Cir.Localize.Labs
public import Silmaril.Proofs.X86.Concurrency.Cir.Localize.Units

/-!
# Localisation: CIR-level helpers

Statement checks on `chain`, register updates of a block, the actions of
a thread's trace, and the units of the block.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Localize

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Tv (chain)
open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Litmus (Byte XAct XTrace actUnits threadUnits seqL)

/-! ## `chain` -/

theorem chain_check {f : Stmt → Bool} (hskip : f .skip = true)
    (hseq : ∀ s t, f (.seq s t) = (f s && f t)) :
    ∀ l : List Stmt, (∀ s ∈ l, f s = true) → f (chain l) = true
  | [], _ => hskip
  | s :: l, h => by
    rw [chain, hseq, h s List.mem_cons_self,
      chain_check hskip hseq l fun t ht => h t (List.mem_cons_of_mem _ ht)]
    rfl

theorem chain_writes : ∀ l : List Stmt, (chain l).writes = l.flatMap Stmt.writes
  | [] => rfl
  | s :: l => by simp [chain, Stmt.writes, chain_writes l]

/-! ## Registers of a block -/

theorem setMany_map (g : Regs) (r : Reg) : ∀ (rs : Regs) (l : List Reg),
    rs.setMany l (l.map fun q => (g q).toNat) r = if r ∈ l then g r else rs r
  | rs, [] => by simp [Regs.setMany]
  | rs, q :: l => by
    simp only [List.map_cons, Regs.setMany, List.mem_cons]
    rw [setMany_map g r _ l]
    by_cases hl : r ∈ l
    · simp [hl]
    · by_cases hq : r = q
      · subst hq; simp [hl, Regs.set]
      · simp [hl, hq, Regs.set]

theorem cellVals_map (g : Nat × Nat → Nat) :
    ∀ cs : List (Nat × Nat), cellVals cs (cs.map g) = cs.map fun c => (c.1, c.2, g c)
  | [] => rfl
  | c :: cs => by simp [cellVals, cellVals_map g cs]

/-! ## Actions of a CIR trace -/

theorem xtrace_acts (th : Thread) (i : Nat) (p : List Lab × Regs) :
    (th.xtrace i p).acts = th.acts i p.1 := by
  simp [Thread.xtrace, Silmaril.X86.Litmus.Trace.acts]

theorem thread_acts_false (b : Stmt) (i : Nat) (tr : List Lab) :
    Thread.acts ⟨b, false⟩ i tr = tr.flatMap Lab.acts := by
  simp [Thread.acts]

/-- Every action of a thread whose body avoids the cells avoids them (its start and end events are
on ghost bytes). -/
theorem thread_avoid {cs : List (Nat × Nat)} (hcs : ∀ c ∈ cs, c.1 + c.2 ≤ ctlAddr 0)
    {th : Thread} (hb : th.body.avoids cs = true) {dom : List Nat} {k : Nat}
    {p : List Lab × Regs} (hp : p ∈ run dom th.body Regs.zero) :
    ∀ a ∈ th.acts k p.1, ActAvoid cs a := by
  intro a ha
  simp only [Thread.acts, List.mem_append, List.mem_flatMap] at ha
  rcases ha with (ha | ⟨l, hl, ha⟩) | ha
  · split at ha
    · simp only [List.mem_singleton] at ha; subst ha
      exact avoid_ghost hcs (by simpa [ctlAct, rmwAct] using ctl_le_ctl k)
    · simp at ha
  · exact run_avoid dom cs hcs th.body hb Regs.zero p hp l hl a ha
  · split at ha
    · simp only [List.mem_singleton] at ha; subst ha
      exact avoid_ghost hcs (by simpa [endAct, rmwAct] using ctl_le_end k)
    · simp at ha

/-! ## Units of the block -/

/-- A unit of the block: a write-back read or write of a cell, unlocked. -/
def UG (cs : List (Nat × Nat)) (ib : Nat → Byte) (u : Ev × List Byte) : Prop :=
  (u.1.isR = true ∨ u.1.isW = true) ∧ u.1.locked = false ∧ u.1.ann = .wb ∧ 0 < u.1.size ∧
    u.1.accAddr = u.1.addr ∧ u.1.accSize = u.1.size ∧
    (u.1.isW = true → u.1.data.length = u.1.size) ∧ (u.1.addr, u.1.size) ∈ cs ∧
    (u.1.isR = true → u.2 = u.1.bytes.map ib)

/-- The block's loads (initial values) then stores. -/
def blkActs (m0 m1 : Mem) (ins outs : List (Nat × Nat)) : List XAct :=
  (ins.map fun c => ldAct .wb c.1 c.2 ((m0.val c.1 c.2).getD 0)) ++
    outs.map fun c => stAct .wb c.1 c.2 ((m1.val c.1 c.2).getD 0)

theorem blk_acts (nm : String) (m0 m1 : Mem) (ins outs : List (Nat × Nat)) (rvs : List Nat) :
    (Lab.blk nm (cellVals ins (ins.map fun c => (m0.val c.1 c.2).getD 0))
      (cellVals outs (outs.map fun c => (m1.val c.1 c.2).getD 0)) rvs).acts =
      blkActs m0 m1 ins outs := by
  simp only [Lab.acts, blkActs, cellVals_map, List.map_map]
  rfl

theorem blk_units (cs : List (Nat × Nat)) (ib : Nat → Byte) (m0 m1 : Mem) (ins outs : List (Nat × Nat))
    (hin : ∀ c ∈ ins ++ outs, c ∈ cs) (hpos : ∀ c ∈ cs, 0 < c.2)
    (hib : ∀ y, ib y = (m0 y).getD 0) (i p : Nat) :
    ∀ u ∈ threadUnits i p (blkActs m0 m1 ins outs), UG cs ib u := by
  refine threadUnits_all p _ fun a ha q u hu => ?_
  simp only [blkActs, List.mem_append, List.mem_map] at ha
  rcases ha with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
  · have hcs := hin c (List.mem_append_left _ hc)
    simp only [actUnits, ldAct, List.mem_singleton] at hu
    subst hu
    refine ⟨.inl rfl, rfl, rfl, hpos c hcs, rfl, rfl, by simp [Ev.isW], hcs, fun _ => ?_⟩
    simp only [Ev.bytes]
    rw [natBytes_val]
    simp [Seq.bytesAt, hib]
  · have hcs := hin c (List.mem_append_right _ hc)
    simp only [actUnits, stAct, List.mem_singleton] at hu
    subst hu
    refine ⟨.inr rfl, rfl, rfl, hpos c hcs, rfl, rfl, fun _ => length_natBytes _ _, hcs, ?_⟩
    simp [Ev.isR]

theorem blk_rw (m0 m1 : Mem) (ins outs : List (Nat × Nat)) (i p : Nat) :
    ∀ k k' (hk : k < (threadUnits i p (blkActs m0 m1 ins outs)).length)
      (hk' : k' < (threadUnits i p (blkActs m0 m1 ins outs)).length), k ≤ k' →
      ((threadUnits i p (blkActs m0 m1 ins outs))[k]).1.isW = true →
      ((threadUnits i p (blkActs m0 m1 ins outs))[k']).1.isW = true := by
  intro k k' hk hk' hkk hW
  have hsplit := threadUnits_append i p (ins.map fun c => ldAct .wb c.1 c.2 ((m0.val c.1 c.2).getD 0))
    (outs.map fun c => stAct .wb c.1 c.2 ((m1.val c.1 c.2).getD 0))
  have hR : ∀ u ∈ threadUnits i p (ins.map fun c => ldAct .wb c.1 c.2 ((m0.val c.1 c.2).getD 0)),
      u.1.isW = false := by
    refine threadUnits_all p _ fun a ha q u hu => ?_
    simp only [List.mem_map] at ha
    obtain ⟨c, -, rfl⟩ := ha
    simp only [actUnits, ldAct, List.mem_singleton] at hu
    subst hu; rfl
  have hW' : ∀ u ∈ threadUnits i (p + (threadUnits i p (ins.map fun c =>
      ldAct .wb c.1 c.2 ((m0.val c.1 c.2).getD 0))).length)
      (outs.map fun c => stAct .wb c.1 c.2 ((m1.val c.1 c.2).getD 0)), u.1.isW = true := by
    refine threadUnits_all _ _ fun a ha q u hu => ?_
    simp only [List.mem_map] at ha
    obtain ⟨c, -, rfl⟩ := ha
    simp only [actUnits, stAct, List.mem_singleton] at hu
    subst hu; rfl
  simp only [blkActs] at hk hk' hW ⊢
  rw [List.getElem_of_eq hsplit] at hW ⊢
  by_cases h1 : k' < (threadUnits i p (ins.map fun c =>
      ldAct .wb c.1 c.2 ((m0.val c.1 c.2).getD 0))).length
  · rw [List.getElem_append_left (by omega)] at hW
    rw [hR _ (List.getElem_mem _)] at hW; cases hW
  · rw [List.getElem_append_right (by omega)]
    exact hW' _ (List.getElem_mem _)

end Silmaril.Proofs.X86.Concurrency.Cir.Localize
