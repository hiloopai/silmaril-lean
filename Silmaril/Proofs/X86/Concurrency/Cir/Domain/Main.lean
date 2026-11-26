module

public import Silmaril.Proofs.X86.Concurrency.Cir.Domain.Units
public import Silmaril.Proofs.X86.Concurrency.Cir.Domain.Rank
public import Silmaril.X86.MemoryModel.Xl.Thms
public import Mathlib.Data.List.Forall2

/-!
# Domain closure on CIR: the theorem

Proof of `Cir.cirDomain` (`Silmaril/X86/Concurrency/Cir/Domain/Thms.lean`).

Take a behaviour over some domain `D`: one run per thread over `D` and a consistent candidate
`x` over their units. In a uniform program no access tears (`units_eq`), so every unit is a
location's cell or a ghost byte, and every read below the ghost bytes takes all its bytes from
one write of its cell or from the initial value (`rf_uniform`). `reads_good` then shows, by
induction along `(po ∪ rf)⁺`, that every such read returns a value of `dom`: a write's label is
the end of a prefix of its thread's run whose reads come earlier in `po`, so (with
`BlocksClosed` for block outputs and `0`/`1` for the futex queues) that prefix is a partial run
over `dom` (`pre_of_run`) and the written value is in `dom` by `preClosedB`. Finally every
thread's run has all its choices in `dom`, so it is a run over `dom` (`run_restrict`), and the
same candidate is a behaviour over `dom`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Domain

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.MemoryModel.Litmus (Byte XAct XTrace Loc Final Test actUnits threadUnits accUnits
  units memB initByte Model cellsOk)
open Silmaril.X86.MemoryModel.Axiomatic (Ev Exec BRel)

/-! ## Small facts -/

theorem memB_iff {a : Nat} : ∀ {l : List Nat}, memB a l = true ↔ a ∈ l
  | [] => by simp [memB]
  | b :: l => by
    simp only [memB, List.mem_cons]
    split
    · rename_i h; simp [h]
    · rename_i h; rw [memB_iff]; simp [h]

theorem xtrace_acts (th : Thread) (i : Nat) (p : List Lab × Regs) :
    (th.xtrace i p).acts = th.acts i p.1 := by
  simp [Thread.xtrace, Silmaril.X86.Litmus.Trace.acts]

theorem mem_accUnits {trs : List XTrace} {u : Ev × List Byte} (h : u ∈ accUnits trs) :
    ∃ i, ∃ hi : i < trs.length, u ∈ threadUnits i 0 trs[i].acts := by
  simp only [accUnits, List.mem_flatten, List.mem_mapIdx] at h
  obtain ⟨l, ⟨i, hi, rfl⟩, hu⟩ := h
  exact ⟨i, hi, hu⟩

theorem accUnits_mem {trs : List XTrace} {i : Nat} (hi : i < trs.length) {u : Ev × List Byte}
    (h : u ∈ threadUnits i 0 trs[i].acts) : u ∈ accUnits trs := by
  simp only [accUnits, List.mem_flatten, List.mem_mapIdx]
  exact ⟨_, ⟨i, hi, rfl⟩, h⟩

theorem thread_of {P : Prog} {D : List Nat} {trs : List XTrace}
    (hT : List.Forall₂ (· ∈ ·) trs (P.traces D)) (i : Nat) (hi : i < trs.length) :
    ∃ hi' : i < P.threads.length, ∃ p ∈ run D P.threads[i].body Regs.zero,
      trs[i] = P.threads[i].xtrace i p := by
  have hlen := hT.length_eq
  simp only [Prog.traces, List.length_mapIdx] at hlen
  have hi' : i < P.threads.length := hlen ▸ hi
  have := hT.get hi (by simp [Prog.traces, hi'])
  simp only [List.get_eq_getElem, Prog.traces, List.getElem_mapIdx, List.mem_map] at this
  obtain ⟨p, hp, he⟩ := this
  exact ⟨hi', p, hp, he.symm⟩

/-- The number of units before a thread's labels (its start event, if spawned). -/
def ctlLen (th : Thread) (i : Nat) : Nat :=
  (threadUnits i 0 (if th.spawned then [ctlAct i 1 2] else [])).length

theorem thread_units_flat (th : Thread) (i : Nat) (tr : List Lab) {u : Ev × List Byte}
    (h : u ∈ threadUnits i (ctlLen th i) (tr.flatMap Lab.acts)) :
    u ∈ threadUnits i 0 (th.acts i tr) := by
  simp only [Thread.acts]
  rw [threadUnits_append, threadUnits_append]
  exact List.mem_append_left _ (List.mem_append_right _ (by simpa [ctlLen] using h))

theorem thread_units_low (th : Thread) (i : Nat) (tr : List Lab) {u : Ev × List Byte}
    (h : u ∈ threadUnits i 0 (th.acts i tr)) (hlow : low u.1) :
    u ∈ threadUnits i (ctlLen th i) (tr.flatMap Lab.acts) := by
  simp only [Thread.acts] at h
  rw [threadUnits_append, threadUnits_append] at h
  unfold low at hlow
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · exfalso
      split at h
      · have := ghost_ctl i
        simp [threadUnits, actUnits, ctlAct, rmwAct] at h
        rcases h with rfl | rfl <;> simp only at hlow <;> omega
      · simp [threadUnits] at h
    · simpa [ctlLen] using h
  · exfalso
    split at h
    · have := ghost_end i
      simp [threadUnits, actUnits, endAct, rmwAct] at h
      rcases h with rfl | rfl <;> simp only at hlow <;> omega
    · simp [threadUnits] at h

theorem pair_mem {x : Exec} {U : List (Ev × List Byte)} (h : x.evs = U.map Prod.fst)
    (r : Fin x.n) : (x.ev r, (U.map Prod.snd).getD r.val []) ∈ U := by
  have hr : r.val < U.length := by have := r.isLt; simp only [Exec.n, h, List.length_map] at this; exact this
  have e1 : x.ev r = U[r.val].1 := by
    show x.evs[r.val] = _
    have : x.evs[r.val] = (U.map Prod.fst)[r.val]'(by simpa using hr) := by simp [h]
    rw [this, List.getElem_map]
  have e2 : (U.map Prod.snd).getD r.val [] = U[r.val].2 := by
    simp [List.getD_eq_getElem?_getD, hr]
  rw [e1, e2]
  exact List.getElem_mem _

theorem mem_pair {x : Exec} {U : List (Ev × List Byte)} (h : x.evs = U.map Prod.fst)
    {u : Ev × List Byte} (hu : u ∈ U) :
    ∃ r : Fin x.n, x.ev r = u.1 ∧ (U.map Prod.snd).getD r.val [] = u.2 := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
  have hj' : j < x.n := by simp only [Exec.n, h, List.length_map]; exact hj
  refine ⟨⟨j, hj'⟩, ?_, by simp [List.getD_eq_getElem?_getD, hj]⟩
  show x.evs[j] = _
  have : x.evs[j] = (U.map Prod.fst)[j]'(by simpa using hj) := by simp [h]
  rw [this, List.getElem_map]

theorem init_bytes {locs : List Loc} (hl : LocsFacts locs) {l : Loc} (hlm : l ∈ locs) :
    (List.range' l.addr l.size).map (fun y => (initByte locs y).getD 0) = natBytes l.init l.size := by
  apply List.ext_getElem
  · simp [length_natBytes]
  · intro j h1 h2
    simp only [List.length_map, List.length_range'] at h1
    simp only [List.getElem_map, List.getElem_range', natBytes, List.getElem_range, Nat.one_mul]
    have hfind : locs.find? (fun l' => decide (l'.addr ≤ l.addr + j) &&
        decide (l.addr + j < l'.addr + l'.size)) = some l := by
      cases hf : locs.find? (fun l' => decide (l'.addr ≤ l.addr + j) &&
          decide (l.addr + j < l'.addr + l'.size)) with
      | none =>
        rw [List.find?_eq_none] at hf
        exact absurd (hf l hlm) (by simp; omega)
      | some l' =>
        have hm := List.mem_of_find?_eq_some hf
        have hp := List.find?_some hf
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
        rcases hl.disj l hlm l' hm with rfl | h | h
        · rfl
        · omega
        · omega
    simp [initByte, hfind]

/-! ## The theorem -/

/-- **Domain closure on CIR** (`Task.cirDomain`). -/
theorem cirDomain : Task.cirDomain := by
  intro P dom hU hC hB M f hb
  obtain ⟨D, trs, hT, x, hevs, hrmw, hwf, hreads, hM, rfl⟩ := hb
  refine ⟨trs, ?_, x, hevs, hrmw, hwf, hreads, hM, rfl⟩
  -- the program's facts
  simp only [Prog.uniformB, Bool.and_eq_true, List.all_eq_true] at hU
  obtain ⟨hlocs, hcells⟩ := hU
  have hl := locsFacts hlocs
  have hcs := cellsOf_lt hl
  simp only [Prog.preClosedB, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true] at hC
  obtain ⟨⟨hpw, hini⟩, hfut⟩ := hC
  have hxl : x.Xl := by
    cases M
    · exact x.xl_of_sc hM
    · exact x.xl_of_tso hM
    · exact hM
  have hdata := thread_of hT
  have hlab : ∀ (i : Nat) (hi' : i < P.threads.length) (p : List Lab × Regs),
      p ∈ run D P.threads[i].body Regs.zero →
      ∀ l ∈ p.1, LabOk (cellsOf P.locs) P.threads[i].body.blocks l :=
    fun i hi' p hp => labs_ok D _ hcs _ (hcells _ (List.getElem_mem _)) _ p hp
  -- uniform units
  have huok : ∀ u ∈ accUnits trs, UOk (cellsOf P.locs) u.1 := by
    intro u hu
    obtain ⟨i, hi, hu⟩ := mem_accUnits hu
    obtain ⟨hi', p, hp, he⟩ := hdata i hi
    rw [he, xtrace_acts] at hu
    exact threadUnits_ok i 0 _ (thread_acts_ok _ i _ (hlab i hi' p hp)) u hu
  have hun : units trs = accUnits trs := units_eq hl huok
  rw [hun] at hevs hreads
  set U := accUnits trs with hUdef
  set exps : Nat → List Byte := fun r => (U.map Prod.snd).getD r [] with hexps
  -- choices: from good reads to `Chosen`
  have hchosen : ∀ (i : Nat) (hi' : i < P.threads.length) (p : List Lab × Regs),
      p ∈ run D P.threads[i].body Regs.zero → ∀ l ∈ p.1, ReadsIn dom l → Chosen dom l := by
    intro i hi' p hp l hlp hR
    have hok := hlab i hi' p hp l hlp
    have h01 : labFutex l = true → 0 ∈ dom ∧ 1 ∈ dom := by
      intro hF
      rcases hfut with hff | h01
      · have := labs_futex D _ (hff _ (List.getElem_mem _)) _ p hp l hlp
        rw [hF] at this; cases this
      · exact ⟨memB_iff.mp h01.1, memB_iff.mp h01.2⟩
    have hbc := hB _ (List.getElem_mem hi')
    cases l with
    | rd m fl a sz v => exact hR
    | rmw m a sz o n => exact hR
    | fwait a e seen r =>
      simp only [LabOk] at hok
      obtain ⟨h0, h1⟩ := h01 rfl
      refine ⟨hR, fun _ => ?_⟩
      rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
      · exact h0
      · exact h1
    | fwake a n q =>
      simp only [LabOk] at hok
      obtain ⟨h0, h1⟩ := h01 rfl
      show q ∈ dom
      rcases (show q = 0 ∨ q = 1 by omega) with rfl | rfl
      · exact h0
      · exact h1
    | blk nm ins outs rvs =>
      simp only [LabOk] at hok
      obtain ⟨-, b, hb, rv, hrv, hspec⟩ := hok
      have hall := hbc b hb rv _ _ hrv (fun v hv => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv; exact hR c hc) hspec
      refine ⟨hR, fun c hc => hall _ (List.mem_append_right _ (List.mem_map_of_mem hc)),
        fun v hv => hall _ (List.mem_append_left _ hv)⟩
    | wr _ _ _ _ _ => trivial
    | fence _ => trivial
    | fblock _ _ => trivial
    | spawn _ => trivial
    | join _ => trivial
  -- the rank argument
  have hwfF := wfFacts hwf
  have hn := noTwo_of_xl hxl
  have hc : cellsOk x.evs = true := by
    rw [hevs]
    refine cellsOk_of hl fun e he => ?_
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp he
    exact huok u hu
  have hreads' : ∀ r : Fin x.n, (x.ev r).isR = true →
      x.readBytes P.memTest.initB r.val = exps r.val := by
    intro r hr
    have := hreads r.val r.isLt (by rw [evN_eq x r.val r.isLt]; exact hr)
    rw [this]
  let G : Nat → Nat → List Byte → Prop := fun a s bs =>
    a < ctlAddr 0 → ∃ v ∈ dom, v < 2 ^ (8 * s) ∧ bs = natBytes v s
  have hcellOf : ∀ r : Fin x.n, (x.ev r).isM = true → low (x.ev r) →
      ((x.ev r).addr, (x.ev r).size) ∈ cellsOf P.locs := by
    intro r hM hlow
    obtain ⟨-, -, h⟩ := huok _ (pair_mem hevs r) hM
    simp only at h
    rcases h with h | ⟨-, h⟩
    · exact h
    · unfold low at hlow; omega
  have hgood := reads_good hwfF hn hc hxl.2.2.1 P.memTest.initB exps hreads' G
    (by
      intro r hr hlow
      obtain ⟨l, hlm, hla, hls⟩ := cell_facts hl (hcellOf r (isM_of_isR hr) hlow)
      simp only at hla hls
      refine ⟨l.init, memB_iff.mp (hini l hlm), by rw [← hls]; exact hl.init l hlm, ?_⟩
      simp only [Ev.bytes]
      rw [← hla, ← hls]
      exact init_bytes hl hlm)
    (by
      intro w hW hpre hlow
      have hwU := pair_mem hevs w
      obtain ⟨i, hi, hu⟩ := mem_accUnits hwU
      obtain ⟨hi', p, hp, he⟩ := hdata i hi
      have hu0 := hu
      rw [he, xtrace_acts] at hu
      have hu2 := thread_units_low _ i _ hu hlow
      obtain ⟨L1, l, L2, hsplit, hul⟩ := labUnits_split i _ p.1 _ hu2
      have htid : (x.ev w).tid = i := (threadUnits_pos i _ _ _ hul).1
      have hposw : labBase i (ctlLen P.threads[i] i) L1 ≤ (x.ev w).pos :=
        (threadUnits_pos i _ _ _ hul).2.1
      have hinU : ∀ u ∈ threadUnits i (ctlLen P.threads[i] i) (p.1.flatMap Lab.acts), u ∈ U := by
        intro u hu'
        refine accUnits_mem hi ?_
        rw [he, xtrace_acts]
        exact thread_units_flat _ i _ hu'
      have hQpre : ∀ u ∈ U, u.1.tid = i → u.1.pos < (x.ev w).pos → QP dom u := by
        intro u hu' htu hpu hR hlo
        obtain ⟨r, h1, h2⟩ := mem_pair hevs hu'
        have hpo : x.po r w = true := by
          simp only [Exec.po, h1, htid, htu, beq_self_eq_true, Bool.true_and, decide_eq_true_eq]
          exact hpu
        have := hpre r (by rw [h1]; exact hR) hpo
        rw [h1] at this
        have h2' : exps r.val = u.2 := h2
        rw [h2'] at this
        exact this hlo
      have hlm : ∀ l' ∈ L1 ++ [l], l' ∈ p.1 := by
        intro l' hl'; rw [hsplit]; simp only [List.mem_append, List.mem_cons] at hl' ⊢
        rcases hl' with h | h
        · exact .inl h
        · simp at h; exact .inr (.inl h)
      have hR1 : ∀ l' ∈ L1, ReadsIn dom l' := by
        intro l' hl'
        obtain ⟨q', hq'⟩ := labUnits_each i (ctlLen P.threads[i] i) L1 l' hl'
        refine lab_reads hl (hlab i hi' p hp l' (hlm l' (List.mem_append_left _ hl'))) i q'
          fun u hu' => ?_
        have h1 := hq' u hu'
        have hpos := (threadUnits_pos i _ _ _ h1)
        have h2 : u ∈ threadUnits i (ctlLen P.threads[i] i) (p.1.flatMap Lab.acts) := by
          rw [hsplit]; exact labUnits_pre_mem i _ L1 (l :: L2) u h1
        exact hQpre u (hinU u h2) hpos.1 (by unfold labBase at hposw; omega)
      have hok := hlab i hi' p hp l (hlm l (by simp))
      have hRl : ReadsIn dom l := by
        refine lab_reads hl hok i (labBase i (ctlLen P.threads[i] i) L1) fun u hu' hR hlo => ?_
        have h2 : u ∈ threadUnits i (ctlLen P.threads[i] i) (p.1.flatMap Lab.acts) := by
          rw [hsplit]; exact labUnits_mem i _ L1 l L2 u hu'
        exact hQpre u (hinU u h2) (threadUnits_pos i _ _ _ hu').1
          (lab_write_after hl hok i _ hul hW hlow u hu' hR) hR hlo
      have hcho : ∀ l' ∈ L1 ++ [l], Chosen dom l' := by
        intro l' hl'
        refine hchosen i hi' p hp l' (hlm l' hl') ?_
        simp only [List.mem_append, List.mem_singleton] at hl'
        rcases hl' with h | rfl
        · exact hR1 l' h
        · exact hRl
      have htake : p.1.take (L1.length + 1) = L1 ++ [l] := by
        rw [hsplit]; simp [List.take_append]
      have hpr := pre_of_run D dom _ _ p hp (L1.length + 1) (by rw [htake]; exact hcho)
      rw [htake] at hpr
      obtain ⟨v, hv, hvb, hd⟩ := lab_write_val hl hok i _ hul hW hlow
      have hvdom : v ∈ dom := by
        refine memB_iff.mp (hpw v ?_)
        simp only [Prog.preWritten, List.mem_flatMap]
        exact ⟨_, List.getElem_mem hi', _, hpr, l, by simp, hv⟩
      refine ⟨v, hvdom, hvb, ?_⟩
      rw [bytes_byte_data (by rw [hd, length_natBytes]), hd])
  -- every unit is good
  have hQP : ∀ u ∈ U, QP dom u := by
    intro u hu hR hlow
    obtain ⟨r, h1, h2⟩ := mem_pair hevs hu
    have := hgood r (by rw [h1]; exact hR)
    rw [h1] at this
    have h2' : exps r.val = u.2 := h2
    rw [h2'] at this
    exact this hlow
  -- every thread's run is a run over `dom`
  have hlen := hT.length_eq
  refine List.forall₂_iff_get.mpr ⟨by simpa [Prog.traces] using hlen, fun i h1 h2 => ?_⟩
  obtain ⟨hi', p, hp, he⟩ := hdata i h1
  simp only [List.get_eq_getElem, Prog.traces, List.getElem_mapIdx, List.mem_map]
  refine ⟨p, run_restrict D dom _ _ p hp fun l hlp => ?_, he.symm⟩
  refine hchosen i hi' p hp l hlp ?_
  obtain ⟨L1, L2, hsplit⟩ := List.append_of_mem hlp
  refine lab_reads hl (hlab i hi' p hp l hlp) i (labBase i (ctlLen P.threads[i] i) L1)
    fun u hu => hQP u ?_
  refine accUnits_mem h1 ?_
  rw [he, xtrace_acts]
  refine thread_units_flat _ i _ ?_
  rw [hsplit]
  exact labUnits_mem i _ L1 l L2 u hu

end Silmaril.Proofs.X86.Concurrency.Cir.Domain
