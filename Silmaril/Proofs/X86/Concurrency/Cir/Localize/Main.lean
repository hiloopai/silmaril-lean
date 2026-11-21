module

public import Silmaril.Proofs.X86.Concurrency.Cir.Localize.Finals

/-!
# Localisation: the theorem

`cirLocalize`: `Tv.Task.cirLocalize` holds.

Take a behaviour of `P`: traces `trs` and a candidate `x`. Thread `i`'s run splits into runs of
`pre`, `ops` and `post`. The fragment's units, restricted, replay sequentially from the initial
memory (`frag_replay`), so the fragment's trace is a `SeqRun` and `B.spec` holds of its inputs
and outputs. The block label with those values is a run of `local B` (over a larger domain), so
thread `i` of the localised program has a run with the same final registers. Its units are the
old ones with the fragment's replaced by the block's (`units_split`), and `Surg.exec x` is a
well-formed candidate over them, with right reads, consistent under the model, and with the same
final memory (`Surg.final_off`, `Surg.final_on`, `Surg.final_r`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Localize

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Seq
open Silmaril.X86.Concurrency.Cir.Tv (chain)
open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Litmus (Byte XAct XTrace threadUnits accUnits units rmwPairs initByte
  finalAx finalOf writtenByte Model Final ReadsOk Loc)

theorem cellsOk_of {B : Block} (h : B.cellsOk = true) : CellsOk (B.ins ++ B.outs) := by
  simp only [Block.cellsOk, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun c hc => ?_, fun c hc d hd => ?_⟩
  · have := h.1 c hc
    simp only [List.contains_iff_mem, List.mem_cons, List.not_mem_nil,
      or_false, beq_iff_eq] at this
    exact this
  · have := h.2 c hc d hd
    simp only [Bool.or_eq_true, beq_iff_eq, Tv.cellsDisjoint, decide_eq_true_eq] at this
    exact this

/-- The stores and read-modify-writes of `post` are plain, under XL. -/
theorem post_plain {l : Lab} (h : WbLab l) :
    ∀ a ∈ l.acts, (a.ev.kind = .store ∨ a.ev.kind = .rmw) → a.flavor = .plain := by
  intro a ha hk
  rcases hk with hk | hk
  · exact wb_acts h a ha hk
  · rcases lab_shape l a ha with ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ |
      ⟨_, rfl⟩ | ⟨_, fl, _, _, _, rfl, rfl⟩
    · simp [ldAct] at hk
    · simp [stAct] at hk
    · rfl
    · simp [fenceAct] at hk
    · simp [stAct] at hk

/-- Write units of plain actions are write-back. -/
theorem units_wb {i q : Nat} {as : List XAct}
    (h : ∀ a ∈ as, (a.ev.kind = .store ∨ a.ev.kind = .rmw) → a.flavor = .plain) :
    ∀ u ∈ threadUnits i q as, u.1.isW = true → u.1.ann = .wb := by
  refine threadUnits_all q as fun a ha p u hu hW => ?_
  unfold Silmaril.X86.MemoryModel.Litmus.actUnits at hu
  cases hk : a.ev.kind with
  | load => simp only [hk, List.mem_singleton] at hu; subst hu; simp [Ev.isW] at hW
  | store =>
    simp only [hk, List.mem_singleton] at hu; subst hu
    simp [h a ha (.inl hk), Silmaril.X86.MemoryModel.Litmus.annOf]
  | rmw =>
    simp only [hk, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> simp [h a ha (.inr hk), Silmaril.X86.MemoryModel.Litmus.annOf]
  | fence f => simp only [hk, List.mem_singleton] at hu; subst hu; simp [Ev.isW] at hW

/-- **Localisation.** -/
theorem cirLocalize : Tv.Task.cirLocalize := by
  intro P i pre ops post B hth hcell hops hloc hctl hpp hoth hrout hspec M f hweak hb
  obtain ⟨dom, trs, hF, x, hevs, hrmw, hwf, hro, hM, rfl⟩ := hb
  -- the cells
  have hcok : CellsOk (B.ins ++ B.outs) := cellsOk_of hcell
  have hpos : ∀ c ∈ B.ins ++ B.outs, 0 < c.2 := fun c hc => by
    rcases (hcok.1 c hc).1 with h | h | h | h <;> omega
  have h64 : ∀ c ∈ B.ins ++ B.outs, c.1 < 2 ^ 64 := fun c hc => by
    have := hctl c hc; simp only [ctlAddr] at this; omega
  -- statement checks
  have hops' : ∀ s ∈ ops, s.onCells (B.ins ++ B.outs) = true ∧ s.storesWithin B.outs = true ∧
      s.threadFree = true ∧ s.futexFree = true := fun s hs => by
    have := List.all_eq_true.mp hops s hs
    simp only [Bool.and_eq_true] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  have hco := chain_check (f := Stmt.onCells (B.ins ++ B.outs)) rfl (fun _ _ => rfl) ops
    fun s hs => (hops' s hs).1
  have hcw := chain_check (f := Stmt.storesWithin B.outs) rfl (fun _ _ => rfl) ops
    fun s hs => (hops' s hs).2.1
  have hct := chain_check (f := Stmt.threadFree) rfl (fun _ _ => rfl) ops
    fun s hs => (hops' s hs).2.2.1
  have hcf := chain_check (f := Stmt.futexFree) rfl (fun _ _ => rfl) ops
    fun s hs => (hops' s hs).2.2.2
  have hpre := chain_check (f := Stmt.avoids (B.ins ++ B.outs)) rfl (fun _ _ => rfl) pre
    fun s hs => List.all_eq_true.mp hpp s (List.mem_append_left _ hs)
  have hpost := chain_check (f := Stmt.avoids (B.ins ++ B.outs)) rfl (fun _ _ => rfl) post
    fun s hs => List.all_eq_true.mp hpp s (List.mem_append_right _ hs)
  -- thread `i`'s run
  have hi : i < P.threads.length := (List.getElem?_eq_some_iff.mp hth).1
  have hthi : P.threads[i] = ⟨chain (pre ++ ops ++ post), false⟩ :=
    (List.getElem?_eq_some_iff.mp hth).2
  have hlen : trs.length = P.threads.length := by rw [hF.length_eq, length_traces]
  have hi' : i < trs.length := by omega
  obtain ⟨hk0, p, hp, htri⟩ := trace_run hF i hi'
  simp only [hthi] at hp htri
  obtain ⟨tr12, rs2, tr3, h12, h3, htr⟩ := (run_chain_append dom (pre ++ ops) post _ _ _).mp hp
  obtain ⟨tr1, rs1, tr2, h1, h2, htr12⟩ := (run_chain_append dom pre ops _ _ _).mp h12
  -- labels
  have hfrag : ∀ l ∈ tr2, FragLab (B.ins ++ B.outs) B.outs l :=
    run_frag dom _ B.outs h64 (chain ops) hco hcw hct hcf rs1 (tr2, rs2) h2
  have hav1 : ∀ l ∈ tr1, ∀ a ∈ l.acts, ActAvoid (B.ins ++ B.outs) a :=
    run_avoid dom _ hctl (chain pre) hpre Regs.zero (tr1, rs1) h1
  have hav3 : ∀ l ∈ tr3, ∀ a ∈ l.acts, ActAvoid (B.ins ++ B.outs) a :=
    run_avoid dom _ hctl (chain post) hpost rs2 (tr3, p.2) h3
  have hacts : (trs[i]).acts = tr1.flatMap Lab.acts ++ tr2.flatMap Lab.acts ++
      tr3.flatMap Lab.acts := by
    rw [htri, xtrace_acts, thread_acts_false, htr, htr12]
    simp [List.flatMap_append]
  have hothA : ∀ k (hk : k < trs.length), k ≠ i →
      ∀ a ∈ (trs[k]).acts, ActAvoid (B.ins ++ B.outs) a := by
    intro k hk hki a ha
    obtain ⟨hk', q, hq, he⟩ := trace_run hF k hk
    rw [he, xtrace_acts] at ha
    exact thread_avoid hctl (hoth k _ hki (List.getElem?_eq_getElem hk')) hq a ha
  have h13 : ∀ a ∈ tr1.flatMap Lab.acts ++ tr3.flatMap Lab.acts, ActAvoid (B.ins ++ B.outs) a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨l, hl, ha⟩ := List.mem_flatMap.mp ha; exact hav1 l hl a ha
    · obtain ⟨l, hl, ha⟩ := List.mem_flatMap.mp ha; exact hav3 l hl a ha
  have h2c : ∀ a ∈ tr2.flatMap Lab.acts,
      (∃ f, a.ev.kind = .fence f) ∨ (a.ev.addr, a.ev.size) ∈ B.ins ++ B.outs := by
    intro a ha
    obtain ⟨l, hl, ha⟩ := List.mem_flatMap.mp ha
    exact (frag_acts (hfrag l hl) a ha).1
  -- the old units
  set a1 := tr1.flatMap Lab.acts with ha1
  set a2 := tr2.flatMap Lab.acts with ha2
  set a3 := tr3.flatMap Lab.acts with ha3
  set p1 := (threadUnits i 0 a1).length with hp1
  have hold := (units_split trs i hi' (trOf (a1 ++ a3)) a1 a2 a3 [] hacts
    (by simp [trOf_acts']) (B.ins ++ B.outs) hcok hothA h13
    (fun a ha => by
      rcases List.mem_append.mp ha with ha | ha
      · exact h2c a ha
      · simp at ha) p1 rfl).1
  set A := (((UL trs).take i).flatten ++ threadUnits i 0 a1).flatMap (sp (accUnits trs)) with hA
  set C := (threadUnits i (p1 + (threadUnits i p1 a2).length) a3 ++
    ((UL trs).drop (i + 1)).flatten).flatMap (sp (accUnits trs)) with hC
  have hl3 : ∀ a ∈ a3, a.ev.locked = true → a.ev.kind = .rmw := fun a ha => by
    obtain ⟨l, -, ha⟩ := List.mem_flatMap.mp ha; exact lab_lock l a ha
  have hAK := partA hothA (fun a ha => h13 a (List.mem_append_left _ ha))
  have hCK := partC (q := p1 + (threadUnits i p1 a2).length) hothA
    (fun a ha => h13 a (List.mem_append_right _ ha)) hl3
  have hFC : ∀ u ∈ threadUnits i p1 a2, UC (B.ins ++ B.outs) u :=
    threadUnits_all _ _ fun a ha p => actUnits_UC (h2c a ha) i p
  -- the initial memory
  set m0 : Mem := initByte P.locs with hm0
  have H0 := mkHyp (B.ins ++ B.outs) (fun y => (m0 y).getD 0) A (threadUnits i p1 a2) [] C i p1
    hAK hCK hFC (by simp) (by simp) (by simp)
  set S0 : Surg := ⟨A, threadUnits i p1 a2, [], C, i, p1, cellB (B.ins ++ B.outs)⟩ with hS0
  have hx0 : x.evs = S0.old.map Prod.fst := by rw [hevs, hold]; rfl
  have hro0 : ∀ r < x.n, (x.evN r).isR = true →
      x.readBytes (fun y => (m0 y).getD 0) r = (S0.old.map Prod.snd).getD r [] := by
    intro r hr hR
    have := hro r hr hR
    rw [hold] at this
    exact this
  have hxl : x.Xl := model_le_xl M x hM
  have hrmw' : x.rmw = rmwPairs x.evs := by rw [hrmw, hevs]
  -- the fragment replays
  have hok : ∀ a ∈ a2, ActOk a := fun a ha => by
    obtain ⟨l, hl, ha⟩ := List.mem_flatMap.mp ha
    exact actOk_of_ok (frag_ok hpos (hfrag l hl)) a ha
  have hrep := frag_replay hcok H0 hx0 hwf hrmw' hro0 hxl a2 rfl h2c hok
  set m1 := finalMem m0 (S0.rexec (units [trOf a2]) x) with hm1
  have hreplay : replay m0 tr2 = some m1 := by
    rw [replay_eq m0 tr2 (fun l hl => frag_ok hpos (hfrag l hl))]; exact hrep
  have hsp := hspec rs1 m0 tr2 rs2 m1 ⟨⟨dom, h2⟩, hreplay⟩
  -- the block
  set ivs := B.ins.map fun c => (m0.val c.1 c.2).getD 0 with hivs
  set rvs := B.rout.map fun r => (rs2 r).toNat with hrvs
  set ovs := B.outs.map fun c => (m1.val c.1 c.2).getD 0 with hovs
  set lb := Lab.blk B.name (cellVals B.ins ivs) (cellVals B.outs ovs) rvs with hlb
  set dom' := dom ++ ivs ++ rvs ++ ovs with hdom'
  have hdom : ∀ v ∈ dom, v ∈ dom' := fun v hv => by simp [hdom', hv]
  have hregs : rs1.setMany B.rout rvs = rs2 := by
    funext r
    rw [hrvs, setMany_map]
    split
    · rfl
    · rename_i hr
      refine (run_frame dom (chain ops) rs1 (tr2, rs2) h2 r ?_).symm
      rw [chain_writes]
      simp only [List.mem_flatMap, not_exists, not_and]
      exact fun s hs hrs => hr (hrout s hs r hrs)
  have hblk : ([lb], rs2) ∈ run dom' (.local B) rs1 := by
    simp only [run, runBlock, List.mem_flatMap, List.mem_filterMap]
    refine ⟨ivs, ?_, rvs, ?_, ovs, ?_, ?_⟩
    · refine seqL_of _ _ _ (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun c _ => ?_))
      exact pick_of (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map_of_mem (f := fun (c : Nat × Nat) => (m0.val c.1 c.2).getD 0) (by assumption)))))
        (getD_val_lt _ _ _)
    · refine seqL_of _ _ _ (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun r hr => ?_))
      exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_map_of_mem (f := fun r => (rs2 r).toNat) hr))
    · refine seqL_of _ _ _ (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun c hc => ?_))
      exact pick_of (List.mem_append_right _
        (List.mem_map_of_mem (f := fun (c : Nat × Nat) => (m1.val c.1 c.2).getD 0) hc)) (getD_val_lt _ _ _)
    · simp only [@decide_eq_true _ (B.dec _ _) hsp, ↓reduceIte, hregs]
      rfl
  -- the new thread
  set th' : Thread := ⟨chain (pre ++ [.local B] ++ post), false⟩ with hth'
  have hrun' : (tr1 ++ [lb] ++ tr3, p.2) ∈ run dom' th'.body Regs.zero := by
    refine (run_chain_append dom' (pre ++ [.local B]) post _ _ _).mpr
      ⟨tr1 ++ [lb], rs2, tr3, ?_, run_mono hdom _ _ _ h3, rfl⟩
    refine (run_chain_append dom' pre [.local B] _ _ _).mpr
      ⟨tr1, rs1, [lb], run_mono hdom _ _ _ h1, ?_, rfl⟩
    show ([lb], rs2) ∈ Res.bind (run dom' (.local B) rs1) (run dom' .skip)
    have := mem_bind (a := ([lb], rs2)) (b := ([], rs2)) (k := run dom' .skip) hblk (by simp [run])
    simpa using this
  set t' := th'.xtrace i (tr1 ++ [lb] ++ tr3, p.2) with ht'
  set b := blkActs m0 m1 B.ins B.outs with hb
  have hlbacts : lb.acts = b := blk_acts B.name m0 m1 B.ins B.outs rvs
  have hacts' : t'.acts = a1 ++ b ++ a3 := by
    rw [ht', xtrace_acts, thread_acts_false]
    simp [List.flatMap_append, hlbacts, ha1, ha3]
  have h2cb : ∀ a ∈ a2 ++ b,
      (∃ f, a.ev.kind = .fence f) ∨ (a.ev.addr, a.ev.size) ∈ B.ins ++ B.outs := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact h2c a ha
    · simp only [hb, blkActs, List.mem_append, List.mem_map] at ha
      rcases ha with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
      · exact .inr (List.mem_append_left _ hc)
      · exact .inr (List.mem_append_right _ hc)
  have hnew := (units_split trs i hi' t' a1 a2 a3 b hacts hacts' (B.ins ++ B.outs) hcok hothA h13
    h2cb p1 rfl).2
  -- the surgery
  have H := mkHyp (B.ins ++ B.outs) (fun y => (m0 y).getD 0) A (threadUnits i p1 a2)
    (threadUnits i p1 b) C i p1 hAK hCK hFC
    (blk_units (B.ins ++ B.outs) _ m0 m1 B.ins B.outs (fun c hc => hc) hpos (fun _ => rfl) i p1)
    (threadUnits_pos i p1 b) (blk_rw m0 m1 B.ins B.outs i p1)
  set S : Surg := ⟨A, threadUnits i p1 a2, threadUnits i p1 b, C, i, p1, cellB (B.ins ++ B.outs)⟩
    with hS
  have hx : x.evs = S.old.map Prod.fst := hx0
  have hnew' : units (trs.set i t') = S.new := by
    rw [hnew]
    rfl
  -- under XL, the writes of thread `i` after the fragment are write-back
  have hwk : M = .xl → ∀ u ∈ S.C, u.1.tid = S.i → u.1.isW = true → u.1.weak = false := by
    intro hxl' u hu ht hW
    have hpw := chain_check (f := Stmt.wbStores) rfl (fun _ _ => rfl) post
      (fun s hs => List.all_eq_true.mp (hweak hxl') s hs)
    have hwl := run_wb dom (chain post) hpw rs2 (tr3, p.2) h3
    have hplain : ∀ a ∈ a3, (a.ev.kind = .store ∨ a.ev.kind = .rmw) → a.flavor = .plain :=
      fun a ha => by
        obtain ⟨l, hl, ha⟩ := List.mem_flatMap.mp ha; exact post_plain (hwl l hl) a ha
    obtain ⟨v, hv, huv⟩ := mem_sp_flatMap hu
    obtain ⟨ht', -, -, -, hann, -⟩ := sp_fields huv
    rcases List.mem_append.mp hv with hv | hv
    · have := units_wb hplain v hv (by rw [← sp_isW huv]; exact hW)
      simp [Ev.weak, hann, this]
    · obtain ⟨k, hk, hik, hv'⟩ := mem_drop_UL hv
      have : u.1.tid = k := by rw [ht', mem_threadUnits_tid hv']
      change u.1.tid = i at ht
      omega
  -- the fragment's writes are on out cells
  have hFW : ∀ u ∈ threadUnits i p1 a2, u.1.isW = true → (u.1.addr, u.1.size) ∈ B.outs := by
    refine threadUnits_all p1 a2 fun a ha q u hu hW => ?_
    obtain ⟨l, hl, ha⟩ := List.mem_flatMap.mp ha
    have hout := (frag_acts (hfrag l hl) a ha).2
    unfold Silmaril.X86.MemoryModel.Litmus.actUnits at hu
    cases hk : a.ev.kind with
    | load => simp only [hk, List.mem_singleton] at hu; subst hu; simp [Ev.isW] at hW
    | store => simp only [hk, List.mem_singleton] at hu; subst hu; exact hout (.inl hk)
    | rmw =>
      simp only [hk, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> exact hout (.inr hk)
    | fence f => simp only [hk, List.mem_singleton] at hu; subst hu; simp [Ev.isW] at hW
  -- the cell bytes are mapped initially
  have hm0 : ∀ y, cellB (B.ins ++ B.outs) y = true → ∃ v, m0 y = some v := by
    intro y hy
    simp only [cellB, List.any_eq_true, decide_eq_true_eq] at hy
    obtain ⟨c, hc, hc1, hc2⟩ := hy
    obtain ⟨l, hl, hl1, hl2⟩ := hloc c hc
    exact initByte_some hl ⟨by omega, by omega⟩
  have R := rhyp_frag (S := S0) hcok a2 rfl h2c
  have hfr := fun y (hy : cellB (B.ins ++ B.outs) y = true) =>
    Surg.final_r (ib := fun y => (m0 y).getD 0) H0 R hx0 hwf hrmw' hy
  have hm1 : ∀ y, cellB (B.ins ++ B.outs) y = true →
      m1 y = if writtenByte x y then some (x.finalByte (fun y => (m0 y).getD 0) y) else m0 y := by
    intro y hy
    obtain ⟨hw1, hw2⟩ := hfr y hy
    simp only [hm1, finalMem]
    rw [hw1]
    split
    · rename_i hw; rw [hw2 hw]
    · rfl
  -- the behaviour
  refine ⟨finalAx (Prog.memTest ⟨P.locs, P.threads.set i th'⟩) (trs.set i t') (S.exec x),
    ⟨dom', trs.set i t', forall2_set hdom hF th' t' ⟨_, hrun', rfl⟩, S.exec x, ?_, ?_, ?_, ?_, ?_,
      rfl⟩, ?_, ?_⟩
  · show S.new.map Prod.fst = _; rw [hnew']
  · show rmwPairs (S.new.map Prod.fst) = _; rw [hnew']
  · exact Surg.wf H hx hwf hrmw'
  · intro r hr hR
    rw [hnew']
    exact Surg.readsOk H hx hwf hro0 r hr hR
  · cases M with
    | sc => exact Surg.sc H hx hwf hrmw' hM
    | tso => exact Surg.tso H hx hwf hrmw' hM
    | xl => exact Surg.xl H hx hwf hrmw' hM (hwk rfl)
  · -- the final memory
    show (fun y => if writtenByte (S.exec x) y then
        some ((S.exec x).finalByte (fun y => (m0 y).getD 0) y) else m0 y) =
      (fun y => if writtenByte x y then some (x.finalByte (fun y => (m0 y).getD 0) y) else m0 y)
    funext y
    cases hy : cellB (B.ins ++ B.outs) y
    · obtain ⟨hw1, hw2⟩ := Surg.final_off (ib := fun y => (m0 y).getD 0) H hx hwf hy
      rw [hw1]
      split
      · rename_i hw; rw [hw2 hw]
      · rfl
    · rw [← hm1 y hy]
      obtain ⟨hw1, hw2⟩ := Surg.final_on (ib := fun y => (m0 y).getD 0) H hx hwf hy
      split
      · rename_i hw
        obtain ⟨k, hk, hW, hC, hfin⟩ := hw2 hw
        rw [hfin, (blk_W m0 m1 B.ins B.outs i p1 (List.getElem_mem hk) hW hC).1]
        obtain ⟨v, hv⟩ : ∃ v, m1 y = some v := by
          rw [hm1 y hy]
          split
          · exact ⟨_, rfl⟩
          · exact hm0 y hy
        rw [hv]; rfl
      · rename_i hw
        rw [hm1 y hy]
        have hnw : writtenByte x y = false := by
          cases hwx : writtenByte x y
          · rfl
          · exfalso
            obtain ⟨w, hw', hW, hC⟩ := written_iff.mp hwx
            have he : x.evs[w] = (S.old.map Prod.fst)[w]'(by rw [← hx]; exact hw') :=
              List.getElem_of_eq hx _
            have hwo : w < S.A.length + S.F.length + S.C.length := lt_of_lt_of_eq hw' (Surg.n_old hx)
            rw [he] at hW hC
            rcases Nat.lt_or_ge w S.A.length with h1 | h1
            · rw [S.old_A h1] at hW hC
              have := cellB_false (hAK _ (List.getElem_mem _)).1 (isM_of_W hW) hC
              rw [hy] at this; cases this
            · rcases Nat.lt_or_ge w (S.A.length + S.F.length) with h2 | h2
              · rw [S.old_F h1 h2] at hW hC
                have hu := List.getElem_mem (l := threadUnits i p1 a2) (n := w - S.A.length)
                  (by change w - S.A.length < S.F.length; omega)
                have hout := hFW _ hu hW
                have hUC := hFC _ hu (isM_of_W hW)
                rw [covers_iff] at hC
                obtain ⟨u, hu', hW', hC'⟩ := blk_W_of m0 m1 B.ins B.outs i p1 hout
                  (y := y) ⟨by simpa using hC.1, by simpa using hC.2⟩
                obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hu'
                exact hw (hw1.mpr ⟨k, hk, hW', hC'⟩)
              · rw [S.old_C h2] at hW hC
                have := cellB_false (hCK _ (List.getElem_mem _)).1 (isM_of_W hW) hC
                rw [hy] at this; cases this
        simp [hnw]
  · -- the final registers
    show (finalOf (trs.set i t') _).regs = (finalOf trs _).regs
    funext k r
    simp only [finalOf, List.getElem?_set]
    split
    · rename_i hik
      subst hik
      rw [List.getElem?_eq_getElem hi', htri]
      simp [ht', Thread.xtrace]
    · rfl

end Silmaril.Proofs.X86.Concurrency.Cir.Localize
