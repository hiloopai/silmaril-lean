module

public import Silmaril.Proofs.X86.Concurrency.Cir.Fj.Exec

/-!
# Fork-join CIR: every behaviour under `M ⊑ XL` is the sequential one

The proof of `Fj.Par.behav_mem`, for any fork-join program with
disjoint footprints and any XL-consistent, well-formed candidate execution:

1. **who touches a data byte** (`data_unit`): only the block loads and stores of the jobs; the
   ghost control bytes of spawn and join lie above the data region;
2. **worker inputs are initial** (`worker_ins`): no unit writes a worker's input byte, so by
   `Exec.Wf` every read of it takes the initial byte;
3. **the combine reads the workers' outputs** (`comb_ins`): a combine load of a worker's
   output byte that took the initial byte would close a `ghbXl` cycle
   `load -fr-> worker store -lock-> worker end -rfe-> join -lock-> load`; any write it takes
   is a worker's store of that byte, which writes the sequential value;
4. **final memory** (`final_mem`): the coherence-last write of a data byte is a job's store of
   it, which writes the sequential value.

Only XL's `acyclic ghbXl` and `Exec.Wf` are used, so the result holds for every `M ⊑ XL`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Fj

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Fj
open Silmaril.X86.MemoryModel.Litmus (Byte XAct XTrace units ReadsOk finalAx finalOf writtenByte
  AxReach initByte actUnits threadUnits)
open Silmaril.X86.MemoryModel.Axiomatic (Ev Exec BRel)

/-! ## The chosen traces -/

/-- The chosen trace and block values of every thread. -/
structure Pick (F : Par) (dom : List Nat) (trs : List XTrace) where
  tr0 : XTrace
  ivc : List Nat
  ovc : List Nat
  trw : Nat → XTrace
  iv : Nat → List Nat
  ov : Nat → List Nat
  len : trs.length = F.jobs.length + 1
  h0 : trs[0]? = some tr0
  fic : Fits dom ivc F.comb.ins
  foc : Fits dom ovc F.comb.outs
  fnc : ovc = F.comb.fn ivc
  acts0 : tr0.acts = (spawnActs F.jobs.length ++ joinActs F.jobs.length) ++ blkActs F.comb ivc ovc
  hw : ∀ k (_ : k < F.jobs.length), trs[k + 1]? = some (trw k)
  fi : ∀ k (hk : k < F.jobs.length), Fits dom (iv k) F.jobs[k].ins
  fo : ∀ k (hk : k < F.jobs.length), Fits dom (ov k) F.jobs[k].outs
  fn : ∀ k (hk : k < F.jobs.length), ov k = F.jobs[k].fn (iv k)
  actsw : ∀ k (hk : k < F.jobs.length), (trw k).acts =
    ([ctlAct (k + 1) 1 2] ++ blkActs F.jobs[k] (iv k) (ov k)) ++ [endAct (k + 1) 0 1]

theorem pick_of_shape {F : Par} {dom : List Nat} {trs : List XTrace} (h : Shape F dom trs) :
    Nonempty (Pick F dom trs) := by
  obtain ⟨tr0, ivc, ovc, h0, fic, foc, fnc, acts0⟩ := h.main
  have hw : ∀ k, ∃ tr ivs ovs, ∀ hk : k < F.jobs.length, trs[k + 1]? = some tr ∧
      Fits dom ivs F.jobs[k].ins ∧ Fits dom ovs F.jobs[k].outs ∧ ovs = F.jobs[k].fn ivs ∧
      tr.acts = ([ctlAct (k + 1) 1 2] ++ blkActs F.jobs[k] ivs ovs) ++ [endAct (k + 1) 0 1] := by
    intro k
    by_cases hk : k < F.jobs.length
    · obtain ⟨tr, ivs, ovs, h⟩ := h.worker k hk
      exact ⟨tr, ivs, ovs, fun _ => h⟩
    · exact ⟨tr0, [], [], fun h => absurd h hk⟩
  choose trw iv ov hall using hw
  exact ⟨⟨tr0, ivc, ovc, trw, iv, ov, h.len, h0, fic, foc, fnc, acts0, fun k hk => (hall k hk).1,
    fun k hk => (hall k hk).2.1, fun k hk => (hall k hk).2.2.1, fun k hk => (hall k hk).2.2.2.1,
    fun k hk => (hall k hk).2.2.2.2⟩⟩

variable {F : Par} {dom : List Nat} {trs : List XTrace}

/-- The position bound of the main thread's spawn and join units. -/
def Pick.l0 (_ : Pick F dom trs) : Nat :=
  (threadUnits 0 0 (spawnActs F.jobs.length ++ joinActs F.jobs.length)).length

/-- The position bound of worker `k`'s start and block units. -/
def Pick.lw (P : Pick F dom trs) (k : Nat) (_hk : k < F.jobs.length) : Nat :=
  (threadUnits (k + 1) 0 ([ctlAct (k + 1) 1 2] ++ blkActs F.jobs[k] (P.iv k) (P.ov k))).length

/-- The traces are the only ones of their threads. -/
theorem Pick.thread (P : Pick F dom trs) {i : Nat} {tr : XTrace} (h : trs[i]? = some tr) :
    (i = 0 ∧ tr = P.tr0) ∨ ∃ k, k < F.jobs.length ∧ i = k + 1 ∧ tr = P.trw k := by
  rcases i with _ | k
  · rw [P.h0] at h; exact .inl ⟨rfl, (Option.some.inj h).symm⟩
  · have hk : k < F.jobs.length := by
      have := (List.getElem?_eq_some_iff.mp h).1; rw [P.len] at this; omega
    rw [P.hw k hk] at h
    exact .inr ⟨k, hk, rfl, (Option.some.inj h).symm⟩

theorem Pick.mem_tr0 (P : Pick F dom trs) {u : Ev × List Byte}
    (hu : u ∈ threadUnits 0 0 P.tr0.acts) :
    ((∃ a ∈ spawnActs F.jobs.length ++ joinActs F.jobs.length, UnitOf 0 a u) ∧ u.1.pos < P.l0) ∨
      ((∃ a ∈ blkActs F.comb P.ivc P.ovc, UnitOf 0 a u) ∧ P.l0 ≤ u.1.pos) := by
  rw [P.acts0] at hu
  simpa [Pick.l0] using threadUnits_pos_append hu

theorem Pick.mem_trw (P : Pick F dom trs) {k : Nat} (hk : k < F.jobs.length) {u : Ev × List Byte}
    (hu : u ∈ threadUnits (k + 1) 0 (P.trw k).acts) :
    ((∃ a ∈ [ctlAct (k + 1) 1 2] ++ blkActs F.jobs[k] (P.iv k) (P.ov k), UnitOf (k + 1) a u) ∧
        u.1.pos < P.lw k hk) ∨
      (UnitOf (k + 1) (endAct (k + 1) 0 1) u ∧ P.lw k hk ≤ u.1.pos) := by
  rw [P.actsw k hk] at hu
  rcases threadUnits_pos_append hu with h | ⟨⟨a, ha, h⟩, h'⟩
  · exact .inl (by simpa [Pick.lw] using h)
  · simp only [List.mem_singleton] at ha; subst ha
    exact .inr ⟨h, by simpa [Pick.lw] using h'⟩

/-! ## Who touches a data byte -/

theorem unitOf_has {i : Nat} {a : XAct} {q : Ev × List Byte} (hq : UnitOf i a q) {y : Nat}
    (hy : q.1.covers y = true) : Act.has a y := hq.cov y hy

/-- **A unit covering a data byte is a block load or store** of the main thread (after its
join units) or of a worker (before its end unit). -/
theorem data_unit (P : Pick F dom trs) {q : Ev × List Byte} (hq : q ∈ units trs)
    {y : Nat} (hy : q.1.covers y = true) (hlow : y < dataTop) :
    (∃ a ∈ blkActs F.comb P.ivc P.ovc, UnitOf 0 a q ∧ P.l0 ≤ q.1.pos) ∨
      ∃ k, ∃ hk : k < F.jobs.length, ∃ a ∈ blkActs F.jobs[k] (P.iv k) (P.ov k),
        UnitOf (k + 1) a q ∧ q.1.pos < P.lw k hk := by
  obtain ⟨i, tr, htr, u, hu, htr', hpos, -, -⟩ := units_src hq
  rcases P.thread htr with ⟨rfl, rfl⟩ | ⟨k, hk, rfl, rfl⟩
  · rcases P.mem_tr0 hu with ⟨⟨a, ha, hau⟩, -⟩ | ⟨⟨a, ha, hau⟩, hp⟩
    · exfalso
      have := unitOf_has (htr' a hau) hy
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨k, -, rfl⟩ := mem_spawnActs ha
        have := ctl_has this; have := dataTop_le_ctl (k + 1); omega
      · obtain ⟨k, -, rfl⟩ := mem_joinActs ha
        have := end_has this; have := dataTop_le_end (k + 1); omega
    · exact .inl ⟨a, ha, htr' a hau, hpos ▸ hp⟩
  · rcases P.mem_trw hk hu with ⟨⟨a, ha, hau⟩, hp⟩ | ⟨hau, -⟩
    · rcases List.mem_append.mp ha with ha | ha
      · exfalso
        simp only [List.mem_singleton] at ha; subst ha
        have := ctl_has (unitOf_has (htr' _ hau) hy); have := dataTop_le_ctl (k + 1); omega
      · exact .inr ⟨k, hk, a, ha, htr' a hau, hpos ▸ hp⟩
    · exfalso
      have := end_has (unitOf_has (htr' _ hau) hy); have := dataTop_le_end (k + 1); omega

/-- A store unit of a block writes the stored value's bytes. -/
theorem st_byte {i : Nat} {c : Nat × Nat × Nat} {q : Ev × List Byte}
    (hq : UnitOf i (stAct .wb c.1 c.2.1 c.2.2) q) (hW : q.1.isW = true) {y : Nat}
    (hy : q.1.covers y = true) :
    Cell.has (cellOf c) y ∧ q.1.byte y = byteOf c.2.2 (y - c.1) := by
  have hh := hq.cov y hy
  simp only [stAct] at hh
  refine ⟨hh, ?_⟩
  rw [hq.wr hW y hy]
  simp only [stAct]
  exact natBytes_getD (by omega)

/-- A load unit of a block expects the loaded value's bytes. -/
theorem ld_byte {i : Nat} {c : Nat × Nat × Nat} {q : Ev × List Byte}
    (hq : UnitOf i (ldAct .wb c.1 c.2.1 c.2.2) q) (hR : q.1.isR = true) {y : Nat}
    (hy : q.1.covers y = true) :
    Cell.has (cellOf c) y ∧ q.2.getD (y - q.1.addr) 0 = byteOf c.2.2 (y - c.1) := by
  have hh := hq.cov y hy
  simp only [ldAct] at hh
  refine ⟨hh, ?_⟩
  rw [hq.rd hR y hy]
  simp only [ldAct]
  exact natBytes_getD (by omega)

/-- **The writers of a data byte**: a store of an output cell of the combine or of a job. -/
theorem data_writer (P : Pick F dom trs) {q : Ev × List Byte} (hq : q ∈ units trs)
    (hW : q.1.isW = true) {y : Nat} (hy : q.1.covers y = true) (hlow : y < dataTop) :
    (∃ c ∈ cellVals F.comb.outs P.ovc, Cell.has (cellOf c) y ∧
        q.1.byte y = byteOf c.2.2 (y - c.1)) ∨
      ∃ k, ∃ hk : k < F.jobs.length, ∃ c ∈ cellVals F.jobs[k].outs (P.ov k),
        Cell.has (cellOf c) y ∧ q.1.byte y = byteOf c.2.2 (y - c.1) ∧ q.1.tid = k + 1 ∧
          q.1.pos < P.lw k hk := by
  rcases data_unit P hq hy hlow with ⟨a, ha, hau, -⟩ | ⟨k, hk, a, ha, hau, hp⟩
  · rcases mem_blkActs ha with ⟨c, -, rfl⟩ | ⟨c, hc, rfl⟩
    · exfalso; rcases hau.kW hW with h | h <;> simp [ldAct] at h
    · exact .inl ⟨c, hc, st_byte hau hW hy⟩
  · rcases mem_blkActs ha with ⟨c, -, rfl⟩ | ⟨c, hc, rfl⟩
    · exfalso; rcases hau.kW hW with h | h <;> simp [ldAct] at h
    · exact .inr ⟨k, hk, c, hc, (st_byte hau hW hy).1, (st_byte hau hW hy).2, hau.tid, hp⟩

/-- **The readers of a data byte**: a load of an input cell of the combine or of a job. -/
theorem data_reader (P : Pick F dom trs) {q : Ev × List Byte} (hq : q ∈ units trs)
    (hR : q.1.isR = true) {y : Nat} (hy : q.1.covers y = true) (hlow : y < dataTop) :
    (∃ c ∈ cellVals F.comb.ins P.ivc, Cell.has (cellOf c) y ∧
        q.2.getD (y - q.1.addr) 0 = byteOf c.2.2 (y - c.1) ∧ q.1.tid = 0 ∧ P.l0 ≤ q.1.pos) ∨
      ∃ k, ∃ hk : k < F.jobs.length, ∃ c ∈ cellVals F.jobs[k].ins (P.iv k),
        Cell.has (cellOf c) y ∧ q.2.getD (y - q.1.addr) 0 = byteOf c.2.2 (y - c.1) := by
  rcases data_unit P hq hy hlow with ⟨a, ha, hau, hp⟩ | ⟨k, hk, a, ha, hau, -⟩
  · rcases mem_blkActs ha with ⟨c, hc, rfl⟩ | ⟨c, -, rfl⟩
    · exact .inl ⟨c, hc, (ld_byte hau hR hy).1, (ld_byte hau hR hy).2, hau.tid, hp⟩
    · exfalso; rcases hau.kR hR with h | h <;> simp [stAct] at h
  · rcases mem_blkActs ha with ⟨c, hc, rfl⟩ | ⟨c, -, rfl⟩
    · exact .inr ⟨k, hk, c, hc, ld_byte hau hR hy⟩
    · exfalso; rcases hau.kR hR with h | h <;> simp [stAct] at h

/-! ## Existence of units -/

/-- A unit of an action in the first part of a thread's actions. -/
theorem exists_left {i : Nat} {tr : XTrace} (htr : trs[i]? = some tr) {l l' : List XAct}
    (hacts : tr.acts = l ++ l') {a : XAct} (ha : a ∈ l) {Q : Ev → Bool} {y : Nat}
    (hP : ∀ p, ∃ u ∈ actUnits i p a, Q u.1 = true ∧ u.1.covers y = true)
    (hQ : ∀ e e' : Ev, e'.pos = e.pos → e'.isR = e.isR → e'.isW = e.isW → Q e = true →
      Q e' = true) :
    ∃ q ∈ units trs, UnitOf i a q ∧ Q q.1 = true ∧ q.1.covers y = true ∧
      q.1.pos < (threadUnits i 0 l).length := by
  obtain ⟨u, hu, hQu, hyu, hau⟩ := threadUnits_exists (P := fun u => Q u.1 = true ∧
    u.1.covers y = true ∧ UnitOf i a u) (fun p => by
      obtain ⟨u, hu, h1, h2⟩ := hP p
      exact ⟨u, hu, h1, h2, (actUnits_src hu).1⟩) (p := 0) ha
  have hpos := (threadUnits_src hu).2.2
  have hu' : u ∈ threadUnits i 0 tr.acts := by
    rw [hacts, threadUnits_append]; exact List.mem_append_left _ hu
  obtain ⟨q, hq, ht, hp, hr, hw, hc⟩ := units_exists htr hu' hyu
  exact ⟨q, hq, ht a hau, hQ _ _ hp hr hw hQu, hc, by omega⟩

/-- A unit of an action in the second part of a thread's actions. -/
theorem exists_right {i : Nat} {tr : XTrace} (htr : trs[i]? = some tr) {l l' : List XAct}
    (hacts : tr.acts = l ++ l') {a : XAct} (ha : a ∈ l') {Q : Ev → Bool} {y : Nat}
    (hP : ∀ p, ∃ u ∈ actUnits i p a, Q u.1 = true ∧ u.1.covers y = true)
    (hQ : ∀ e e' : Ev, e'.pos = e.pos → e'.isR = e.isR → e'.isW = e.isW → Q e = true →
      Q e' = true) :
    ∃ q ∈ units trs, UnitOf i a q ∧ Q q.1 = true ∧ q.1.covers y = true ∧
      (threadUnits i 0 l).length ≤ q.1.pos := by
  obtain ⟨u, hu, hQu, hyu, hau⟩ := threadUnits_exists (P := fun u => Q u.1 = true ∧
    u.1.covers y = true ∧ UnitOf i a u) (fun p => by
      obtain ⟨u, hu, h1, h2⟩ := hP p
      exact ⟨u, hu, h1, h2, (actUnits_src hu).1⟩) (p := (threadUnits i 0 l).length) ha
  have hpos := (threadUnits_src hu).2.1
  have hu' : u ∈ threadUnits i 0 tr.acts := by
    rw [hacts, threadUnits_append]; exact List.mem_append_right _ (by simpa using hu)
  obtain ⟨q, hq, ht, hp, hr, hw, hc⟩ := units_exists htr hu' hyu
  exact ⟨q, hq, ht a hau, hQ _ _ hp hr hw hQu, hc, by omega⟩

theorem qR : ∀ e e' : Ev, e'.pos = e.pos → e'.isR = e.isR → e'.isW = e.isW → e.isR = true →
    e'.isR = true := fun _ _ _ h _ h' => h ▸ h'

theorem qW : ∀ e e' : Ev, e'.pos = e.pos → e'.isR = e.isR → e'.isW = e.isW → e.isW = true →
    e'.isW = true := fun _ _ _ _ h h' => h ▸ h'

theorem qRP (l : Nat) : ∀ e e' : Ev, e'.pos = e.pos → e'.isR = e.isR → e'.isW = e.isW →
    (e.isR && decide (l ≤ e.pos)) = true → (e'.isR && decide (l ≤ e'.pos)) = true := by
  intro e e' h1 h2 _ h; simpa [h1, h2] using h

/-- Every byte of a block load has a read unit. -/
theorem ld_units {i p : Nat} {c : Nat × Nat × Nat} {y : Nat} (hy : Cell.has (cellOf c) y) :
    ∃ u ∈ actUnits i p (ldAct .wb c.1 c.2.1 c.2.2), u.1.isR = true ∧ u.1.covers y = true :=
  actUnits_exists_r (by simp [ldAct]) (by simpa [ldAct, cellOf, Cell.has] using hy) p

/-- Every byte of a block store has a write unit. -/
theorem st_units {i p : Nat} {c : Nat × Nat × Nat} {y : Nat} (hy : Cell.has (cellOf c) y) :
    ∃ u ∈ actUnits i p (stAct .wb c.1 c.2.1 c.2.2), u.1.isW = true ∧ u.1.covers y = true :=
  actUnits_exists_w (by simp [stAct]) (by simpa [stAct, cellOf, Cell.has] using hy) p


/-! ## Values -/

theorem fits_lt {dom : List Nat} : ∀ {vs : List Nat} {cs : List (Nat × Nat)}, Fits dom vs cs →
    ∀ c ∈ cellVals cs vs, c.2.2 < 2 ^ (8 * c.2.1)
  | [], [], _ => by simp [cellVals]
  | v :: vs, d :: cs, h => by
    cases h with
    | cons hv h =>
      intro c hc
      simp only [cellVals, List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp only [pick, List.mem_filter, decide_eq_true_eq] at hv; exact hv.2
      · exact fits_lt h c hc
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

theorem vals_eq {dom : List Nat} {g : Nat × Nat → Nat} : ∀ {vs : List Nat} {cs : List (Nat × Nat)},
    Fits dom vs cs → (∀ c ∈ cellVals cs vs, c.2.2 = g (cellOf c)) → vs = cs.map g
  | [], [], _, _ => rfl
  | v :: vs, d :: cs, h, hg => by
    cases h with
    | cons _ h =>
      simp only [cellVals, List.mem_cons, forall_eq_or_imp] at hg
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨hg.1, vals_eq h hg.2⟩
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h

theorem cellVals_cover {dom : List Nat} :
    ∀ {vs : List Nat} {cs : List (Nat × Nat)}, Fits dom vs cs →
    ∀ d ∈ cs, ∃ c ∈ cellVals cs vs, cellOf c = d
  | [], [], _ => by simp
  | v :: vs, d :: cs, h => by
    cases h with
    | cons _ h =>
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨(e.1, e.2, v), by simp [cellVals], rfl⟩
      · obtain ⟨c, hc, hce⟩ := cellVals_cover h e he
        exact ⟨c, by simp [cellVals, hc], hce⟩
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

theorem blk_low {j : Job} (hj : ∀ c ∈ j.ins ++ j.outs, c.1 + c.2 ≤ dataTop) {ivs ovs : List Nat}
    {a : XAct} (ha : a ∈ blkActs j ivs ovs) {y : Nat} (hy : Act.has a y) : y < dataTop := by
  rcases mem_blkActs ha with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
  · exact cell_low (hj _ (List.mem_append_left _ (mem_cellVals hc))) (ld_has.mp hy)
  · exact cell_low (hj _ (List.mem_append_right _ (mem_cellVals hc))) (st_has.mp hy)

theorem init_high {locs : List Silmaril.X86.MemoryModel.Litmus.Loc}
    (h : ∀ l ∈ locs, l.addr + l.size ≤ dataTop) {a : Nat} (ha : dataTop ≤ a) :
    initByte locs a = none := by
  simp only [initByte, Option.map_eq_none_iff, List.find?_eq_none, Bool.and_eq_true,
    decide_eq_true_eq, not_and, not_lt]
  intro l hl _; have := h l hl; omega

/-! ## The end bytes -/

theorem endAddr_inj {t t' : Nat} (h : endAddr t = endAddr t') : t = t' := by
  simp [endAddr, ctlAddr] at h; omega

theorem end_ne_ctl (t t' : Nat) : endAddr t ≠ ctlAddr t' := by
  simp [endAddr, ctlAddr]; omega

theorem rmw_byte {i : Nat} {a sz o n : Nat} {q : Ev × List Byte} (hq : UnitOf i (rmwAct a sz o n) q)
    (hW : q.1.isW = true) (hy : q.1.covers a = true) (hsz : 0 < sz) : q.1.byte a = byteOf n 0 := by
  rw [hq.wr hW a hy]; simp only [rmwAct, Nat.sub_self]; exact natBytes_getD hsz

theorem rmw_rd {i : Nat} {a sz o n : Nat} {q : Ev × List Byte} (hq : UnitOf i (rmwAct a sz o n) q)
    (hR : q.1.isR = true) (hy : q.1.covers a = true) (hsz : 0 < sz) :
    q.2.getD (a - q.1.addr) 0 = byteOf o 0 := by
  rw [hq.rd hR a hy]; simp only [rmwAct, Nat.sub_self]; exact natBytes_getD hsz

/-- **The writers of worker `k`'s end byte**: the main thread's join (writing `2`), or worker
`k`'s end event (a locked write, after its block units). -/
theorem end_writer (hok : F.Ok) (P : Pick F dom trs) {k : Nat} (hk : k < F.jobs.length)
    {q : Ev × List Byte} (hq : q ∈ units trs) (hW : q.1.isW = true)
    (hy : q.1.covers (endAddr (k + 1)) = true) :
    q.1.byte (endAddr (k + 1)) = byteOf 2 0 ∨
      (q.1.tid = k + 1 ∧ P.lw k hk ≤ q.1.pos ∧ q.1.locked = true) := by
  have hlow := dataTop_le_end (k + 1)
  obtain ⟨i, tr, htr, u, hu, htr', hpos, -, -⟩ := units_src hq
  rcases P.thread htr with ⟨rfl, rfl⟩ | ⟨k', hk', rfl, rfl⟩
  · rcases P.mem_tr0 hu with ⟨⟨a, ha, hau⟩, -⟩ | ⟨⟨a, ha, hau⟩, -⟩
    · rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨k', -, rfl⟩ := mem_spawnActs ha
        exact absurd (ctl_has (unitOf_has (htr' _ hau) hy)) (end_ne_ctl _ _)
      · obtain ⟨k', -, rfl⟩ := mem_joinActs ha
        have hkk := endAddr_inj (end_has (unitOf_has (htr' _ hau) hy))
        obtain rfl : k' = k := by omega
        exact .inl (rmw_byte (htr' _ hau) hW hy (by omega))
    · have := blk_low hok.combLow ha (unitOf_has (htr' _ hau) hy); omega
  · rcases P.mem_trw hk' hu with ⟨⟨a, ha, hau⟩, -⟩ | ⟨hau, hp⟩
    · rcases List.mem_append.mp ha with ha | ha
      · simp only [List.mem_singleton] at ha; subst ha
        exact absurd (ctl_has (unitOf_has (htr' _ hau) hy)) (end_ne_ctl _ _)
      · have := blk_low (hok.jobsLow _ (List.getElem_mem hk')) ha (unitOf_has (htr' _ hau) hy)
        omega
    · have hkk := endAddr_inj (end_has (unitOf_has (htr' _ hau) hy))
      obtain rfl : k' = k := by omega
      have hq' := htr' _ hau
      refine .inr ⟨hq'.tid, hpos ▸ hp, ?_⟩
      rw [hq'.locked (by simp [Ev.isM, hW])]; rfl


/-! ## The execution -/

/-- The facts of one candidate execution of a fork-join program that the proof uses. -/
structure Cand (F : Par) (trs : List XTrace) (x : Exec) : Prop where
  evs : x.evs = (units trs).map Prod.fst
  wf : x.Wf = true
  reads : ReadsOk F.prog.memTest x ((units trs).map Prod.snd)
  xl : x.Xl

variable {x : Exec}

theorem Cand.unit (hC : Cand F trs x) (a : Fin x.n) :
    ∃ q ∈ units trs, q.1 = x.ev a ∧ ((units trs).map Prod.snd).getD a [] = q.2 :=
  units_idx hC.evs a

/-- What a read unit returns at a byte it covers, from its unit's expected bytes. -/
theorem Cand.read (hC : Cand F trs x) {q : Ev × List Byte} {r : Fin x.n} (hrq : x.ev r = q.1)
    (hexp : ((units trs).map Prod.snd).getD r [] = q.2) (hR : q.1.isR = true) {y : Nat}
    (hy : q.1.covers y = true) :
    x.readByte F.prog.memTest.initB r y = q.2.getD (y - q.1.addr) 0 := by
  rw [readByte_eq hC.reads r (hrq ▸ hR) (hrq ▸ hy), hexp, hrq]

theorem initB_eq (F : Par) (y : Nat) : F.prog.memTest.initB y = (F.init y).getD 0 := rfl

theorem po_of {a b : Fin x.n} (ht : (x.ev a).tid = (x.ev b).tid)
    (hp : (x.ev a).pos < (x.ev b).pos) :
    x.po a b = true := by
  simp [Exec.po, ht, hp]

/-- **The combine reads every worker output byte from some write** (not the initial value):
the `ghbXl` cycle `load -fr-> store -lock-> end -rfe-> join -lock-> load`. -/
theorem comb_not_init (hok : F.Ok) (P : Pick F dom trs) (hC : Cand F trs x) {r : Fin x.n}
    (hR : (x.ev r).isR = true) {y : Nat} (hy : (x.ev r).covers y = true) (htid : (x.ev r).tid = 0)
    (hpos : P.l0 ≤ (x.ev r).pos) {k : Nat} (hk : k < F.jobs.length) {c : Nat × Nat × Nat}
    (hc : c ∈ cellVals F.jobs[k].outs (P.ov k)) (hcy : Cell.has (cellOf c) y) :
    x.rf r.val y ≠ none := by
  intro hnone
  -- the worker's store of `y`
  have hst : stAct .wb c.1 c.2.1 c.2.2 ∈
      [ctlAct (k + 1) 1 2] ++ blkActs F.jobs[k] (P.iv k) (P.ov k) :=
    List.mem_append_right _ (List.mem_append_right _ (List.mem_map_of_mem hc))
  obtain ⟨q0, hq0, hu0, hW0, hy0, hp0⟩ := exists_left (P.hw k hk) (P.actsw k hk) hst
    (Q := Ev.isW) (fun _ => st_units hcy) qW
  obtain ⟨w0, hw0e, -⟩ := idx_units hC.evs hq0
  -- the main thread's join of worker `k`
  have hjn : endAct (k + 1) 1 2 ∈ spawnActs F.jobs.length ++ joinActs F.jobs.length :=
    List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
  obtain ⟨qj, hqj, huj, hRj, hyj, hpj⟩ := exists_left P.h0 P.acts0 hjn (Q := Ev.isR)
    (y := endAddr (k + 1)) (fun p => actUnits_exists_r (by simp [endAct, rmwAct])
      (by simp [endAct, rmwAct]) p) qR
  obtain ⟨jr, hjre, hjrx⟩ := idx_units hC.evs hqj
  -- it read `1` from worker `k`'s end event
  have hread := hC.read hjre hjrx hRj hyj
  rw [rmw_rd huj hRj hyj (by omega)] at hread
  unfold Exec.readByte at hread
  cases hrf : x.rf jr.val (endAddr (k + 1)) with
  | none =>
    rw [hrf] at hread
    simp only [initB_eq, Par.init, init_high hok.locsLow (dataTop_le_end _)] at hread
    simp [byteOf] at hread
  | some w =>
    rw [hrf] at hread
    obtain ⟨hwn, hwW, hwy⟩ := wf_rf hC.wf (hjre ▸ hRj) (hjre ▸ hyj) hrf
    obtain ⟨qw, hqw, hqwe, -⟩ := hC.unit ⟨w, hwn⟩
    have hN : x.evN w = qw.1 := (evN_eq ⟨w, hwn⟩).trans hqwe.symm
    simp only at hread
    rw [hN] at hwW hwy hread
    rcases end_writer hok P hk hqw hwW hwy with h2 | ⟨hwt, hwp, hwl⟩
    · rw [h2] at hread; simp [byteOf] at hread
    · -- the cycle
      simp only [Pick.lw] at hwp
      simp only [Pick.l0] at hpos
      have e1 : x.ghbXl r w0 = true := ghb_of_fr (by
        simp only [Exec.frR, Bool.and_eq_true]
        refine ⟨⟨hR, hw0e ▸ hW0⟩, List.any_eq_true.mpr ⟨y, mem_bytes.mpr hy, ?_⟩⟩
        simp [hnone, hw0e ▸ hy0])
      have e2 : x.ghbXl w0 ⟨w, hwn⟩ = true := ghb_of_lock (by
        have hpo : x.po w0 ⟨w, hwn⟩ = true := po_of (by rw [hw0e, ← hqwe, hu0.tid, hwt])
          (by rw [hw0e, ← hqwe]; omega)
        simp [Exec.lockXl, hpo, Ev.isM, Ev.isA, ← hqwe, hwW, hwl, hw0e, hW0])
      have e3 : x.ghbXl ⟨w, hwn⟩ jr = true := ghb_of_rfe (by
        simp only [Exec.rfe, BRel.inter, Exec.rfR, Exec.ext, Bool.and_eq_true]
        refine ⟨⟨⟨by rw [← hqwe]; exact hwW, by rw [hjre]; exact hRj⟩,
          List.any_eq_true.mpr ⟨endAddr (k + 1), mem_bytes.mpr (hjre ▸ hyj), ?_⟩⟩, ?_⟩
        · simp [hrf, ← hqwe, hwy]
        · simp [← hqwe, hjre, hwt, huj.tid])
      have e4 : x.ghbXl jr r = true := ghb_of_lock (by
        have hpo : x.po jr r = true := po_of (by rw [hjre, huj.tid, htid]) (by rw [hjre]; omega)
        have hl : qj.1.locked = true := by
          rw [huj.locked (by simp [Ev.isM, hRj])]; rfl
        simp [Exec.lockXl, hpo, Ev.isM, Ev.isA, hjre, hRj, hl, hR])
      exact hC.xl.2.2.2 r (.tail (.tail (.tail (.single e1) e2) e3) e4)


/-! ## Worker inputs, combine inputs, final memory -/

/-- No write unit covers a byte of a worker's input cell. -/
theorem no_write_ins (hok : F.Ok) (P : Pick F dom trs) {q : Ev × List Byte} (hq : q ∈ units trs)
    (hW : q.1.isW = true) {y : Nat} (hy : q.1.covers y = true) {j : Job} (hj : j ∈ F.jobs)
    {d : Nat × Nat} (hd : d ∈ j.ins) (hdy : Cell.has d y) : False := by
  have hlow := cell_low (hok.jobsLow j hj d (List.mem_append_left _ hd)) hdy
  rcases data_writer P hq hW hy hlow with ⟨c, hc, hcy, -⟩ | ⟨k, hk, c, hc, hcy, -⟩
  · exact disjB_iff (hok.insFree j hj d hd F.comb (by simp) _ (mem_cellVals hc)) y ⟨hdy, hcy⟩
  · exact disjB_iff (hok.insFree j hj d hd F.jobs[k] (List.mem_append_left _ (List.getElem_mem hk))
      _ (mem_cellVals hc)) y ⟨hdy, hcy⟩

/-- **Worker inputs are initial.** -/
theorem worker_ins (hok : F.Ok) (P : Pick F dom trs) (hC : Cand F trs x) {k : Nat}
    (hk : k < F.jobs.length) : P.iv k = F.jobs[k].ins.map (cellVal F.init) := by
  refine vals_eq (P.fi k hk) fun c hc => (cellVal_of_bytes (fits_lt (P.fi k hk) c hc) ?_).symm
  intro o ho
  have hcy : Cell.has (cellOf c) (c.1 + o) := by simp [Cell.has, cellOf]; omega
  have hld : ldAct .wb c.1 c.2.1 c.2.2 ∈
      [ctlAct (k + 1) 1 2] ++ blkActs F.jobs[k] (P.iv k) (P.ov k) :=
    List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem hc))
  obtain ⟨q, hq, hu, hR, hy, -⟩ := exists_left (P.hw k hk) (P.actsw k hk) hld (Q := Ev.isR)
    (fun _ => ld_units hcy) qR
  obtain ⟨r, hre, hrx⟩ := idx_units hC.evs hq
  have hread := hC.read hre hrx hR hy
  rw [(ld_byte hu hR hy).2, Nat.add_sub_cancel_left] at hread
  rw [← hread]
  unfold Exec.readByte
  cases hrf : x.rf r.val (c.1 + o) with
  | none => rfl
  | some w =>
    exfalso
    obtain ⟨hwn, hwW, hwy⟩ := wf_rf hC.wf (hre ▸ hR) (hre ▸ hy) hrf
    obtain ⟨qw, hqw, hqwe, -⟩ := hC.unit ⟨w, hwn⟩
    have hN : x.evN w = qw.1 := (evN_eq ⟨w, hwn⟩).trans hqwe.symm
    rw [hN] at hwW hwy
    exact no_write_ins hok P hqw hwW hwy (List.getElem_mem hk) (mem_cellVals hc) hcy

/-- The worker outputs are their jobs' sequential outputs. -/
theorem worker_outs (hok : F.Ok) (P : Pick F dom trs) (hC : Cand F trs x) {k : Nat}
    (hk : k < F.jobs.length) : P.ov k = F.jobs[k].fn (F.jobs[k].ins.map (cellVal F.init)) := by
  rw [P.fn k hk, worker_ins hok P hC hk]

/-- A write of a data byte by a worker writes the sequential value. -/
theorem worker_write_val (hok : F.Ok) (P : Pick F dom trs) (hC : Cand F trs x) {k : Nat}
    (hk : k < F.jobs.length) {c : Nat × Nat × Nat} (hc : c ∈ cellVals F.jobs[k].outs (P.ov k))
    {y : Nat} (hcy : Cell.has (cellOf c) y) : F.jobsMem y = some (byteOf c.2.2 (y - c.1)) := by
  rw [worker_outs hok P hC hk] at hc
  exact jobsMem_in hok (List.getElem_mem hk) hc hcy

/-- **The combine reads the workers' outputs.** -/
theorem comb_ins (hok : F.Ok) (P : Pick F dom trs) (hC : Cand F trs x) :
    P.ivc = F.comb.ins.map (cellVal F.jobsMem) := by
  refine vals_eq P.fic fun c hc => (cellVal_of_bytes (fits_lt P.fic c hc) ?_).symm
  intro o ho
  have hcy : Cell.has (cellOf c) (c.1 + o) := by simp [Cell.has, cellOf]; omega
  have hlow := cell_low (hok.combLow _ (List.mem_append_left _ (mem_cellVals hc))) hcy
  have hld : ldAct .wb c.1 c.2.1 c.2.2 ∈ blkActs F.comb P.ivc P.ovc :=
    List.mem_append_left _ (List.mem_map_of_mem hc)
  obtain ⟨q, hq, hu, hR, hy, hp⟩ := exists_right P.h0 P.acts0 hld (Q := Ev.isR)
    (fun _ => ld_units hcy) qR
  obtain ⟨r, hre, hrx⟩ := idx_units hC.evs hq
  have hread := hC.read hre hrx hR hy
  rw [(ld_byte hu hR hy).2, Nat.add_sub_cancel_left] at hread
  rw [← hread]
  unfold Exec.readByte
  cases hrf : x.rf r.val (c.1 + o) with
  | none =>
    simp only [initB_eq]
    by_cases hw : ∃ k, ∃ hk : k < F.jobs.length, ∃ d ∈ F.jobs[k].outs, Cell.has d (c.1 + o)
    · exfalso
      obtain ⟨k, hk, d, hd, hdy⟩ := hw
      obtain ⟨c', hc', rfl⟩ := cellVals_cover (P.fo k hk) d hd
      exact comb_not_init hok P hC (hre ▸ hR) (hre ▸ hy) (by rw [hre, hu.tid])
        (by rw [hre]; exact hp) hk hc' hdy hrf
    · rw [jobsMem_out]
      intro j hj d hd hdy
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hj
      exact hw ⟨k, hk, d, hd, hdy⟩
  | some w =>
    obtain ⟨hwn, hwW, hwy⟩ := wf_rf hC.wf (hre ▸ hR) (hre ▸ hy) hrf
    obtain ⟨qw, hqw, hqwe, -⟩ := hC.unit ⟨w, hwn⟩
    have hN : x.evN w = qw.1 := (evN_eq ⟨w, hwn⟩).trans hqwe.symm
    rw [hN] at hwW hwy
    simp only [hN]
    rcases data_writer P hqw hwW hwy hlow with ⟨c', hc', hcy', -⟩ | ⟨k, hk, c', hc', hcy', hb, -⟩
    · exact absurd ⟨hcy, hcy'⟩
        (disjB_iff (hok.combDisj _ (mem_cellVals hc) _ (mem_cellVals hc')) _)
    · rw [worker_write_val hok P hC hk hc' hcy', hb]; rfl

/-- The combine's outputs are its sequential outputs. -/
theorem comb_outs (hok : F.Ok) (P : Pick F dom trs) (hC : Cand F trs x) :
    P.ovc = F.comb.fn (F.comb.ins.map (cellVal F.jobsMem)) := by
  rw [P.fnc, comb_ins hok P hC]

theorem writtenByte_of {q : Ev × List Byte} (hevs : x.evs = (units trs).map Prod.fst)
    (hq : q ∈ units trs) (hW : q.1.isW = true) {y : Nat} (hy : q.1.covers y = true) :
    writtenByte x y = true := by
  simp only [writtenByte, hevs, List.any_map, List.any_eq_true]
  exact ⟨q, hq, by simp [hW, hy]⟩

/-- **The final data bytes are the sequential ones.** -/
theorem final_mem (hok : F.Ok) (P : Pick F dom trs) (hC : Cand F trs x) {y : Nat}
    (hlow : y < dataTop) :
    (finalAx F.prog.memTest trs x).mem y = F.seqMem y := by
  simp only [finalAx, finalOf]
  by_cases hwb : writtenByte x y = true
  · simp only [hwb, ↓reduceIte]
    obtain ⟨e, he, hey⟩ := List.any_eq_true.mp hwb
    obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem he
    simp only [Bool.and_eq_true] at hey
    obtain ⟨v, hv, hvn, hvW, hvy⟩ := wf_coLast hC.wf ⟨a, ha⟩ hey.1 hey.2
    obtain ⟨qv, hqv, hqve, -⟩ := hC.unit ⟨v, hvn⟩
    have hN : x.evN v = qv.1 := (evN_eq ⟨v, hvn⟩).trans hqve.symm
    rw [hN] at hvW hvy
    simp only [Exec.finalByte, hv, hN]
    rcases data_writer P hqv hvW hvy hlow with ⟨c, hc, hcy, hb⟩ | ⟨k, hk, c, hc, hcy, hb, -⟩
    · rw [hb, comb_outs hok P hC] at *
      exact (seqMem_in hok hc hcy).symm
    · rw [hb, seqMem_out, worker_write_val hok P hC hk hc hcy]
      intro d hd hdy
      exact disjB_iff (jobs_comb_disj hok (List.getElem_mem hk) (mem_cellVals hc) hd) y ⟨hcy, hdy⟩
  · simp only [hwb, Bool.false_eq_true, ↓reduceIte]
    have hnc : ∀ d ∈ F.comb.outs, ¬ Cell.has d y := by
      intro d hd hdy
      obtain ⟨c, hc, rfl⟩ := cellVals_cover P.foc d hd
      have hst : stAct .wb c.1 c.2.1 c.2.2 ∈ blkActs F.comb P.ivc P.ovc :=
        List.mem_append_right _ (List.mem_map_of_mem hc)
      obtain ⟨q, hq, -, hW, hy, -⟩ := exists_right P.h0 P.acts0 hst (Q := Ev.isW)
        (fun _ => st_units hdy) qW
      exact hwb (writtenByte_of hC.evs hq hW hy)
    have hnj : ∀ j ∈ F.jobs, ∀ d ∈ j.outs, ¬ Cell.has d y := by
      intro j hj d hd hdy
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hj
      obtain ⟨c, hc, rfl⟩ := cellVals_cover (P.fo k hk) d hd
      have hst : stAct .wb c.1 c.2.1 c.2.2 ∈
          [ctlAct (k + 1) 1 2] ++ blkActs F.jobs[k] (P.iv k) (P.ov k) :=
        List.mem_append_right _ (List.mem_append_right _ (List.mem_map_of_mem hc))
      obtain ⟨q, hq, -, hW, hy, -⟩ := exists_left (P.hw k hk) (P.actsw k hk) hst (Q := Ev.isW)
        (fun _ => st_units hdy) qW
      exact hwb (writtenByte_of hC.evs hq hW hy)
    rw [seqMem_out hnc, jobsMem_out hnj]
    rfl

/-- **The fork-join theorem**: under every model `M ⊑ XL`, every behaviour of a fork-join
program with disjoint footprints ends with the sequential memory on every data byte. -/
theorem behav_mem (F : Par) (hok : F.Ok) {M : Exec → Prop} (hM : ∀ x, M x → x.Xl) {f}
    (h : Behav F.prog M f) : ∀ y < dataTop, f.mem y = F.seqMem y := by
  obtain ⟨dom, trs, hT, x, hevs, -, hwf, hreads, hMx, rfl⟩ := h
  obtain ⟨P⟩ := pick_of_shape (shape_of hT)
  exact fun y hy => final_mem hok P ⟨hevs, hwf, hreads, hM x hMx⟩ hy

end Silmaril.Proofs.X86.Concurrency.Cir.Fj
