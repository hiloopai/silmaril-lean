module

public import Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun.Units

/-!
# From a store-buffer candidate to a litmus candidate

Take traces `trs` whose actions are `ActOk` and whose units the litmus translation does not split
(`NoTear`), and a TSO-consistent candidate `x` that `OpAx.Explains` a complete run of the
store-buffer
machine on `trs.mapIdx traceX`, with paired locked read-modify-writes. The candidate `axX` over
the litmus units of `trs` reads `rf` and `co` through the index maps between the two unit lists:

* `cnt l p a`: the index of `l[a]` among the elements of `l` satisfying `p` (the litmus units
  without
  `lfence`/`sfence`, which match the store-buffer machine units in order, `progUnits_strip`);
* the permutation between the store-buffer machine units in order (`progUnits`) and in `x`'s order
  (`Explains`).

`axX_emb`: these maps are an embedding (`Emb`), so `axX` is TSO-consistent (`tso_of_emb`).
`axX_wf`, `axX_readsOk`, `axX_final`: it is well-formed, its reads return the traces' bytes,
and its final memory is the run's on every byte some unit writes or whose initial value the
run and the test share. `axReach_of_explains` puts these together.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun

open Silmaril.X86.MemoryModel.Axiomatic (Ev Exec Act BRel)
open Silmaril.X86.MemoryModel.Litmus (XAct XTrace Test actX traceX actUnits accUnits units Byte
  rmwPairs ReadsOk finalAx finalOf writtenByte AxReach tearAcc)
open Silmaril.X86.MemoryModel.Tso (XEvent XState Mem)
open Silmaril.X86.MemoryModel.OpAx (evUnits progUnits Explains RmwPaired dflt)
open Silmaril.X86.Concurrency.Bridge.PoolRun

/-! ## Counting -/

/-- The number of elements of `l` before index `a` satisfying `p`. -/
def cnt {α : Type} (l : List α) (p : α → Bool) (a : Nat) : Nat := (l.take a).countP p

theorem cnt_get {α : Type} (l : List α) (p : α → Bool) {a : Nat} (ha : a < l.length)
    (hp : p l[a] = true) : ∃ h : cnt l p a < (l.filter p).length, (l.filter p)[cnt l p a] = l[a] := by
  have hl : l = l.take a ++ l[a] :: l.drop (a + 1) := by
    conv_lhs => rw [← List.take_append_drop a l, List.drop_eq_getElem_cons ha]
  have hf : l.filter p = (l.take a).filter p ++ l[a] :: (l.drop (a + 1)).filter p := by
    conv_lhs => rw [hl]
    rw [List.filter_append, List.filter_cons]
    simp [hp]
  have hc : cnt l p a = ((l.take a).filter p).length := List.countP_eq_length_filter
  refine ⟨by rw [hf, hc]; simp, ?_⟩
  simp only [hf, hc]
  rw [List.getElem_append_right (by omega)]
  simp

theorem cnt_succ {α : Type} (l : List α) (p : α → Bool) {a : Nat} (ha : a < l.length) :
    cnt l p (a + 1) = cnt l p a + if p l[a] then 1 else 0 := by
  simp only [cnt, List.take_add_one, List.getElem?_eq_getElem ha, Option.toList_some,
    List.countP_append, List.countP_singleton]

theorem cnt_mono {α : Type} (l : List α) (p : α → Bool) {a b : Nat} (h : a ≤ b) :
    cnt l p a ≤ cnt l p b :=
  (List.take_sublist_take_left h).countP_le

theorem cnt_lt {α : Type} (l : List α) (p : α → Bool) {a b : Nat} (ha : a < l.length)
    (hp : p l[a] = true) (hab : a < b) : cnt l p a < cnt l p b := by
  have h1 := cnt_succ l p ha
  simp only [hp, ite_true] at h1
  have := cnt_mono l p (show a + 1 ≤ b by omega)
  omega

theorem cnt_lt_iff {α : Type} (l : List α) (p : α → Bool) {a b : Nat} (ha : a < l.length)
    (hb : b < l.length) (hpa : p l[a] = true) (_hpb : p l[b] = true) :
    cnt l p a < cnt l p b ↔ a < b := by
  constructor
  · intro h
    by_contra hab
    have := cnt_mono l p (show b ≤ a by omega)
    omega
  · exact cnt_lt l p ha hpa

theorem cnt_inj {α : Type} (l : List α) (p : α → Bool) {a b : Nat} (ha : a < l.length)
    (hb : b < l.length) (hpa : p l[a] = true) (hpb : p l[b] = true)
    (h : cnt l p a = cnt l p b) : a = b := by
  have h1 := (cnt_lt_iff l p ha hb hpa hpb).not
  have h2 := (cnt_lt_iff l p hb ha hpb hpa).not
  omega

theorem cnt_exists {α : Type} (p : α → Bool) :
    ∀ (l : List α) (j : Nat), j < (l.filter p).length →
      ∃ (a : Nat) (ha : a < l.length), p l[a] = true ∧ cnt l p a = j
  | [], j, h => by simp at h
  | u :: l, j, h => by
    by_cases hu : p u = true
    · simp only [List.filter_cons, hu, ite_true] at h
      rcases j with _ | j
      · exact ⟨0, by simp, hu, by simp [cnt]⟩
      · obtain ⟨a, ha, hp, hc⟩ := cnt_exists p l j (by simpa using h)
        refine ⟨a + 1, by simpa using ha, by simpa using hp, ?_⟩
        simp only [cnt, List.take_succ_cons, List.countP_cons, hu, ite_true] at hc ⊢
        omega
    · simp only [List.filter_cons, hu, Bool.false_eq_true, ite_false] at h
      obtain ⟨a, ha, hp, hc⟩ := cnt_exists p l j h
      refine ⟨a + 1, by simpa using ha, by simpa using hp, ?_⟩
      simp only [cnt, List.take_succ_cons, List.countP_cons, hu] at hc ⊢
      simpa using hc

/-- The index in `l` of the `j`-th element satisfying `p`. -/
noncomputable def uncnt {α : Type} (l : List α) (p : α → Bool) (j : Nat) : Nat :=
  if h : j < (l.filter p).length then Classical.choose (cnt_exists p l j h) else 0

theorem uncnt_spec {α : Type} (l : List α) (p : α → Bool) {j : Nat}
    (h : j < (l.filter p).length) :
    ∃ ha : uncnt l p j < l.length, p l[uncnt l p j] = true ∧ cnt l p (uncnt l p j) = j := by
  simp only [uncnt, h, dite_true]
  exact Classical.choose_spec (cnt_exists p l j h)

/-! ## Permutations -/

section perm
variable {β : Type} [BEq β] [LawfulBEq β] {us cs : List β} (d : β)

theorem idxOf_perm (hp : us.Perm cs) {k : Nat} (hk : k < cs.length) :
    ∃ h : us.idxOf (cs.getD k d) < us.length, us[us.idxOf (cs.getD k d)] = cs[k] := by
  have hmem : cs.getD k d ∈ us := hp.mem_iff.2 (by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem _)
  have h1 := List.idxOf_lt_length_iff.2 hmem
  refine ⟨h1, ?_⟩
  rw [List.getElem_idxOf h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

theorem idxOf_getElem_nodup {l : List β} (hn : l.Nodup) {k : Nat} (hk : k < l.length) :
    l.idxOf (l.getD k d) = k := by
  have hg : l.getD k d = l[k] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
  rw [hg]
  have h1 := List.idxOf_lt_length_iff.2 (List.getElem_mem hk)
  exact (hn.getElem_inj_iff).1 (List.getElem_idxOf h1)

end perm

/-! ## The candidate over the litmus units -/

/-- The store-buffer machine units of the traces, in order. -/
def csOf (trs : List XTrace) : List (Ev × List Byte) := progUnits (trs.mapIdx traceX)

/-- The default unit of `Explains`. -/
def d0 : Ev × List Byte := (dflt, [])

/-- The unit of `x` (units `us`) standing for the litmus unit `a`. -/
def eIdx (trs : List XTrace) (us : List (Ev × List Byte)) (a : Nat) : Nat :=
  us.idxOf ((csOf trs).getD (cnt (accUnits trs) realU a) d0)

/-- The litmus unit standing for the unit `w` of `x`. -/
noncomputable def σIdx (trs : List XTrace) (us : List (Ev × List Byte)) (w : Nat) : Nat :=
  uncnt (accUnits trs) realU ((csOf trs).idxOf (us.getD w d0))

/-- **The candidate over the litmus units**: `rf` and `co` of `x` read through the index maps. -/
noncomputable def axX (x : Exec) (trs : List XTrace) (us : List (Ev × List Byte)) : Exec where
  evs := (accUnits trs).map Prod.fst
  rf := fun r y => (x.rf (eIdx trs us r) y).map (σIdx trs us)
  co := fun y => (x.co y).map (σIdx trs us)
  rmw := rmwPairs ((accUnits trs).map Prod.fst)

theorem evN_getD (x : Exec) (l : List (Ev × List Byte)) (hx : x.evs = l.map Prod.fst) {a : Nat}
    (ha : a < l.length) : x.evN a = l[a].1 := by
  simp [Exec.evN, hx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha]

section main
variable {trs : List XTrace} {us : List (Ev × List Byte)}

theorem filter_length (hok : TracesOk trs) :
    ((accUnits trs).filter realU).length = (csOf trs).length := by
  have := congrArg List.length (progUnits_strip hok)
  simp only [List.length_map] at this
  exact this.symm

/-- The litmus real unit `a` and the store-buffer machine unit `cnt a` agree once stripped. -/
theorem strip_cs (hok : TracesOk trs) {a : Nat} (ha : a < (accUnits trs).length)
    (hr : realU (accUnits trs)[a] = true) :
    ∃ h : cnt (accUnits trs) realU a < (csOf trs).length,
      strip (csOf trs)[cnt (accUnits trs) realU a] = strip (accUnits trs)[a] := by
  obtain ⟨h1, h2⟩ := cnt_get (accUnits trs) realU ha hr
  have hl := filter_length hok
  have h3 : cnt (accUnits trs) realU a < (csOf trs).length := lt_of_lt_of_eq h1 hl
  refine ⟨h3, ?_⟩
  have := congrArg (fun l => l[cnt (accUnits trs) realU a]?) (progUnits_strip hok)
  simp only [List.getElem?_map] at this
  rw [List.getElem?_eq_getElem (show cnt (accUnits trs) realU a < (progUnits (trs.mapIdx traceX)).length from h3),
    List.getElem?_eq_getElem h1, h2] at this
  exact Option.some.inj this

variable (hperm : us.Perm (csOf trs))
include hperm

theorem eIdx_spec (hok : TracesOk trs) {a : Nat} (ha : a < (accUnits trs).length)
    (hr : realU (accUnits trs)[a] = true) :
    ∃ h : eIdx trs us a < us.length,
      ∃ h' : cnt (accUnits trs) realU a < (csOf trs).length,
        us[eIdx trs us a] = (csOf trs)[cnt (accUnits trs) realU a] ∧
          strip (csOf trs)[cnt (accUnits trs) realU a] = strip (accUnits trs)[a] := by
  obtain ⟨h', hs⟩ := strip_cs hok ha hr
  obtain ⟨h1, h2⟩ := idxOf_perm d0 hperm h'
  exact ⟨h1, h', h2, hs⟩

omit hperm in
theorem cs_nodup : (csOf trs).Nodup := (posOrd_prog _).nodup

theorem us_nodup : us.Nodup := hperm.nodup_iff.2 cs_nodup

theorem σIdx_spec (hok : TracesOk trs) {w : Nat} (hw : w < us.length) :
    ∃ h : σIdx trs us w < (accUnits trs).length, realU (accUnits trs)[σIdx trs us w] = true ∧
      eIdx trs us (σIdx trs us w) = w := by
  have hmem : us.getD w d0 ∈ csOf trs := hperm.mem_iff.1 (by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw]; exact List.getElem_mem _)
  have hk := List.idxOf_lt_length_iff.2 hmem
  have hk' : (csOf trs).idxOf (us.getD w d0) < ((accUnits trs).filter realU).length := by
    rw [filter_length hok]; exact hk
  obtain ⟨h1, h2, h3⟩ := uncnt_spec (accUnits trs) realU hk'
  refine ⟨h1, h2, ?_⟩
  simp only [eIdx, σIdx] at h3 ⊢
  rw [h3]
  have h4 := List.getElem_idxOf hk
  have : (csOf trs).getD ((csOf trs).idxOf (us.getD w d0)) d0 = us.getD w d0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, h4]; rfl
  rw [this]
  exact idxOf_getElem_nodup d0 (us_nodup hperm) hw

end main

theorem getElem_idx_eq {α : Type} {l : List α} {i j : Nat} (h : i = j) (hi : i < l.length)
    (hj : j < l.length) : l[i] = l[j] := by subst h; rfl

theorem strip_eq_iff {u v : Ev × List Byte} : strip u = strip v ↔
    u.1.tid = v.1.tid ∧ u.1.act = v.1.act ∧ u.1.addr = v.1.addr ∧ u.1.size = v.1.size ∧
      u.1.locked = v.1.locked ∧ u.1.data = v.1.data ∧ u.2 = v.2 := by
  simp [strip]

theorem mem_rmwPairs_iff (evs : List Ev) (p q : Nat) : (p, q) ∈ rmwPairs evs ↔
    ∃ (hp : p < evs.length) (hq : q < evs.length), (evs[p].isR && evs[p].locked) = true ∧
      (evs[q].isW && evs[q].locked && evs[p].tid == evs[q].tid && evs[q].pos == evs[p].pos + 1 &&
        evs[p].addr == evs[q].addr && evs[p].size == evs[q].size) = true := by
  simp only [rmwPairs, List.mem_flatMap]
  constructor
  · rintro ⟨qa, hqa, hq⟩
    split at hq
    · rw [List.mem_filterMap] at hq
      obtain ⟨qb, hqb, hq⟩ := hq
      split at hq
      · simp only [Option.some.injEq, Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        obtain ⟨ha1, ha2⟩ := List.mem_zipIdx' hqa
        obtain ⟨hb1, hb2⟩ := List.mem_zipIdx' hqb
        refine ⟨ha1, hb1, ?_, ?_⟩
        · rwa [← ha2]
        · rwa [← ha2, ← hb2]
      · cases hq
    · simp at hq
  · rintro ⟨hp, hq, h1, h2⟩
    refine ⟨(evs[p], p), List.mem_zipIdx_iff_getElem?.2 (by simp [hp]), ?_⟩
    simp only [h1, ite_true]
    rw [List.mem_filterMap]
    exact ⟨(evs[q], q), List.mem_zipIdx_iff_getElem?.2 (by simp [hq]), by simp only [h2, ite_true]⟩

section emb
variable {trs : List XTrace} {us : List (Ev × List Byte)} (hperm : us.Perm (csOf trs))
  (hok : TracesOk trs) {x : Exec} (hx : x.evs = us.map Prod.fst)
include hperm hok hx

omit hperm hok in
theorem x_n : x.n = us.length := by simp [Exec.n, hx]

/-- The unit of `x` standing for the litmus real unit `a` is the store-buffer machine unit `cnt a`,
which agrees with
`a` once stripped. -/
theorem x_eIdx {a : Nat} (ha : a < (accUnits trs).length) (hr : realU (accUnits trs)[a] = true) :
    ∃ (_ : eIdx trs us a < x.n) (h' : cnt (accUnits trs) realU a < (csOf trs).length),
      x.evN (eIdx trs us a) = (csOf trs)[cnt (accUnits trs) realU a].1 ∧
        strip (csOf trs)[cnt (accUnits trs) realU a] = strip (accUnits trs)[a] := by
  obtain ⟨h1, h2, h3, h4⟩ := eIdx_spec hperm hok ha hr
  refine ⟨by rw [x_n hx]; exact h1, h2, ?_, h4⟩
  rw [evN_getD x us hx h1, h3]

omit hperm hok hx in
theorem ax_evN {a : Nat} (ha : a < (accUnits trs).length) :
    (axX x trs us).evN a = (accUnits trs)[a].1 :=
  evN_getD _ (accUnits trs) rfl ha

omit hperm hok hx in
theorem ax_n : (axX x trs us).n = (accUnits trs).length := by simp [axX, Exec.n]

/-- **The index maps are an embedding.** -/
theorem axX_emb
    (hrf : ∀ r y w, x.rf r y = some w → w < x.n ∧ (x.evN w).isW = true ∧ (x.evN w).covers y = true)
    (hco : ∀ y w, w ∈ x.co y ↔ w < x.n ∧ (x.evN w).isW = true ∧ (x.evN w).covers y = true)
    (hp : RmwPaired x) : Emb x (axX x trs us) (eIdx trs us) (σIdx trs us) := by
  have hn := ax_n (x := x) (trs := trs) (us := us)
  -- facts at a real unit
  have key : ∀ a < (axX x trs us).n, realE ((axX x trs us).evN a) = true →
      ∃ (ha : a < (accUnits trs).length) (h : eIdx trs us a < x.n)
        (h' : cnt (accUnits trs) realU a < (csOf trs).length),
        (axX x trs us).evN a = (accUnits trs)[a].1 ∧ realU (accUnits trs)[a] = true ∧
        x.evN (eIdx trs us a) = (csOf trs)[cnt (accUnits trs) realU a].1 ∧
        strip (csOf trs)[cnt (accUnits trs) realU a] = strip (accUnits trs)[a] := by
    intro a ha hr
    rw [hn] at ha
    have hr' : realU (accUnits trs)[a] = true := by rw [ax_evN (x := x) (us := us) ha] at hr; exact hr
    obtain ⟨h1, h2, h3, h4⟩ := x_eIdx hperm hok hx ha hr'
    exact ⟨ha, h1, h2, ax_evN (x := x) (us := us) ha, hr', h3, h4⟩
  refine
    { lt := ?_, tid := ?_, act := ?_, addr := ?_, size := ?_, locked := ?_, data := ?_,
      pos := ?_, uniq := ?_, σlt := ?_, σreal := ?_, eσ := ?_, rf := fun _ _ => rfl,
      rfLt := fun r y w h => (hrf r y w h).1, co := fun _ => rfl,
      coLt := fun y w h => ((hco y w).1 h).1, rmw := ?_ }
  · intro a ha hr; obtain ⟨_, h, _⟩ := key a ha hr; exact h
  · intro a ha hr; obtain ⟨_, _, _, h1, _, h3, h4⟩ := key a ha hr
    rw [h1, h3]; exact ((strip_eq_iff.1 h4).1).symm
  · intro a ha hr; obtain ⟨_, _, _, h1, _, h3, h4⟩ := key a ha hr
    rw [h1, h3]; exact ((strip_eq_iff.1 h4).2.1).symm
  · intro a ha hr; obtain ⟨_, _, _, h1, _, h3, h4⟩ := key a ha hr
    rw [h1, h3]; exact ((strip_eq_iff.1 h4).2.2.1).symm
  · intro a ha hr; obtain ⟨_, _, _, h1, _, h3, h4⟩ := key a ha hr
    rw [h1, h3]; exact ((strip_eq_iff.1 h4).2.2.2.1).symm
  · intro a ha hr; obtain ⟨_, _, _, h1, _, h3, h4⟩ := key a ha hr
    rw [h1, h3]; exact ((strip_eq_iff.1 h4).2.2.2.2.1).symm
  · intro a ha hr; obtain ⟨_, _, _, h1, _, h3, h4⟩ := key a ha hr
    rw [h1, h3]; exact ((strip_eq_iff.1 h4).2.2.2.2.2.1).symm
  · intro a ha b hb hra hrb ht
    obtain ⟨ha', _, hca, h1, hr1, h3, h4⟩ := key a ha hra
    obtain ⟨hb', _, hcb, h1', hr1', h3', h4'⟩ := key b hb hrb
    rw [h1, h1'] at ht ⊢
    rw [h3, h3']
    have hta := (strip_eq_iff.1 h4).1
    have htb := (strip_eq_iff.1 h4').1
    have hpo : PosOrd (csOf trs) := posOrd_prog _
    rw [(posOrd_acc trs).lt_iff ha' hb' ht, hpo.lt_iff hca hcb (by rw [hta, htb]; exact ht)]
    exact (cnt_lt_iff _ _ ha' hb' hr1 hr1').symm
  · intro a ha b hb ht hp'
    rw [hn] at ha hb
    rw [ax_evN (x := x) (us := us) ha, ax_evN (x := x) (us := us) hb] at ht hp'
    exact (posOrd_acc trs).eq ha hb ht hp'
  · intro w hw
    rw [x_n hx] at hw
    obtain ⟨h1, _, _⟩ := σIdx_spec hperm hok hw
    rw [hn]; exact h1
  · intro w hw
    rw [x_n hx] at hw
    obtain ⟨h1, h2, _⟩ := σIdx_spec hperm hok hw
    rw [ax_evN (x := x) (us := us) h1]; exact h2
  · intro w hw
    rw [x_n hx] at hw
    exact (σIdx_spec hperm hok hw).2.2
  · intro a b hab ha hb hra hrb
    obtain ⟨ha', hea, hca, h1, hr1, h3, h4⟩ := key a ha hra
    obtain ⟨hb', heb, hcb, h1', hr1', h3', h4'⟩ := key b hb hrb
    have hab' := hab
    simp only [axX] at hab'
    rw [mem_rmwPairs_iff] at hab'
    obtain ⟨_, _, hR, hW⟩ := hab'
    simp only [List.getElem_map, Bool.and_eq_true, beq_iff_eq] at hR hW
    obtain ⟨⟨⟨⟨⟨hW1, hL1⟩, ht⟩, hpos⟩, _⟩, _⟩ := hW
    have hb1 : b = a + 1 := consec_acc trs a b ha' hb' ht hpos
    subst hb1
    have hcs := cnt_succ (accUnits trs) realU ha'
    simp only [hr1, ite_true] at hcs
    have sa := strip_eq_iff.1 h4
    have sb := strip_eq_iff.1 h4'
    have hRk : ((csOf trs)[cnt (accUnits trs) realU a].1.isR &&
        (csOf trs)[cnt (accUnits trs) realU a].1.locked) = true := by
      simp only [Ev.isR, sa.2.1, sa.2.2.2.2.1, Bool.and_eq_true, beq_iff_eq]
      simpa [Ev.isR] using hR
    obtain ⟨hk1, hnt, hnp⟩ := (rmwNext_prog (trs.mapIdx traceX) : RmwNext (csOf trs)) _ hca hRk
    have hnt' : (csOf trs)[cnt (accUnits trs) realU a + 1].1.tid =
        (csOf trs)[cnt (accUnits trs) realU a].1.tid := hnt
    have hnp' : (csOf trs)[cnt (accUnits trs) realU a + 1].1.pos =
        (csOf trs)[cnt (accUnits trs) realU a].1.pos + 1 := hnp
    have hcb' : (csOf trs)[cnt (accUnits trs) realU (a + 1)] =
        (csOf trs)[cnt (accUnits trs) realU a + 1] := getElem_idx_eq hcs _ _
    apply hp _ hea _ heb
    · rw [h3]; simp only [Ev.isR, sa.2.1]; simpa [Ev.isR] using hR.1
    · rw [h3', hcb']; rw [hcb'] at sb; simp only [Ev.isW, sb.2.1]; exact hW1
    · rw [h3]; rw [sa.2.2.2.2.1]; exact hR.2
    · rw [h3', hcb']; rw [hcb'] at sb; rw [sb.2.2.2.2.1]; exact hL1
    · rw [h3, h3', hcb', hnt']
    · rw [h3, h3', hcb', hnp']

end emb

/-! ## The litmus units of `ActOk` actions -/

theorem actUnits_props (i p : Nat) (a : XAct) (h : ActOk a) :
    ∀ u ∈ actUnits i p a, u.1.accAddr = u.1.addr ∧ u.1.accSize = u.1.size ∧
      (u.1.isM = true → 0 < u.1.size ∧ (u.1.isW = true → u.1.data.length = u.1.size)) ∧
      (u.1.isM = false → u.1.size = 0) ∧
      (u.1.isR = true → a.ev.kind.reads = true ∧ u.1.addr = a.ev.addr ∧ u.1.size = a.ev.size) := by
  obtain ⟨-, -, -, hw, hpos⟩ := h
  intro u hu
  unfold actUnits at hu
  split at hu
  all_goals rename_i hk
  all_goals simp only [hk, Silmaril.X86.MemEvent.Kind.reads,
    Silmaril.X86.MemEvent.Kind.writes] at hw hpos
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  all_goals first
    | (subst hu; simp_all [Ev.isM, Ev.isR, Ev.isW, Silmaril.X86.MemEvent.Kind.reads])
    | (rcases hu with rfl | rfl <;> simp_all [Ev.isM, Ev.isR, Ev.isW,
        Silmaril.X86.MemEvent.Kind.reads])

theorem threadUnits_mem (i : Nat) :
    ∀ (p : Nat) (as : List XAct), ∀ u ∈ Silmaril.X86.MemoryModel.Litmus.threadUnits i p as,
      ∃ a ∈ as, ∃ p', u ∈ actUnits i p' a
  | _, [], u, hu => by simp [Silmaril.X86.MemoryModel.Litmus.threadUnits] at hu
  | p, a :: as, u, hu => by
    simp only [Silmaril.X86.MemoryModel.Litmus.threadUnits, List.mem_append] at hu
    rcases hu with hu | hu
    · exact ⟨a, List.mem_cons_self .., p, hu⟩
    · obtain ⟨b, hb, p', h⟩ := threadUnits_mem i _ as u hu
      exact ⟨b, List.mem_cons_of_mem _ hb, p', h⟩

theorem acc_mem {trs : List XTrace} {u : Ev × List Byte} (h : u ∈ accUnits trs) :
    ∃ tr ∈ trs, ∃ a ∈ tr.acts, ∃ i p, u ∈ actUnits i p a := by
  simp only [accUnits, List.mem_flatten, List.mem_mapIdx] at h
  obtain ⟨l, ⟨i, hi, rfl⟩, hu⟩ := h
  obtain ⟨a, ha, p, h⟩ := threadUnits_mem i 0 _ u hu
  exact ⟨_, List.getElem_mem hi, a, ha, i, p, h⟩

theorem acc_props {trs : List XTrace} (hok : TracesOk trs) {u : Ev × List Byte}
    (h : u ∈ accUnits trs) :
    u.1.accAddr = u.1.addr ∧ u.1.accSize = u.1.size ∧
      (u.1.isM = true → 0 < u.1.size ∧ (u.1.isW = true → u.1.data.length = u.1.size)) ∧
      (u.1.isM = false → u.1.size = 0) ∧
      (u.1.isR = true → ∃ tr ∈ trs, ∃ a ∈ tr.acts, a.ev.kind.reads = true ∧
        u.1.addr = a.ev.addr ∧ u.1.size = a.ev.size) := by
  obtain ⟨tr, htr, a, ha, i, p, hu⟩ := acc_mem h
  obtain ⟨h1, h2, h3, h4, h5⟩ := actUnits_props i p a (hok tr htr a ha) u hu
  exact ⟨h1, h2, h3, h4, fun hr => ⟨tr, htr, a, ha, h5 hr⟩⟩

theorem units_eq {trs : List XTrace} (h : NoTear trs) : units trs = accUnits trs := by
  simp only [units]
  have : ∀ u ∈ accUnits trs, (if tearAcc (accUnits trs) u.1 = true then
      Silmaril.X86.MemoryModel.Litmus.splitUnit u else [u]) = [u] := fun u hu => by simp [h u hu]
  rw [List.flatMap_congr this]
  simp

/-! ## Well-formedness, reads and final memory -/

section wf
variable {trs : List XTrace} {us : List (Ev × List Byte)} (hperm : us.Perm (csOf trs))
  (hok : TracesOk trs) {x : Exec} (hx : x.evs = us.map Prod.fst)
  (hrf : ∀ r y w, x.rf r y = some w → w < x.n ∧ (x.evN w).isW = true ∧ (x.evN w).covers y = true)
  (hco : ∀ y w, w ∈ x.co y ↔ w < x.n ∧ (x.evN w).isW = true ∧ (x.evN w).covers y = true)
  (hp : RmwPaired x)
include hperm hok hx hrf hco hp

omit hx hrf hco hp in
/-- `σ` undoes `e` on real units. -/
theorem σ_e {a : Nat} (ha : a < (accUnits trs).length) (hr : realU (accUnits trs)[a] = true) :
    σIdx trs us (eIdx trs us a) = a := by
  obtain ⟨h1, h2, h3, -⟩ := eIdx_spec hperm hok ha hr
  have hg : us.getD (eIdx trs us a) d0 = (csOf trs).getD (cnt (accUnits trs) realU a) d0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, h3,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  have hc : (csOf trs).idxOf (us.getD (eIdx trs us a) d0) = cnt (accUnits trs) realU a := by
    rw [hg]; exact idxOf_getElem_nodup d0 cs_nodup h2
  have hfl : cnt (accUnits trs) realU a < ((accUnits trs).filter realU).length := by
    rw [filter_length hok]; exact h2
  obtain ⟨h4, h5, h6⟩ := uncnt_spec (accUnits trs) realU hfl
  simp only [σIdx, hc]
  exact cnt_inj _ _ h4 ha h5 hr h6

/-- The unit `σ w` of `axX` is the unit `w` of `x` (up to position and annotation). -/
theorem evN_σ {w : Nat} (hw : w < x.n) :
    ((axX x trs us).evN (σIdx trs us w)).act = (x.evN w).act ∧
      ((axX x trs us).evN (σIdx trs us w)).addr = (x.evN w).addr ∧
      ((axX x trs us).evN (σIdx trs us w)).size = (x.evN w).size ∧
      ((axX x trs us).evN (σIdx trs us w)).data = (x.evN w).data := by
  have E := axX_emb hperm hok hx hrf hco hp
  have h1 := E.σlt w hw
  have h2 := E.σreal w hw
  have h3 := E.eσ w hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [E.act _ h1 h2, h3]
  · rw [E.addr _ h1 h2, h3]
  · rw [E.size _ h1 h2, h3]
  · rw [E.data _ h1 h2, h3]

theorem isW_σ {w : Nat} (hw : w < x.n) :
    ((axX x trs us).evN (σIdx trs us w)).isW = (x.evN w).isW := by
  simp [Ev.isW, (evN_σ hperm hok hx hrf hco hp hw).1]

theorem covers_σ {w : Nat} (hw : w < x.n) (y : Nat) :
    ((axX x trs us).evN (σIdx trs us w)).covers y = (x.evN w).covers y := by
  obtain ⟨-, h2, h3, -⟩ := evN_σ hperm hok hx hrf hco hp hw
  simp [Ev.covers, h2, h3]

theorem byte_σ {w : Nat} (hw : w < x.n) (y : Nat) :
    ((axX x trs us).evN (σIdx trs us w)).byte y = (x.evN w).byte y := by
  obtain ⟨-, h2, -, h4⟩ := evN_σ hperm hok hx hrf hco hp hw
  simp [Ev.byte, h2, h4]

theorem axX_wf (hnd : ∀ y, (x.co y).Nodup) : (axX x trs us).Wf = true := by
  have E := axX_emb hperm hok hx hrf hco hp
  have hn := ax_n (x := x) (trs := trs) (us := us)
  simp only [Exec.Wf, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.mem_finRange, forall_const]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · -- `rf`
    intro r
    by_cases hR : (axX x trs us).ev r |>.isR
    · right
      intro y _
      show (match (x.rf (eIdx trs us r.val) y).map (σIdx trs us) with
        | none => true
        | some w => (axX x trs us).valid w && ((axX x trs us).evN w).isW &&
            ((axX x trs us).evN w).covers y) = true
      cases hw : x.rf (eIdx trs us r.val) y with
      | none => rfl
      | some w =>
        obtain ⟨h1, h2, h3⟩ := hrf _ _ _ hw
        simp only [Option.map_some, Exec.valid, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨E.σlt w h1, by rw [isW_σ hperm hok hx hrf hco hp h1]; exact h2⟩,
          by rw [covers_σ hperm hok hx hrf hco hp h1]; exact h3⟩
    · left; simpa using hR
  · -- `co`
    intro y _
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [decide_eq_true_eq]
      show ((x.co y).map (σIdx trs us)).Nodup
      refine List.Nodup.map_on ?_ (hnd y)
      intro a ha b hb hab
      have := congrArg (eIdx trs us) hab
      rwa [E.eσ a ((hco y a).1 ha).1, E.eσ b ((hco y b).1 hb).1] at this
    · intro w hw
      obtain ⟨w₀, hw₀, rfl⟩ := List.mem_map.1 hw
      obtain ⟨h1, h2, h3⟩ := (hco y w₀).1 hw₀
      simp only [Exec.valid, decide_eq_true_eq]
      exact ⟨⟨E.σlt w₀ h1, by rw [isW_σ hperm hok hx hrf hco hp h1]; exact h2⟩,
        by rw [covers_σ hperm hok hx hrf hco hp h1]; exact h3⟩
    · intro w
      by_cases hw : ((axX x trs us).ev w).isW && ((axX x trs us).ev w).covers y
      · right
        simp only [Bool.and_eq_true] at hw
        have hr : realE ((axX x trs us).evN w.val) = true := by
          rw [evN_eq]; exact real_of_isW hw.1
        have h1 : (x.evN (eIdx trs us w.val)).isW = true := by
          have := E.act w.val w.2 hr
          simp only [Ev.isW, ← this, evN_eq]; simpa [Ev.isW] using hw.1
        have h2 : (x.evN (eIdx trs us w.val)).covers y = true := by
          have ha := E.addr w.val w.2 hr
          have hs := E.size w.val w.2 hr
          simp only [Ev.covers, ← ha, ← hs, evN_eq]; exact hw.2
        have hmem := (hco y _).2 ⟨E.lt w.val w.2 hr, h1, h2⟩
        simp only [List.contains_eq_mem, decide_eq_true_eq]
        show w.val ∈ (x.co y).map (σIdx trs us)
        have hwn : w.val < (accUnits trs).length := hn ▸ w.2
        have hru : realU (accUnits trs)[w.val] = true := by
          rw [ax_evN (x := x) (us := us) hwn] at hr; exact hr
        exact List.mem_map.2 ⟨_, hmem, σ_e hperm hok hwn hru⟩
      · left; simpa using hw
  · -- `rmw`
    intro q hq
    simp only [axX] at hq
    obtain ⟨a, b⟩ := q
    rw [mem_rmwPairs_iff] at hq
    obtain ⟨ha, hb, hR, hW⟩ := hq
    simp only [List.length_map] at ha hb
    simp only [List.getElem_map, Bool.and_eq_true, beq_iff_eq] at hR hW
    have ea := ax_evN (x := x) (us := us) ha
    have eb := ax_evN (x := x) (us := us) hb
    obtain ⟨hac, hsc, -⟩ := acc_props hok (List.getElem_mem ha)
    obtain ⟨hac', hsc', -⟩ := acc_props hok (List.getElem_mem hb)
    simp only [Exec.valid, ea, eb, decide_eq_true_eq, beq_iff_eq, hn]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hR.1⟩, hW.1.1.1.1.1⟩, hW.1.1.1.2⟩, by omega⟩, hR.2⟩, hW.1.1.1.1.2⟩,
      by rw [hac, hac', hW.1.2]⟩, by rw [hsc, hsc', hW.2]⟩
  · -- units of one access
    intro a b
    by_cases hs : (axX x trs us).sm a b
    · right
      have := E.sm_eq a b hs
      subst this
      simp
    · left; simpa using hs
  · -- unit shapes
    intro e he
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (show e ∈ (accUnits trs).map Prod.fst from he)
    obtain ⟨h1, h2, h3, h4, -⟩ := acc_props hok hu
    split
    · rename_i hM
      obtain ⟨h5, h6⟩ := h3 hM
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
        beq_iff_eq, h1, h2]
      refine ⟨⟨⟨h5, le_refl _⟩, le_refl _⟩, ?_⟩
      cases hW : u.1.isW
      · left; rfl
      · right; exact h6 hW
    · rename_i hM
      simp [h4 (by simpa using hM)]

end wf

theorem mem_bytes {e : Ev} {y : Nat} (h : y ∈ e.bytes) : e.addr ≤ y ∧ y < e.addr + e.size := by
  simp only [Ev.bytes, List.mem_range'_1] at h; omega

section reads
variable {trs : List XTrace} {us : List (Ev × List Byte)} (hperm : us.Perm (csOf trs))
  (hok : TracesOk trs) {x : Exec} (hx : x.evs = us.map Prod.fst)
  (hrf : ∀ r y w, x.rf r y = some w → w < x.n ∧ (x.evN w).isW = true ∧ (x.evN w).covers y = true)
  (hco : ∀ y w, w ∈ x.co y ↔ w < x.n ∧ (x.evN w).isW = true ∧ (x.evN w).covers y = true)
  (hp : RmwPaired x)
include hperm hok hx hrf hco hp

/-- **The reads of `axX` return the traces' bytes.** -/
theorem axX_readsOk {t : Test} {init : Mem} (hI : InitReads t init trs)
    (hreads : ∀ r < x.n, (x.evN r).isR = true →
      x.readBytes (fun y => (init y).getD 0) r = (us.getD r d0).2) :
    ReadsOk t (axX x trs us) ((accUnits trs).map Prod.snd) := by
  intro r hr hR
  have E := axX_emb hperm hok hx hrf hco hp
  have hn := ax_n (x := x) (trs := trs) (us := us)
  have hrn : r < (accUnits trs).length := hn ▸ hr
  have ev := ax_evN (x := x) (us := us) hrn
  have hreal : realE ((axX x trs us).evN r) = true := real_of_isR hR
  have hru : realU (accUnits trs)[r] = true := by rw [ev] at hreal; exact hreal
  obtain ⟨h1, h2, h3, h4⟩ := x_eIdx hperm hok hx hrn hru
  have hact := E.act r hr hreal
  have hxR : (x.evN (eIdx trs us r)).isR = true := by
    have : (x.evN (eIdx trs us r)).act = Act.read := by
      rw [← hact]; simpa [Ev.isR] using hR
    simp [Ev.isR, this]
  have hb := hreads _ h1 hxR
  obtain ⟨h5, h6, h7⟩ := eIdx_spec hperm hok hrn hru
  have hus : (us.getD (eIdx trs us r) d0).2 = (accUnits trs)[r].2 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h5, h7.1]
    exact (strip_eq_iff.1 h7.2).2.2.2.2.2.2
  rw [hus] at hb
  have rhs : ((accUnits trs).map Prod.snd).getD r [] = (accUnits trs)[r].2 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hrn]; rfl
  rw [rhs, ← hb]
  have hbytes : ((axX x trs us).evN r).bytes = (x.evN (eIdx trs us r)).bytes := by
    simp [Ev.bytes, E.addr r hr hreal, E.size r hr hreal]
  simp only [Exec.readBytes]
  rw [hbytes]
  apply List.map_congr_left
  intro y hy
  simp only [Exec.readByte, axX]
  cases hw : x.rf (eIdx trs us r) y with
  | none =>
    simp only [Option.map_none]
    have hy' : y ∈ ((accUnits trs)[r].1).bytes := by rw [← ev, hbytes]; exact hy
    have hRu : ((accUnits trs)[r].1).isR = true := by rw [← ev]; exact hR
    obtain ⟨-, -, -, -, h8⟩ := acc_props hok (List.getElem_mem hrn)
    obtain ⟨tr, htr, a, ha, hra, hadr, hsz⟩ := h8 hRu
    have := mem_bytes hy'
    exact (hI tr htr a ha hra y (by omega) (by omega)).symm
  | some w =>
    simp only [Option.map_some]
    exact byte_σ hperm hok hx hrf hco hp (hrf _ _ _ hw).1 y

/-- **The final memory of `axX`** is the run's on every byte some unit writes, and the test's
initial value elsewhere (where the run's final memory is its initial memory). -/
theorem axX_final {init : Mem} {s : XState Nat}
    (hfin : ∀ y, s.memory y = match (x.co y).getLast? with
      | none => init y
      | some w => some ((x.evN w).byte y)) (t : Test) (y : Nat) :
    (if writtenByte (axX x trs us) y then some ((axX x trs us).finalByte t.initB y)
      else t.initMem y) = s.memory y ∨
    ((if writtenByte (axX x trs us) y then some ((axX x trs us).finalByte t.initB y)
      else t.initMem y) = t.initMem y ∧ s.memory y = init y) := by
  have E := axX_emb hperm hok hx hrf hco hp
  have hn := ax_n (x := x) (trs := trs) (us := us)
  cases hwb : writtenByte (axX x trs us) y
  · right
    refine ⟨rfl, ?_⟩
    rw [hfin y]
    cases hl : (x.co y).getLast? with
    | none => rfl
    | some v =>
      exfalso
      have hv : v ∈ x.co y := List.mem_of_getLast? hl
      obtain ⟨h1, h2, h3⟩ := (hco y v).1 hv
      have hσ := E.σlt v h1
      have : writtenByte (axX x trs us) y = true := by
        simp only [writtenByte, List.any_eq_true, Bool.and_eq_true]
        refine ⟨(axX x trs us).evN (σIdx trs us v), ?_, ?_, ?_⟩
        · simp only [Exec.evN, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hσ,
            Option.getD_some]
          exact List.getElem_mem _
        · rw [isW_σ hperm hok hx hrf hco hp h1]; exact h2
        · rw [covers_σ hperm hok hx hrf hco hp h1]; exact h3
      rw [hwb] at this; cases this
  · left
    simp only [ite_true]
    simp only [writtenByte, List.any_eq_true, Bool.and_eq_true] at hwb
    obtain ⟨e, he, hW, hC⟩ := hwb
    obtain ⟨w, hw, rfl⟩ := List.getElem_of_mem he
    have hwn : w < (axX x trs us).n := hw
    have h0 : (axX x trs us).evN w = (axX x trs us).evs[w] := by
      simp [Exec.evN, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw]
    have hW' : ((axX x trs us).evN w).isW = true := h0 ▸ hW
    have hC' : ((axX x trs us).evN w).covers y = true := h0 ▸ hC
    have hr : realE ((axX x trs us).evN w) = true := real_of_isW hW'
    have heW : (x.evN (eIdx trs us w)).isW = true := by
      have : (x.evN (eIdx trs us w)).act = Act.write := by
        rw [← E.act w hwn hr]; simpa [Ev.isW] using hW'
      simp [Ev.isW, this]
    have heC : (x.evN (eIdx trs us w)).covers y = true := by
      simpa [Ev.covers, E.addr w hwn hr, E.size w hwn hr] using hC'
    have hmem := (hco y _).2 ⟨E.lt w hwn hr, heW, heC⟩
    obtain ⟨v, hv⟩ : ∃ v, (x.co y).getLast? = some v := by
      cases h : (x.co y).getLast? with
      | none => rw [List.getLast?_eq_none_iff] at h; rw [h] at hmem; cases hmem
      | some v => exact ⟨v, rfl⟩
    have hvn := ((hco y v).1 (List.mem_of_getLast? hv)).1
    rw [hfin y, hv]
    simp only [Exec.finalByte, axX, List.getLast?_map, hv, Option.map_some, Option.some.injEq]
    exact byte_σ hperm hok hx hrf hco hp hvn y

end reads

/-- **From a store-buffer candidate to a litmus candidate** (piece (6) of `Task.tsoRunCir`'s plan).
-/
theorem axReach_of_explains {t : Test} {T : List (List XTrace)} {trs : List XTrace}
    (hT : List.Forall₂ (· ∈ ·) trs T) (hok : TracesOk trs) (hnt : NoTear trs)
    {init : Mem} (hI : InitReads t init trs) {s : XState Nat} {x : Exec}
    (hx : Explains Exec.Tso (trs.mapIdx traceX) init s x) (hp : RmwPaired x) :
    ∃ m, AxReach t T Exec.Tso (finalOf trs m) ∧
      ∀ y, m y = s.memory y ∨ (m y = t.initMem y ∧ s.memory y = init y) := by
  obtain ⟨us, hperm, hevs, hM, hreads, hrf, hco, hnd, hfin⟩ := hx
  have hperm' : us.Perm (csOf trs) := hperm
  have hrf' : ∀ r y w, x.rf r y = some w → w < x.n ∧ (x.evN w).isW = true ∧
      (x.evN w).covers y = true := hrf
  have E := axX_emb hperm' hok hevs hrf' hco hp
  refine ⟨_, ⟨trs, hT, axX x trs us, ?_, ?_, ?_, ?_, tso_of_emb E hM, rfl⟩,
    axX_final hperm' hok hevs hrf' hco hp hfin t⟩
  · rw [units_eq hnt]; rfl
  · rw [units_eq hnt]; rfl
  · exact axX_wf hperm' hok hevs hrf' hco hp hnd
  · rw [units_eq hnt]
    exact axX_readsOk hperm' hok hevs hrf' hco hp hI hreads

end Silmaril.Proofs.X86.Concurrency.Bridge.PoolRun
