module

public import Silmaril.Proofs.X86.Concurrency.Cir.Chan.Drop

/-!
# Dropping a plain load from a choice of traces: the units

Take per-thread action lists `L` and drop one action `d` of thread `i`
(`L[i] = as1 ++ d :: as2` becomes `as1 ++ as2`), where `d` is an unlocked load with a **twin**
(an action with the same `MemEvent.Event`) left in some thread. Then the `units` of the new
lists are those of the old ones without the units of `d`, renumbered (`units_drop`), and the
hypotheses `Drop.Hyp` of the execution-level restriction hold.
-/

@[expose] public section

-- Some `try`/`all_goals` combinators below are needed on some goals only.
set_option linter.unusedTactic false

namespace Silmaril.Proofs.X86.Concurrency.Cir.Chan.Drop

open Silmaril.X86.MemoryModel.Axiomatic (Ev Exec Act)
open Silmaril.X86.MemoryModel.Litmus (XAct XTrace Byte actUnits threadUnits accUnits units splitUnit
  tearAcc)
open Silmaril.X86.MemEvent (Kind)

/-- The unsplit units of per-thread action lists. -/
def accU (L : List (List XAct)) : List (Ev × List Byte) :=
  (L.mapIdx fun k as => threadUnits k 0 as).flatten

/-- One unit, split into bytes if it may tear among `us`. -/
def gU (us : List (Ev × List Byte)) (u : Ev × List Byte) : List (Ev × List Byte) :=
  if tearAcc us u.1 then splitUnit u else [u]

/-- The units of per-thread action lists. -/
def unitsU (L : List (List XAct)) : List (Ev × List Byte) := (accU L).flatMap (gU (accU L))

theorem mapIdx_map' {α β γ : Type} (l : List α) (g : α → β) (f : Nat → β → γ) :
    (l.map g).mapIdx f = l.mapIdx fun i a => f i (g a) := by
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp [List.getElem_mapIdx]

theorem accUnits_eq (trs : List XTrace) : accUnits trs = accU (trs.map (fun tr : XTrace => tr.acts)) := by
  simp only [accUnits, accU, mapIdx_map']

theorem units_eq (trs : List XTrace) : units trs = unitsU (trs.map (fun tr : XTrace => tr.acts)) := by
  simp only [units, unitsU, accUnits_eq]; rfl

/-! ## Units of actions -/

theorem actUnits_tid {k q : Nat} {a : XAct} {u : Ev × List Byte} (h : u ∈ actUnits k q a) :
    u.1.tid = k := by
  unfold actUnits at h
  split at h <;> simp at h <;> (try rcases h with h | h) <;> (try subst h) <;> rfl

theorem actUnits_pos {k q : Nat} {a : XAct} {u : Ev × List Byte} (h : u ∈ actUnits k q a) :
    q ≤ u.1.pos ∧ u.1.pos < q + (actUnits k q a).length := by
  unfold actUnits at h ⊢
  split at h <;> simp at h <;> (try rcases h with h | h) <;> (try subst h) <;> simp

theorem actUnits_length (k q k' q' : Nat) (a : XAct) :
    (actUnits k q a).length = (actUnits k' q' a).length := by
  unfold actUnits; split <;> simp

theorem actUnits_succ (k q : Nat) (a : XAct) :
    actUnits k (q + 1) a = (actUnits k q a).map fun u => ({ u.1 with pos := u.1.pos + 1 }, u.2) := by
  unfold actUnits; split <;> simp

theorem threadUnits_append (k : Nat) :
    ∀ (q : Nat) (l l' : List XAct),
      threadUnits k q (l ++ l') = threadUnits k q l ++ threadUnits k (q + (threadUnits k q l).length) l'
  | q, [], l' => by simp [threadUnits]
  | q, a :: l, l' => by
    simp only [List.cons_append, threadUnits, List.length_append, List.append_assoc]
    rw [threadUnits_append k _ l l', Nat.add_assoc]

theorem threadUnits_succ (k : Nat) :
    ∀ (q : Nat) (l : List XAct),
      threadUnits k (q + 1) l = (threadUnits k q l).map fun u => ({ u.1 with pos := u.1.pos + 1 }, u.2)
  | q, [] => by simp [threadUnits]
  | q, a :: l => by
    simp only [threadUnits, List.map_append]
    rw [actUnits_succ, List.length_map, Nat.add_right_comm, threadUnits_succ k _ l]

theorem threadUnits_mem {k : Nat} :
    ∀ {q : Nat} {l : List XAct} {u : Ev × List Byte}, u ∈ threadUnits k q l →
      u.1.tid = k ∧ q ≤ u.1.pos ∧ u.1.pos < q + (threadUnits k q l).length ∧
      ∃ a ∈ l, ∃ q', u ∈ actUnits k q' a ∧ ∀ w ∈ actUnits k q' a, w ∈ threadUnits k q l
  | q, [], u, h => by simp [threadUnits] at h
  | q, a :: l, u, h => by
    simp only [threadUnits, List.mem_append, List.length_append] at h ⊢
    rcases h with h | h
    · have := actUnits_pos h
      exact ⟨actUnits_tid h, this.1, by omega, a, List.mem_cons_self .., q, h,
        fun w hw => Or.inl hw⟩
    · obtain ⟨ht, h1, h2, b, hb, q', hu, hw⟩ := threadUnits_mem h
      exact ⟨ht, by omega, by omega, b, List.mem_cons_of_mem _ hb, q', hu,
        fun w hw' => Or.inr (hw w hw')⟩

theorem mem_accU {L : List (List XAct)} {u : Ev × List Byte} :
    u ∈ accU L ↔ ∃ k as, L[k]? = some as ∧ u ∈ threadUnits k 0 as := by
  unfold accU
  simp only [List.mem_flatten, List.mem_mapIdx]
  constructor
  · rintro ⟨l, ⟨k, hk, rfl⟩, hu⟩
    exact ⟨k, L[k], by simp [hk], hu⟩
  · rintro ⟨k, as, hk, hu⟩
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hk
    exact ⟨_, ⟨k, hlt, rfl⟩, hu⟩

/-- Where a unit comes from: an action of a thread, all of whose units are present. -/
theorem accU_src {L : List (List XAct)} {u : Ev × List Byte} (h : u ∈ accU L) :
    ∃ k as, L[k]? = some as ∧ ∃ a ∈ as, ∃ q, u ∈ actUnits k q a ∧ ∀ w ∈ actUnits k q a, w ∈ accU L := by
  obtain ⟨k, as, hk, hu⟩ := mem_accU.1 h
  obtain ⟨-, -, -, a, ha, q, hq, hw⟩ := threadUnits_mem hu
  exact ⟨k, as, hk, a, ha, q, hq, fun w hw' => mem_accU.2 ⟨k, as, hk, hw w hw'⟩⟩

/-! ## Splitting -/

/-- Two units agree on what `tearAcc` looks at. -/
def Sim (u v : Ev) : Prop :=
  u.isM = v.isM ∧ u.addr = v.addr ∧ u.size = v.size ∧ u.accAddr = v.accAddr ∧ u.accSize = v.accSize

theorem Sim.symm {u v : Ev} (h : Sim u v) : Sim v u := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h; exact ⟨h1.symm, h2.symm, h3.symm, h4.symm, h5.symm⟩

theorem Sim.trans {u v w : Ev} (h : Sim u v) (h' : Sim v w) : Sim u w := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h; obtain ⟨g1, g2, g3, g4, g5⟩ := h'
  exact ⟨h1.trans g1, h2.trans g2, h3.trans g3, h4.trans g4, h5.trans g5⟩

theorem tearAcc_sim (us : List (Ev × List Byte)) {u v : Ev} (h : Sim u v) :
    tearAcc us u = tearAcc us v := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only [tearAcc, Ev.singleCopy, Ev.accOverlap, h1, h2, h3, h4, h5]

theorem tearAcc_any {us us' : List (Ev × List Byte)} (u : Ev)
    (h : ∀ w ∈ us, ∃ w' ∈ us', Sim w.1 w'.1) (h' : ∀ w' ∈ us', ∃ w ∈ us, Sim w.1 w'.1) :
    tearAcc us u = tearAcc us' u := by
  simp only [tearAcc]
  congr 2
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨w, hw, hp⟩
    obtain ⟨w', hw', h1, h2, h3, h4, h5⟩ := h w hw
    exact ⟨w', hw', by simpa only [Ev.accOverlap, h1, h2, h3, h4, h5] using hp⟩
  · rintro ⟨w', hw', hp⟩
    obtain ⟨w, hw, h1, h2, h3, h4, h5⟩ := h' w' hw'
    exact ⟨w, hw, by simpa only [Ev.accOverlap, h1, h2, h3, h4, h5] using hp⟩

/-- The pieces of a unit keep its thread, position, direction, lock and access footprint. -/
theorem mem_gU {us : List (Ev × List Byte)} {u w : Ev × List Byte} (h : w ∈ gU us u) :
    w.1.tid = u.1.tid ∧ w.1.pos = u.1.pos ∧ w.1.act = u.1.act ∧ w.1.locked = u.1.locked ∧
      w.1.accAddr = u.1.accAddr ∧ w.1.accSize = u.1.accSize := by
  unfold gU at h
  split at h
  · simp only [splitUnit, List.mem_map] at h
    obtain ⟨y, -, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [List.mem_singleton] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem gU_ne_nil {us : List (Ev × List Byte)} {u v : Ev × List Byte} (h : Sim u.1 v.1)
    (hu : gU us u ≠ []) : gU us v ≠ [] := by
  unfold gU at hu ⊢
  rw [tearAcc_sim us h] at hu
  split
  · rename_i ht; simp only [ht, ↓reduceIte] at hu
    simpa [splitUnit, Ev.bytes, h.2.2.1] using hu
  · simp

theorem isM_of_isR {e : Ev} (h : e.isR = true) : e.isM = true := by simp [Ev.isM, h]

theorem isM_of_isW {e : Ev} (h : e.isW = true) : e.isM = true := by simp [Ev.isM, h]

theorem W_not_R {e : Ev} (hW : e.isW = true) : e.isR = false := by
  simp only [Ev.isW, Ev.isR, beq_iff_eq] at hW ⊢; rw [hW]; rfl

/-- The unit of a load. -/
theorem actUnits_load {k q : Nat} {a : XAct} (h : a.ev.kind = .load) :
    ∃ u, actUnits k q a = [u] ∧ u.1.tid = k ∧ u.1.pos = q ∧ u.1.isR = true ∧
      u.1.locked = a.ev.locked ∧ u.1.addr = a.ev.addr ∧ u.1.size = a.ev.size ∧
      u.1.accAddr = a.ev.addr ∧ u.1.accSize = a.ev.size := by
  simp only [actUnits, h]
  exact ⟨_, rfl, rfl, by simp, by simp [Ev.isR], rfl, rfl, rfl, rfl, rfl⟩

/-- A locked read unit is the read half of a read-modify-write, or of a locked load. -/
theorem actUnits_locked {k q : Nat} {a : XAct} {u : Ev × List Byte} (hu : u ∈ actUnits k q a)
    (hR : u.1.isR = true) (hL : u.1.locked = true) :
    (∃ w ∈ actUnits k q a, w.1.isW = true ∧ w.1.tid = u.1.tid ∧ w.1.pos = u.1.pos + 1 ∧
      Sim w.1 u.1) ∨ (a.ev.kind = .load ∧ a.ev.locked = true) := by
  unfold actUnits at hu ⊢
  split at hu <;> rename_i hk
  · simp only [List.mem_singleton] at hu; subst hu; exact Or.inr ⟨hk, hL⟩
  · simp only [List.mem_singleton] at hu; subst hu; simp [Ev.isR] at hR
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact Or.inl ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), by simp [Ev.isW], rfl,
        by simp, by simp [Ev.isM, Ev.isR, Ev.isW], rfl, rfl, rfl, rfl⟩
    · simp [Ev.isR] at hR
  · simp only [List.mem_singleton] at hu; subst hu; simp [Ev.isR] at hR

theorem threadUnits_of_mem {k : Nat} :
    ∀ {q : Nat} {l : List XAct} {a : XAct}, a ∈ l →
      ∃ q', ∀ w ∈ actUnits k q' a, w ∈ threadUnits k q l
  | q, [], a, h => by simp at h
  | q, b :: l, a, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨q, fun w hw => by simp only [threadUnits, List.mem_append]; exact Or.inl hw⟩
    · obtain ⟨q', hq⟩ := threadUnits_of_mem (q := q + (actUnits k q b).length) h
      exact ⟨q', fun w hw => by simp only [threadUnits, List.mem_append]; exact Or.inr (hq w hw)⟩

theorem accU_split (pre suf : List (List XAct)) (X : List XAct) :
    accU (pre ++ X :: suf) = accU pre ++ threadUnits pre.length 0 X ++
      (suf.mapIdx fun k as => threadUnits (k + 1 + pre.length) 0 as).flatten := by
  simp only [accU, List.mapIdx_append, List.mapIdx_cons, List.flatten_append, List.flatten_cons,
    Nat.zero_add, List.append_assoc]

theorem accU_tid_lt {L : List (List XAct)} {u : Ev × List Byte} (h : u ∈ accU L) : u.1.tid < L.length := by
  obtain ⟨k, as, hk, hu⟩ := mem_accU.1 h
  rw [(threadUnits_mem hu).1]
  exact (List.getElem?_eq_some_iff.1 hk).1

theorem suf_tid {suf : List (List XAct)} {n : Nat} {u : Ev × List Byte}
    (h : u ∈ (suf.mapIdx fun k as => threadUnits (k + 1 + n) 0 as).flatten) : n < u.1.tid := by
  simp only [List.mem_flatten, List.mem_mapIdx] at h
  obtain ⟨l, ⟨k, hk, rfl⟩, hu⟩ := h
  rw [(threadUnits_mem hu).1]; omega

theorem rp_self {f : Ev → Nat} {u : Ev} (h : f u = u.pos) : rp f u = u := by
  unfold rp; rw [h]

theorem if_pos' {c : Prop} [Decidable c] {α : Type} {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem if_neg' {c : Prop} [Decidable c] {α : Type} {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

/-- The renumbering of a drop at position `p` of thread `i`. -/
def fDrop (i p : Nat) (u : Ev) : Nat := if u.tid = i ∧ p < u.pos then u.pos - 1 else u.pos

/-- Renumber a unit with its bytes. -/
def R (f : Ev → Nat) (q : Ev × List Byte) : Ev × List Byte := (rp f q.1, q.2)

theorem map_R_self {f : Ev → Nat} {l : List (Ev × List Byte)} (h : ∀ q ∈ l, f q.1 = q.1.pos) :
    l.map (R f) = l := by
  conv => rhs; rw [← List.map_id l]
  apply List.map_congr_left
  intro q hq
  simp only [R, rp_self (h q hq), id]

theorem sim_rp (f : Ev → Nat) (u : Ev) : Sim (rp f u) u := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem splitUnit_R (i p : Nat) (u : Ev × List Byte) :
    splitUnit (R (fDrop i p) u) = (splitUnit u).map (R (fDrop i p)) := by
  simp only [splitUnit, R, List.map_map]
  apply List.map_congr_left
  intro y _
  rfl

/-- **Dropping one load from a thread**: the units before and after. -/
theorem units_drop (L : List (List XAct)) (i : Nat) (as1 as2 : List XAct) (d : XAct)
    (hi : L[i]? = some (as1 ++ d :: as2)) (hd : d.ev.kind = .load) (hdl : d.ev.locked = false)
    (htw : ∃ (k : Nat) (as : List XAct), (L.set i (as1 ++ as2))[k]? = some as ∧
      ∃ tw : XAct, tw ∈ as ∧ tw.ev = d.ev)
    (hlk : ∀ (k : Nat) (as : List XAct), L[k]? = some as → ∀ a : XAct, a ∈ as →
      a.ev.kind = .load → a.ev.locked = false) :
    ∃ (UA UB UC : List (Ev × List Byte)) (f : Ev → Nat), unitsU L = UA ++ UB ++ UC ∧
      unitsU (L.set i (as1 ++ as2)) = (UA ++ UC).map (fun q => (rp f q.1, q.2)) ∧
      Hyp (UA.map Prod.fst) (UB.map Prod.fst) (UC.map Prod.fst) f := by
  -- the shape of the lists
  have hiL : i < L.length := (List.getElem?_eq_some_iff.1 hi).1
  have hLi : L[i] = as1 ++ d :: as2 := (List.getElem?_eq_some_iff.1 hi).2
  set pre := L.take i with hpre
  set suf := L.drop (i + 1) with hsuf
  have hlen : pre.length = i := by simp [hpre]; omega
  have hL : L = pre ++ (as1 ++ d :: as2) :: suf := by
    rw [hpre, hsuf, ← hLi]; simp
  have hL' : L.set i (as1 ++ as2) = pre ++ (as1 ++ as2) :: suf := by
    rw [List.set_eq_take_append_cons_drop]; simp only [hiL, ↓reduceIte]; rfl
  set T1 := threadUnits i 0 as1 with hT1
  set p := T1.length with hp
  obtain ⟨du, hdu, hdt, hdp, hdR, hdL, hda, hds, hdaa, hdas⟩ := actUnits_load (k := i) (q := p) hd
  set T2' := threadUnits i p as2 with hT2'
  set T2 := threadUnits i (p + 1) as2 with hT2
  set Pre := accU pre with hPre
  set Suf := (suf.mapIdx fun k as => threadUnits (k + 1 + i) 0 as).flatten with hSuf
  have hus : accU L = (Pre ++ T1) ++ [du] ++ (T2 ++ Suf) := by
    rw [hL, accU_split, hlen, threadUnits_append, threadUnits, Nat.zero_add, ← hT1, ← hp, hdu]
    simp only [List.length_singleton, List.append_assoc, List.cons_append, List.nil_append]
    rfl
  have hus' : accU (L.set i (as1 ++ as2)) = (Pre ++ T1) ++ (T2' ++ Suf) := by
    rw [hL', accU_split, hlen, threadUnits_append, Nat.zero_add, ← hT1, ← hp]
    simp only [List.append_assoc]
    rfl
  -- positions
  have hPre_t : ∀ q ∈ Pre, q.1.tid < i := fun q hq => hlen ▸ accU_tid_lt hq
  have hSuf_t : ∀ q ∈ Suf, i < q.1.tid := fun q hq => suf_tid hq
  have hT1_p : ∀ q ∈ T1, q.1.tid = i ∧ q.1.pos < p := fun q hq => by
    have := threadUnits_mem hq; exact ⟨this.1, by rw [hp, hT1]; omega⟩
  have hT2_p : ∀ q ∈ T2, q.1.tid = i ∧ p + 1 ≤ q.1.pos := fun q hq => by
    have := threadUnits_mem hq; exact ⟨this.1, this.2.1⟩
  have hT2'_p : ∀ q ∈ T2', q.1.tid = i ∧ p ≤ q.1.pos := fun q hq => by
    have := threadUnits_mem hq; exact ⟨this.1, this.2.1⟩
  set f := fDrop i p with hf
  have hkept : ∀ q ∈ (Pre ++ T1) ++ (T2 ++ Suf), q.1.tid = i → q.1.pos ≠ p := by
    intro q hq ht
    simp only [List.mem_append] at hq
    rcases hq with (hq | hq) | (hq | hq)
    · exact absurd ht (by have := hPre_t q hq; omega)
    · have := hT1_p q hq; omega
    · have := hT2_p q hq; omega
    · exact absurd ht (by have := hSuf_t q hq; omega)
  -- the new units are the renumbered old ones
  have hmap : (Pre ++ T1) ++ (T2' ++ Suf) = ((Pre ++ T1) ++ (T2 ++ Suf)).map (R f) := by
    simp only [List.map_append]
    rw [map_R_self (l := Pre), map_R_self (l := T1), map_R_self (l := Suf)]
    · congr 2
      rw [hT2, threadUnits_succ, List.map_map, ← hT2']
      conv => lhs; rw [← List.map_id T2']
      apply List.map_congr_left
      intro q hq
      have := hT2'_p q hq
      simp only [Function.comp, R, rp, hf, fDrop, id]
      rw [if_pos' (⟨this.1, by omega⟩ : q.1.tid = i ∧ p < q.1.pos + 1)]
      simp
    · intro q hq; have := hSuf_t q hq; simp only [hf, fDrop]; exact if_neg' (by omega)
    · intro q hq; have := hT1_p q hq; simp only [hf, fDrop]; exact if_neg' (by omega)
    · intro q hq; have := hPre_t q hq; simp only [hf, fDrop]; exact if_neg' (by omega)
  set K := (Pre ++ T1) ++ (T2 ++ Suf) with hK
  set us := accU L with hus_def
  set us' := accU (L.set i (as1 ++ as2)) with hus'_def
  -- the twin
  obtain ⟨tu, htuK, htu⟩ : ∃ tu ∈ K, Sim tu.1 du.1 ∧ tu.1.isR = true := by
    obtain ⟨k, as, hk, tw, htw, hte⟩ := htw
    obtain ⟨q', hq'⟩ := threadUnits_of_mem (k := k) (q := 0) htw
    obtain ⟨tu', htu', -, -, htR, -, hta, hts, htaa, htas⟩ :=
      actUnits_load (k := k) (q := q') (a := tw) (by rw [hte]; exact hd)
    have hmem : tu' ∈ us' := mem_accU.2 ⟨k, as, hk, hq' tu' (by rw [htu']; simp)⟩
    rw [hus', hmap, List.mem_map] at hmem
    obtain ⟨tu, htuK, rfl⟩ := hmem
    refine ⟨tu, htuK, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [R, rp_isR] at htR; rw [isM_of_isR htR, isM_of_isR hdR]
    · simp only [R, rp_addr] at hta; rw [hta, hte, hda]
    · simp only [R, rp_size] at hts; rw [hts, hte, hds]
    · simp only [R, rp_accAddr] at htaa; rw [htaa, hte, hdaa]
    · simp only [R, rp_accSize] at htas; rw [htas, hte, hdas]
    · simpa only [R, rp_isR] using htR
  -- splitting commutes with the renumbering
  have hsim : ∀ w ∈ us, ∃ w' ∈ us', Sim w.1 w'.1 := by
    intro w hw
    rw [hus, List.mem_append, List.mem_append, List.mem_singleton] at hw
    rw [hus', hmap]
    rcases hw with (hw | rfl) | hw
    · exact ⟨R f w, List.mem_map_of_mem (List.mem_append_left _ hw), (sim_rp f w.1).symm⟩
    · exact ⟨R f tu, List.mem_map_of_mem htuK, htu.1.symm.trans (sim_rp f tu.1).symm⟩
    · exact ⟨R f w, List.mem_map_of_mem (List.mem_append_right _ hw), (sim_rp f w.1).symm⟩
  have hsim' : ∀ w' ∈ us', ∃ w ∈ us, Sim w.1 w'.1 := by
    intro w' hw'
    rw [hus', hmap, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    refine ⟨w, ?_, (sim_rp f w.1).symm⟩
    rw [hus]
    simp only [hK, List.mem_append] at hw ⊢
    tauto
  have hg : ∀ u ∈ K, gU us' (R f u) = (gU us u).map (R f) := by
    intro u _
    unfold gU
    have ht : tearAcc us' (R f u).1 = tearAcc us u.1 := by
      show tearAcc us' (rp f u.1) = _
      rw [tearAcc_sim us' (sim_rp f u.1), tearAcc_any u.1 hsim hsim']
    rw [ht]
    split
    · exact splitUnit_R i p u
    · rfl
  have hfl : us.flatMap (gU us) = (Pre ++ T1).flatMap (gU us) ++ gU us du ++
      (T2 ++ Suf).flatMap (gU us) := by
    rw [hus]; simp only [List.flatMap_append, List.flatMap_singleton]
  have hfl' : us'.flatMap (gU us') = ((Pre ++ T1).flatMap (gU us) ++ (T2 ++ Suf).flatMap (gU us)).map (R f) := by
    have hh : ∀ (l : List (Ev × List Byte)) (g : Ev × List Byte → List (Ev × List Byte)),
        l = K.map (R f) → l.flatMap g = (K.map (R f)).flatMap g := by
      intro l g hl; rw [hl]
    rw [hh us' (gU us') (by rw [hus', hmap]), List.flatMap_map, ← List.flatMap_append, List.map_flatMap]
    apply List.flatMap_congr
    intro u hu
    exact hg u hu
  refine ⟨(Pre ++ T1).flatMap (gU us), gU us du, (T2 ++ Suf).flatMap (gU us), f, hfl, hfl', ?_⟩
  -- the hypotheses of the restriction
  have hsrc : ∀ w ∈ ((Pre ++ T1).flatMap (gU us)).map Prod.fst ++ ((T2 ++ Suf).flatMap (gU us)).map Prod.fst,
      ∃ q v, v ∈ K ∧ q ∈ gU us v ∧ w = q.1 := by
    intro w hw
    simp only [List.mem_append, List.mem_map, List.mem_flatMap] at hw
    rcases hw with ⟨q, ⟨v, hv, hq⟩, rfl⟩ | ⟨q, ⟨v, hv, hq⟩, rfl⟩
    · exact ⟨q, v, by simp only [hK, List.mem_append]; tauto, hq, rfl⟩
    · exact ⟨q, v, by simp only [hK, List.mem_append]; tauto, hq, rfl⟩
  have hne : ∀ w ∈ ((Pre ++ T1).flatMap (gU us)).map Prod.fst ++ ((T2 ++ Suf).flatMap (gU us)).map Prod.fst,
      w.tid = i → w.pos ≠ p := by
    intro w hw ht
    obtain ⟨q, v, hv, hq, rfl⟩ := hsrc w hw
    obtain ⟨h1, h2, -⟩ := mem_gU hq
    rw [h2]; exact hkept v hv (h1 ▸ ht)
  have hKsub : ∀ v ∈ K, ∀ q ∈ gU us v, q.1 ∈ ((Pre ++ T1).flatMap (gU us)).map Prod.fst ++
      ((T2 ++ Suf).flatMap (gU us)).map Prod.fst := by
    intro v hv q hq
    simp only [hK, List.mem_append] at hv
    simp only [List.mem_append, List.mem_map, List.mem_flatMap]
    rcases hv with hv | hv
    · exact Or.inl ⟨q, ⟨v, by simpa only [List.mem_append] using hv, hq⟩, rfl⟩
    · exact Or.inr ⟨q, ⟨v, by simpa only [List.mem_append] using hv, hq⟩, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro u hu v hv ht
    have hu' := hne u hu
    have hv' := hne v hv
    simp only [hf, fDrop]
    by_cases hti : u.tid = i
    · have hup := hu' hti; have hvp := hv' (ht ▸ hti)
      split_ifs <;> omega
    · have hvi : v.tid ≠ i := ht ▸ hti
      simp only [hti, hvi, false_and, ↓reduceIte]
  · intro w hw
    simp only [List.mem_map] at hw
    obtain ⟨q, hq, rfl⟩ := hw
    obtain ⟨-, -, ha, hl, haa, has⟩ := mem_gU hq
    refine ⟨by simp only [Ev.isR] at hdR ⊢; rw [ha]; exact hdR, by rw [hl, hdL, hdl], ?_⟩
    have hne' : gU us tu ≠ [] := gU_ne_nil htu.1.symm (List.ne_nil_of_mem hq)
    obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hne'
    obtain ⟨-, -, ha', -, haa', has'⟩ := mem_gU hw
    refine ⟨w.1, hKsub tu htuK w hw, ?_, ?_, ?_⟩
    · have : w.1.isR = true := by simp only [Ev.isR] at htu ⊢; rw [ha']; exact htu.2
      exact isM_of_isR this
    · rw [haa', haa]; exact htu.1.2.2.2.1
    · rw [has', has]; exact htu.1.2.2.2.2
  · intro u hu hR hL
    obtain ⟨q, v, hv, hq, rfl⟩ := hsrc u hu
    obtain ⟨h1, h2, ha, hl, -, -⟩ := mem_gU hq
    have hvR : v.1.isR = true := by simp only [Ev.isR] at hR ⊢; rw [← ha]; exact hR
    have hvL : v.1.locked = true := by rw [← hl]; exact hL
    have hvus : v ∈ us := by
      rw [hus]; simp only [hK, List.mem_append] at hv ⊢; tauto
    obtain ⟨k, as, hk, a, ha', q0, hvq, hall⟩ := accU_src hvus
    rcases actUnits_locked hvq hvR hvL with ⟨w, hw, hwW, hwt, hwp, hws⟩ | ⟨hka, hla⟩
    · have hwus : w ∈ us := hall w hw
      have hwK : w ∈ K := by
        rw [hus] at hwus
        simp only [List.mem_append, List.mem_singleton] at hwus
        simp only [hK, List.mem_append]
        rcases hwus with ((h | h) | h) | (h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · subst h; rw [W_not_R hwW] at hdR; cases hdR
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      have hne' : gU us w ≠ [] := gU_ne_nil hws.symm (List.ne_nil_of_mem hq)
      obtain ⟨w', hw'⟩ := List.exists_mem_of_ne_nil _ hne'
      obtain ⟨g1, g2, -⟩ := mem_gU hw'
      exact ⟨w'.1, hKsub w hwK w' hw', by rw [g1, hwt, h1], by rw [g2, hwp, h2]⟩
    · exact absurd (hlk k as hk a ha' hka) (by rw [hla]; decide)

end Silmaril.Proofs.X86.Concurrency.Cir.Chan.Drop
