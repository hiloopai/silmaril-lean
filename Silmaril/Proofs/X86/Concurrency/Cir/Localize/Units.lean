module

public import Silmaril.Proofs.X86.Concurrency.Cir.Localize.Run

/-!
# Localisation: the units of a choice of traces

The `units` of a choice of traces in which thread `i`'s actions are
`a1 ++ a2 ++ a3`, and of the same choice with thread `i`'s actions replaced by `a1 ++ b ++ a3`,
when `a2` and `b` access only cells (aligned, at most eight bytes, equal or disjoint) and every
other action avoids them:

* `units_split`: the old units are `A ++ threadUnits i p1 a2 ++ C` and the new ones
  `A ++ threadUnits i p1 b ++ C'`, with `C'` the units of `C` whose positions in thread `i` move
  by `|b's units| - |a2's units|` (no cell unit tears, and whether another unit tears does not
  depend on the cell units).
-/

@[expose] public section

-- Some `try`/`all_goals` combinators below are needed on some goals only.
set_option linter.unusedTactic false

namespace Silmaril.Proofs.X86.Concurrency.Cir.Localize

open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Litmus (Byte XAct XTrace actUnits threadUnits accUnits units tearAcc
  splitUnit annOf)

/-! ## Thread units -/

/-- Retag a unit: thread `i`, position moved by `p`. -/
def rt (i p : Nat) (u : Ev × List Byte) : Ev × List Byte :=
  ({ u.1 with tid := i, pos := u.1.pos + p }, u.2)

theorem actUnits_rt' (i p q : Nat) (a : XAct) :
    actUnits i (q + p) a = (actUnits 0 q a).map (rt i p) := by
  unfold actUnits
  cases a.ev.kind <;> simp [rt]; omega

theorem length_actUnits (i p : Nat) (a : XAct) :
    (actUnits i p a).length = (actUnits 0 0 a).length := by
  unfold actUnits; cases a.ev.kind <;> simp

theorem threadUnits_rt' (i p : Nat) : ∀ (q : Nat) (as : List XAct),
    threadUnits i (q + p) as = (threadUnits 0 q as).map (rt i p)
  | q, [] => rfl
  | q, a :: as => by
    simp only [threadUnits, List.map_append]
    rw [actUnits_rt' i p q a, List.length_map,
      show q + p + (actUnits 0 q a).length = (q + (actUnits 0 q a).length) + p by omega,
      threadUnits_rt' i p _ as]

theorem threadUnits_rt (i p : Nat) (as : List XAct) :
    threadUnits i p as = (threadUnits 0 0 as).map (rt i p) := by
  have := threadUnits_rt' i p 0 as; rwa [Nat.zero_add] at this

theorem length_threadUnits (i p : Nat) (as : List XAct) :
    (threadUnits i p as).length = (threadUnits 0 0 as).length := by
  rw [threadUnits_rt]; simp

theorem threadUnits_append (i : Nat) : ∀ (p : Nat) (as bs : List XAct),
    threadUnits i p (as ++ bs) = threadUnits i p as ++ threadUnits i (p + (threadUnits i p as).length) bs
  | p, [], bs => by simp [threadUnits]
  | p, a :: as, bs => by
    simp only [List.cons_append, threadUnits, List.length_append, List.append_assoc]
    rw [threadUnits_append i _ as bs, Nat.add_assoc]

theorem actUnits_pos (i p : Nat) (a : XAct) :
    ∀ k (hk : k < (actUnits i p a).length), ((actUnits i p a)[k]).1.tid = i ∧
      ((actUnits i p a)[k]).1.pos = p + k := by
  unfold actUnits
  cases a.ev.kind <;> intro k hk <;> simp at hk ⊢
  · subst hk; simp
  · subst hk; simp
  · obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    all_goals simp
  · subst hk; simp

theorem threadUnits_pos (i : Nat) : ∀ (p : Nat) (as : List XAct) k
    (hk : k < (threadUnits i p as).length),
    ((threadUnits i p as)[k]).1.tid = i ∧ ((threadUnits i p as)[k]).1.pos = p + k
  | p, [], k, hk => by simp [threadUnits] at hk
  | p, a :: as, k, hk => by
    simp only [threadUnits] at hk ⊢
    by_cases h : k < (actUnits i p a).length
    · rw [List.getElem_append_left h]; exact actUnits_pos i p a k h
    · rw [List.getElem_append_right (by omega)]
      have := threadUnits_pos i (p + (actUnits i p a).length) as (k - (actUnits i p a).length)
        (by simp only [List.length_append] at hk; omega)
      refine ⟨this.1, by rw [this.2]; omega⟩

/-- A property of the units of every action is a property of the thread's units. -/
theorem threadUnits_all {P : Ev × List Byte → Prop} {i : Nat} :
    ∀ (p : Nat) (as : List XAct), (∀ a ∈ as, ∀ p, ∀ u ∈ actUnits i p a, P u) →
      ∀ u ∈ threadUnits i p as, P u
  | p, [], _, u, hu => by simp [threadUnits] at hu
  | p, a :: as, h, u, hu => by
    simp only [threadUnits, List.mem_append] at hu
    rcases hu with hu | hu
    · exact h a List.mem_cons_self p u hu
    · exact threadUnits_all _ as (fun a' ha' => h a' (List.mem_cons_of_mem _ ha')) u hu

/-- Locked write units of a thread come after its first position (their read is before). -/
theorem actUnits_lockW (i p : Nat) (a : XAct) (ha : a.ev.locked = true → a.ev.kind = .rmw) :
    ∀ u ∈ actUnits i p a, u.1.isW = true → u.1.locked = true → p < u.1.pos := by
  intro u hu hW hL
  unfold actUnits at hu
  cases hk : a.ev.kind <;> simp only [hk, List.mem_cons, List.not_mem_nil, or_false] at hu
  · subst hu; simp [Ev.isW] at hW
  · subst hu; simp at hL; rw [hk] at ha; cases ha hL
  · rcases hu with rfl | rfl
    · simp [Ev.isW] at hW
    · simp
  · subst hu; simp [Ev.isW] at hW

theorem threadUnits_lockW (i : Nat) : ∀ (p : Nat) (as : List XAct),
    (∀ a ∈ as, a.ev.locked = true → a.ev.kind = .rmw) →
    ∀ u ∈ threadUnits i p as, u.1.isW = true → u.1.locked = true → p < u.1.pos
  | p, [], _, u, hu => by simp [threadUnits] at hu
  | p, a :: as, h, u, hu => by
    simp only [threadUnits, List.mem_append] at hu
    rcases hu with hu | hu
    · exact actUnits_lockW i p a (h a List.mem_cons_self) u hu
    · intro hW hL
      have := threadUnits_lockW i _ as (fun a' ha' => h a' (List.mem_cons_of_mem _ ha')) u hu hW hL
      omega

theorem mem_threadUnits_tid {i p : Nat} {as : List XAct} {u : Ev × List Byte}
    (h : u ∈ threadUnits i p as) : u.1.tid = i := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem h
  exact (threadUnits_pos i p as k hk).1

theorem mem_threadUnits_pos {i p : Nat} {as : List XAct} {u : Ev × List Byte}
    (h : u ∈ threadUnits i p as) : p ≤ u.1.pos ∧ u.1.pos < p + (threadUnits i p as).length := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem h
  rw [(threadUnits_pos i p as k hk).2]; omega

/-! ## Per-thread lists -/

/-- The unit lists of the threads. -/
def UL (trs : List XTrace) : List (List (Ev × List Byte)) :=
  trs.mapIdx fun k tr => threadUnits k 0 tr.acts

theorem length_UL (trs : List XTrace) : (UL trs).length = trs.length := by simp [UL]

theorem UL_get (trs : List XTrace) (k : Nat) (hk : k < (UL trs).length) :
    (UL trs)[k] = threadUnits k 0 (trs[k]'(by rw [length_UL] at hk; exact hk)).acts := by
  simp [UL]

theorem UL_set (trs : List XTrace) (i : Nat) (t : XTrace) :
    UL (trs.set i t) = (UL trs).set i (threadUnits i 0 t.acts) := by
  apply List.ext_getElem
  · simp [UL]
  · intro k h1 h2
    simp only [UL, List.getElem_mapIdx, List.getElem_set]
    split <;> rename_i h
    · subst h; simp
    · rfl

theorem flatten_mid {α : Type} (L : List (List α)) (i : Nat) (hi : i < L.length) :
    L.flatten = (L.take i).flatten ++ L[i] ++ (L.drop (i + 1)).flatten := by
  have := List.take_append_drop i L
  rw [List.drop_eq_getElem_cons hi] at this
  calc L.flatten = (List.take i L ++ L[i] :: List.drop (i + 1) L).flatten := by rw [this]
    _ = _ := by simp only [List.flatten_append, List.flatten_cons, List.append_assoc]

theorem flatten_set {α : Type} (L : List (List α)) (i : Nat) (hi : i < L.length) (X : List α) :
    (L.set i X).flatten = (L.take i).flatten ++ X ++ (L.drop (i + 1)).flatten := by
  rw [flatten_mid (L.set i X) i (by simpa using hi)]
  simp [List.take_set_of_le (le_refl i), List.drop_set_of_lt (Nat.lt_succ_self i)]

theorem mem_take_UL {trs : List XTrace} {i : Nat} {u : Ev × List Byte}
    (h : u ∈ ((UL trs).take i).flatten) :
    ∃ k, ∃ hk : k < trs.length, k < i ∧ u ∈ threadUnits k 0 (trs[k]).acts := by
  obtain ⟨l, hl, hu⟩ := List.mem_flatten.mp h
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hl
  simp only [List.length_take, length_UL] at hk
  refine ⟨k, by omega, by omega, ?_⟩
  rw [List.getElem_take, UL_get] at hu
  exact hu

theorem mem_drop_UL {trs : List XTrace} {i : Nat} {u : Ev × List Byte}
    (h : u ∈ ((UL trs).drop (i + 1)).flatten) :
    ∃ k, ∃ hk : k < trs.length, i < k ∧ u ∈ threadUnits k 0 (trs[k]).acts := by
  obtain ⟨l, hl, hu⟩ := List.mem_flatten.mp h
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hl
  simp only [List.length_drop, length_UL] at hk
  refine ⟨i + 1 + k, by omega, by omega, ?_⟩
  rw [List.getElem_drop, UL_get] at hu
  exact hu

/-! ## Cells and tearing -/

/-- Aligned cells of 1, 2, 4 or 8 bytes, any two equal or disjoint. -/
def CellsOk (cs : List (Nat × Nat)) : Prop :=
  (∀ c ∈ cs, (c.2 = 1 ∨ c.2 = 2 ∨ c.2 = 4 ∨ c.2 = 8) ∧ c.1 % c.2 = 0) ∧
    ∀ c ∈ cs, ∀ d ∈ cs, c = d ∨ c.1 + c.2 ≤ d.1 ∨ d.1 + d.2 ≤ c.1

/-- A unit of an action that avoids the cells. -/
def UK (cs : List (Nat × Nat)) (u : Ev × List Byte) : Prop :=
  u.1.isM = true → u.1.accAddr ≤ u.1.addr ∧ u.1.addr + u.1.size ≤ u.1.accAddr + u.1.accSize ∧
    ∀ c ∈ cs, u.1.accAddr + u.1.accSize ≤ c.1 ∨ c.1 + c.2 ≤ u.1.accAddr

/-- An (unsplit) unit of a cell action. -/
def UC (cs : List (Nat × Nat)) (u : Ev × List Byte) : Prop :=
  u.1.isM = true → u.1.addr = u.1.accAddr ∧ u.1.size = u.1.accSize ∧ (u.1.addr, u.1.size) ∈ cs

theorem actUnits_UK {cs : List (Nat × Nat)} {a : XAct} (ha : ActAvoid cs a) (k p : Nat) :
    ∀ u ∈ actUnits k p a, UK cs u := by
  intro u hu hM
  unfold actUnits at hu
  cases hk : a.ev.kind with
  | load => simp only [hk, List.mem_singleton] at hu; subst hu; exact ⟨le_refl _, le_refl _, ha⟩
  | store => simp only [hk, List.mem_singleton] at hu; subst hu; exact ⟨le_refl _, le_refl _, ha⟩
  | rmw =>
    simp only [hk, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> exact ⟨le_refl _, le_refl _, ha⟩
  | fence f =>
    simp only [hk, List.mem_singleton] at hu; subst hu; simp [Ev.isM, Ev.isR, Ev.isW] at hM

theorem actUnits_UC {cs : List (Nat × Nat)} {a : XAct}
    (ha : (∃ f, a.ev.kind = .fence f) ∨ (a.ev.addr, a.ev.size) ∈ cs) (k p : Nat) :
    ∀ u ∈ actUnits k p a, UC cs u := by
  intro u hu hM
  unfold actUnits at hu
  cases hk : a.ev.kind with
  | load =>
    simp only [hk, List.mem_singleton] at hu; subst hu
    exact ⟨rfl, rfl, ha.resolve_left (by simp [hk])⟩
  | store =>
    simp only [hk, List.mem_singleton] at hu; subst hu
    exact ⟨rfl, rfl, ha.resolve_left (by simp [hk])⟩
  | rmw =>
    simp only [hk, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> exact ⟨rfl, rfl, ha.resolve_left (by simp [hk])⟩
  | fence f =>
    simp only [hk, List.mem_singleton] at hu; subst hu; simp [Ev.isM, Ev.isR, Ev.isW] at hM

/-- The tearing test against one unit. -/
def tq (e : Ev) (v : Ev × List Byte) : Bool :=
  v.1.isM && e.accOverlap v.1 && (e.addr != v.1.addr || e.size != v.1.size)

theorem tearAcc_eq (us : List (Ev × List Byte)) (e : Ev) :
    tearAcc us e = (e.isM && (!e.singleCopy || us.any (tq e))) := rfl

theorem tq_KC {cs : List (Nat × Nat)} {e : Ev} (he : e.isM = true → ∀ c ∈ cs,
      e.accAddr + e.accSize ≤ c.1 ∨ c.1 + c.2 ≤ e.accAddr) (hM : e.isM = true)
    {v : Ev × List Byte} (hv : UC cs v) : tq e v = false := by
  unfold tq
  cases hvM : v.1.isM
  · rfl
  obtain ⟨h1, h2, h3⟩ := hv hvM
  have := he hM _ h3
  have hov : e.accOverlap v.1 = false := by
    simp only [Ev.accOverlap, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    (try simp only at this); omega
  simp [hov]

theorem tq_CK {cs : List (Nat × Nat)} {e : Ev} (he : e.isM = true → e.addr = e.accAddr ∧
      e.size = e.accSize ∧ (e.addr, e.size) ∈ cs) (hM : e.isM = true)
    {v : Ev × List Byte} (hv : UK cs v) : tq e v = false := by
  unfold tq
  cases hvM : v.1.isM
  · rfl
  obtain ⟨h1, h2, h3⟩ := he hM
  have := (hv hvM).2.2 _ h3
  have hov : e.accOverlap v.1 = false := by
    simp only [Ev.accOverlap, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    (try simp only at this); omega
  simp [hov]

theorem tq_CC {cs : List (Nat × Nat)} (hcs : CellsOk cs) {e : Ev} (he : e.isM = true →
      e.addr = e.accAddr ∧ e.size = e.accSize ∧ (e.addr, e.size) ∈ cs) (hM : e.isM = true)
    {v : Ev × List Byte} (hv : UC cs v) : tq e v = false := by
  unfold tq
  cases hvM : v.1.isM
  · rfl
  obtain ⟨h1, h2, h3⟩ := he hM
  obtain ⟨g1, g2, g3⟩ := hv hvM
  rcases hcs.2 _ h3 _ g3 with h | h | h
  · simp only [Prod.mk.injEq] at h
    simp [h.1, h.2]
  · have hov : e.accOverlap v.1 = false := by
      simp only [Ev.accOverlap, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      (try simp only at h); omega
    simp [hov]
  · have hov : e.accOverlap v.1 = false := by
      simp only [Ev.accOverlap, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      (try simp only at h); omega
    simp [hov]

/-- A cell unit never tears. -/
theorem tear_C {cs : List (Nat × Nat)} (hcs : CellsOk cs) {us : List (Ev × List Byte)}
    (hus : ∀ v ∈ us, UK cs v ∨ UC cs v) {u : Ev × List Byte} (hu : UC cs u) :
    tearAcc us u.1 = false := by
  rw [tearAcc_eq]
  cases hM : u.1.isM
  · rfl
  obtain ⟨h1, h2, h3⟩ := hu hM
  have hsc : u.1.singleCopy = true := by
    obtain ⟨hs, ha⟩ := hcs.1 _ h3
    simp only [Ev.singleCopy, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, ← h1, ← h2]
    simp only at hs ha
    exact ⟨by omega, ha⟩
  simp only [hsc, Bool.not_true, Bool.false_or, Bool.true_and, List.any_eq_false]
  intro v hv
  rcases hus v hv with h | h
  · simp [tq_CK hu hM h]
  · simp [tq_CC hcs hu hM h]

/-! ## Splitting -/

/-- The splitting of one unit. -/
def sp (us : List (Ev × List Byte)) (u : Ev × List Byte) : List (Ev × List Byte) :=
  if tearAcc us u.1 then splitUnit u else [u]

theorem units_eq' (trs : List XTrace) : units trs = (accUnits trs).flatMap (sp (accUnits trs)) := rfl

/-- Move the positions of thread `i` by `+d - e`. -/
def mvE (i d e : Nat) (x : Ev) : Ev := if x.tid = i then { x with pos := x.pos + d - e } else x

/-- `mvE` on a unit with its expected bytes. -/
def mvU (i d e : Nat) (u : Ev × List Byte) : Ev × List Byte := (mvE i d e u.1, u.2)

theorem splitUnit_mv (i d e : Nat) (u : Ev × List Byte) :
    splitUnit (mvU i d e u) = (splitUnit u).map (mvU i d e) := by
  unfold mvU mvE splitUnit
  split
  · rename_i h
    simp only [List.map_map]
    refine List.map_congr_left fun y _ => ?_
    simp [h, Ev.byte, Ev.isR]
  · rename_i h
    simp only [List.map_map]
    refine List.map_congr_left fun y _ => ?_
    simp [h]

theorem tq_mv (i d f : Nat) (e : Ev) (v : Ev × List Byte) : tq e (mvU i d f v) = tq e v := by
  unfold tq mvU mvE; split <;> rfl

theorem tearAcc_mvE (i d f : Nat) (us : List (Ev × List Byte)) (e : Ev) :
    tearAcc us (mvE i d f e) = tearAcc us e := by
  unfold mvE; split <;> rfl

theorem any_map_mv (i d f : Nat) (e : Ev) (us : List (Ev × List Byte)) :
    (us.map (mvU i d f)).any (tq e) = us.any (tq e) := by
  simp only [List.any_map, Function.comp_def, tq_mv]

theorem mvU_id {i d f : Nat} {u : Ev × List Byte} (h : u.1.tid ≠ i) : mvU i d f u = u := by
  simp [mvU, mvE, h]

theorem mem_bytes' {e : Ev} {y : Nat} : y ∈ e.bytes ↔ e.addr ≤ y ∧ y < e.addr + e.size := by
  simp [Ev.bytes, List.mem_range'_1]

theorem sp_fields {us : List (Ev × List Byte)} {v u : Ev × List Byte} (h : u ∈ sp us v) :
    u.1.tid = v.1.tid ∧ u.1.pos = v.1.pos ∧ u.1.act = v.1.act ∧ u.1.locked = v.1.locked ∧
      u.1.ann = v.1.ann ∧ u.1.accAddr = v.1.accAddr ∧ u.1.accSize = v.1.accSize ∧
      v.1.addr ≤ u.1.addr ∧ u.1.addr + u.1.size ≤ v.1.addr + v.1.size := by
  unfold sp at h
  split at h
  · simp only [splitUnit, List.mem_map] at h
    obtain ⟨y, hy, rfl⟩ := h
    have := mem_bytes'.mp hy
    simp only [true_and]
    omega
  · simp only [List.mem_singleton] at h; subst h
    simp

theorem sp_UK {cs : List (Nat × Nat)} {us : List (Ev × List Byte)} {v u : Ev × List Byte}
    (hv : UK cs v) (h : u ∈ sp us v) : UK cs u := by
  intro hM
  obtain ⟨-, -, hact, -, -, ha, hs, h1, h2⟩ := sp_fields h
  have hM' : v.1.isM = true := by simp only [Ev.isM, Ev.isR, Ev.isW, ← hact] at hM ⊢; exact hM
  obtain ⟨g1, g2, g3⟩ := hv hM'
  rw [ha, hs]
  exact ⟨by omega, by omega, g3⟩

theorem sp_isM {us : List (Ev × List Byte)} {v u : Ev × List Byte} (h : u ∈ sp us v) :
    u.1.isM = v.1.isM := by
  simp only [Ev.isM, Ev.isR, Ev.isW, (sp_fields h).2.2.1]

theorem sp_isW {us : List (Ev × List Byte)} {v u : Ev × List Byte} (h : u ∈ sp us v) :
    u.1.isW = v.1.isW := by
  simp only [Ev.isW, (sp_fields h).2.2.1]

/-- With the positions of thread `i` moved, the units of `a3` start later. -/
theorem threadUnits_mv (i p q d : Nat) (as : List XAct) :
    threadUnits i (p + q + d) as = (threadUnits i (p + q) as).map (mvU i d 0) := by
  rw [threadUnits_rt i (p + q + d), threadUnits_rt i (p + q), List.map_map]
  refine List.map_congr_left fun u _ => ?_
  simp [mvU, mvE, rt, Nat.add_assoc]

theorem threadUnits_mv' (i p f g : Nat) (as : List XAct) :
    threadUnits i (p + g) as = (threadUnits i (p + f) as).map (mvU i g f) := by
  rw [threadUnits_rt i (p + g), threadUnits_rt i (p + f), List.map_map]
  refine List.map_congr_left fun u _ => ?_
  simp only [Function.comp, mvU, mvE, rt, ite_true, Prod.mk.injEq, and_true]
  congr 1; omega

theorem any_append_tq (e : Ev) (l l' : List (Ev × List Byte)) :
    (l ++ l').any (tq e) = (l.any (tq e) || l'.any (tq e)) := List.any_append

theorem flatMap_sp_self {us : List (Ev × List Byte)} :
    ∀ l : List (Ev × List Byte), (∀ v ∈ l, tearAcc us v.1 = false) → l.flatMap (sp us) = l
  | [], _ => rfl
  | v :: l, h => by
    simp only [List.flatMap_cons, sp, h v List.mem_cons_self, Bool.false_eq_true, ite_false,
      List.singleton_append]
    rw [flatMap_sp_self l fun w hw => h w (List.mem_cons_of_mem _ hw)]

theorem flatMap_sp_congr {us us' : List (Ev × List Byte)} :
    ∀ l : List (Ev × List Byte), (∀ v ∈ l, tearAcc us v.1 = tearAcc us' v.1) →
      l.flatMap (sp us) = l.flatMap (sp us')
  | [], _ => rfl
  | v :: l, h => by
    simp only [List.flatMap_cons, sp, h v List.mem_cons_self]
    rw [flatMap_sp_congr l fun w hw => h w (List.mem_cons_of_mem _ hw)]

theorem flatMap_sp_mv {us us' : List (Ev × List Byte)} (i d f : Nat) :
    ∀ l : List (Ev × List Byte), (∀ v ∈ l, tearAcc us' v.1 = tearAcc us v.1) →
      (l.map (mvU i d f)).flatMap (sp us') = (l.flatMap (sp us)).map (mvU i d f)
  | [], _ => rfl
  | v :: l, h => by
    simp only [List.map_cons, List.flatMap_cons, List.map_append]
    rw [flatMap_sp_mv i d f l fun w hw => h w (List.mem_cons_of_mem _ hw)]
    congr 1
    simp only [sp, mvU, tearAcc_mvE, h v List.mem_cons_self]
    split
    · exact splitUnit_mv i d f v
    · rfl

/-- **The units of the old and the new choice of traces.** -/
theorem units_split (trs : List XTrace) (i : Nat) (hi : i < trs.length) (t' : XTrace)
    (a1 a2 a3 b : List XAct) (h1 : (trs[i]).acts = a1 ++ a2 ++ a3) (h2 : t'.acts = a1 ++ b ++ a3)
    (cs : List (Nat × Nat)) (hcs : CellsOk cs)
    (hoth : ∀ k (hk : k < trs.length), k ≠ i → ∀ a ∈ (trs[k]).acts, ActAvoid cs a)
    (h13 : ∀ a ∈ a1 ++ a3, ActAvoid cs a)
    (h2c : ∀ a ∈ a2 ++ b, (∃ f, a.ev.kind = .fence f) ∨ (a.ev.addr, a.ev.size) ∈ cs)
    (p1 : Nat) (hp1 : p1 = (threadUnits i 0 a1).length) :
    units trs = (((UL trs).take i).flatten ++ threadUnits i 0 a1).flatMap (sp (accUnits trs)) ++
        threadUnits i p1 a2 ++
        (threadUnits i (p1 + (threadUnits i p1 a2).length) a3 ++
          ((UL trs).drop (i + 1)).flatten).flatMap (sp (accUnits trs)) ∧
      units (trs.set i t') =
        (((UL trs).take i).flatten ++ threadUnits i 0 a1).flatMap (sp (accUnits trs)) ++
        threadUnits i p1 b ++
        ((threadUnits i (p1 + (threadUnits i p1 a2).length) a3 ++
          ((UL trs).drop (i + 1)).flatten).flatMap (sp (accUnits trs))).map
          (mvU i (threadUnits i p1 b).length (threadUnits i p1 a2).length) := by
  subst hp1
  -- the names
  set Lb := ((UL trs).take i).flatten with hLb
  set La := ((UL trs).drop (i + 1)).flatten with hLa
  set p1 := (threadUnits i 0 a1).length with hp1
  set U1 := threadUnits i 0 a1
  set U2 := threadUnits i p1 a2
  set Ub := threadUnits i p1 b
  set U3 := threadUnits i (p1 + U2.length) a3
  set U3' := threadUnits i (p1 + Ub.length) a3
  have hiu : i < (UL trs).length := by rw [length_UL]; exact hi
  have hus : accUnits trs = Lb ++ (U1 ++ U2 ++ U3) ++ La := by
    show (UL trs).flatten = _
    rw [flatten_mid _ i hiu, UL_get, h1, threadUnits_append, threadUnits_append]
    simp only [List.length_append, Nat.zero_add]; rfl
  have hus' : accUnits (trs.set i t') = Lb ++ (U1 ++ Ub ++ U3') ++ La := by
    show (UL (trs.set i t')).flatten = _
    rw [UL_set, flatten_set _ i hiu, h2, threadUnits_append, threadUnits_append]
    simp only [List.length_append, Nat.zero_add]; rfl
  have h3' : U3' = U3.map (mvU i Ub.length U2.length) := threadUnits_mv' i p1 _ _ a3
  have hLa' : La.map (mvU i Ub.length U2.length) = La := by
    refine (List.map_congr_left fun u hu => ?_).trans (List.map_id La)
    obtain ⟨k, hk, hik, hu'⟩ := mem_drop_UL hu
    exact mvU_id (by rw [mem_threadUnits_tid hu']; omega)
  -- unit facts
  have hLbK : ∀ v ∈ Lb, UK cs v := by
    intro v hv
    obtain ⟨k, hk, hik, hv'⟩ := mem_take_UL hv
    exact threadUnits_all 0 _ (fun a ha p => actUnits_UK (hoth k hk (by omega) a ha) k p) v hv'
  have hLaK : ∀ v ∈ La, UK cs v := by
    intro v hv
    obtain ⟨k, hk, hik, hv'⟩ := mem_drop_UL hv
    exact threadUnits_all 0 _ (fun a ha p => actUnits_UK (hoth k hk (by omega) a ha) k p) v hv'
  have hU1K : ∀ v ∈ U1, UK cs v := threadUnits_all 0 _
    (fun a ha p => actUnits_UK (h13 a (List.mem_append_left _ ha)) i p)
  have hU3K : ∀ v ∈ U3, UK cs v := threadUnits_all _ _
    (fun a ha p => actUnits_UK (h13 a (List.mem_append_right _ ha)) i p)
  have hU3'K : ∀ v ∈ U3', UK cs v := threadUnits_all _ _
    (fun a ha p => actUnits_UK (h13 a (List.mem_append_right _ ha)) i p)
  have hU2C : ∀ v ∈ U2, UC cs v := threadUnits_all _ _
    (fun a ha p => actUnits_UC (h2c a (List.mem_append_left _ ha)) i p)
  have hUbC : ∀ v ∈ Ub, UC cs v := threadUnits_all _ _
    (fun a ha p => actUnits_UC (h2c a (List.mem_append_right _ ha)) i p)
  have noC : ∀ v, UK cs v → v.1.isM = true → ∀ l : List (Ev × List Byte), (∀ w ∈ l, UC cs w) →
      l.any (tq v.1) = false := by
    intro v hv hM l hl
    exact List.any_eq_false.mpr fun w hw => by
      rw [tq_KC (fun h => (hv h).2.2) hM (hl w hw)]; simp
  have tK : ∀ v, UK cs v → tearAcc (accUnits trs) v.1 = tearAcc (accUnits (trs.set i t')) v.1 := by
    intro v hv
    rw [hus, hus', tearAcc_eq, tearAcc_eq]
    cases hM : v.1.isM
    · rfl
    simp only [any_append_tq, h3', any_map_mv, noC v hv hM U2 hU2C, noC v hv hM Ub hUbC,
      Bool.or_false]
  have hall : ∀ v ∈ accUnits trs, UK cs v ∨ UC cs v := by
    intro v hv
    rw [hus] at hv
    simp only [List.mem_append] at hv
    rcases hv with ((h | (h | h) | h) | h)
    · exact .inl (hLbK v h)
    · exact .inl (hU1K v h)
    · exact .inr (hU2C v h)
    · exact .inl (hU3K v h)
    · exact .inl (hLaK v h)
  have hall' : ∀ v ∈ accUnits (trs.set i t'), UK cs v ∨ UC cs v := by
    intro v hv
    rw [hus'] at hv
    simp only [List.mem_append] at hv
    rcases hv with ((h | (h | h) | h) | h)
    · exact .inl (hLbK v h)
    · exact .inl (hU1K v h)
    · exact .inr (hUbC v h)
    · exact .inl (hU3'K v h)
    · exact .inl (hLaK v h)
  constructor
  · calc units trs = (accUnits trs).flatMap (sp (accUnits trs)) := rfl
      _ = (Lb ++ (U1 ++ U2 ++ U3) ++ La).flatMap (sp (accUnits trs)) :=
          congrArg (fun L => L.flatMap (sp (accUnits trs))) hus
      _ = _ := by
          simp only [List.flatMap_append, List.append_assoc]
          rw [flatMap_sp_self U2 fun v hv => tear_C hcs hall (hU2C v hv)]
  · calc units (trs.set i t') = (accUnits (trs.set i t')).flatMap (sp (accUnits (trs.set i t'))) := rfl
      _ = (Lb ++ (U1 ++ Ub ++ U3') ++ La).flatMap (sp (accUnits (trs.set i t'))) :=
          congrArg (fun L => L.flatMap (sp (accUnits (trs.set i t')))) hus'
      _ = _ := by
          rw [h3', ← hLa']
          simp only [List.flatMap_append, List.append_assoc, List.map_append]
          rw [flatMap_sp_self Ub fun v hv => tear_C hcs hall' (hUbC v hv),
            flatMap_sp_congr (us := accUnits (trs.set i t')) (us' := accUnits trs) Lb
              (fun v hv => (tK v (hLbK v hv)).symm),
            flatMap_sp_congr (us := accUnits (trs.set i t')) (us' := accUnits trs) U1
              (fun v hv => (tK v (hU1K v hv)).symm),
            flatMap_sp_mv i _ _ U3 (fun v hv => (tK v (hU3K v hv)).symm),
            flatMap_sp_mv i _ _ La (fun v hv => (tK v (hLaK v hv)).symm), hLa']

end Silmaril.Proofs.X86.Concurrency.Cir.Localize
