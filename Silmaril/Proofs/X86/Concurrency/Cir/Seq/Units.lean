module

public import Silmaril.Proofs.X86.Concurrency.Cir.Seq.Exec

/-!
# The single-threaded lift: the units of one thread

For one thread's actions (each `ActOk`), the units `units` builds:

* `uReplay_units`: replaying the units is replaying the actions (`actsReplay`): splitting a
  tearable access into byte units does not change its sequential meaning;
* `units_shape`, `units_shapeWf`: the units satisfy `Shape` and `ShapeWf` for `rmwPairs`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Seq

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Seq
open Silmaril.X86.MemoryModel.Litmus (Byte XAct XTrace dummyEv actUnits threadUnits accUnits units
  splitUnit tearAcc rmwPairs annOf)
open Silmaril.X86.MemoryModel.Axiomatic (Ev Exec Act)
open Silmaril.X86.MemEvent (Kind)

/-! ## Replay -/

theorem bytesAt_one (m : Mem) (y : Nat) : bytesAt m y 1 = [(m y).getD 0] := by
  simp [bytesAt]

theorem uReplay_actUnits (m : Mem) (i p : Nat) (a : XAct) :
    uReplay m (actUnits i p a) = actStep m a := by
  simp only [actUnits, actStep]
  rcases a.ev.kind with _ | _ | _ | k
  · simp only [uReplay, uStep]; split <;> rfl
  · rfl
  · simp only [uReplay, uStep]; split <;> rfl
  · rfl

theorem uReplay_threadUnits (m : Mem) (i : Nat) : ∀ (p : Nat) (as : List XAct),
    uReplay m (threadUnits i p as) = actsReplay m as
  | _, [] => rfl
  | p, a :: as => by
    simp only [threadUnits, uReplay_append, uReplay_actUnits, actsReplay]
    cases actStep m a with
    | none => rfl
    | some m' => exact uReplay_threadUnits m' i _ as

/-- The byte-`y` piece of a split unit. -/
def piece (u : Ev × List Byte) (y : Nat) : Ev × List Byte :=
  ({ u.1 with addr := y, size := 1, data := if u.1.act == .write then [u.1.byte y] else [] },
    if u.1.isR then [(u.2[y - u.1.addr]?).getD 0] else [])

theorem splitUnit_eq (u : Ev × List Byte) : splitUnit u = u.1.bytes.map (piece u) := rfl

theorem uReplay_pieces_read (m : Mem) (u : Ev × List Byte) (hR : u.1.act = .read) :
    ∀ ys : List Nat, uReplay m (ys.map (piece u)) =
      if ∀ y ∈ ys, (m y).getD 0 = (u.2[y - u.1.addr]?).getD 0 then some m else none
  | [] => by simp [uReplay]
  | y :: ys => by
    have hisR : u.1.isR = true := by simp [Ev.isR, hR]
    simp only [List.map_cons, uReplay, uStep, piece, hR, hisR, ite_true, bytesAt_one,
      List.cons.injEq, and_true]
    by_cases h : (m y).getD 0 = (u.2[y - u.1.addr]?).getD 0
    · simp only [h, ite_true, Option.bind_some]
      rw [uReplay_pieces_read m u hR ys]
      simp at h; simp [h]
    · simp at h; simp [h]

theorem uReplay_pieces_write (m : Mem) (u : Ev × List Byte) (hW : u.1.act = .write) :
    ∀ ys : List Nat, uReplay m (ys.map (piece u)) =
      some fun z => if z ∈ ys then some (u.1.byte z) else m z
  | [] => by simp [uReplay]
  | y :: ys => by
    simp only [List.map_cons, uReplay, uStep, piece, hW, Option.bind_some]
    rw [uReplay_pieces_write _ u hW ys]
    congr 1; funext z
    simp only [putBytes, beq_self_eq_true, ite_true, List.mem_cons]
    by_cases hz : z ∈ ys
    · simp [hz]
    · by_cases hzy : z = y
      · subst hzy; simp [hz, Ev.byte]
      · have : ¬ (y ≤ z ∧ z < y + 1) := by omega
        simp [hz, hzy, this]

theorem uReplay_pieces_fence (m : Mem) (u : Ev × List Byte) {k} (hF : u.1.act = .fence k) :
    ∀ ys : List Nat, uReplay m (ys.map (piece u)) = some m
  | [] => rfl
  | y :: ys => by
    simp only [List.map_cons, uReplay, uStep, piece, hF, Option.bind_some]
    exact uReplay_pieces_fence m u hF ys

theorem bytesAt_eq_iff (m : Mem) (a n : Nat) (l : List Byte) (hl : l.length = n) :
    bytesAt m a n = l ↔ ∀ y ∈ List.range' a n, (m y).getD 0 = (l[y - a]?).getD 0 := by
  constructor
  · rintro rfl y hy
    obtain ⟨h1, h2⟩ := List.mem_range'_1.mp hy
    obtain ⟨k, rfl⟩ : ∃ k, y = a + k := ⟨y - a, by omega⟩
    simp only [bytesAt, Nat.add_sub_cancel_left, List.getElem?_map]
    rw [List.getElem?_range' (by omega)]
    simp
  · intro h
    apply List.ext_getElem (by simp [bytesAt, hl])
    intro k hk1 hk2
    simp only [bytesAt, List.getElem_map, List.getElem_range', Nat.one_mul]
    have := h (a + k) (List.mem_range'_1.mpr (by simp [bytesAt] at hk1; omega))
    rw [this, Nat.add_sub_cancel_left, List.getElem?_eq_getElem hk2]
    rfl

/-- **Splitting does not change the sequential meaning** of a unit. -/
theorem uReplay_splitUnit (m : Mem) (u : Ev × List Byte) (hR : u.1.isR = true → u.2.length = u.1.size) :
    uReplay m (splitUnit u) = uStep m u := by
  rw [splitUnit_eq]
  rcases hact : u.1.act with _ | _ | k
  · have hisR : u.1.isR = true := by simp [Ev.isR, hact]
    rw [uReplay_pieces_read m u hact, uStep, hact]
    have key := bytesAt_eq_iff m u.1.addr u.1.size u.2 (hR hisR)
    by_cases hb : bytesAt m u.1.addr u.1.size = u.2
    · exact (ite_eq_left (key.mp hb)).trans (ite_eq_left hb).symm
    · exact (ite_eq_right (fun h => hb (key.mpr h))).trans (ite_eq_right hb).symm
  · rw [uReplay_pieces_write m u hact, uStep, hact]
    congr 1; funext z
    simp only [Ev.bytes, List.mem_range'_1, putBytes, Ev.byte]
  · rw [uReplay_pieces_fence m u hact, uStep, hact]

/-- Split the units satisfying `p`. -/
def splitBy (p : Ev → Bool) (us : List (Ev × List Byte)) : List (Ev × List Byte) :=
  us.flatMap fun u => if p u.1 then splitUnit u else [u]

theorem uReplay_splitBy (p : Ev → Bool) (m : Mem) :
    ∀ us : List (Ev × List Byte), (∀ u ∈ us, u.1.isR = true → u.2.length = u.1.size) →
      uReplay m (splitBy p us) = uReplay m us
  | [], _ => rfl
  | u :: us, h => by
    simp only [splitBy, List.flatMap_cons] at *
    rw [uReplay_append]
    have hu : uReplay m (if p u.1 then splitUnit u else [u]) = uStep m u := by
      split
      · exact uReplay_splitUnit m u (h u List.mem_cons_self)
      · simp only [uReplay]; cases uStep m u <;> rfl
    rw [hu, uReplay]
    cases uStep m u with
    | none => rfl
    | some m' => exact uReplay_splitBy p m' us fun v hv => h v (List.mem_cons_of_mem _ hv)

theorem units_eq (tr : XTrace) : units [tr] = splitBy (tearAcc (accUnits [tr])) (threadUnits 0 0 tr.acts) := by
  simp [units, splitBy, accUnits]

/-! ## Shape of the units of one action list -/

/-- The facts of one unsplit unit. -/
def UnitOk (u : Ev × List Byte) : Prop :=
  u.1.accAddr = u.1.addr ∧ u.1.accSize = u.1.size ∧
    (if u.1.isM then 0 < u.1.size ∧ (u.1.isW = true → u.1.data.length = u.1.size) ∧
        (u.1.isR = true → u.2.length = u.1.size)
      else u.1.size = 0)

/-- The order facts between two unsplit units. -/
def UQ (u v : Ev × List Byte) : Prop :=
  u.1.pos < v.1.pos ∧ (u.1.isR = true → u.1.locked = true → v.1.pos = u.1.pos + 1 →
    v.1.addr = u.1.addr ∧ v.1.size = u.1.size)

theorem actUnits_facts (i p : Nat) (a : XAct) (ha : ActOk a) :
    ∀ u ∈ actUnits i p a, u.1.tid = i ∧ p ≤ u.1.pos ∧ u.1.pos < p + (actUnits i p a).length ∧
      UnitOk u ∧ (u.1.isR = true → u.1.locked = true → a.ev.kind = .rmw ∧ u.1.pos = p) := by
  obtain ⟨hl, hk⟩ := ha
  simp only [actUnits]
  rcases hkind : a.ev.kind with _ | _ | _ | k <;> rw [hkind] at hk <;> simp only at hk
  · intro u hu
    simp only [List.mem_singleton] at hu; subst hu
    refine ⟨rfl, le_refl _, by simp, ⟨rfl, rfl, ?_⟩, fun _ h => absurd (hkind.symm.trans (hl h)) (by simp)⟩
    simp [Ev.isM, Ev.isR, Ev.isW, hk.1, hk.2]
  · intro u hu
    simp only [List.mem_singleton] at hu; subst hu
    refine ⟨rfl, le_refl _, by simp, ⟨rfl, rfl, ?_⟩, fun h _ => by simp [Ev.isR] at h⟩
    simp [Ev.isM, Ev.isR, Ev.isW, hk.1, hk.2]
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · refine ⟨rfl, by simp, by simp, ⟨rfl, rfl, ?_⟩, fun _ _ => ⟨rfl, by simp⟩⟩
      simp [Ev.isM, Ev.isR, Ev.isW, hk.1, hk.2.1]
    · refine ⟨rfl, by simp, by simp, ⟨rfl, rfl, ?_⟩, fun h _ => by simp [Ev.isR] at h⟩
      simp [Ev.isM, Ev.isR, Ev.isW, hk.1, hk.2.2]
  · intro u hu
    simp only [List.mem_singleton] at hu; subst hu
    refine ⟨rfl, le_refl _, by simp, ⟨rfl, rfl, ?_⟩, fun h _ => by simp [Ev.isR] at h⟩
    simp [Ev.isM, Ev.isR, Ev.isW]

theorem actUnits_pairwise (i p : Nat) (a : XAct) : (actUnits i p a).Pairwise UQ := by
  simp only [actUnits]
  rcases a.ev.kind with _ | _ | _ | k
  · simp
  · simp
  · simp [UQ]
  · simp

theorem threadUnits_facts (i : Nat) : ∀ (p : Nat) (as : List XAct), (∀ a ∈ as, ActOk a) →
    (∀ u ∈ threadUnits i p as, u.1.tid = i ∧ p ≤ u.1.pos ∧ UnitOk u) ∧
      (threadUnits i p as).Pairwise UQ
  | _, [], _ => by simp [threadUnits]
  | p, a :: as, h => by
    have ha := h a List.mem_cons_self
    obtain ⟨ih1, ih2⟩ := threadUnits_facts i (p + (actUnits i p a).length) as
      fun b hb => h b (List.mem_cons_of_mem _ hb)
    have hA := actUnits_facts i p a ha
    simp only [threadUnits, List.mem_append, List.pairwise_append]
    refine ⟨fun u hu => ?_, actUnits_pairwise i p a, ih2, fun u hu v hv => ?_⟩
    · rcases hu with hu | hu
      · obtain ⟨h1, h2, -, h4, -⟩ := hA u hu; exact ⟨h1, h2, h4⟩
      · obtain ⟨h1, h2, h4⟩ := ih1 u hu; exact ⟨h1, by omega, h4⟩
    · obtain ⟨-, -, hu3, -, hu5⟩ := hA u hu
      obtain ⟨-, hv2, -⟩ := ih1 v hv
      refine ⟨by omega, fun hR hL hpos => ?_⟩
      obtain ⟨hk, hp⟩ := hu5 hR hL
      have : (actUnits i p a).length = 2 := by simp [actUnits, hk]
      omega

/-! ## Shape after splitting -/

/-- The order facts between two units after splitting. -/
def UD (u v : Ev) : Prop :=
  (u.pos < v.pos ∨ (u.pos = v.pos ∧ u.act = v.act ∧ u.locked = v.locked ∧ u.ann = v.ann ∧
      u.accAddr = v.accAddr ∧ u.accSize = v.accSize ∧ ∀ y, ¬ (u.covers y = true ∧ v.covers y = true))) ∧
    (u.isR = true → u.locked = true → v.pos = u.pos + 1 → v.accAddr = u.accAddr ∧ v.accSize = u.accSize)

theorem mem_piece {u : Ev × List Byte} {q : Ev × List Byte} (h : q ∈ splitUnit u) :
    ∃ y, u.1.addr ≤ y ∧ y < u.1.addr + u.1.size ∧ q = piece u y := by
  rw [splitUnit_eq] at h
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
  obtain ⟨h1, h2⟩ := List.mem_range'_1.mp hy
  exact ⟨y, h1, h2, rfl⟩

/-- What a part of a (possibly split) unit keeps of it. -/
theorem part_facts {p : Ev → Bool} {u q : Ev × List Byte} (h : q ∈ (if p u.1 then splitUnit u else [u])) :
    q.1.tid = u.1.tid ∧ q.1.pos = u.1.pos ∧ q.1.act = u.1.act ∧ q.1.locked = u.1.locked ∧
      q.1.ann = u.1.ann ∧ q.1.accAddr = u.1.accAddr ∧ q.1.accSize = u.1.accSize ∧
      q.1.isR = u.1.isR ∧ q.1.isW = u.1.isW ∧ q.1.isM = u.1.isM := by
  split at h
  · obtain ⟨y, -, -, rfl⟩ := mem_piece h
    simp [piece, Ev.isR, Ev.isW, Ev.isM]
  · simp only [List.mem_singleton] at h; subst h; simp

theorem pieces_pairwise (u : Ev × List Byte) : (splitUnit u).Pairwise fun a b => UD a.1 b.1 := by
  rw [splitUnit_eq, List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ (List.pairwise_lt_range' (s := u.1.addr) (n := u.1.size))
  intro y z _ _ hyz
  refine ⟨.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun w hw => ?_⟩, fun _ _ h => by simp [piece] at h⟩
  simp [piece, Ev.covers] at hw
  omega

theorem splitBy_facts (p : Ev → Bool) (us : List (Ev × List Byte)) (h1 : ∀ u ∈ us, UnitOk u)
    (h2 : us.Pairwise UQ) :
    (∀ q ∈ splitBy p us, ∃ u ∈ us, q.1.tid = u.1.tid ∧
      (if q.1.isM then 0 < q.1.size ∧ q.1.accAddr ≤ q.1.addr ∧
          q.1.addr + q.1.size ≤ q.1.accAddr + q.1.accSize ∧ (q.1.isW = true → q.1.data.length = q.1.size)
        else q.1.size = 0)) ∧
      (splitBy p us).Pairwise fun a b => UD a.1 b.1 := by
  refine ⟨fun q hq => ?_, ?_⟩
  · simp only [splitBy, List.mem_flatMap] at hq
    obtain ⟨u, hu, hq⟩ := hq
    obtain ⟨hA, hS, hk⟩ := h1 u hu
    refine ⟨u, hu, (part_facts hq).1, ?_⟩
    split at hq
    · obtain ⟨y, hy1, hy2, rfl⟩ := mem_piece hq
      by_cases hM : u.1.isM = true
      · rw [ite_eq_left (by simpa [piece, Ev.isM, Ev.isR, Ev.isW] using hM)]
        refine ⟨by simp [piece], by simp [piece]; omega, by simp [piece]; omega, fun hw => ?_⟩
        have : u.1.act = .write := by simpa [piece, Ev.isW] using hw
        simp [piece, this]
      · rw [ite_eq_right hM] at hk
        omega
    · simp only [List.mem_singleton] at hq; subst hq
      split
      · rename_i hM; simp only [hM, ite_true] at hk
        exact ⟨hk.1, by omega, by omega, hk.2.1⟩
      · rename_i hM; rw [ite_eq_right hM] at hk; exact hk
  · simp only [splitBy]
    rw [List.pairwise_flatMap]
    refine ⟨fun u _ => ?_, ?_⟩
    · split
      · exact pieces_pairwise u
      · simp
    · refine List.Pairwise.imp_of_mem ?_ h2
      intro u v hu hv ⟨hlt, hrmw⟩ a ha b hb
      have fa := part_facts ha
      have fb := part_facts hb
      refine ⟨.inl (by rw [fa.2.1, fb.2.1]; exact hlt), fun hR hL hpos => ?_⟩
      rw [fa.2.2.2.2.2.2.2.1] at hR
      rw [fa.2.2.2.1] at hL
      rw [fa.2.1, fb.2.1] at hpos
      obtain ⟨e1, e2⟩ := hrmw hR hL hpos
      obtain ⟨ua, us', -⟩ := h1 u hu
      obtain ⟨va, vs, -⟩ := h1 v hv
      rw [fa.2.2.2.2.2.1, fb.2.2.2.2.2.1, fa.2.2.2.2.2.2.1, fb.2.2.2.2.2.2.1, ua, us', va, vs, e1, e2]
      exact ⟨rfl, rfl⟩

/-! ## The units of one thread -/

theorem mem_rmwPairs {evs : List Ev} {q : Nat × Nat} (h : q ∈ rmwPairs evs) :
    ∃ (h1 : q.1 < evs.length) (h2 : q.2 < evs.length), evs[q.1].isR = true ∧
      evs[q.1].locked = true ∧ evs[q.2].isW = true ∧ evs[q.2].locked = true ∧
      evs[q.2].pos = evs[q.1].pos + 1 ∧ evs[q.1].addr = evs[q.2].addr ∧
      evs[q.1].size = evs[q.2].size := by
  simp only [rmwPairs, List.mem_flatMap] at h
  obtain ⟨qa, hqa, hq⟩ := h
  by_cases hA : (qa.1.isR && qa.1.locked) = true
  · rw [ite_eq_left hA, List.mem_filterMap] at hq
    obtain ⟨qb, hqb, hq⟩ := hq
    simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hq
    obtain ⟨hB, rfl⟩ := hq
    · obtain ⟨ha1, ha2⟩ := List.mem_zipIdx' (x := qa.1) (i := qa.2) hqa
      obtain ⟨hb1, hb2⟩ := List.mem_zipIdx' (x := qb.1) (i := qb.2) hqb
      refine ⟨ha1, hb1, ?_⟩
      rw [← ha2, ← hb2]
      simp only [Bool.and_eq_true, beq_iff_eq] at hA hB
      exact ⟨hA.1, hA.2, hB.1.1.1.1.1, hB.1.1.1.1.2, hB.1.1.2, hB.1.2, hB.2⟩
  · rw [ite_eq_right hA] at hq; simp at hq

/-- The units of one thread satisfy `Shape` and `ShapeWf`. -/
theorem units_shape (tr : XTrace) (hok : ∀ a ∈ tr.acts, ActOk a) :
    Shape ((units [tr]).map Prod.fst) ∧
      ShapeWf ((units [tr]).map Prod.fst) (rmwPairs ((units [tr]).map Prod.fst)) := by
  obtain ⟨f1, f2⟩ := threadUnits_facts 0 0 tr.acts hok
  obtain ⟨g1, g2⟩ := splitBy_facts (tearAcc (accUnits [tr])) _ (fun u hu => (f1 u hu).2.2) f2
  rw [← units_eq] at g1 g2
  set evs := (units [tr]).map Prod.fst with hevs
  have hP : evs.Pairwise UD := by rw [hevs, List.pairwise_map]; exact g2
  have hPg := List.pairwise_iff_getElem.mp hP
  have tid0 : ∀ e ∈ evs, e.tid = 0 := by
    intro e he
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
    obtain ⟨u, hu, ht, -⟩ := g1 q hq
    rw [ht, (f1 u hu).1]
  refine ⟨⟨tid0, fun i j hi hj hij => ?_, fun i j hi hj hij hpos y hy => ?_⟩, ⟨fun i j hi hj hpos => ?_,
    fun e he => ?_, fun q hq => ?_⟩⟩
  · rcases Nat.lt_or_eq_of_le hij with h | rfl
    · rcases (hPg i j hi hj h).1 with h | h
      · exact le_of_lt h
      · exact le_of_eq h.1
    · exact le_refl _
  · rcases Nat.lt_or_gt_of_ne hij with h | h
    · rcases (hPg i j hi hj h).1 with h' | h'
      · omega
      · exact h'.2.2.2.2.2.2 y hy
    · rcases (hPg j i hj hi h).1 with h' | h'
      · omega
      · exact h'.2.2.2.2.2.2 y ⟨hy.2, hy.1⟩
  · rcases Nat.lt_trichotomy i j with h | rfl | h
    · rcases (hPg i j hi hj h).1 with h' | h'
      · omega
      · exact ⟨h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2.1, h'.2.2.2.2.2.1⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · rcases (hPg j i hj hi h).1 with h' | h'
      · omega
      · exact ⟨h'.2.1.symm, h'.2.2.1.symm, h'.2.2.2.1.symm, h'.2.2.2.2.1.symm, h'.2.2.2.2.2.1.symm⟩
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
    obtain ⟨u, -, -, h⟩ := g1 q hq
    split at h
    · rename_i hM; simp only [hM, ite_true]; exact h
    · rename_i hM; simp only [hM]; exact h
  · obtain ⟨h1, h2, hR, hL1, hW, hL2, hpos, ha, hs⟩ := mem_rmwPairs hq
    have hlt : q.1 < q.2 := by
      rcases Nat.lt_or_ge q.1 q.2 with h | h
      · exact h
      · exfalso
        rcases Nat.lt_or_eq_of_le h with h | h
        · rcases (hPg q.2 q.1 h2 h1 h).1 with h' | h' <;> omega
        · simp only [h] at hpos; omega
    obtain ⟨e1, e2⟩ := (hPg q.1 q.2 h1 h2 hlt).2 hR hL1 hpos
    exact ⟨h1, h2, hR, hW, by omega, hL1, hL2, e1.symm, e2.symm⟩

/-- **Replaying the units of one thread is replaying its actions.** -/
theorem uReplay_units (tr : XTrace) (hok : ∀ a ∈ tr.acts, ActOk a) (m : Mem) :
    uReplay m (units [tr]) = actsReplay m tr.acts := by
  obtain ⟨f1, -⟩ := threadUnits_facts 0 0 tr.acts hok
  rw [units_eq, uReplay_splitBy _ _ _ ?_, uReplay_threadUnits]
  intro u hu hR
  obtain ⟨-, -, -, -, hk⟩ := f1 u hu
  have hM : u.1.isM = true := by simp [Ev.isM, hR]
  simp only [hM, ite_true] at hk
  exact hk.2.2 hR

end Silmaril.Proofs.X86.Concurrency.Cir.Seq
