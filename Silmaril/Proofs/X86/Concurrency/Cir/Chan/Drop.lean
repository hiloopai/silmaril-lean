module

public import Silmaril.X86.MemoryModel.Litmus.Models.Defs

/-!
# Dropping read units from a candidate execution

A candidate execution whose
units are `A ++ B ++ C`, where the units of `B` are plain (unlocked) reads, each with a
**twin** in `A ++ C` (a memory unit of the same access footprint), restricts to a candidate
over `A ++ C` (positions renumbered by `f`, monotonically within each thread): `dropExec`.

* `dropExec_wf`: it is well-formed;
* `dropExec_readsOk`: every kept read returns the bytes it returned before;
* `dropExec_sc`, `dropExec_tso`, `dropExec_xl`: it is consistent under SC, TSO and XL when the
  original is: every relation of the models on the kept units is contained in the relation
  on their images (`Hom`), and `tearable` is unchanged because a dropped unit's twin is a
  witness of the same tearing;
* `dropExec_written`, `dropExec_finalByte`: the written bytes and their coherence-last values
  are unchanged (no write is dropped).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Chan.Drop

open Silmaril.X86.MemoryModel.Axiomatic (Ev Exec BRel before)
open Silmaril.X86.MemoryModel.Litmus (rmwPairs writtenByte units Test ReadsOk finalAx finalOf Model XTrace Byte)
open Relation (TransGen)

/-! ## Index maps -/

/-- The index in `A ++ B ++ C` of index `i` of `A ++ C` (`a = |A|`, `b = |B|`). -/
def eN (a b i : Nat) : Nat := if i < a then i else i + b

/-- The inverse of `eN` (`none` on `B`). -/
def preN (a b k : Nat) : Option Nat :=
  if k < a then some k else if k < a + b then none else some (k - b)

theorem preN_eq_some {a b k w : Nat} : preN a b k = some w ↔ k = eN a b w := by
  unfold preN eN
  by_cases h1 : k < a <;> by_cases h2 : k < a + b <;> by_cases h3 : w < a <;>
    simp [h1, h2, h3] <;> omega

theorem preN_eN (a b w : Nat) : preN a b (eN a b w) = some w := preN_eq_some.2 rfl

theorem eN_inj {a b i j : Nat} (h : eN a b i = eN a b j) : i = j := by
  unfold eN at h; split_ifs at h <;> omega

theorem preN_none {a b k : Nat} : preN a b k = none ↔ a ≤ k ∧ k < a + b := by
  unfold preN; split_ifs <;> simp <;> omega

theorem mem_filterMap_preN {a b : Nat} {l : List Nat} {w : Nat} :
    w ∈ l.filterMap (preN a b) ↔ eN a b w ∈ l := by
  simp only [List.mem_filterMap, preN_eq_some, exists_eq_right]

theorem before_filterMap {a b : Nat} :
    ∀ {l : List Nat} {u v : Nat}, before (l.filterMap (preN a b)) u v = true →
      before l (eN a b u) (eN a b v) = true
  | [], _, _, h => by simp [before] at h
  | c :: l, u, v, h => by
    rw [List.filterMap_cons] at h
    cases hc : preN a b c with
    | none =>
      rw [hc] at h
      have hne : c ≠ eN a b u := fun he => by rw [he, preN_eN] at hc; cases hc
      simp only [before, beq_iff_eq, hne, ite_false]
      exact before_filterMap h
    | some c' =>
      rw [hc] at h
      have hce := preN_eq_some.1 hc
      simp only [before, beq_iff_eq] at h ⊢
      by_cases hcu : c' = u
      · subst hcu
        simp only [ite_true, List.contains_eq_mem, decide_eq_true_eq] at h
        simp only [hce, ite_true, List.contains_eq_mem, decide_eq_true_eq]
        exact mem_filterMap_preN.1 h
      · simp only [hcu, ite_false] at h
        have : c ≠ eN a b u := fun he => hcu (eN_inj (hce.symm.trans he))
        simp only [this, ite_false]
        exact before_filterMap h

theorem nodup_filterMap_preN {a b : Nat} {l : List Nat} (h : l.Nodup) :
    (l.filterMap (preN a b)).Nodup :=
  h.filterMap fun k k' w h1 h2 => by
    rw [Option.mem_def, preN_eq_some] at h1 h2
    rw [h1, h2]

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

/-! ## The restricted execution -/

/-- Renumber the position of a unit. -/
def rp (f : Ev → Nat) (u : Ev) : Ev := { u with pos := f u }

/-- **The execution over the kept units** `evs'` (the images of `A ++ C`): `rf` and `co` are
those of `x` read back through the index map. -/
def dropExec (x : Exec) (a b : Nat) (evs' : List Ev) : Exec where
  evs := evs'
  rf := fun r y => (x.rf (eN a b r) y).bind (preN a b)
  co := fun y => (x.co y).filterMap (preN a b)
  rmw := rmwPairs evs'

/-- What the restriction needs of the dropped units `B` and the renumbering `f`. -/
structure Hyp (A B C : List Ev) (f : Ev → Nat) : Prop where
  /-- The renumbering keeps program order between kept units of one thread. -/
  ord : ∀ u ∈ A ++ C, ∀ v ∈ A ++ C, u.tid = v.tid → (f u < f v ↔ u.pos < v.pos)
  /-- Dropped units are unlocked reads with a kept twin of the same access footprint. -/
  drop : ∀ d ∈ B, d.isR = true ∧ d.locked = false ∧
    ∃ w ∈ A ++ C, w.isM = true ∧ w.accAddr = d.accAddr ∧ w.accSize = d.accSize
  /-- A kept locked read has a kept unit of its thread at the next position (its write half). -/
  succ : ∀ u ∈ A ++ C, u.isR = true → u.locked = true →
    ∃ w ∈ A ++ C, w.tid = u.tid ∧ w.pos = u.pos + 1


@[simp] theorem rp_tid (f : Ev → Nat) (u : Ev) : (rp f u).tid = u.tid := rfl
@[simp] theorem rp_pos (f : Ev → Nat) (u : Ev) : (rp f u).pos = f u := rfl
@[simp] theorem rp_act (f : Ev → Nat) (u : Ev) : (rp f u).act = u.act := rfl
@[simp] theorem rp_addr (f : Ev → Nat) (u : Ev) : (rp f u).addr = u.addr := rfl
@[simp] theorem rp_size (f : Ev → Nat) (u : Ev) : (rp f u).size = u.size := rfl
@[simp] theorem rp_accAddr (f : Ev → Nat) (u : Ev) : (rp f u).accAddr = u.accAddr := rfl
@[simp] theorem rp_accSize (f : Ev → Nat) (u : Ev) : (rp f u).accSize = u.accSize := rfl
@[simp] theorem rp_locked (f : Ev → Nat) (u : Ev) : (rp f u).locked = u.locked := rfl
@[simp] theorem rp_ann (f : Ev → Nat) (u : Ev) : (rp f u).ann = u.ann := rfl
@[simp] theorem rp_data (f : Ev → Nat) (u : Ev) : (rp f u).data = u.data := rfl
@[simp] theorem rp_isR (f : Ev → Nat) (u : Ev) : (rp f u).isR = u.isR := rfl
@[simp] theorem rp_isW (f : Ev → Nat) (u : Ev) : (rp f u).isW = u.isW := rfl
@[simp] theorem rp_isM (f : Ev → Nat) (u : Ev) : (rp f u).isM = u.isM := rfl
@[simp] theorem rp_isA (f : Ev → Nat) (u : Ev) : (rp f u).isA = u.isA := rfl
@[simp] theorem rp_weak (f : Ev → Nat) (u : Ev) : (rp f u).weak = u.weak := rfl
@[simp] theorem rp_isFence (f : Ev → Nat) (u : Ev) k : (rp f u).isFence k = u.isFence k := rfl
@[simp] theorem rp_covers' (f : Ev → Nat) (u : Ev) : (rp f u).covers = u.covers := rfl
@[simp] theorem rp_covers (f : Ev → Nat) (u : Ev) (y : Nat) : (rp f u).covers y = u.covers y := rfl
@[simp] theorem rp_bytes (f : Ev → Nat) (u : Ev) : (rp f u).bytes = u.bytes := rfl
@[simp] theorem rp_byte (f : Ev → Nat) (u : Ev) (y : Nat) : (rp f u).byte y = u.byte y := rfl
@[simp] theorem rp_singleCopy (f : Ev → Nat) (u : Ev) : (rp f u).singleCopy = u.singleCopy := rfl
@[simp] theorem rp_accOverlap (f : Ev → Nat) (u v : Ev) : (rp f u).accOverlap v = u.accOverlap v := rfl
@[simp] theorem accOverlap_rp (f : Ev → Nat) (u v : Ev) : u.accOverlap (rp f v) = u.accOverlap v := rfl

/-- The restriction of `x` (units `A ++ B ++ C`) to `A ++ C`, renumbered by `f`. -/
def dx (x : Exec) (A B C : List Ev) (f : Ev → Nat) : Exec :=
  dropExec x A.length B.length ((A ++ C).map (rp f))

/-- A morphism of relations along an index map. -/
def Hom {n m : Nat} (E : Fin n → Fin m) (R' : BRel n) (R : BRel m) : Prop :=
  ∀ i j, R' i j = true → R (E i) (E j) = true

namespace Hom
variable {n m : Nat} {E : Fin n → Fin m}

theorem union {R₁ R₂ : BRel n} {S₁ S₂ : BRel m} (h₁ : Hom E R₁ S₁) (h₂ : Hom E R₂ S₂) :
    Hom E (R₁.union R₂) (S₁.union S₂) := by
  intro i j h
  simp only [BRel.union, Bool.or_eq_true] at h ⊢
  exact h.elim (fun h => Or.inl (h₁ _ _ h)) (fun h => Or.inr (h₂ _ _ h))

theorem inter {R₁ R₂ : BRel n} {S₁ S₂ : BRel m} (h₁ : Hom E R₁ S₁) (h₂ : Hom E R₂ S₂) :
    Hom E (R₁.inter R₂) (S₁.inter S₂) := by
  intro i j h
  simp only [BRel.inter, Bool.and_eq_true] at h ⊢
  exact ⟨h₁ _ _ h.1, h₂ _ _ h.2⟩

theorem seq {R₁ R₂ : BRel n} {S₁ S₂ : BRel m} (h₁ : Hom E R₁ S₁) (h₂ : Hom E R₂ S₂) :
    Hom E (R₁.seq R₂) (S₁.seq S₂) := by
  intro i j h
  simp only [BRel.seq, List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true] at h ⊢
  obtain ⟨c, h1, h2⟩ := h
  exact ⟨E c, h₁ _ _ h1, h₂ _ _ h2⟩

theorem acyclic {R' : BRel n} {R : BRel m} (h : Hom E R' R) (hR : BRel.Acyclic R) :
    BRel.Acyclic R' := by
  intro a ha
  apply hR (E a)
  have key : ∀ b c, TransGen R'.Holds b c → TransGen R.Holds (E b) (E c) := by
    intro b c hbc
    induction hbc with
    | single h' => exact TransGen.single (h _ _ h')
    | tail _ h' ih => exact ih.tail (h _ _ h')
  exact key a a ha

end Hom

section
variable {x : Exec} {A B C : List Ev} {f : Ev → Nat}

theorem dx_n : (dx x A B C f).n = A.length + C.length := by
  simp [dx, dropExec, Exec.n]

theorem x_n (hx : x.evs = A ++ B ++ C) : x.n = A.length + B.length + C.length := by
  simp [Exec.n, hx]; omega

theorem lt_AC (i : Fin (dx x A B C f).n) : i.val < (A ++ C).length := by
  have h := i.2
  have h2 : (dx x A B C f).n = A.length + C.length := dx_n
  simp only [List.length_append]; omega

theorem eN_lt (hx : x.evs = A ++ B ++ C) {i : Nat} (hi : i < (dx x A B C f).n) :
    eN A.length B.length i < x.n := by
  rw [dx_n] at hi; rw [x_n hx]; unfold eN; split_ifs <;> omega

/-- The index map. -/
def E (hx : x.evs = A ++ B ++ C) (i : Fin (dx x A B C f).n) : Fin x.n :=
  ⟨eN A.length B.length i.val, eN_lt hx i.2⟩

theorem getElem_eN (i : Nat) (hi : i < (A ++ C).length) (h : eN A.length B.length i < (A ++ B ++ C).length) :
    (A ++ B ++ C)[eN A.length B.length i] = (A ++ C)[i] := by
  simp only [List.length_append] at hi h
  by_cases hia : i < A.length
  · have he : eN A.length B.length i = i := by simp [eN, hia]
    simp only [he]
    rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by omega),
      List.getElem_append_left (by omega)]
  · have he : eN A.length B.length i = i + B.length := by simp [eN, hia]
    simp only [he]
    rw [List.getElem_append_right (by simp; omega), List.getElem_append_right (by omega)]
    simp only [List.length_append]
    congr 1; omega

theorem ev_x (hx : x.evs = A ++ B ++ C) (k : Fin x.n) :
    x.ev k = (A ++ B ++ C)[k.val]'(by rw [← hx]; exact k.2) := by
  simp only [Exec.ev]
  exact List.getElem_of_eq hx _

theorem ev_dx (i : Fin (dx x A B C f).n) :
    (dx x A B C f).ev i = rp f ((A ++ C)[i.val]'(lt_AC i)) := by
  show ((A ++ C).map (rp f))[i.val] = _
  exact List.getElem_map ..

theorem ev_E (hx : x.evs = A ++ B ++ C) (i : Fin (dx x A B C f).n) :
    (dx x A B C f).ev i = rp f (x.ev (E hx i)) := by
  rw [ev_dx, ev_x hx]
  simp only [E]
  rw [getElem_eN]

theorem ev_E_mem (hx : x.evs = A ++ B ++ C) (i : Fin (dx x A B C f).n) :
    x.ev (E hx i) ∈ A ++ C := by
  have := ev_E (f := f) hx i
  rw [ev_dx] at this
  have h2 : x.ev (E hx i) = (A ++ C)[i.val]'(lt_AC i) := by
    rw [ev_x hx]; simp only [E]; rw [getElem_eN]
  rw [h2]; exact List.getElem_mem _

@[simp] theorem E_val (hx : x.evs = A ++ B ++ C) (i : Fin (dx x A B C f).n) :
    (E hx i).val = eN A.length B.length i.val := rfl

/-- Every unit of `x` is an image or in `B`. -/
theorem ev_cases (hx : x.evs = A ++ B ++ C) (k : Fin x.n) :
    (∃ i, E (f := f) hx i = k) ∨ x.ev k ∈ B := by
  have hk := k.2
  have hn := x_n hx
  by_cases h1 : k.val < A.length
  · left
    refine ⟨⟨k.val, by rw [dx_n]; omega⟩, ?_⟩
    ext; simp [E, eN, h1]
  · by_cases h2 : k.val < A.length + B.length
    · right
      rw [ev_x hx, List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
      exact List.getElem_mem _
    · left
      refine ⟨⟨k.val - B.length, by rw [dx_n]; omega⟩, ?_⟩
      ext; simp only [E, eN]; split_ifs <;> omega

/-- A unit of `A ++ C` is an image. -/
theorem exists_of_mem (hx : x.evs = A ++ B ++ C) {w : Ev} (hw : w ∈ A ++ C) :
    ∃ i, (dx x A B C f).ev i = rp f w ∧ x.ev (E hx i) = w := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
  have hi' : i < (dx x A B C f).n := by rw [dx_n]; simpa using hi
  refine ⟨⟨i, hi'⟩, by rw [ev_dx], ?_⟩
  rw [ev_x hx]; simp only [E]; rw [getElem_eN]

@[simp] theorem dx_rf (r yb : Nat) :
    (dx x A B C f).rf r yb = (x.rf (eN A.length B.length r) yb).bind (preN A.length B.length) := rfl
@[simp] theorem dx_co (yb : Nat) :
    (dx x A B C f).co yb = (x.co yb).filterMap (preN A.length B.length) := rfl
theorem dx_rmw : (dx x A B C f).rmw = rmwPairs (dx x A B C f).evs := rfl
theorem dx_evs : (dx x A B C f).evs = (A ++ C).map (rp f) := rfl

theorem W_ne_R {e : Ev} (hW : e.isW = true) (hR : e.isR = true) : False := by
  simp only [Ev.isW, Ev.isR, beq_iff_eq] at hW hR; rw [hW] at hR; cases hR

/-- A write of `x` is an image. -/
theorem write_image (hx : x.evs = A ++ B ++ C) (H : Hyp A B C f) (k : Fin x.n)
    (hW : (x.ev k).isW = true) : ∃ i, E (f := f) hx i = k := by
  rcases ev_cases (f := f) hx k with h | h
  · exact h
  · exact (W_ne_R hW (H.drop _ h).1).elim

theorem evN_eq' (x : Exec) {i : Nat} (h : i < x.n) : x.evN i = x.ev ⟨i, h⟩ := by
  simp [Exec.evN, Exec.ev, List.getD_eq_getElem?_getD, h]

theorem covers_of_mem {e : Ev} {y : Nat} (h : y ∈ e.bytes) : e.covers y = true := by
  simp only [Ev.bytes, List.mem_range'_1] at h
  simp only [Ev.covers, Bool.and_eq_true, decide_eq_true_eq]; omega

theorem mem_of_covers {e : Ev} {y : Nat} (h : e.covers y = true) : y ∈ e.bytes := by
  simp only [Ev.covers, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [Ev.bytes, List.mem_range'_1]; omega

/-- `Wf` on `rf`. -/
theorem wf_rf {x : Exec} (h : x.Wf = true) (r : Fin x.n) (hr : (x.ev r).isR = true) {y : Nat}
    (hy : (x.ev r).covers y = true) {w : Nat} (hw : x.rf r.val y = some w) :
    ∃ h : w < x.n, (x.ev ⟨w, h⟩).isW = true ∧ (x.ev ⟨w, h⟩).covers y = true := by
  simp only [Exec.Wf, Bool.and_eq_true, List.all_eq_true] at h
  have := h.1.1.1.1 r (List.mem_finRange r)
  simp only [hr, Bool.not_true, Bool.false_or, List.all_eq_true] at this
  have := this y (mem_of_covers hy)
  rw [hw] at this
  simp only [Exec.valid, Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨⟨hv, hW⟩, hC⟩ := this
  exact ⟨hv, by rwa [← evN_eq'], by rwa [← evN_eq']⟩

theorem getLast?_filterMap {g : Nat → Option Nat} {l : List Nat} (h : ∀ k ∈ l, (g k).isSome = true) :
    (l.filterMap g).getLast? = l.getLast?.bind g := by
  rcases List.eq_nil_or_concat' l with rfl | ⟨L, k, rfl⟩
  · rfl
  · have hk := h k (by simp)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hk
    rw [List.filterMap_append]
    simp [hv]

section rel

-- Some lemmas below do not need `H`; they keep it so that every lemma of the section has the
-- same arguments.
set_option linter.unusedSectionVars false
variable (hx : x.evs = A ++ B ++ C) (H : Hyp A B C f)
include hx H

theorem pos_iff (i j : Fin (dx x A B C f).n) (ht : (x.ev (E hx i)).tid = (x.ev (E hx j)).tid) :
    f (x.ev (E hx i)) < f (x.ev (E hx j)) ↔ (x.ev (E hx i)).pos < (x.ev (E hx j)).pos :=
  H.ord _ (ev_E_mem hx i) _ (ev_E_mem hx j) ht

theorem pos_eq_iff (i j : Fin (dx x A B C f).n) (ht : (x.ev (E hx i)).tid = (x.ev (E hx j)).tid) :
    f (x.ev (E hx i)) = f (x.ev (E hx j)) ↔ (x.ev (E hx i)).pos = (x.ev (E hx j)).pos := by
  have h1 := pos_iff hx H i j ht
  have h2 := pos_iff hx H j i ht.symm
  omega

theorem hom_po : Hom (E hx) (dx x A B C f).po x.po := by
  intro i j h
  simp only [Exec.po, ev_E hx, rp_tid, rp_pos, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h ⊢
  exact ⟨h.1, (pos_iff hx H i j h.1).1 h.2⟩

theorem hom_sm : Hom (E hx) (dx x A B C f).sm x.sm := by
  intro i j h
  simp only [Exec.sm, ev_E hx, rp_tid, rp_pos, Bool.and_eq_true, beq_iff_eq] at h ⊢
  exact ⟨h.1, (pos_eq_iff hx H i j h.1).1 h.2⟩

theorem hom_ext : Hom (E hx) (dx x A B C f).ext x.ext := by
  intro i j h
  simpa only [Exec.ext, ev_E hx, rp_tid] using h

theorem hom_loc : Hom (E hx) (dx x A B C f).loc x.loc := by
  intro i j h
  simpa only [Exec.loc, ev_E hx, rp_isM, rp_bytes, rp_covers'] using h

theorem hom_rfR : Hom (E hx) (dx x A B C f).rfR x.rfR := by
  intro i j h
  simp only [Exec.rfR, ev_E hx, rp_isW, rp_isR, rp_bytes, rp_covers, dx_rf, Bool.and_eq_true,
    List.any_eq_true, beq_iff_eq, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨⟨hW, hR⟩, yb, hyb, ⟨k, hk, hp⟩, hc⟩ := h
  refine ⟨⟨hW, hR⟩, yb, hyb, ?_, hc⟩
  rw [E_val, hk, preN_eq_some.1 hp]; rfl

theorem hom_coR : Hom (E hx) (dx x A B C f).coR x.coR := by
  intro i j h
  simp only [Exec.coR, ev_E hx, rp_isW, rp_bytes, rp_covers, dx_co, Bool.and_eq_true,
    List.any_eq_true] at h ⊢
  obtain ⟨⟨hW, hW'⟩, yb, hyb, hc, hb⟩ := h
  exact ⟨⟨hW, hW'⟩, yb, hyb, hc, before_filterMap hb⟩

theorem rf_some (hwf : x.Wf = true) (r : Fin (dx x A B C f).n) (hr : (x.ev (E hx r)).isR = true)
    {yb : Nat} (hy : (x.ev (E hx r)).covers yb = true) :
    x.rf (E hx r).val yb = ((dx x A B C f).rf r.val yb).map (eN A.length B.length) := by
  rw [dx_rf]
  cases hk : x.rf (eN A.length B.length r.val) yb with
  | none => rw [E_val, hk]; rfl
  | some k =>
    obtain ⟨hkn, hW, -⟩ := wf_rf hwf (E hx r) hr hy hk
    obtain ⟨w, hw⟩ := write_image hx H ⟨k, hkn⟩ hW
    have hkw : k = eN A.length B.length w.val := by
      have := congrArg Fin.val hw; rw [E_val] at this; exact this.symm
    rw [E_val, hk, Option.bind_some, hkw, preN_eN]; rfl

theorem hom_frR (hwf : x.Wf = true) : Hom (E hx) (dx x A B C f).frR x.frR := by
  intro i j h
  simp only [Exec.frR, ev_E hx, rp_isW, rp_isR, rp_bytes, rp_covers, Bool.and_eq_true,
    List.any_eq_true] at h ⊢
  obtain ⟨⟨hR, hW⟩, yb, hyb, hc, hm⟩ := h
  refine ⟨⟨hR, hW⟩, yb, hyb, hc, ?_⟩
  rw [rf_some hx H hwf i hR (covers_of_mem hyb)]
  cases hv : (dx x A B C f).rf i.val yb with
  | none => rfl
  | some v =>
    rw [hv] at hm
    simp only [Option.map_some, dx_co] at hm ⊢
    exact before_filterMap hm

theorem hom_com (hwf : x.Wf = true) : Hom (E hx) (dx x A B C f).com x.com :=
  (hom_rfR hx H).union ((hom_coR hx H).union (hom_frR hx H hwf))

theorem hom_fencerel (k) : Hom (E hx) ((dx x A B C f).fencerel k) (x.fencerel k) := by
  intro i j h
  simp only [Exec.fencerel, List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true] at h ⊢
  obtain ⟨g, ⟨hf, h1⟩, h2⟩ := h
  rw [ev_E hx, rp_isFence] at hf
  exact ⟨E hx g, ⟨hf, hom_po hx H _ _ h1⟩, hom_po hx H _ _ h2⟩

theorem hom_rmwR (hrmw : x.rmw = rmwPairs x.evs) : Hom (E hx) (dx x A B C f).rmwR x.rmwR := by
  intro i j h
  simp only [Exec.rmwR, List.contains_eq_mem, decide_eq_true_eq, dx_rmw] at h ⊢
  rw [mem_rmwPairs_iff] at h
  obtain ⟨hi, hj, h1, h2⟩ := h
  have ei : (dx x A B C f).evs[i.val] = rp f (x.ev (E hx i)) := ev_E hx i
  have ej : (dx x A B C f).evs[j.val] = rp f (x.ev (E hx j)) := ev_E hx j
  rw [ei] at h1 h2; rw [ej] at h2
  simp only [rp_isR, rp_locked, rp_isW, rp_tid, rp_pos, rp_addr, rp_size, Bool.and_eq_true,
    beq_iff_eq] at h1 h2
  obtain ⟨⟨⟨⟨⟨hW, hL⟩, ht⟩, hp⟩, ha⟩, hs⟩ := h2
  set u := x.ev (E hx i)
  set v := x.ev (E hx j)
  have hu : u ∈ A ++ C := ev_E_mem hx i
  have hv : v ∈ A ++ C := ev_E_mem hx j
  obtain ⟨w, hw, hwt, hwp⟩ := H.succ u hu h1.1 h1.2
  have huv := (H.ord u hu v hv ht).1 (by omega)
  have huw := (H.ord u hu w hw hwt.symm).2 (by omega)
  have hvw : ¬ w.pos < v.pos := fun hlt =>
    absurd ((H.ord w hw v hv (hwt.trans ht)).2 hlt) (by omega)
  rw [hrmw, mem_rmwPairs_iff]
  refine ⟨(E hx i).2, (E hx j).2, ?_, ?_⟩
  · show (u.isR && u.locked) = true
    simp [h1.1, h1.2]
  · show (v.isW && v.locked && u.tid == v.tid && v.pos == u.pos + 1 && u.addr == v.addr &&
      u.size == v.size) = true
    simp only [hW, hL, ht, ha, hs, Bool.and_eq_true, beq_iff_eq, and_true, true_and]
    omega

theorem tear_E (i : Fin (dx x A B C f).n) (h : x.tearable (E hx i) = true) :
    (dx x A B C f).tearable i = true := by
  simp only [Exec.tearable, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.any_eq_true, List.mem_finRange, true_and] at h ⊢
  rw [ev_E hx i]
  simp only [rp_isM, rp_singleCopy, rp_accOverlap, rp_accAddr, rp_accSize]
  refine ⟨h.1, ?_⟩
  rcases h.2 with h2 | ⟨b, hb⟩
  · exact Or.inl h2
  · right
    rcases ev_cases (f := f) hx b with ⟨b', rfl⟩ | hB
    · exact ⟨b', by rw [ev_E hx b']; simpa only [rp_isM, accOverlap_rp, rp_accAddr, rp_accSize] using hb⟩
    · obtain ⟨-, -, w, hw, hwM, hwa, hws⟩ := H.drop _ hB
      obtain ⟨i', hi', -⟩ := exists_of_mem (f := f) hx hw
      refine ⟨i', ?_⟩
      rw [hi']
      simp only [rp_isM, rp_accAddr, rp_accSize, hwM, hwa, hws, true_and,
        Ev.accOverlap] at hb ⊢
      exact ⟨hb.1.2, hb.2⟩

theorem hom_smT : Hom (E hx) (dx x A B C f).smT x.smT := by
  intro i j h
  simp only [Exec.smT, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
  rcases h with rfl | ⟨h1, h2⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨hom_sm hx H _ _ h1, ?_⟩
    cases ht : x.tearable (E hx i)
    · rfl
    · rw [tear_E hx H i ht] at h2; cases h2

theorem hom_ppo : Hom (E hx) (dx x A B C f).ppo x.ppo := by
  intro i j h
  have hp := hom_po hx H i j
  simp only [Exec.ppo, Bool.and_eq_true] at h ⊢
  rw [ev_E hx i, ev_E hx j] at h
  simp only [rp_isW, rp_isR, rp_isM] at h
  exact ⟨hp h.1, h.2⟩

theorem hom_implied : Hom (E hx) (dx x A B C f).implied x.implied := by
  intro i j h
  have hp := hom_po hx H i j
  simp only [Exec.implied, Bool.and_eq_true] at h ⊢
  rw [ev_E hx i, ev_E hx j] at h
  simp only [rp_isW, rp_isR, rp_isA] at h
  exact ⟨⟨⟨hp h.1.1.1, h.1.1.2⟩, h.1.2⟩, h.2⟩

theorem hom_ppoXl : Hom (E hx) (dx x A B C f).ppoXl x.ppoXl := by
  intro i j h
  have hp := hom_ppo hx H i j
  simp only [Exec.ppoXl, Bool.and_eq_true] at h ⊢
  rw [ev_E hx i, ev_E hx j] at h
  simp only [rp_weak] at h
  exact ⟨⟨hp h.1.1, h.1.2⟩, h.2⟩

theorem hom_lockXl : Hom (E hx) (dx x A B C f).lockXl x.lockXl := by
  intro i j h
  simp only [Exec.lockXl, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true,
    List.mem_finRange, true_and] at h ⊢
  rw [ev_E hx i, ev_E hx j] at h
  simp only [rp_isM, rp_isA] at h
  refine ⟨⟨⟨h.1.1.1, h.1.1.2⟩, hom_po hx H _ _ h.1.2⟩, ?_⟩
  rcases h.2 with (h2 | h2) | ⟨l, ⟨hl, h1⟩, h3⟩
  · exact Or.inl (Or.inl h2)
  · exact Or.inl (Or.inr h2)
  · rw [ev_E hx l, rp_isA] at hl
    exact Or.inr ⟨E hx l, ⟨hl, hom_po hx H _ _ h1⟩, hom_po hx H _ _ h3⟩

theorem hom_sfenceXl : Hom (E hx) (dx x A B C f).sfenceXl x.sfenceXl := by
  intro i j h
  have hf := hom_fencerel hx H .sfence i j
  simp only [Exec.sfenceXl, Bool.and_eq_true] at h ⊢
  rw [ev_E hx i, ev_E hx j] at h
  simp only [rp_isW] at h
  exact ⟨h.1, hf h.2⟩

theorem atomic (hwf : x.Wf = true) (hrmw : x.rmw = rmwPairs x.evs) (h : x.atomicB = true) :
    (dx x A B C f).atomicB = true := by
  have hh : Hom (E hx) ((dx x A B C f).rmwR.inter ((dx x A B C f).fre.seq (dx x A B C f).coe))
      (x.rmwR.inter (x.fre.seq x.coe)) :=
    (hom_rmwR hx H hrmw).inter (((hom_frR hx H hwf).inter (hom_ext hx H)).seq
      ((hom_coR hx H).inter (hom_ext hx H)))
  simp only [Exec.atomicB, BRel.emptyB, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.not_eq_true'] at h ⊢
  intro a b
  cases hab : (BRel.inter (dx x A B C f).rmwR ((dx x A B C f).fre.seq (dx x A B C f).coe)) a b
  · rfl
  · have := h (E hx a) (E hx b)
    rw [hh a b hab] at this; cases this

theorem dx_sc (hwf : x.Wf = true) (hrmw : x.rmw = rmwPairs x.evs) (h : x.Sc) : (dx x A B C f).Sc :=
  ⟨atomic hx H hwf hrmw h.1,
    ((hom_po hx H).union ((hom_com hx H hwf).seq (hom_sm hx H))).acyclic h.2⟩

theorem dx_tso (hwf : x.Wf = true) (hrmw : x.rmw = rmwPairs x.evs) (h : x.Tso) : (dx x A B C f).Tso :=
  ⟨atomic hx H hwf hrmw h.1,
    (((hom_po hx H).inter (hom_loc hx H)).union ((hom_com hx H hwf).seq (hom_sm hx H))).acyclic h.2.1,
    ((hom_fencerel hx H .mfence).union ((hom_implied hx H).union ((hom_ppo hx H).union
      ((((hom_rfR hx H).inter (hom_ext hx H)).union ((hom_frR hx H hwf).union (hom_coR hx H))).seq
        (hom_sm hx H))))).acyclic h.2.2⟩

theorem dx_xl (hwf : x.Wf = true) (hrmw : x.rmw = rmwPairs x.evs) (h : x.Xl) : (dx x A B C f).Xl :=
  ⟨atomic hx H hwf hrmw h.1,
    (((hom_po hx H).inter (hom_loc hx H)).union ((hom_com hx H hwf).seq (hom_smT hx H))).acyclic h.2.1,
    ((hom_po hx H).union (hom_rfR hx H)).acyclic h.2.2.1,
    ((hom_fencerel hx H .mfence).union ((hom_ppoXl hx H).union ((hom_lockXl hx H).union
      ((hom_sfenceXl hx H).union
      ((((hom_rfR hx H).inter (hom_ext hx H)).union ((hom_frR hx H hwf).union (hom_coR hx H))).seq
        (hom_smT hx H)))))).acyclic h.2.2.2⟩

theorem lt_of_eN {w : Nat} (h : eN A.length B.length w < x.n) : w < (dx x A B C f).n := by
  have h1 := x_n hx; have h2 : (dx x A B C f).n = A.length + C.length := dx_n
  unfold eN at h; split_ifs at h <;> omega

theorem evN_dx {w : Nat} (h : w < (dx x A B C f).n) :
    (dx x A B C f).evN w = rp f (x.evN (eN A.length B.length w)) := by
  rw [evN_eq' _ h, evN_eq' _ (eN_lt hx h), ev_E hx ⟨w, h⟩]; rfl

theorem mem_of_dx {e : Ev} (he : e ∈ (dx x A B C f).evs) : ∃ u ∈ A ++ C, e = rp f u := by
  rw [dx_evs, List.mem_map] at he
  obtain ⟨u, hu, rfl⟩ := he
  exact ⟨u, hu, rfl⟩

theorem mem_x {u : Ev} (hu : u ∈ A ++ C) : u ∈ x.evs := by
  rw [hx]; simp only [List.mem_append] at hu ⊢; tauto

theorem touched_dx {yb : Nat} (h : yb ∈ (dx x A B C f).touched) : yb ∈ x.touched := by
  simp only [Exec.touched, List.mem_flatMap, List.mem_filter] at h ⊢
  obtain ⟨e, ⟨he, hM⟩, hy⟩ := h
  obtain ⟨u, hu, rfl⟩ := mem_of_dx (hx := hx) (H := H) he
  exact ⟨u, ⟨mem_x hx H hu, hM⟩, hy⟩

theorem dx_wf (hwf : x.Wf = true) (hrmw : x.rmw = rmwPairs x.evs) : (dx x A B C f).Wf = true := by
  have hw0 := hwf
  simp only [Exec.Wf, Bool.and_eq_true, List.all_eq_true] at hw0 ⊢
  obtain ⟨⟨⟨⟨w1, w2⟩, w3⟩, w4⟩, w5⟩ := hw0
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro r _
    rw [ev_E hx r]
    simp only [rp_isR, rp_bytes, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true]
    cases hR : (x.ev (E hx r)).isR
    · exact Or.inl rfl
    · refine Or.inr fun yb hyb => ?_
      have hrf := rf_some hx H hwf r hR (covers_of_mem hyb)
      cases hv : (dx x A B C f).rf r.val yb with
      | none => rfl
      | some w =>
        rw [hv, Option.map_some] at hrf
        obtain ⟨hk, hW, hC⟩ := wf_rf hwf (E hx r) hR (covers_of_mem hyb) hrf
        have hw' := lt_of_eN hx H hk
        simp only [Exec.valid, hw', evN_dx hx H hw', rp_isW, rp_covers',
          evN_eq' _ hk, hW, hC, Bool.and_self, decide_true]
  · intro yb hyb
    have hxt := touched_dx hx H hyb
    have := w2 yb hxt
    simp only [decide_eq_true_eq, List.mem_finRange,
      true_implies, Bool.or_eq_true, Bool.not_eq_true', List.contains_eq_mem] at this ⊢
    obtain ⟨⟨hnd, hmem⟩, hall⟩ := this
    refine ⟨⟨by rw [dx_co]; exact nodup_filterMap_preN hnd, ?_⟩, ?_⟩
    · intro w hw
      rw [dx_co, mem_filterMap_preN] at hw
      have := hmem _ hw
      simp only [Exec.valid, decide_eq_true_eq] at this
      obtain ⟨⟨hk, hW⟩, hC⟩ := this
      have hw' := lt_of_eN hx H hk
      simp only [Exec.valid, hw', evN_dx hx H hw', rp_isW, rp_covers', hW, hC,
        decide_true, and_self]
    · intro w
      rw [ev_E hx w]
      simp only [rp_isW, rp_covers']
      rcases hall (E hx w) with h | h
      · exact Or.inl h
      · right; rw [dx_co, mem_filterMap_preN]; exact h
  · intro p hp
    rw [dx_rmw] at hp
    obtain ⟨p1, p2⟩ := p
    have hp' := hom_rmwR hx H hrmw ⟨p1, ?_⟩ ⟨p2, ?_⟩ (by
      simp only [Exec.rmwR, List.contains_eq_mem, decide_eq_true_eq, dx_rmw]; exact hp)
    rotate_left
    · obtain ⟨h1, -⟩ := (mem_rmwPairs_iff _ _ _).1 hp; exact h1
    · obtain ⟨-, h2, -⟩ := (mem_rmwPairs_iff _ _ _).1 hp; exact h2
    obtain ⟨h1, h2, hc1, hc2⟩ := (mem_rmwPairs_iff _ _ _).1 hp
    simp only [Exec.rmwR, List.contains_eq_mem, decide_eq_true_eq] at hp'
    have := w3 _ hp'
    simp only [Exec.valid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this hc1 hc2 ⊢
    have ha := this.1.2
    have hs := this.2
    have e1 := evN_dx hx H (f := f) h1
    have e2 := evN_dx hx H (f := f) h2
    have g1 : (dx x A B C f).evN p1 = (dx x A B C f).evs[p1] := by simp [Exec.evN, h1]
    have g2 : (dx x A B C f).evN p2 = (dx x A B C f).evs[p2] := by simp [Exec.evN, h2]
    rw [e1, e2]
    rw [← g1, e1] at hc1; rw [← g1, ← g2, e1, e2] at hc2
    simp only [rp_isR, rp_isW, rp_tid, rp_pos, rp_locked, rp_accAddr, rp_accSize] at hc1 hc2 ⊢
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, hc1.1⟩, hc2.1.1.1.1.1⟩, hc2.1.1.1.2⟩, by omega⟩, hc1.2⟩,
      hc2.1.1.1.1.2⟩, ha⟩, hs⟩
  · intro a _ b _
    have := w4 (E hx a) (List.mem_finRange _) (E hx b) (List.mem_finRange _)
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at this ⊢
    cases hs : (dx x A B C f).sm a b
    · exact Or.inl rfl
    · rcases this with h | h
      · rw [hom_sm hx H a b hs] at h; cases h
      · right; rw [ev_E hx a, ev_E hx b]; simp only [rp_act, rp_locked, rp_ann, rp_accAddr, rp_accSize]; exact h
  · intro e he
    obtain ⟨u, hu, rfl⟩ := mem_of_dx (hx := hx) (H := H) he
    have := w5 u (mem_x hx H hu)
    exact this

theorem dx_readsOk {init : Nat → BitVec 8} {exps exps' : List (List (BitVec 8))} (hwf : x.Wf = true)
    (he : ∀ r < (dx x A B C f).n, exps'.getD r [] = exps.getD (eN A.length B.length r) [])
    (h : ∀ r < x.n, (x.evN r).isR = true → x.readBytes init r = exps.getD r []) :
    ∀ r < (dx x A B C f).n, ((dx x A B C f).evN r).isR = true →
      (dx x A B C f).readBytes init r = exps'.getD r [] := by
  intro r hr hR
  rw [he r hr, ← h _ (eN_lt hx hr) (by rw [evN_dx hx H hr] at hR; exact hR)]
  simp only [Exec.readBytes, evN_dx hx H hr, rp_bytes]
  apply List.map_congr_left
  intro yb hyb
  rw [evN_dx hx H hr, rp_isR, evN_eq' _ (eN_lt hx hr)] at hR
  rw [evN_eq' _ (eN_lt hx hr)] at hyb
  have hrf := rf_some hx H hwf ⟨r, hr⟩ hR (covers_of_mem hyb)
  simp only [E_val] at hrf
  simp only [Exec.readByte, hrf]
  cases hv : (dx x A B C f).rf r yb with
  | none => rfl
  | some w =>
    simp only [Option.map_some]
    obtain ⟨hk, -, -⟩ := wf_rf hwf ⟨eN A.length B.length r, eN_lt hx hr⟩ hR (covers_of_mem hyb)
      (by rw [hrf, hv]; rfl)
    rw [evN_dx hx H (lt_of_eN hx H hk), rp_byte]

theorem dx_written (yb : Nat) : writtenByte (dx x A B C f) yb = writtenByte x yb := by
  simp only [writtenByte, dx_evs, hx, List.any_append, List.any_map]
  have hB : B.any (fun e => e.isW && e.covers yb) = false := by
    rw [List.any_eq_false]
    intro d hd
    have := (H.drop d hd).1
    cases hW : d.isW
    · simp
    · exact (W_ne_R hW this).elim
  rw [hB, Bool.or_false]
  rfl

theorem dx_finalByte (hwf : x.Wf = true) (init : Nat → BitVec 8) {yb : Nat} (hy : writtenByte x yb = true) :
    (dx x A B C f).finalByte init yb = x.finalByte init yb := by
  have ht : yb ∈ x.touched := by
    simp only [writtenByte, List.any_eq_true, Bool.and_eq_true] at hy
    obtain ⟨e, he, hW, hC⟩ := hy
    simp only [Exec.touched, List.mem_flatMap, List.mem_filter]
    exact ⟨e, ⟨he, by simp [Ev.isM, hW]⟩, mem_of_covers hC⟩
  have hw0 := hwf
  simp only [Exec.Wf, Bool.and_eq_true, List.all_eq_true] at hw0
  have hco := (hw0.1.1.1.2 yb ht)
  simp only [decide_eq_true_eq, Exec.valid] at hco
  have hall : ∀ k ∈ x.co yb, (preN A.length B.length k).isSome = true := by
    intro k hk
    obtain ⟨⟨hkn, hW⟩, -⟩ := hco.1.2 k hk
    rw [evN_eq' _ hkn] at hW
    obtain ⟨w, hw⟩ := write_image hx H ⟨k, hkn⟩ hW
    have : k = eN A.length B.length w.val := by
      have := congrArg Fin.val hw; rw [E_val] at this; exact this.symm
    rw [this, preN_eN]; rfl
  simp only [Exec.finalByte, dx_co, getLast?_filterMap hall]
  cases hl : (x.co yb).getLast? with
  | none => rfl
  | some k =>
    have hk := List.mem_of_getLast? hl
    obtain ⟨⟨hkn, hW⟩, -⟩ := hco.1.2 k hk
    rw [evN_eq' _ hkn] at hW
    obtain ⟨w, hw⟩ := write_image hx H ⟨k, hkn⟩ hW
    have hkw : k = eN A.length B.length w.val := by
      have := congrArg Fin.val hw; rw [E_val] at this; exact this.symm
    simp only [Option.bind_some, hkw, preN_eN]
    rw [evN_dx hx H w.2, rp_byte]

end rel

end

/-! ## On candidates of trace choices -/

/-- The candidate part of `AxReach` for one choice of traces. -/
def Cand (t : Test) (trs : List XTrace) (M : Exec → Prop) (fin : Silmaril.X86.MemoryModel.Litmus.Final) :
    Prop :=
  ∃ x : Exec, x.evs = (units trs).map Prod.fst ∧ x.rmw = rmwPairs ((units trs).map Prod.fst) ∧
    x.Wf = true ∧ ReadsOk t x ((units trs).map Prod.snd) ∧ M x ∧ fin = finalAx t trs x

theorem getD_eN {α : Type} (A B C : List α) (d : α) (r : Nat) :
    (A ++ B ++ C).getD (eN A.length B.length r) d = (A ++ C).getD r d := by
  simp only [List.getD_eq_getElem?_getD]
  unfold eN
  split_ifs with h
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by omega),
      List.getElem?_append_left (by omega)]
  · rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by omega)]
    simp only [List.length_append]
    congr 2; omega

/-- **Dropping read units keeps a candidate**: if the units of `trs'` are those of `trs`
without the block `UB` (renumbered by `f`), `Hyp` holds, and the final registers agree, then
every candidate of `trs` under SC, TSO or XL gives one of `trs'` with the same final state. -/
theorem cand_drop (t : Test) (M : Model) {trs trs' : List XTrace}
    {UA UB UC : List (Ev × List Byte)} {f : Ev → Nat}
    (hu : units trs = UA ++ UB ++ UC)
    (hu' : units trs' = (UA ++ UC).map fun q => (rp f q.1, q.2))
    (H : Hyp (UA.map Prod.fst) (UB.map Prod.fst) (UC.map Prod.fst) f)
    (hfin : ∀ m, finalOf trs' m = finalOf trs m) {fin : Silmaril.X86.MemoryModel.Litmus.Final}
    (h : Cand t trs M.Holds fin) : Cand t trs' M.Holds fin := by
  obtain ⟨x, hx, hrmw, hwf, hrd, hM, rfl⟩ := h
  have hx' : x.evs = UA.map Prod.fst ++ UB.map Prod.fst ++ UC.map Prod.fst := by
    rw [hx, hu]; simp
  have he' : (units trs').map Prod.fst = (UA.map Prod.fst ++ UC.map Prod.fst).map (rp f) := by
    rw [hu']; simp only [List.map_map, List.map_append]; rfl
  have hrmw' : x.rmw = rmwPairs x.evs := by rw [hrmw, hx]
  refine ⟨dx x (UA.map Prod.fst) (UB.map Prod.fst) (UC.map Prod.fst) f, he'.symm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [dx_rmw, dx_evs, he']
  · exact dx_wf hx' H hwf hrmw'
  · intro r hr hR
    refine dx_readsOk hx' H hwf ?_ hrd r hr hR
    intro r _
    have e1 : (units trs).map Prod.snd = UA.map Prod.snd ++ UB.map Prod.snd ++ UC.map Prod.snd := by
      rw [hu]; simp
    have e2 : (units trs').map Prod.snd = UA.map Prod.snd ++ UC.map Prod.snd := by
      rw [hu']; simp only [List.map_map, List.map_append]; rfl
    rw [e1, e2]
    have := getD_eN (UA.map Prod.snd) (UB.map Prod.snd) (UC.map Prod.snd) [] r
    simp only [List.length_map] at this ⊢
    exact this.symm
  · cases M with
    | sc => exact dx_sc hx' H hwf hrmw' hM
    | tso => exact dx_tso hx' H hwf hrmw' hM
    | xl => exact dx_xl hx' H hwf hrmw' hM
  · simp only [finalAx]
    rw [hfin]
    congr 1
    funext yb
    rw [dx_written hx' H]
    split
    · rename_i hw; rw [dx_finalByte hx' H hwf _ hw]
    · rfl

end Silmaril.Proofs.X86.Concurrency.Cir.Chan.Drop
