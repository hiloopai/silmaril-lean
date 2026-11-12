module

public import Silmaril.Libc.X86Alloc.Ladder.Boundary.Defs
public import Silmaril.Raw.Libc.X86Alloc.Frame

/-!
# Proofs: rung 08 (boundary tags) — the free list and the tables

* `dll_append`, `dll_mid`, `dll_snoc`: a doubly linked list split at a block (the links of the
  neighbours are exposed, so unlinking is two word writes and a re-fold);
* `wf_mid`, `wf_replace`, `wf_cons`: well-formedness under removal, shrinking in place, push;
* `firstT`/`lastT` under the same three operations;
* `tbl_split`, `tblR_update`, `tblPt_congr`: one byte of a table.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Libc.X86Alloc.Ladder.Boundary

open Silmaril.X86 (Word Byte)
open Silmaril.X86.Sep

/-! ## The doubly linked list -/

theorem hdOr_append (l1 l2 : List (Nat × Nat)) (n : Nat) :
    hdOr (l1 ++ l2) n = hdOr l1 (hdOr l2 n) := by cases l1 <;> rfl

theorem lastOr_append : ∀ (l1 l2 : List (Nat × Nat)) (p : Nat),
    lastOr (l1 ++ l2) p = lastOr l2 (lastOr l1 p)
  | [], _, _ => rfl
  | x :: l1, l2, _ => lastOr_append l1 l2 x.1

theorem lastOr_snoc (l : List (Nat × Nat)) (y : Nat × Nat) (p : Nat) :
    lastOr (l ++ [y]) p = y.1 := by rw [lastOr_append]; rfl

theorem dll_append : ∀ (l1 l2 : List (Nat × Nat)) (p n : Nat),
    dll (l1 ++ l2) p n = (dll l1 p (hdOr l2 n) ∗ dll l2 (lastOr l1 p) n)
  | [], l2, p, n => by
    show dll l2 p n = (emp ∗ dll l2 p n); rw [emp_sep]
  | x :: l1, l2, p, n => by
    show (blk x (hdOr (l1 ++ l2) n) p ∗ dll (l1 ++ l2) x.1 n) =
      ((blk x (hdOr l1 (hdOr l2 n)) p ∗ dll l1 x.1 (hdOr l2 n)) ∗ dll l2 (lastOr l1 x.1) n)
    rw [hdOr_append, dll_append l1 l2 x.1 n, sep_assoc]

/-- **A block in the middle**, with its neighbours' links. -/
theorem dll_mid (l1 : List (Nat × Nat)) (x : Nat × Nat) (l2 : List (Nat × Nat)) (p n : Nat) :
    dll (l1 ++ x :: l2) p n = (dll l1 p x.1 ∗ blk x (hdOr l2 n) (lastOr l1 p) ∗ dll l2 x.1 n) := by
  rw [dll_append]; rfl

/-- The last block of a segment. -/
theorem dll_snoc (l : List (Nat × Nat)) (y : Nat × Nat) (p n : Nat) :
    dll (l ++ [y]) p n = (dll l p y.1 ∗ blk y n (lastOr l p)) := by
  rw [dll_append]
  show (dll l p y.1 ∗ (blk y n (lastOr l p) ∗ emp)) = _
  rw [sep_emp]

theorem dll_cons (x : Nat × Nat) (l : List (Nat × Nat)) (p n : Nat) :
    dll (x :: l) p n = (blk x (hdOr l n) p ∗ dll l x.1 n) := rfl

theorem dll_nil (p n : Nat) : dll [] p n = emp := rfl

/-! ## Well-formedness -/

theorem heap_eq : heap = 0x4032c0 := rfl

theorem apart_comm {x y : Nat × Nat} : Apart x y ↔ Apart y x := by
  unfold Apart; constructor <;> intro h <;> omega

theorem good_pos {x : Nat × Nat} (h : Good x) : 0 < x.1 := by
  unfold Good at h; rw [heap_eq] at h; omega

theorem mem_mid {l1 l2 : List (Nat × Nat)} {x y : Nat × Nat} (h : y ∈ l1 ++ l2) :
    y ∈ l1 ++ x :: l2 := by
  simp only [List.mem_append, List.mem_cons] at h ⊢; tauto

/-- Removing a block. -/
theorem wf_mid {l1 l2 : List (Nat × Nat)} {x : Nat × Nat} (h : WF (l1 ++ x :: l2)) :
    Good x ∧ WF (l1 ++ l2) ∧ ∀ y ∈ l1 ++ l2, Apart x y := by
  obtain ⟨hg, hp⟩ := h
  rw [List.pairwise_append, List.pairwise_cons] at hp
  obtain ⟨p1, ⟨px, p2⟩, cross⟩ := hp
  refine ⟨hg x (by simp), ⟨fun y hy => hg y (mem_mid hy),
    List.pairwise_append.2 ⟨p1, p2, fun a ha b hb => cross a ha b (List.mem_cons_of_mem _ hb)⟩⟩,
    fun y hy => ?_⟩
  rcases List.mem_append.1 hy with hy | hy
  · exact apart_comm.1 (cross y hy x List.mem_cons_self)
  · exact px y hy

/-- Shrinking a block in place. -/
theorem wf_replace {l1 l2 : List (Nat × Nat)} {x x' : Nat × Nat} (h : WF (l1 ++ x :: l2))
    (hg : Good x') (hsub : x.1 ≤ x'.1 ∧ x'.1 + x'.2 ≤ x.1 + x.2) : WF (l1 ++ x' :: l2) := by
  obtain ⟨hgs, hp⟩ := h
  rw [List.pairwise_append, List.pairwise_cons] at hp
  obtain ⟨p1, ⟨px, p2⟩, cross⟩ := hp
  refine ⟨fun y hy => ?_, ?_⟩
  · simp only [List.mem_append, List.mem_cons] at hy
    rcases hy with hy | rfl | hy
    · exact hgs y (by simp [hy])
    · exact hg
    · exact hgs y (by simp [hy])
  · rw [List.pairwise_append, List.pairwise_cons]
    refine ⟨p1, ⟨fun y hy => ?_, p2⟩, fun a ha b hb => ?_⟩
    · have := px y hy; unfold Apart at this ⊢; omega
    · rcases List.mem_cons.1 hb with rfl | hb
      · have := cross a ha x List.mem_cons_self; unfold Apart at this ⊢; omega
      · exact cross a ha b (List.mem_cons_of_mem _ hb)

/-- Pushing a block. -/
theorem wf_cons {x : Nat × Nat} {fs : List (Nat × Nat)} (h : WF fs) (hg : Good x)
    (ha : ∀ y ∈ fs, Apart x y) : WF (x :: fs) := by
  refine ⟨fun y hy => ?_, List.pairwise_cons.2 ⟨ha, h.2⟩⟩
  rcases List.mem_cons.1 hy with rfl | hy
  · exact hg
  · exact h.1 y hy

theorem hdOr_mem : ∀ {l : List (Nat × Nat)} (n : Nat), l ≠ [] → ∃ y ∈ l, hdOr l n = y.1
  | [], _, h => absurd rfl h
  | x :: _, _, _ => ⟨x, List.mem_cons_self, rfl⟩

theorem lastOr_mem : ∀ {l : List (Nat × Nat)} (p : Nat), l ≠ [] → ∃ y ∈ l, lastOr l p = y.1
  | [], _, h => absurd rfl h
  | [x], _, _ => ⟨x, List.mem_cons_self, rfl⟩
  | x :: y :: l, _, _ => by
    obtain ⟨z, hz, he⟩ := lastOr_mem (l := y :: l) x.1 (by simp)
    exact ⟨z, List.mem_cons_of_mem _ hz, he⟩

/-- The neighbour links of a well-formed list are `0` exactly at the ends. -/
theorem hdOr_zero {l : List (Nat × Nat)} (hg : ∀ y ∈ l, Good y) : hdOr l 0 = 0 ↔ l = [] := by
  cases l with
  | nil => simp [hdOr]
  | cons x l => simp only [hdOr, reduceCtorEq, iff_false]; exact (good_pos (hg x (by simp))).ne'

theorem lastOr_zero {l : List (Nat × Nat)} (hg : ∀ y ∈ l, Good y) : lastOr l 0 = 0 ↔ l = [] := by
  by_cases hl : l = []
  · subst hl; simp [lastOr]
  · obtain ⟨y, hy, he⟩ := lastOr_mem 0 hl
    simp only [hl, iff_false, he]; exact (good_pos (hg y hy)).ne'

theorem good_lt {l : List (Nat × Nat)} (hg : ∀ y ∈ l, Good y) {v : Nat}
    (hv : ∃ y ∈ l, v = y.1) : heap ≤ v ∧ v + 32 ≤ heap + 4096 ∧ v % 16 = 0 := by
  obtain ⟨y, hy, rfl⟩ := hv
  have := hg y hy; unfold Good at this; omega

/-! ## The tables as functions of the free list -/

theorem firstT_congr {fs fs' : List (Nat × Nat)} {j : Nat}
    (h : (∃ x ∈ fs, x.1 = heap + 16 * j) ↔ (∃ x ∈ fs', x.1 = heap + 16 * j)) :
    firstT fs j = firstT fs' j := by
  unfold firstT
  have : fs.any (fun x => x.1 == heap + 16 * j) = fs'.any (fun x => x.1 == heap + 16 * j) := by
    rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]; simpa using h
  rw [this]

theorem lastT_congr {fs fs' : List (Nat × Nat)} {j : Nat}
    (h : (∃ x ∈ fs, x.1 + x.2 = heap + 16 * (j + 1)) ↔
      (∃ x ∈ fs', x.1 + x.2 = heap + 16 * (j + 1))) :
    lastT fs j = lastT fs' j := by
  unfold lastT
  have : fs.any (fun x => x.1 + x.2 == heap + 16 * (j + 1)) =
      fs'.any (fun x => x.1 + x.2 == heap + 16 * (j + 1)) := by
    rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]; simpa using h
  rw [this]

theorem firstT_one {fs : List (Nat × Nat)} {j : Nat} :
    firstT fs j = 1 ↔ ∃ x ∈ fs, x.1 = heap + 16 * j := by
  unfold firstT
  by_cases h : fs.any (fun x => x.1 == heap + 16 * j) = true
  · simp only [h, ite_true, true_iff]
    obtain ⟨x, hx, he⟩ := List.any_eq_true.1 h
    exact ⟨x, hx, by simpa using he⟩
  · simp only [h, Bool.false_eq_true, ite_false]
    constructor
    · intro e; exact absurd e (by decide)
    · rintro ⟨x, hx, he⟩; exact absurd (List.any_eq_true.2 ⟨x, hx, by simp [he]⟩) h

theorem firstT_zero {fs : List (Nat × Nat)} {j : Nat} :
    firstT fs j = 0 ↔ ∀ x ∈ fs, x.1 ≠ heap + 16 * j := by
  unfold firstT
  by_cases h : fs.any (fun x => x.1 == heap + 16 * j) = true
  · simp only [h, ite_true]
    obtain ⟨x, hx, he⟩ := List.any_eq_true.1 h
    constructor
    · intro e; exact absurd e (by decide)
    · intro hall; exact absurd (by simpa using he) (hall x hx)
  · simp only [h, Bool.false_eq_true, ite_false, true_iff]
    intro x hx he; exact h (List.any_eq_true.2 ⟨x, hx, by simp [he]⟩)

theorem lastT_one {fs : List (Nat × Nat)} {j : Nat} :
    lastT fs j = 1 ↔ ∃ x ∈ fs, x.1 + x.2 = heap + 16 * (j + 1) := by
  unfold lastT
  by_cases h : fs.any (fun x => x.1 + x.2 == heap + 16 * (j + 1)) = true
  · simp only [h, ite_true, true_iff]
    obtain ⟨x, hx, he⟩ := List.any_eq_true.1 h
    exact ⟨x, hx, by simpa using he⟩
  · simp only [h, Bool.false_eq_true, ite_false]
    constructor
    · intro e; exact absurd e (by decide)
    · rintro ⟨x, hx, he⟩; exact absurd (List.any_eq_true.2 ⟨x, hx, by simp [he]⟩) h

theorem lastT_zero {fs : List (Nat × Nat)} {j : Nat} :
    lastT fs j = 0 ↔ ∀ x ∈ fs, x.1 + x.2 ≠ heap + 16 * (j + 1) := by
  unfold lastT
  by_cases h : fs.any (fun x => x.1 + x.2 == heap + 16 * (j + 1)) = true
  · simp only [h, ite_true]
    obtain ⟨x, hx, he⟩ := List.any_eq_true.1 h
    constructor
    · intro e; exact absurd e (by decide)
    · intro hall; exact absurd (by simpa using he) (hall x hx)
  · simp only [h, Bool.false_eq_true, ite_false, true_iff]
    intro x hx he; exact h (List.any_eq_true.2 ⟨x, hx, by simp [he]⟩)

theorem firstT_cases (fs : List (Nat × Nat)) (j : Nat) : firstT fs j = 0 ∨ firstT fs j = 1 := by
  unfold firstT; split <;> simp

theorem lastT_cases (fs : List (Nat × Nat)) (j : Nat) : lastT fs j = 0 ∨ lastT fs j = 1 := by
  unfold lastT; split <;> simp

/-- Removing a block that does not start at granule `j`. -/
theorem firstT_mid_ne {l1 l2 : List (Nat × Nat)} {x : Nat × Nat} {j : Nat}
    (h : x.1 ≠ heap + 16 * j) : firstT (l1 ++ l2) j = firstT (l1 ++ x :: l2) j := by
  refine firstT_congr ⟨fun ⟨y, hy, he⟩ => ⟨y, mem_mid hy, he⟩, fun ⟨y, hy, he⟩ => ⟨y, ?_, he⟩⟩
  simp only [List.mem_append, List.mem_cons] at hy ⊢
  rcases hy with hy | rfl | hy
  · exact .inl hy
  · exact absurd he h
  · exact .inr hy

/-- Removing a block that does not end with granule `j`. -/
theorem lastT_mid_ne {l1 l2 : List (Nat × Nat)} {x : Nat × Nat} {j : Nat}
    (h : x.1 + x.2 ≠ heap + 16 * (j + 1)) : lastT (l1 ++ l2) j = lastT (l1 ++ x :: l2) j := by
  refine lastT_congr ⟨fun ⟨y, hy, he⟩ => ⟨y, mem_mid hy, he⟩, fun ⟨y, hy, he⟩ => ⟨y, ?_, he⟩⟩
  simp only [List.mem_append, List.mem_cons] at hy ⊢
  rcases hy with hy | rfl | hy
  · exact .inl hy
  · exact absurd he h
  · exact .inr hy

/-- After removing a block, nothing starts where it started. -/
theorem firstT_mid_self {l1 l2 : List (Nat × Nat)} {x : Nat × Nat} {j : Nat}
    (hw : WF (l1 ++ x :: l2)) (h : x.1 = heap + 16 * j) : firstT (l1 ++ l2) j = 0 := by
  obtain ⟨hgx, ⟨hg, -⟩, ha⟩ := wf_mid hw
  refine firstT_zero.2 fun y hy he => ?_
  have h1 := hg y hy; have h2 := ha y hy
  unfold Good at h1 hgx; unfold Apart at h2; omega

/-- After removing a block, nothing ends where it ended. -/
theorem lastT_mid_self {l1 l2 : List (Nat × Nat)} {x : Nat × Nat} {j : Nat}
    (hw : WF (l1 ++ x :: l2)) (h : x.1 + x.2 = heap + 16 * (j + 1)) : lastT (l1 ++ l2) j = 0 := by
  obtain ⟨hgx, ⟨hg, -⟩, ha⟩ := wf_mid hw
  refine lastT_zero.2 fun y hy he => ?_
  have h1 := hg y hy; have h2 := ha y hy
  unfold Good at h1 hgx; unfold Apart at h2; omega

theorem firstT_replace (l1 l2 : List (Nat × Nat)) {x x' : Nat × Nat} (h : x'.1 = x.1) (j : Nat) :
    firstT (l1 ++ x' :: l2) j = firstT (l1 ++ x :: l2) j := by
  refine firstT_congr ⟨fun ⟨y, hy, he⟩ => ?_, fun ⟨y, hy, he⟩ => ?_⟩ <;>
    simp only [List.mem_append, List.mem_cons] at hy
  · rcases hy with hy | rfl | hy
    · exact ⟨y, by simp [hy], he⟩
    · exact ⟨x, by simp, h ▸ he⟩
    · exact ⟨y, by simp [hy], he⟩
  · rcases hy with hy | rfl | hy
    · exact ⟨y, by simp [hy], he⟩
    · exact ⟨x', by simp, h.symm ▸ he⟩
    · exact ⟨y, by simp [hy], he⟩

theorem lastT_replace (l1 l2 : List (Nat × Nat)) {x x' : Nat × Nat} {j : Nat}
    (h : x.1 + x.2 ≠ heap + 16 * (j + 1)) (h' : x'.1 + x'.2 ≠ heap + 16 * (j + 1)) :
    lastT (l1 ++ x' :: l2) j = lastT (l1 ++ x :: l2) j := by
  rw [← lastT_mid_ne h', ← lastT_mid_ne h]

theorem lastT_mid_one (l1 l2 : List (Nat × Nat)) (x : Nat × Nat) {j : Nat}
    (h : x.1 + x.2 = heap + 16 * (j + 1)) : lastT (l1 ++ x :: l2) j = 1 :=
  lastT_one.2 ⟨x, by simp, h⟩

theorem firstT_cons (x : Nat × Nat) (fs : List (Nat × Nat)) (j : Nat) :
    firstT (x :: fs) j = if x.1 = heap + 16 * j then 1 else firstT fs j := by
  split
  · exact firstT_one.2 ⟨x, by simp, by assumption⟩
  · rename_i h
    refine firstT_congr ⟨fun ⟨y, hy, he⟩ => ⟨y, ?_, he⟩, fun ⟨y, hy, he⟩ => ⟨y, by simp [hy], he⟩⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact absurd he h
    · exact hy

theorem lastT_cons (x : Nat × Nat) (fs : List (Nat × Nat)) (j : Nat) :
    lastT (x :: fs) j = if x.1 + x.2 = heap + 16 * (j + 1) then 1 else lastT fs j := by
  split
  · exact lastT_one.2 ⟨x, by simp, by assumption⟩
  · rename_i h
    refine lastT_congr ⟨fun ⟨y, hy, he⟩ => ⟨y, ?_, he⟩, fun ⟨y, hy, he⟩ => ⟨y, by simp [hy], he⟩⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact absurd he h
    · exact hy

/-! ## One byte of a table -/

/-- A table without byte `g`. -/
def tblR (a : Nat) (t : Nat → Byte) (g : Nat) : SProp :=
  bytesPt a (((List.range 256).map t).take g) ∗
    bytesPt (a + g + 1) (((List.range 256).map t).drop (g + 1))

theorem tblPt_congr (a : Nat) {t t' : Nat → Byte} (h : ∀ j < 256, t j = t' j) :
    tblPt a t = tblPt a t' := by
  unfold tblPt
  congr 1
  exact List.map_congr_left fun j hj => h j (List.mem_range.1 hj)

/-- **Byte `g` of a table.** -/
theorem tbl_split (a : Nat) (t : Nat → Byte) {g : Nat} (hg : g < 256) :
    tblPt a t = (bytePt (a + g) (t g) ∗ tblR a t g) := by
  unfold tblPt tblR
  have hlen : ((List.range 256).map t).length = 256 := by simp
  have e : (List.range 256).map t = ((List.range 256).map t).take g ++
      (t g :: ((List.range 256).map t).drop (g + 1)) := by
    conv_lhs => rw [← List.take_append_drop g ((List.range 256).map t)]
    rw [List.drop_eq_getElem_cons (by omega)]
    simp
  have ht : (((List.range 256).map t).take g).length = g := by simp; omega
  conv_lhs => rw [e]
  unfold bytesPt
  rw [bytesAt_append, ht]
  show (_ ∗ (bytePt (a + g) (t g) ∗ _)) = _
  ac_rfl

theorem tblR_update (a : Nat) (t : Nat → Byte) (g : Nat) (v : Byte) :
    tblR a (Function.update t g v) g = tblR a t g := by
  unfold tblR
  congr 2
  · refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    simp only [List.length_take, List.length_map, List.length_range] at h1
    simp only [List.getElem_take, List.getElem_map, List.getElem_range]
    rw [Function.update_of_ne (by omega)]
  · refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    simp only [List.getElem_drop, List.getElem_map, List.getElem_range]
    rw [Function.update_of_ne (by omega)]

/-- Writing byte `g`. -/
theorem tbl_write (a : Nat) (t : Nat → Byte) {g : Nat} (hg : g < 256) (v : Byte) :
    (bytePt (a + g) v ∗ tblR a t g) = tblPt a (Function.update t g v) := by
  rw [tbl_split a (Function.update t g v) hg, Function.update_self, tblR_update]

end Silmaril.Libc.X86Alloc.Ladder.Boundary
