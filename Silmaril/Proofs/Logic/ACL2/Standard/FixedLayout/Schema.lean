module

public import Silmaril.Logic.ACL2.Standard.FixedLayout.Schema.Defs
public import Silmaril.Logic.ACL2.Standard.FixedLayout.Thms

@[expose] public section

namespace Silmaril.Proofs.Logic.ACL2.Standard.FixedLayout.Schema

open Silmaril.Logic.ACL2.Standard
open Silmaril.Logic.ACL2.Standard.FixedLayout.Schema
open Object

theorem recognizes_nil (x : Object) : recognizes [] x = true ↔ x = nil := by
  cases x <;> simp [recognizes, fieldsAccept, trueListp, spineLength, nil]

theorem recognizes_cons (slot : Slot) (layout : List Slot) (head tail : Object) :
    recognizes (slot :: layout) (cons head tail) =
      (slot.accepts head && recognizes layout tail) := by
  simp [recognizes, fieldsAccept, trueListp, spineLength, car, cdr, Bool.and_comm, Bool.and_assoc]

theorem recognizes_cons_iff (slot : Slot) (layout : List Slot) (x : Object) :
    recognizes (slot :: layout) x = true ↔
      ∃ head tail, x = cons head tail ∧ slot.accepts head = true ∧ recognizes layout tail = true := by
  cases x with
  | cons head tail => simp [recognizes_cons]
  | _ => simp [recognizes, spineLength]

theorem initial_accepts (slot : Slot) : slot.accepts slot.initialObject = true := by
  cases slot with
  | scalar n => exact integerp_integer n
  | array size n =>
    simp [Slot.accepts, Slot.initialObject, listAll_ofList, spineLength_ofList, integerp_integer]

theorem initial_recognized (layout : List Slot) : recognizes layout (initial layout) = true := by
  induction layout with
  | nil => rfl
  | cons slot layout ih =>
    change recognizes (slot :: layout) (cons slot.initialObject (initial layout)) = true
    rw [recognizes_cons, initial_accepts, ih]
    rfl

private theorem readAt_ofList (xs : List Object) (i : Nat) {v : Object}
    (h : xs[i]? = some v) : readAt i (ofList xs) = v := by
  induction xs generalizing i with
  | nil => simp at h
  | cons head tail ih =>
    cases i with
    | zero =>
      change head = v
      simpa using h
    | succ i => exact ih i h

theorem read_initial (layout : List Slot) (i : Nat) {slot : Slot}
    (h : layout[i]? = some slot) : readAt i (initial layout) = slot.initialObject := by
  apply readAt_ofList
  simp [h]

theorem readCell_initial (layout : List Slot) (i : Nat) (index : Object) {size : Nat} {n : Int}
    (h : layout[i]? = some (.array size n)) (bound : index.natRank < size) :
    readCell i index (initial layout) = integer n := by
  rw [readCell, read_initial layout i h, mvNth_eq_readAt, Slot.initialObject]
  apply readAt_ofList
  simp [bound]

theorem read_accepts (layout : List Slot) (i : Nat) {slot : Slot} (h : layout[i]? = some slot)
    {x : Object} (valid : recognizes layout x = true) : slot.accepts (readAt i x) = true := by
  induction layout generalizing i x with
  | nil => simp at h
  | cons head tail ih =>
    obtain ⟨v, rest, rfl, vh, rh⟩ := (recognizes_cons_iff head tail x).1 valid
    cases i with
    | zero =>
      have same : head = slot := by simpa using h
      subst head
      exact vh
    | succ i => exact ih i h rh

theorem write_preserves (layout : List Slot) (i : Nat) {slot : Slot} (h : layout[i]? = some slot)
    {x v : Object} (valid : recognizes layout x = true) (accepts : slot.accepts v = true) :
    recognizes layout (writeAt i v x) = true := by
  induction layout generalizing i x with
  | nil => simp at h
  | cons head tail ih =>
    obtain ⟨original, rest, rfl, vh, rh⟩ := (recognizes_cons_iff head tail x).1 valid
    cases i with
    | zero =>
      have same : head = slot := by simpa using h
      subst head
      simp [writeAt, cdr, recognizes_cons, accepts, rh]
    | succ i =>
      simp [writeAt, car, cdr, recognizes_cons, vh, ih i h rh]

private theorem listAll_writeAt (p : Object → Bool) (i : Nat) {v x : Object}
    (present : i < x.spineLength) (value : p v = true) (old : x.listAll p = true) :
    (writeAt i v x).listAll p = true := by
  induction i generalizing x with
  | zero =>
    cases x <;> simp_all [listAll, writeAt, spineLength, cdr]
  | succ i ih =>
    cases x with
    | cons head tail =>
      have present' : i < tail.spineLength := Nat.lt_of_succ_lt_succ present
      simp only [listAll, Bool.and_eq_true] at old
      simp [writeAt, listAll, car, cdr, old.1, ih present' old.2]
    | _ => simp [spineLength] at present

theorem writeCell_preserves (layout : List Slot) (i : Nat) (index : Object) {size : Nat} {n : Int}
    (h : layout[i]? = some (.array size n)) (bound : index.natRank < size)
    {x : Object} (valid : recognizes layout x = true) (v : Int) :
    recognizes layout (writeCell i index (integer v) x) = true := by
  have old := read_accepts layout i h valid
  simp only [Slot.accepts, Bool.and_eq_true, decide_eq_true_eq] at old
  have present : index.natRank < (readAt i x).spineLength := old.2.symm ▸ bound
  apply write_preserves layout i h valid
  simp only [Slot.accepts, updateNth, Bool.and_eq_true]
  refine ⟨listAll_writeAt integerp _ present (integerp_integer v) old.1, ?_⟩
  apply decide_eq_true
  rw [writeAt_spineLength, max_eq_left (by omega), old.2]

theorem readCell_writeCell (i : Nat) (index v x : Object) :
    readCell i index (writeCell i index v x) = v := by
  simp only [readCell, writeCell, readAt_writeAt, mvNth_eq_readAt, updateNth]

theorem readOtherCell_writeCell (i : Nat) (index key v x : Object)
    (h : index.natRank ≠ key.natRank) :
    readCell i index (writeCell i key v x) = readCell i index x := by
  simp only [readCell, writeCell, readAt_writeAt, mvNth_eq_readAt, updateNth,
    readAt_writeAt_other _ _ h]

theorem readAt_writeCell_other (i j : Nat) (h : i ≠ j) (key v x : Object) :
    readAt i (writeCell j key v x) = readAt i x :=
  readAt_writeAt_other i j h _ x

end Silmaril.Proofs.Logic.ACL2.Standard.FixedLayout.Schema
