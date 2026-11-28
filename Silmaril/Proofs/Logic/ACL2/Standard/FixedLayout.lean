module

public import Silmaril.Logic.ACL2.Standard.FixedLayout.Source
public import Silmaril.Logic.ACL2.Standard.Pure.Thms

@[expose] public section

namespace Silmaril.Proofs.Logic.ACL2.Standard.FixedLayout

open Silmaril.Logic.ACL2.Standard
open Silmaril.Logic.ACL2.Standard.FixedLayout
open Object

private theorem natRank_integer (n : Int) : (integer n).natRank = n.toNat := by
  have h := (integerValue?_eq_some_iff (integer n) n).2 rfl
  simp [natRank, h]

private theorem ofBool_eq_nil (b : Bool) : ofBool b = nil ↔ b = false := by
  cases b <;> decide

private theorem integer_eq_integer (m n : Int) : integer m = integer n ↔ m = n := by
  constructor
  · intro h
    have get (k : Int) := (integerValue?_eq_some_iff (integer k) k).2 rfl
    exact Option.some.inj ((get m).symm.trans ((congrArg integerValue? h).trans (get n)))
  · rintro rfl
    rfl

private theorem add_integer (m n : Int) : (integer m).binaryAdd (integer n) = integer (m + n) := by
  have add := Rat.intCast_add m n
  change Rat.ofInt (m + n) = Rat.ofInt m + Rat.ofInt n at add
  change ofParts (Rat.ofInt m + Rat.ofInt n) (0 + 0) = rational (Rat.ofInt (m + n))
  rw [Rat.add_zero, ofParts_zero, ← add]

theorem natRank_eq_zero_of_zp {index : Object} (h : index.zp ≠ nil) : index.natRank = 0 := by
  unfold natRank
  cases value : index.integerValue? with
  | none => rfl
  | some n =>
    have nonpos : n ≤ 0 := by
      by_contra! pos
      exact h ((zp_eq_nil_iff index).2 ⟨n, pos, (integerValue?_eq_some_iff index n).1 value⟩)
    simpa using Int.toNat_eq_zero.mpr nonpos

private theorem natRank_pred {index : Object} (h : index.zp = nil) :
    index.natRank = ((integer (-1)).binaryAdd index).natRank + 1 := by
  obtain ⟨n, hn, rfl⟩ := (zp_eq_nil_iff index).1 h
  simp only [add_integer, natRank_integer]
  omega

theorem len_source (x : Object) : x.len = Source.lenBody Object.len x := by
  cases x <;> simp [Source.lenBody, len, spineLength, consp, cdr,
    ofBool_eq_nil, add_integer, Int.add_comm]

theorem nth_source (i x : Object) : i.mvNth x = Source.nthBody Object.mvNth i x :=
  Pure.mvNth_native i x

theorem updateNth_source (i value x : Object) :
    updateNth i value x = Source.updateNthBody Object.updateNth i value x := by
  by_cases h : i.zp = nil
  · simp only [Source.updateNthBody, h, ite_true, updateNth]
    rw [natRank_pred h]
    rfl
  · simp [Source.updateNthBody, h, updateNth, natRank_eq_zero_of_zp h, writeAt]

theorem makeListAc_source (n value tail : Object) :
    makeListAc n value tail = Source.makeListAcBody Object.makeListAc n value tail := by
  by_cases h : n.zp = nil
  · simp only [Source.makeListAcBody, h, ite_true, makeListAc]
    rw [natRank_pred h, List.replicate_succ, List.foldl_cons]
  · simp [Source.makeListAcBody, h, makeListAc, natRank_eq_zero_of_zp h]

private theorem readAt_nil (i : Nat) : readAt i nil = nil := by
  induction i with
  | zero => rfl
  | succ _ ih => exact ih

private theorem readAt_atom (i : Nat) {x : Object} (h : x.consp = false) :
    readAt i x = nil := by
  cases i with
  | zero => exact car_atom h
  | succ i => rw [readAt, cdr_atom h, readAt_nil]

theorem mvNth_eq_readAt (index x : Object) : index.mvNth x = readAt index.natRank x := by
  induction x generalizing index with
  | cons head tail _ ih =>
    rw [mvNth]
    split
    · rename_i h
      rw [ih, natRank_pred h]
      rfl
    · rename_i h
      rw [natRank_eq_zero_of_zp h]
      rfl
  | _ => exact (readAt_atom _ rfl).symm

theorem readAfterWrite (i : Nat) (value x : Object) : readAt i (writeAt i value x) = value := by
  induction i generalizing x with
  | zero => rfl
  | succ _ ih => exact ih x.cdr

theorem readOther (i j : Nat) (h : i ≠ j) (value x : Object) :
    readAt i (writeAt j value x) = readAt i x := by
  induction i generalizing j x with
  | zero => cases j with
    | zero => exact (h rfl).elim
    | succ _ => rfl
  | succ i ih => cases j with
    | zero => rfl
    | succ j => exact ih j (fun e => h (congrArg Nat.succ e)) x.cdr

theorem writeAt_ofList (xs : List Object) (i : Nat) (h : i < xs.length) (value : Object) :
    writeAt i value (ofList xs) = ofList (xs.set i value) := by
  induction xs generalizing i with
  | nil => exact (Nat.not_lt_zero _ h).elim
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change cons x (writeAt i value (ofList xs)) = cons x (ofList (xs.set i value))
      rw [ih i (Nat.lt_of_succ_lt_succ h)]

theorem readAt_past_spine (i : Nat) (x : Object) (h : x.spineLength ≤ i) :
    readAt i x = nil := by
  induction x generalizing i with
  | cons head tail _ ih =>
    cases i with
    | zero => exact (Nat.not_succ_le_zero _ h).elim
    | succ i => exact ih i (Nat.le_of_succ_le_succ h)
  | _ => exact readAt_atom _ rfl

theorem writeAt_spineLength (i : Nat) (v x : Object) :
    (writeAt i v x).spineLength = max x.spineLength (i + 1) := by
  induction i generalizing x with
  | zero =>
    cases x <;> simp [writeAt, spineLength, cdr, nil]
  | succ i ih =>
    rw [writeAt, spineLength, ih]
    cases x <;> simp [spineLength, cdr, nil, Nat.succ_max_succ]

private theorem length_of_trueListp (x : Object) (h : x.trueListp = true) : Source.length x = x.len := by
  have notString : x.stringp = false := by
    cases x <;> simp_all [stringp, trueListp, nil]
  simp [Source.length, notString, ofBool_eq_nil]

theorem cellsP_source (x : Object) : Toy.cellsP x = Source.cellsPBody Toy.cellsP x := by
  cases x with
  | cons head tail =>
    cases h : head.integerp <;>
      simp [Toy.cellsP, Source.cellsPBody, Pure.atom_native, listAll, consp, cdr, car, h, ofBool]
    rfl
  | _ => rfl

private theorem len_equal (x : Object) (n : Nat) :
    x.len.equal (integer n) = ofBool (decide (x.spineLength = n)) := by
  simp only [equal, len, integer_eq_integer, Int.natCast_inj]

private theorem testAnd (p q : Bool) :
    (if ofBool p = nil then nil else ofBool q) = ofBool (p && q) := by
  cases p <;> rfl

private theorem testLast (p : Bool) :
    (if ofBool p = nil then nil else truth) = ofBool p := by
  cases p <;> rfl

private theorem mvNth_zero (x : Object) : (integer 0).mvNth x = x.car := by
  rw [mvNth_eq_readAt]
  rfl

private theorem mvNth_one (x : Object) : (integer 1).mvNth x = x.cdr.car := by
  rw [mvNth_eq_readAt]
  rfl

theorem recognizer_source (x : Object) : Toy.recognizer x = Source.recognizer x := by
  cases ht : x.trueListp with
  | false => simp [Toy.recognizer, Toy.recognizes, Source.recognizer, ht, ofBool]
  | true =>
    rw [Source.recognizer, length_of_trueListp x ht]
    simp only [Source.numericEqual, mvNth_zero, mvNth_one, Source.scalarP, Toy.cellsP]
    have outer : x.len.equal (integer 2) = ofBool (decide (x.spineLength = 2)) := len_equal x 2
    have cells : x.cdr.car.len.equal (integer 3) = ofBool (decide (x.cdr.car.spineLength = 3)) :=
      len_equal x.cdr.car 3
    rw [outer, cells]
    simp only [testLast, testAnd, Toy.recognizer, Toy.recognizes, Bool.and_assoc]

theorem readScalar_source (x : Object) : Toy.readScalar x = Source.readScalar x := by
  simp only [Toy.readScalar, Source.readScalar, mvNth_eq_readAt, natRank_integer]
  rfl

theorem readCell_source (i x : Object) : Toy.readCell i x = Source.readCell i x := by
  simp only [Toy.readCell, Source.readCell, mvNth_eq_readAt, natRank_integer]
  rfl

theorem writeScalar_source (v x : Object) : Toy.writeScalar v x = Source.writeScalar v x := by
  simp only [Toy.writeScalar, Source.writeScalar, updateNth, natRank_integer]
  rfl

theorem writeCell_source (i v x : Object) : Toy.writeCell i v x = Source.writeCell i v x := by
  simp only [Toy.writeCell, Source.writeCell, Source.updateNthArray, updateNth, mvNth_eq_readAt, natRank_integer]
  rfl

theorem initial_source : Toy.initial = Source.initial := by decide +kernel

theorem readCell_writeCell (i v x : Object) : Toy.readCell i (Toy.writeCell i v x) = v := by
  simp only [Toy.readCell, Toy.writeCell, writeAt, cdr_cons, car_cons, mvNth_eq_readAt, updateNth,
    readAfterWrite]

theorem readOtherCell_writeCell (i j : Object) (h : i.natRank ≠ j.natRank) (v x : Object) :
    Toy.readCell i (Toy.writeCell j v x) = Toy.readCell i x := by
  simp only [Toy.readCell, Toy.writeCell, writeAt, cdr_cons, car_cons, mvNth_eq_readAt,
    updateNth, readOther _ _ h]

private theorem spineLength_ofList (xs : List Object) : (ofList xs).spineLength = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (ofList xs).spineLength + 1 = xs.length + 1
    rw [ih]

private theorem listAll_ofList (p : Object → Bool) (xs : List Object) :
    (ofList xs).listAll p = xs.all p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (p x && (ofList xs).listAll p) = (p x && xs.all p)
    rw [ih]

private theorem integerp_integer (n : Int) : (integer n).integerp = true := by
  have h := (integerValue?_eq_some_iff (integer n) n).2 rfl
  simp [integerp, h]

theorem recognizes_encode (s : Int) (cells : List Int) :
    Toy.recognizes (Toy.encode s cells) = decide (cells.length = 3) := by
  change (true && true && (integer s).integerp &&
    (ofList (cells.map integer)).listAll integerp &&
    decide ((ofList (cells.map integer)).spineLength = 3)) = _
  rw [listAll_ofList, spineLength_ofList, List.length_map, integerp_integer]
  have all : (cells.map integer).all integerp = true := by
    simp [integerp_integer]
  simp [all]

private theorem exists_ofList (x : Object) (h : x.trueListp = true) : ∃ xs, x = ofList xs := by
  induction x with
  | cons head tail _ ih =>
    obtain ⟨xs, rfl⟩ := ih h
    exact ⟨head :: xs, rfl⟩
  | _ => exact ⟨[], of_decide_eq_true h⟩

private theorem exists_integer (x : Object) (h : x.integerp = true) : ∃ n, x = integer n := by
  cases value : x.integerValue? with
  | none => simp [integerp, value] at h
  | some n => exact ⟨n, (integerValue?_eq_some_iff x n).1 value⟩

private theorem exists_integer_list (x : Object) (h : x.listAll integerp = true) :
    ∃ cells : List Int, x = ofList (cells.map integer) := by
  induction x with
  | cons head tail _ ih =>
    simp only [listAll, Bool.and_eq_true] at h
    obtain ⟨v, rfl⟩ := exists_integer head h.1
    obtain ⟨cells, rfl⟩ := ih h.2
    exact ⟨v :: cells, rfl⟩
  | _ => exact ⟨[], of_decide_eq_true h⟩

theorem recognizes_iff_encode (x : Object) :
    Toy.recognizes x = true ↔ ∃ s cells, cells.length = 3 ∧ x = Toy.encode s cells := by
  constructor
  · intro h
    simp only [Toy.recognizes, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨proper, outerSize⟩, scalarType⟩, cellsType⟩, innerSize⟩ := h
    obtain ⟨xs, rfl⟩ := exists_ofList x proper
    have outer : xs.length = 2 := (spineLength_ofList xs) ▸ of_decide_eq_true outerSize
    rw [List.eq_getElem_of_length_eq_two xs outer] at scalarType cellsType innerSize ⊢
    obtain ⟨s, hs⟩ := exists_integer _ scalarType
    obtain ⟨cells, hc⟩ := exists_integer_list _ cellsType
    change (xs[0]'(by omega)) = integer s at hs
    change (xs[1]'(by omega)) = ofList (cells.map integer) at hc
    have three : (xs[1]'(by omega)).spineLength = 3 := of_decide_eq_true innerSize
    refine ⟨s, cells, ?_, ?_⟩
    · rw [hc, spineLength_ofList, List.length_map] at three
      exact three
    · rw [hs, hc, Toy.encode]
  · rintro ⟨s, cells, size, rfl⟩
    simp [recognizes_encode, size]

theorem writeScalar_encode (s v : Int) (cells : List Int) :
    Toy.writeScalar (integer v) (Toy.encode s cells) = Toy.encode v cells := rfl

theorem writeCell_encode (s v : Int) (cells : List Int) (i : Nat) (h : i < cells.length) :
    Toy.writeCell (integer i) (integer v) (Toy.encode s cells) = Toy.encode s (cells.set i v) := by
  have present : i < (cells.map integer).length := by simpa using h
  simp only [Toy.writeCell, updateNth, natRank_integer, Int.toNat_natCast]
  change ofList [integer s, writeAt i (integer v) (ofList (cells.map integer))] = _
  rw [writeAt_ofList _ _ present, ← List.map_set]
  rfl

theorem writeScalar_preserves (x : Object) (h : Toy.recognizes x = true) (v : Int) :
    Toy.recognizes (Toy.writeScalar (integer v) x) = true := by
  obtain ⟨s, cells, size, rfl⟩ := (recognizes_iff_encode x).1 h
  simp [writeScalar_encode, recognizes_encode, size]

theorem writeCell_preserves (x : Object) (h : Toy.recognizes x = true)
    (i : Nat) (bound : i < 3) (v : Int) :
    Toy.recognizes (Toy.writeCell (integer i) (integer v) x) = true := by
  obtain ⟨s, cells, size, rfl⟩ := (recognizes_iff_encode x).1 h
  have present : i < cells.length := size.symm ▸ bound
  simp [writeCell_encode s v cells i present, recognizes_encode, size]

end Silmaril.Proofs.Logic.ACL2.Standard.FixedLayout
