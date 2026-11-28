module

public import Silmaril.Logic.ACL2.Standard.FixedLayout.Source
import Silmaril.Proofs.Logic.ACL2.Standard.FixedLayout

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard.Object

open Silmaril.Logic.ACL2.Standard.FixedLayout

theorem len_source (x : Object) : x.len = Source.lenBody Object.len x :=
  Proofs.Logic.ACL2.Standard.FixedLayout.len_source x

/-- The translated NTH and MV-NTH have the same total recursion on standard objects. -/
theorem nth_source (index x : Object) : index.mvNth x = Source.nthBody Object.mvNth index x :=
  Proofs.Logic.ACL2.Standard.FixedLayout.nth_source index x

theorem updateNth_source (index value x : Object) :
    updateNth index value x = Source.updateNthBody Object.updateNth index value x :=
  Proofs.Logic.ACL2.Standard.FixedLayout.updateNth_source index value x

theorem makeListAc_source (n value tail : Object) :
    makeListAc n value tail = Source.makeListAcBody Object.makeListAc n value tail :=
  Proofs.Logic.ACL2.Standard.FixedLayout.makeListAc_source n value tail

theorem mvNth_eq_readAt (index x : Object) : index.mvNth x = readAt index.natRank x :=
  Proofs.Logic.ACL2.Standard.FixedLayout.mvNth_eq_readAt index x

theorem updateNth_of_zp {index : Object} (h : index.zp ≠ nil) (value x : Object) :
    updateNth index value x = cons value x.cdr := by
  rw [updateNth, Proofs.Logic.ACL2.Standard.FixedLayout.natRank_eq_zero_of_zp h]
  rfl

theorem readAt_writeAt (i : Nat) (value x : Object) : readAt i (writeAt i value x) = value :=
  Proofs.Logic.ACL2.Standard.FixedLayout.readAfterWrite i value x

theorem readAt_writeAt_other (i j : Nat) (h : i ≠ j) (value x : Object) :
    readAt i (writeAt j value x) = readAt i x :=
  Proofs.Logic.ACL2.Standard.FixedLayout.readOther i j h value x

/-- In bounds, a logical update of a proper list agrees with Lean's List.set. -/
theorem writeAt_ofList (xs : List Object) (i : Nat) (h : i < xs.length) (value : Object) :
    writeAt i value (ofList xs) = ofList (xs.set i value) :=
  Proofs.Logic.ACL2.Standard.FixedLayout.writeAt_ofList xs i h value

theorem readAt_past_spine (i : Nat) (x : Object) (h : x.spineLength ≤ i) :
    readAt i x = nil :=
  Proofs.Logic.ACL2.Standard.FixedLayout.readAt_past_spine i x h

/-- A logical write grows the cons spine to include the requested position. -/
theorem writeAt_spineLength (i : Nat) (v x : Object) :
    (writeAt i v x).spineLength = max x.spineLength (i + 1) :=
  Proofs.Logic.ACL2.Standard.FixedLayout.writeAt_spineLength i v x

end Silmaril.Logic.ACL2.Standard.Object

namespace Silmaril.Logic.ACL2.Standard.FixedLayout.Toy

open Object

theorem cellsP_source (x : Object) : cellsP x = Source.cellsPBody cellsP x :=
  Proofs.Logic.ACL2.Standard.FixedLayout.cellsP_source x

theorem recognizer_source (x : Object) : recognizer x = Source.recognizer x :=
  Proofs.Logic.ACL2.Standard.FixedLayout.recognizer_source x

theorem initial_source : initial = Source.initial :=
  Proofs.Logic.ACL2.Standard.FixedLayout.initial_source

theorem readScalar_source (x : Object) : readScalar x = Source.readScalar x :=
  Proofs.Logic.ACL2.Standard.FixedLayout.readScalar_source x

theorem writeScalar_source (v x : Object) : writeScalar v x = Source.writeScalar v x :=
  Proofs.Logic.ACL2.Standard.FixedLayout.writeScalar_source v x

theorem readCell_source (i x : Object) : readCell i x = Source.readCell i x :=
  Proofs.Logic.ACL2.Standard.FixedLayout.readCell_source i x

theorem writeCell_source (i v x : Object) : writeCell i v x = Source.writeCell i v x :=
  Proofs.Logic.ACL2.Standard.FixedLayout.writeCell_source i v x

/-- The recognizer accepts exactly two slots with an integer and a proper list of three integers. -/
theorem recognizes_iff_encode (x : Object) :
    recognizes x = true ↔ ∃ s cells, cells.length = 3 ∧ x = encode s cells :=
  Proofs.Logic.ACL2.Standard.FixedLayout.recognizes_iff_encode x

theorem initial_recognized : recognizes initial = true := by decide +kernel

theorem readScalar_writeScalar (v x : Object) : readScalar (writeScalar v x) = v := rfl

theorem readScalar_writeCell (i v x : Object) : readScalar (writeCell i v x) = readScalar x := rfl

theorem readCell_writeScalar (i v x : Object) : readCell i (writeScalar v x) = readCell i x := rfl

theorem readCell_writeCell (i v x : Object) : readCell i (writeCell i v x) = v :=
  Proofs.Logic.ACL2.Standard.FixedLayout.readCell_writeCell i v x

theorem readOtherCell_writeCell (i j : Object) (h : i.natRank ≠ j.natRank) (v x : Object) :
    readCell i (writeCell j v x) = readCell i x :=
  Proofs.Logic.ACL2.Standard.FixedLayout.readOtherCell_writeCell i j h v x

theorem writeScalar_preserves (x : Object) (h : recognizes x = true) (v : Int) :
    recognizes (writeScalar (integer v) x) = true :=
  Proofs.Logic.ACL2.Standard.FixedLayout.writeScalar_preserves x h v

theorem writeCell_preserves (x : Object) (h : recognizes x = true) (i : Nat) (bound : i < 3) (v : Int) :
    recognizes (writeCell (integer i) (integer v) x) = true :=
  Proofs.Logic.ACL2.Standard.FixedLayout.writeCell_preserves x h i bound v

end Silmaril.Logic.ACL2.Standard.FixedLayout.Toy
