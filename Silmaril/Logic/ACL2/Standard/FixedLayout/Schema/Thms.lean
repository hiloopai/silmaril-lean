module

public import Silmaril.Logic.ACL2.Standard.FixedLayout.Schema.Defs
public import Silmaril.Logic.ACL2.Standard.FixedLayout.Thms
import Silmaril.Proofs.Logic.ACL2.Standard.FixedLayout.Schema

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard.FixedLayout.Schema

open Object

theorem recognizes_nil (x : Object) : recognizes [] x = true ↔ x = nil :=
  Proofs.Logic.ACL2.Standard.FixedLayout.Schema.recognizes_nil x

/-- An accepted nonempty layout has one accepted value followed by the accepted remaining slots. -/
theorem recognizes_cons_iff (slot : Slot) (layout : List Slot) (x : Object) :
    recognizes (slot :: layout) x = true ↔
      ∃ head tail, x = cons head tail ∧ slot.accepts head = true ∧ recognizes layout tail = true :=
  Proofs.Logic.ACL2.Standard.FixedLayout.Schema.recognizes_cons_iff slot layout x

theorem initial_recognized (layout : List Slot) : recognizes layout (initial layout) = true :=
  Proofs.Logic.ACL2.Standard.FixedLayout.Schema.initial_recognized layout

theorem read_initial (layout : List Slot) (i : Nat) {slot : Slot}
    (h : layout[i]? = some slot) : readAt i (initial layout) = slot.initialObject :=
  Proofs.Logic.ACL2.Standard.FixedLayout.Schema.read_initial layout i h

theorem readCell_initial (layout : List Slot) (i : Nat) (index : Object) {size : Nat} {n : Int}
    (h : layout[i]? = some (.array size n)) (bound : index.natRank < size) :
    readCell i index (initial layout) = integer n :=
  Proofs.Logic.ACL2.Standard.FixedLayout.Schema.readCell_initial layout i index h bound

theorem read_accepts (layout : List Slot) (i : Nat) {slot : Slot} (h : layout[i]? = some slot)
    {x : Object} (valid : recognizes layout x = true) : slot.accepts (readAt i x) = true :=
  Proofs.Logic.ACL2.Standard.FixedLayout.Schema.read_accepts layout i h valid

theorem write_preserves (layout : List Slot) (i : Nat) {slot : Slot} (h : layout[i]? = some slot)
    {x v : Object} (valid : recognizes layout x = true) (accepts : slot.accepts v = true) :
    recognizes layout (writeAt i v x) = true :=
  Proofs.Logic.ACL2.Standard.FixedLayout.Schema.write_preserves layout i h valid accepts

theorem writeScalar_preserves (layout : List Slot) (i : Nat) {n : Int}
    (h : layout[i]? = some (.scalar n)) {x : Object} (valid : recognizes layout x = true) (v : Int) :
    recognizes layout (writeAt i (integer v) x) = true :=
  write_preserves layout i h valid (integerp_integer v)

theorem writeCell_preserves (layout : List Slot) (i : Nat) (index : Object) {size : Nat} {n : Int}
    (h : layout[i]? = some (.array size n)) (bound : index.natRank < size)
    {x : Object} (valid : recognizes layout x = true) (v : Int) :
    recognizes layout (writeCell i index (integer v) x) = true :=
  Proofs.Logic.ACL2.Standard.FixedLayout.Schema.writeCell_preserves layout i index h bound valid v

theorem readCell_writeCell (i : Nat) (index v x : Object) :
    readCell i index (writeCell i index v x) = v :=
  Proofs.Logic.ACL2.Standard.FixedLayout.Schema.readCell_writeCell i index v x

theorem readOtherCell_writeCell (i : Nat) (index key v x : Object)
    (h : index.natRank ≠ key.natRank) :
    readCell i index (writeCell i key v x) = readCell i index x :=
  Proofs.Logic.ACL2.Standard.FixedLayout.Schema.readOtherCell_writeCell i index key v x h

theorem readAt_writeCell_other (i j : Nat) (h : i ≠ j) (key v x : Object) :
    readAt i (writeCell j key v x) = readAt i x :=
  Proofs.Logic.ACL2.Standard.FixedLayout.Schema.readAt_writeCell_other i j h key v x

theorem readAt_source (i : Nat) (x : Object) : (integer i).mvNth x = readAt i x := by
  rw [mvNth_eq_readAt, natRank_integer, Int.toNat_natCast]

theorem writeAt_source (i : Nat) (value x : Object) :
    updateNth (integer i) value x = writeAt i value x := by
  rw [updateNth, natRank_integer, Int.toNat_natCast]

theorem readCell_source (i : Nat) (index x : Object) :
    index.mvNth ((integer i).mvNth x) = readCell i index x := by
  rw [readCell, readAt_source]

theorem writeCell_source (i : Nat) (index value x : Object) :
    Source.updateNthArray (integer i) index value x = writeCell i index value x := by
  rw [Source.updateNthArray, writeAt_source, readAt_source, writeCell]

theorem integerListP_source (x : Object) : Source.cellsPBody integerListP x = integerListP x :=
  (Toy.cellsP_source x).symm

end Silmaril.Logic.ACL2.Standard.FixedLayout.Schema
