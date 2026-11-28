module

public import Silmaril.Logic.ACL2.Standard.FixedLayout.Schema.Fixtures
public import Silmaril.Logic.ACL2.Standard.FixedLayout.Schema.Thms

@[expose] public section

namespace Silmaril.Proofs.Logic.ACL2.Standard.FixedLayout.SchemaFixtures

open Silmaril.Logic.ACL2.Standard
open Silmaril.Logic.ACL2.Standard.FixedLayout
open Silmaril.Logic.ACL2.Standard.FixedLayout.Schema.Fixtures
open Object

theorem silToy_initial : SilToy.initial = Schema.initial SilToy.layout := by decide +kernel

theorem silToy_recognizer (x : Object) :
    SilToy.recognizer x = Schema.recognizer SilToy.layout x := by
  have source : SilToy.recognizer x = Source.recognizer x := rfl
  rw [source, ← Toy.recognizer_source]
  simp [Toy.recognizer, Toy.recognizes, Schema.recognizer, Schema.recognizes,
    SilToy.layout, Schema.fieldsAccept, Schema.Slot.accepts, Bool.and_assoc]

/-- All generated field declarations, including the constant length and identity resize. -/
theorem silToy_fields :
    (∀ x, SilToy.slot0Recognizer x = ofBool x.integerp) ∧
    (∀ x, SilToy.slot1Recognizer Schema.integerListP x = Schema.integerListP x) ∧
    (∀ x, SilToy.slot0Read x = readAt 0 x) ∧
    (∀ v x, SilToy.slot0Write v x = writeAt 0 v x) ∧
    (∀ x, SilToy.slot1Length x = integer 3) ∧
    (∀ i x, SilToy.slot1Resize i x = x) ∧
    (∀ i x, SilToy.slot1Read i x = Schema.readCell 1 i x) ∧
    (∀ i v x, SilToy.slot1Write i v x = Schema.writeCell 1 i v x) :=
  ⟨fun _ => rfl, Schema.integerListP_source, Schema.readAt_source 0, Schema.writeAt_source 0,
    fun _ => rfl, fun _ _ => rfl, Schema.readCell_source 1, Schema.writeCell_source 1⟩

theorem silShelves_initial : SilShelves.initial = Schema.initial SilShelves.layout := by decide +kernel

theorem silShelves_recognizer (x : Object) :
    SilShelves.recognizer x = Schema.recognizer SilShelves.layout x := by
  unfold SilShelves.recognizer
  by_cases proper : x.trueListp = true
  · rw [Source.length_of_trueListp x proper]
    have length1 (y : Object) : y.len.equal (integer 1) = ofBool (decide (y.spineLength = 1)) :=
      Source.len_equal y 1
    have length2 (y : Object) : y.len.equal (integer 2) = ofBool (decide (y.spineLength = 2)) :=
      Source.len_equal y 2
    have length3 (y : Object) : y.len.equal (integer 3) = ofBool (decide (y.spineLength = 3)) :=
      Source.len_equal y 3
    have read0 (y : Object) : (integer 0).mvNth y = readAt 0 y := Schema.readAt_source 0 y
    have read1 (y : Object) : (integer 1).mvNth y = readAt 1 y := Schema.readAt_source 1 y
    have read2 (y : Object) : (integer 2).mvNth y = readAt 2 y := Schema.readAt_source 2 y
    simp only [Source.numericEqual, length1, length2, length3, read0, read1, read2,
      Schema.integerListP, SilShelves.slot1Recognizer, Source.testLast, Source.testAnd,
      Schema.recognizer, Schema.recognizes, SilShelves.layout, Schema.fieldsAccept,
      Schema.Slot.accepts, readAt, Bool.and_assoc, Bool.and_true]
    rfl
  · simp [proper, ofBool, Schema.recognizer, Schema.recognizes]

theorem silShelves_fields :
    (∀ x, SilShelves.slot0Recognizer Schema.integerListP x = Schema.integerListP x) ∧
    (∀ x, SilShelves.slot1Recognizer x = ofBool x.integerp) ∧
    (∀ x, SilShelves.slot2Recognizer Schema.integerListP x = Schema.integerListP x) ∧
    (∀ x, SilShelves.slot0Length x = integer 2) ∧
    (∀ i x, SilShelves.slot0Resize i x = x) ∧
    (∀ i x, SilShelves.slot0Read i x = Schema.readCell 0 i x) ∧
    (∀ i v x, SilShelves.slot0Write i v x = Schema.writeCell 0 i v x) ∧
    (∀ x, SilShelves.slot1Read x = readAt 1 x) ∧
    (∀ v x, SilShelves.slot1Write v x = writeAt 1 v x) ∧
    (∀ x, SilShelves.slot2Length x = integer 1) ∧
    (∀ i x, SilShelves.slot2Resize i x = x) ∧
    (∀ i x, SilShelves.slot2Read i x = Schema.readCell 2 i x) ∧
    (∀ i v x, SilShelves.slot2Write i v x = Schema.writeCell 2 i v x) :=
  ⟨Schema.integerListP_source, fun _ => rfl, Schema.integerListP_source, fun _ => rfl, fun _ _ => rfl,
    Schema.readCell_source 0, Schema.writeCell_source 0, Schema.readAt_source 1, Schema.writeAt_source 1,
    fun _ => rfl, fun _ _ => rfl, Schema.readCell_source 2, Schema.writeCell_source 2⟩

end Silmaril.Proofs.Logic.ACL2.Standard.FixedLayout.SchemaFixtures
