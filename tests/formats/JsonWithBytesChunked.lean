module

import Silmaril.Formats.JsonWithBytes.Chunked.Thms
import Silmaril.Formats.Json.Fast.Elab

open Silmaril.Formats
open Silmaril.Formats.JsonWithBytes.Chunked

private theorem scalar_view {Number : Type} [SizeOf Number] (value : JsonWithBytes.Scalar Number) :
    (Canonical.scalar value).toSimple = .scalar value := Canonical.equiv.right_inv _

example :
    let value : Canonical Int64 := Canonical.ofArray [Canonical.scalar (.bytes [0, 255])]
    value.val.index? 0 = some (.scalar (.bytes [0, 255])) ∧
    (value.val.index? 1).isNone = true := ⟨rfl, rfl⟩

def sourceResult : Except Json.Fast.Error Json.Fast.Value :=
  json% r#"{"z":-0e-7,"\ud83d\ude00":1.20,"\u007a":[true,null]}"#

def lowered := sourceResult.toOption.bind (Canonical.fromFast? 2)

private theorem lowered_layout : lowered = some (Canonical.ofObject
    [("z", Canonical.scalar (.number ⟨true, 0, -7⟩)), ("😀", Canonical.scalar (.number ⟨false, 120, -2⟩)),
      ("z", Canonical.ofArray [Canonical.scalar (.bool true), Canonical.scalar .null])]) := rfl

example : lowered.map Canonical.toSimple = some (.map
    (.objCons "z" (.scalar (.number ⟨true, 0, -7⟩))
    (.objCons "😀" (.scalar (.number ⟨false, 120, -2⟩))
    (.objCons "z" (.list (.cons (.scalar (.bool true)) (.cons (.scalar .null) .nil))) .objNil)))) := by
  rw [lowered_layout, Option.map_some, Canonical.toSimple_ofObject]
  simp [Canonical.toSimple_ofArray, scalar_view]

example : (sourceResult.toOption.bind (Canonical.fromFast? 1)).isNone = true := rfl

example : lowered.map (fun value => value.toUnordered.isOk) = some false := by
  rw [lowered_layout, Option.map_some, Canonical.toUnordered, Canonical.toSimple_ofObject]
  simp only [List.map_cons, List.map_nil, scalar_view, Canonical.toSimple_ofArray]
  unfold RawSyn.validate
  split
  · rfl
  · rename_i witness
    simp [RawSyn.dupWitness?, RawSyn.ofEntries, firstDup?] at witness

#print axioms Canonical.equiv
#print axioms Canonical.index_ofSimple
#print axioms Canonical.entry_ofSimple
#print axioms Canonical.toSimple_fromFast
