module

public import Silmaril.Formats.JsonWithBytes.Chunked.Defs
import Silmaril.Proofs.Formats.JsonWithBytes.Chunked.Lowering

public section
namespace Silmaril.Formats.JsonWithBytes.Chunked.Canonical

variable {Number : Type} [SizeOf Number]

theorem toSimple_ofArray (items : List (Canonical Number)) :
    (ofArray items).toSimple = .list (RawSyn.ofList (items.map toSimple)) :=
  Proofs.Formats.JsonWithBytes.Chunked.Lowering.toSimple_ofArray items

theorem toSimple_ofObject (entries : List (String × Canonical Number)) :
    (ofObject entries).toSimple = .map (RawSyn.ofEntries (entries.map (fun entry => (entry.1, entry.2.toSimple)))) :=
  Proofs.Formats.JsonWithBytes.Chunked.Lowering.toSimple_ofObject entries

theorem index_ofSimple (items : RawSyn String (Scalar Number) .arr) (index : Nat) :
    (ofSimple (.list items)).val.index? index = items.toList[index]?.map TreeValue.ofSimple :=
  Proofs.Formats.JsonWithBytes.Chunked.Lowering.index_ofSimple items index

theorem entry_ofSimple (entries : RawSyn String (Scalar Number) .obj) (index : Nat) :
    (ofSimple (.map entries)).val.entry? index =
      entries.toEntries[index]?.map (fun entry => (entry.1, TreeValue.ofSimple entry.2)) :=
  Proofs.Formats.JsonWithBytes.Chunked.Lowering.entry_ofSimple entries index

/-- Direct lowering agrees with the ordered, cache-free view, including depth failure. -/
theorem toSimple_fromFast (depth : Nat) (value : Json.Fast.Value) :
    (fromFast? depth value).map toSimple = orderedView? depth value :=
  Proofs.Formats.JsonWithBytes.Chunked.Lowering.toSimple_fromFast depth value

end Silmaril.Formats.JsonWithBytes.Chunked.Canonical
