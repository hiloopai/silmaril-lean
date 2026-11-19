module

public import Silmaril.Formats.Json.Fast
import Silmaril.Prelude.ChunkSeq.Thms
import Silmaril.Proofs.Formats.Json.Fast.Lookup

public section
namespace Silmaril.Formats.Json.Fast

theorem parseBytes_toUTF8 (text : String) (limits : Limits) :
    parseBytes text.toUTF8 limits = parseText text limits := by
  cases text
  simp [parseBytes, String.fromUTF8?, *]

theorem Value.index?_ofArray (items : Array Value) (pos : Nat) :
    (Value.ofArray items).index? pos = items[pos]? := by
  simpa [Value.ofArray, Value.index?, ChunkSeq.toList_ofArray] using
    (ChunkSeq.get?_eq _ (ChunkSeq.wellSized_ofArray items) pos)

theorem Value.entries?_ofObject (items : Array (String × Value)) :
    ((Value.ofObject items).entries?.map ChunkSeq.toList) = some items.toList := by
  simp [Value.ofObject, Value.entries?, ChunkSeq.toList_ofArray]

/-- Even a manually supplied index cannot return a value under the wrong key. This is a
soundness claim, not a completeness or first-occurrence theorem for arbitrary indexes. -/
theorem Value.member?_sound {entries : ChunkSeq (String × Value)} {index : Option KeyIndex}
    {key : String} {value : Value} (wellSized : entries.WellSized)
    (found : (Value.object entries index).member? key = some value) : (key, value) ∈ entries.toList :=
  Proofs.Json.Fast.member?_sound wellSized found

end Silmaril.Formats.Json.Fast
