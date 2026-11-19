module

public import Silmaril.Formats.Json.Fast.Defs
import Silmaril.Prelude.ChunkSeq.Thms
import Init.Data.Array.Find
import Init.Data.List.Nat.TakeDrop

public section
namespace Silmaril.Proofs.Json.Fast

open Silmaril.Formats.Json.Fast

private theorem selected {entries : ChunkSeq (String × Value)} {key : String} {value : Value}
    (matchFound : entries.findSome? (fun (name, child) => if name == key then some child else none) =
      some value) : (key, value) ∈ entries.toList := by
  rw [ChunkSeq.findSome?_eq] at matchFound
  obtain ⟨⟨name, child⟩, mem, found⟩ := List.exists_of_findSome?_eq_some matchFound
  by_cases equal : name = key
  · have : child = value := by simpa [equal] using found
    simpa [equal, this] using mem
  · simp [equal] at found

theorem member?_sound {entries : ChunkSeq (String × Value)} {index : Option KeyIndex}
    {key : String} {value : Value} (wellSized : entries.WellSized)
    (found : (Value.object entries index).member? key = some value) : (key, value) ∈ entries.toList := by
  cases index with
  | none => exact selected found
  | some index =>
    unfold Value.member? at found
    cases buckets : index.find? (keyHash key) with
    | none => simp [buckets] at found
    | some positions =>
      simp only [buckets] at found
      obtain ⟨pos, _, atPos⟩ := Array.exists_of_findSome?_eq_some found
      rw [ChunkSeq.get?_eq entries wellSized] at atPos
      cases lookup : entries.toList[pos]? with
      | none => simp [lookup] at atPos
      | some entry =>
        have inList := List.mem_of_getElem? lookup
        obtain ⟨name, child⟩ := entry
        by_cases equal : name = key
        · have : child = value := by simpa [lookup, equal] using atPos
          simpa [equal, this] using inList
        · simp [lookup, equal] at atPos

end Silmaril.Proofs.Json.Fast
