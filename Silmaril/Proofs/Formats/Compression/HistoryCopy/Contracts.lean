module

public import Silmaril.Formats.Compression.HistoryCopy.Defs

public section

namespace Silmaril.Proofs.Formats.Compression.HistoryCopy

open Silmaril.Formats.Compression.HistoryCopy

theorem copy_sound {distance : Nat} (positive : 0 < distance) (count : Nat)
    (data : Array UInt8) (available : distance ≤ data.size) :
    ∃ bytes, (copy distance positive count data available).toList = data.toList ++ bytes ∧
      bytes.length = count ∧ Wire distance data.toList bytes := by
  induction count generalizing data with
  | zero => exact ⟨[], by simp [copy], rfl, .nil _⟩
  | succ count ih =>
    have index : data.size - distance < data.size := by omega
    let byte := data[data.size - distance]
    have more : distance ≤ (data.push byte).size := by simp; omega
    obtain ⟨bytes, shape, length, wire⟩ := ih (data.push byte) more
    have lookup : data.toList[data.toList.length - distance]? = some byte := by
      simp [byte, index, getElem?_pos]
    refine ⟨byte :: bytes, ?_, by simp [length], .cons positive (by simpa) lookup ?_⟩
    · simpa [copy, byte, List.append_assoc] using shape
    · simpa using wire

theorem Wire.byte_at {distance : Nat} {history bytes : List UInt8} (wire : Wire distance history bytes)
    {index : Nat} (bound : index < bytes.length) :
    bytes[index]? = (history ++ bytes.take index)[history.length + index - distance]? := by
  induction wire generalizing index with
  | nil => simp at bound
  | @cons history bytes byte _ _ found _ ih =>
    cases index with
    | zero => simpa using found.symm
    | succ index =>
      have within : index < bytes.length := by simpa using bound
      have atIndex := ih within
      have position : (history ++ [byte]).length + index = history.length + (index + 1) := by
        simp only [List.length_append, List.length_singleton]
        omega
      simpa only [position, List.getElem?_cons_succ, List.take_succ_cons, List.append_assoc,
        List.singleton_append] using atIndex

end Silmaril.Proofs.Formats.Compression.HistoryCopy
