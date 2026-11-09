module

public import Silmaril.Formats.Compression.Zlib.DictionaryHistory
public import Silmaril.Raw.Formats.Compression.Zlib.Dictionary

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Zlib.DictionaryHistory`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.ZlibDictionaryHistory

open ZlibDictionary

theorem installedHistory_length (retained dictionary : List UInt8) :
    (installedHistory retained dictionary).length ≤ 32768 :=
  history_length _

theorem installedHistory_suffix (retained dictionary : List UInt8) :
    installedHistory retained dictionary <:+ retained ++ dictionary :=
  history_suffix _

theorem installedHistory_empty (dictionary : List UInt8) :
    installedHistory [] dictionary = history dictionary := rfl

theorem installedHistory_of_short (retained dictionary : List UInt8)
    (h : retained.length + dictionary.length ≤ 32768) :
    installedHistory retained dictionary = retained ++ dictionary :=
  history_of_short _ (by simpa only [List.length_append] using h)

theorem installedHistory_of_large_dictionary (retained dictionary : List UInt8)
    (h : 32768 ≤ dictionary.length) :
    installedHistory retained dictionary = history dictionary := by
  unfold installedHistory history
  have hindex : retained.length + dictionary.length - 32768 =
      retained.length + (dictionary.length - 32768) := by omega
  rw [List.length_append, hindex, List.drop_length_add_append]

/-- The original dictionary specification is precisely the empty-history case. -/
theorem takeWithRetainedHistory_empty (dictionary input : List UInt8) :
    takeWithRetainedHistory [] dictionary input = takeWithDictionary dictionary input := by
  simp only [takeWithRetainedHistory, takeWithDictionary, installedHistory_empty]
  rfl

theorem takeWithRetainedHistory_noDictionary (retained dictionary input body : List UInt8)
    (header : Header) (hheader : checkHeader input = some (header, body))
    (hfree : header.dictionaryID = none) :
    takeWithRetainedHistory retained dictionary input = zlibTake input := by
  rw [← takeWithDictionary_noDictionary dictionary input body header hheader hfree]
  simp only [takeWithRetainedHistory, takeWithDictionary, hheader, Option.bind_some, hfree]

/-- Identifier validation remains a check of the newly supplied full bytes,
regardless of earlier history or how much of the new dictionary is retained. -/
theorem takeWithRetainedHistory_wrong_dictionary (retained dictionary offered body : List UInt8)
    (hwrong : dictionaryChecksum offered ≠ dictionaryChecksum dictionary) :
    takeWithRetainedHistory retained offered
      ([0x78, 0x20] ++ be32Bytes (dictionaryChecksum dictionary) ++ body) = none := by
  rw [takeWithRetainedHistory, checkHeader_dictionary]
  simp only [Option.bind_some]
  rw [ite_eq_right (fun h => hwrong h.2)]

theorem takeWithRetainedHistory_storedBytes (retained dictionary data tail : List UInt8) :
    takeWithRetainedHistory retained dictionary
      ([0x78, 0x20] ++ be32Bytes (dictionaryChecksum dictionary) ++
        (Deflate.storedBytes data ++ ((zlibTrailer ⟨data.toArray⟩).data.toList ++ tail))) =
      some (data, tail) := by
  rw [takeWithRetainedHistory, checkHeader_dictionary]
  simp only [Option.bind_some]
  rw [ite_eq_left ⟨rfl, trivial⟩, Deflate.deflateTakeWithHistory_storedBytes]
  simp only [finish]
  rw [zlibCheckTrailer_zlibTrailer_append ⟨data.toArray⟩ tail]
  rfl

/-- Two successful short installations append, rather than replace, history. -/
theorem repeated_AB_history :
    installedHistory (installedHistory [] [65, 66]) [65, 66] = [65, 66, 65, 66] := by
  decide

theorem repeated_AB_is_not_replacement :
    installedHistory (installedHistory [] [65, 66]) [65, 66] ≠ history [65, 66] := by
  decide

end Silmaril.Formats.Compression.ZlibDictionaryHistory
