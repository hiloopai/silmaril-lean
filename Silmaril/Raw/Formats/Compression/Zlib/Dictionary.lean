module

public import Silmaril.Formats.Compression.Zlib.Dictionary
public import Silmaril.Raw.Formats.Compression.Zlib.Take
public import Silmaril.Raw.Formats.Compression.Deflate.WithHistory

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Zlib.Dictionary`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.ZlibDictionary

theorem history_length (dictionary : List UInt8) : (history dictionary).length ≤ 32768 := by
  simp only [history, List.length_drop]
  omega

theorem history_suffix (dictionary : List UInt8) : history dictionary <:+ dictionary :=
  List.drop_suffix _ _

theorem history_of_short (dictionary : List UInt8) (h : dictionary.length ≤ 32768) :
    history dictionary = dictionary := by
  simp only [history, Nat.sub_eq_zero_of_le h, List.drop_zero]

theorem history_append_window (before window : List UInt8) (h : window.length = 32768) :
    history (before ++ window) = window := by
  simp only [history, List.length_append, h, Nat.add_sub_cancel_right, List.drop_left]

/-- Forgetting dictionary-bearing headers recovers exactly the existing
dictionary-free header checker, including all invalid and truncated cases. -/
theorem checkHeader_noDictionary (input : List UInt8) :
    (checkHeader input).bind (fun pair =>
      match pair.1.dictionaryID with
      | none => some pair.2
      | some _ => none) = zlibCheckHeader input := by
  match input with
  | [] | [_] => rfl
  | cmf :: flg :: rest =>
    simp only [checkHeader, zlibCheckHeader]
    by_cases hbase : cmf &&& 0x0F = 8 ∧ cmf.toNat / 16 ≤ 7 ∧
        (cmf.toNat * 256 + flg.toNat) % 31 = 0
    · rw [ite_eq_left hbase]
      by_cases hfree : flg &&& 0x20 = 0
      · rw [ite_eq_left hfree]
        simp only [Option.bind_some]
        rw [ite_eq_left ⟨hbase.1, hbase.2.1, hbase.2.2, hfree⟩]
      · rw [ite_eq_right hfree]
        rw [ite_eq_right (fun h => hfree h.2.2.2)]
        cases rest with
        | nil => rfl
        | cons d0 rest =>
          cases rest with
          | nil => rfl
          | cons d1 rest =>
            cases rest with
            | nil => rfl
            | cons d2 rest => cases rest <;> rfl
    · rw [ite_eq_right hbase]
      rw [ite_eq_right (fun h => hbase ⟨h.1, h.2.1, h.2.2.1⟩)]
      rfl

theorem checkHeader_windowBits (input body : List UInt8) (header : Header)
    (h : checkHeader input = some (header, body)) :
    8 ≤ header.windowBits ∧ header.windowBits ≤ 15 := by
  match input with
  | [] | [_] => cases h
  | cmf :: flg :: rest =>
    simp only [checkHeader] at h
    split at h
    · rename_i hbase
      split at h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        dsimp only
        omega
      · split at h
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          dsimp only
          omega
        · cases h
    · cases h

theorem zlibCheckHeader_of_noDictionary (input body : List UInt8) (header : Header)
    (hheader : checkHeader input = some (header, body)) (hfree : header.dictionaryID = none) :
    zlibCheckHeader input = some body := by
  rw [← checkHeader_noDictionary, hheader]
  simp only [Option.bind_some, hfree]

/-- Complete arbitrary-input agreement on the dictionary-free header profile,
with every checksum failure and suffix observation retained. -/
theorem takeWithDictionary_noDictionary (dictionary input body : List UInt8) (header : Header)
    (hheader : checkHeader input = some (header, body)) (hfree : header.dictionaryID = none) :
    takeWithDictionary dictionary input = zlibTake input := by
  rw [takeWithDictionary, hheader]
  simp only [Option.bind_some, hfree]
  rw [zlibTake, zlibCheckHeader_of_noDictionary input body header hheader hfree]
  dsimp only
  cases Deflate.deflateTake body with
  | error _ => rfl
  | ok pair =>
    obtain ⟨data, rest⟩ := pair
    unfold finish
    dsimp only
    cases zlibCheckTrailer data rest <;> rfl

theorem takeWithDictionary_ignores_offered (first second input body : List UInt8) (header : Header)
    (hheader : checkHeader input = some (header, body)) (hfree : header.dictionaryID = none) :
    takeWithDictionary first input = takeWithDictionary second input :=
  (takeWithDictionary_noDictionary first input body header hheader hfree).trans
    (takeWithDictionary_noDictionary second input body header hheader hfree).symm

/-- If the parsed header does not request a dictionary, even offered
dictionary bytes that are unrelated to the output have no effect. Invalid
header parses are included: both member specifications reject them. -/
theorem takeWithDictionary_eq_zlibTake (dictionary input : List UInt8)
    (hfree : ∀ header body, checkHeader input = some (header, body) → header.dictionaryID = none) :
    takeWithDictionary dictionary input = zlibTake input := by
  cases hheader : checkHeader input with
  | none =>
    have hold : zlibCheckHeader input = none := by
      rw [← checkHeader_noDictionary, hheader]
      rfl
    simp only [takeWithDictionary, hheader, Option.bind_none, zlibTake, hold]
  | some pair =>
    obtain ⟨header, body⟩ := pair
    exact takeWithDictionary_noDictionary dictionary input body header hheader (hfree header body hheader)

theorem checkHeader_dictionary (dictionary body : List UInt8) :
    checkHeader ([0x78, 0x20] ++ be32Bytes (dictionaryChecksum dictionary) ++ body) =
      some (⟨15, some (dictionaryChecksum dictionary)⟩, body) := by
  simp only [List.cons_append, List.nil_append, checkHeader, be32Bytes]
  rw [ite_eq_left (by decide), ite_eq_right (by decide), be32Val_be32Bytes]
  have hbound : dictionaryChecksum dictionary < 4294967296 :=
    (adler32 ⟨dictionary.toArray⟩).toNat_lt_size
  rw [Nat.mod_eq_of_lt hbound]
  rfl

/-- A wrong dictionary checksum rejects before raw decoding, regardless of
the body. This does not assert that equal identifiers imply equal dictionaries. -/
theorem takeWithDictionary_wrong_dictionary (dictionary offered body : List UInt8)
    (hwrong : dictionaryChecksum offered ≠ dictionaryChecksum dictionary) :
    takeWithDictionary offered ([0x78, 0x20] ++ be32Bytes (dictionaryChecksum dictionary) ++ body) =
      none := by
  rw [takeWithDictionary, checkHeader_dictionary]
  simp only [Option.bind_some]
  rw [ite_eq_right (fun h => hwrong h.2)]

/-- Stored data works with every dictionary, checks the full DICTID and the
data-only Adler trailer, and leaves an arbitrary following suffix intact. -/
theorem takeWithDictionary_storedBytes (dictionary data tail : List UInt8) :
    takeWithDictionary dictionary
      ([0x78, 0x20] ++ be32Bytes (dictionaryChecksum dictionary) ++
        (Deflate.storedBytes data ++ ((zlibTrailer ⟨data.toArray⟩).data.toList ++ tail))) =
      some (data, tail) := by
  rw [takeWithDictionary, checkHeader_dictionary]
  simp only [Option.bind_some]
  rw [ite_eq_left ⟨rfl, trivial⟩, Deflate.deflateTakeWithHistory_storedBytes]
  simp only [finish]
  have htrailer := zlibCheckTrailer_zlibTrailer_append ⟨data.toArray⟩ tail
  rw [htrailer]
  rfl

/-! A real back-reference consumes the supplied "AB" dictionary history and
then overlaps newly produced output. The emitted "ABABAB" alone determines
the trailer. A different supplied dictionary fails the independent DICTID. -/

set_option maxRecDepth 8192 in
theorem dictionary_match_checked :
    takeWithDictionary [65, 66]
      [120, 32, 0, 198, 0, 132, 115, 4, 67, 0, 5, 100, 1, 138, 170] =
        some ([65, 66, 65, 66, 65, 66], [170]) := by
  decide

theorem wrong_dictionary_rejected :
    takeWithDictionary [65, 67]
      [120, 32, 0, 198, 0, 132, 115, 4, 67, 0, 5, 100, 1, 138, 170] = none := by
  decide

theorem truncated_dictionaryID_rejected : checkHeader [120, 32, 0, 198, 0] = none := by
  decide

/-- A smaller dictionary window is parsed honestly as metadata; this does not
silently turn it into the fixed 32 KiB dictionary profile. -/
theorem small_dictionary_window_metadata (body : List UInt8) :
    checkHeader ([104, 36, 0, 198, 0, 132] ++ body) =
      some (⟨14, some 0x00c60084⟩, body) := by
  rfl

theorem small_dictionary_profile_rejected (body : List UInt8) :
    takeWithDictionary [65, 66] ([104, 36, 0, 198, 0, 132] ++ body) = none := by
  rfl

end Silmaril.Formats.Compression.ZlibDictionary
