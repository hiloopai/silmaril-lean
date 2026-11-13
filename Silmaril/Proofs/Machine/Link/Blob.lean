module

public import Silmaril.Machine.Link.Blob.Defs

/-! # The blob readers are the public readers

Each fast reader of `Silmaril.Machine.Link.Blob.Defs` equals the public certified
reader applied to `bytesOf n len`:

* `readLE_bytesOf`: one little-endian field is one shift and one modulus;
* `readHeader_bytesOf`, `readProgramHeaders_bytesOf`, `readSectionHeaders_bytesOf`,
  `sectionData_bytesOf`;
* `readObject_bytesOf : readObject (bytesOf n len) = readObjectN n len`;
* `parse_bytesOf : ELFImage.parse policy (bytesOf n len) = parseN policy n len`;
* `bytes_ofBytes`: every byte array is the denotation of a blob.
-/

@[expose] public section

namespace Silmaril.Machine.Link.Blob

open Silmaril.Formats.ELF
open Silmaril.Process.LPS

theorem toList_bytesOf (n len : Nat) :
    (bytesOf n len).toList = (List.range len).map (byteAt n) := by
  simp [bytesOf]

@[simp] theorem size_bytesOf (n len : Nat) : (bytesOf n len).size = len := by
  simp [bytesOf]

theorem getElem?_bytesOf (n len i : Nat) :
    (bytesOf n len).toList[i]? = if i < len then some (byteAt n i) else none := by
  rw [toList_bytesOf]
  split <;> simp_all

theorem byteAt_toNat (n i : Nat) : (byteAt n i).toNat = (n >>> (8 * i)) % 256 := by
  simp [byteAt, BitVec.toNat_ofNat]

theorem byteAt_shift (n a i : Nat) : byteAt (n >>> (8 * a)) i = byteAt n (a + i) := by
  simp only [byteAt, ← Nat.shiftRight_add, Nat.mul_add]

theorem readLE_bytesOf (n len off w : Nat) :
    readLE (bytesOf n len) off w = readLEN n len off w := by
  induction w generalizing off with
  | zero => simp [readLE, readLEN, Nat.mod_one]
  | succ w ih =>
    simp only [readLE, getElem?_bytesOf, ih]
    by_cases hoff : off < len
    · simp only [hoff, ite_true, readLEN]
      by_cases hw : w = 0 ∨ off + 1 + w ≤ len
      · have hw' : w + 1 = 0 ∨ off + (w + 1) ≤ len := by omega
        simp only [hw, hw', ite_true, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          byteAt_toNat]
        congr 1
        have hpow : 2 ^ (8 * (w + 1)) = 256 * 2 ^ (8 * w) := by
          rw [Nat.mul_add, Nat.pow_add, Nat.mul_comm]
        rw [hpow, Nat.mod_mul]
        congr 2
        rw [Nat.mul_add, Nat.mul_one, Nat.shiftRight_add, Nat.shiftRight_eq_div_pow]
      · have hw' : ¬ (w + 1 = 0 ∨ off + (w + 1) ≤ len) := by omega
        simp [hw]; omega
    · have hw' : ¬ (w + 1 = 0 ∨ off + (w + 1) ≤ len) := by omega
      simp [hoff, readLEN]; omega

theorem readHeader_bytesOf (n len : Nat) : readHeader (bytesOf n len) = readHeaderN n len := by
  simp only [readHeader, readHeaderN, readLE_bytesOf, size_bytesOf]

theorem readSectionHeader_bytesOf (n len : Nat) :
    readSectionHeader (bytesOf n len) = readSectionHeaderN n len := by
  funext offset
  simp only [readSectionHeader, readSectionHeaderN, readLE_bytesOf]

theorem readProgramHeader_bytesOf (n len : Nat) :
    readProgramHeader (bytesOf n len) = readProgramHeaderN n len := by
  funext offset
  simp only [readProgramHeader, readProgramHeaderN, readLE_bytesOf]

theorem readSymbol_bytesOf (n len offset : Nat) :
    readSymbol (bytesOf n len) offset = readSymbolN n len offset := by
  simp only [readSymbol, readSymbolN, readLE_bytesOf]

theorem readRela_bytesOf (n len offset : Nat) :
    readRela (bytesOf n len) offset = readRelaN n len offset := by
  simp only [readRela, readRelaN, readLE_bytesOf]

theorem readTable_bytesOf {R : Type} (reader : Bytes → Nat → Option R) (n len off w c : Nat) :
    readTable reader (bytesOf n len) off w c = readTableN (reader (bytesOf n len)) len off w c := by
  simp only [readTable, readTableN, size_bytesOf]

theorem readSectionHeaders_bytesOf (n len : Nat) (header : Header) :
    readSectionHeaders (bytesOf n len) header = readSectionHeadersN n len header := by
  simp only [readSectionHeaders, readSectionHeadersN, readTable_bytesOf,
    readSectionHeader_bytesOf]

theorem readProgramHeaders_bytesOf (n len : Nat) (header : Header) :
    readProgramHeaders (bytesOf n len) header = readProgramHeadersN n len header := by
  simp only [readProgramHeaders, readProgramHeadersN, readTable_bytesOf,
    readProgramHeader_bytesOf]

/-- A file slice of a blob is the blob shifted to the slice start. -/
theorem slice_bytesOf {n len off sz : Nat} (h : off + sz ≤ len) :
    (((bytesOf n len).toList.drop off).take sz) = (bytesOf (n >>> (8 * off)) sz).toList := by
  apply List.ext_getElem?
  intro i
  rw [getElem?_bytesOf, List.getElem?_take, List.getElem?_drop, getElem?_bytesOf, byteAt_shift]
  by_cases hi : i < sz
  · have : off + i < len := by omega
    simp [hi, this]
  · simp [hi]

theorem sectionData_bytesOf (n len : Nat) (part : SectionHeader) :
    sectionData (bytesOf n len) part = sectionDataN n len part := by
  unfold sectionData sectionDataN
  by_cases hk : part.kind = 8
  · simp [hk]
  · by_cases hb : part.offset + part.size ≤ len
    · simp only [hk, ite_false, size_bytesOf, hb, guard_true, Option.pure_def,
        Option.bind_eq_bind, Option.bind_some, slice_bytesOf hb]
    · simp [hk, hb]

theorem readObjectSections_bytesOf (n len : Nat) (headers : List SectionHeader)
    (strings : Bytes) :
    readObjectSections (bytesOf n len) headers strings =
      readObjectSectionsN n len headers strings := by
  simp only [readObjectSections, readObjectSectionsN, sectionData_bytesOf]

theorem readObjectSymbols_bytesOf (n len : Nat) (sections : List ObjectSection) (t : Nat) :
    readObjectSymbols (bytesOf n len) sections t = readObjectSymbolsN n len sections t := by
  simp only [readObjectSymbols, readObjectSymbolsN, readSymbol_bytesOf]

theorem readObjectRelocations_bytesOf (n len : Nat) (sections : List ObjectSection)
    (t c : Nat) :
    readObjectRelocations (bytesOf n len) sections t c =
      readObjectRelocationsN n len sections t c := by
  simp only [readObjectRelocations, readObjectRelocationsN, readRela_bytesOf]

/-- The public certified object reader, evaluated by arithmetic. -/
theorem readObject_bytesOf (n len : Nat) : readObject (bytesOf n len) = readObjectN n len := by
  simp only [readObject, readObjectN, readHeader_bytesOf, readSectionHeaders_bytesOf,
    sectionData_bytesOf, readObjectSections_bytesOf, readObjectSymbols_bytesOf,
    readObjectRelocations_bytesOf]
  rfl

theorem validLoadN_iff (policy : ELFImage.Policy) (n len : Nat) (ph : ProgramHeader) :
    ValidLoadN policy len ph ↔ ELFImage.ValidLoad policy (bytesOf n len) ph := by
  simp only [ValidLoadN, ELFImage.ValidLoad, size_bytesOf]

theorem recordsValidN_iff (policy : ELFImage.Policy) (n len : Nat) (records : ELFImage.Records) :
    RecordsValidN policy len records ↔ ELFImage.RecordsValid policy (bytesOf n len) records := by
  simp only [RecordsValidN, ELFImage.RecordsValid, validLoadN_iff policy n len,
    ELFImage.Records.image, List.pairwise_map]
  rfl

/-- The public checked ELF image extraction, evaluated by arithmetic. -/
theorem parse_bytesOf (policy : ELFImage.Policy) (n len : Nat) :
    ELFImage.parse policy (bytesOf n len) = parseN policy n len := by
  simp only [ELFImage.parse, parseN, readHeader_bytesOf, readProgramHeaders_bytesOf,
    recordsValidN_iff policy n len]

theorem byteAt_valueLE (l : List (BitVec 8)) (i : Nat) (h : i < l.length) :
    byteAt (valueLE l) i = l[i] := by
  induction l generalizing i with
  | nil => simp at h
  | cons x r ih =>
    have hx := x.isLt
    cases i with
    | zero =>
      apply BitVec.eq_of_toNat_eq
      simp [byteAt_toNat, valueLE, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    | succ i =>
      have hi : i < r.length := by simpa using h
      rw [List.getElem_cons_succ, ← ih i hi]
      have hdrop : (x.toNat + 256 * valueLE r) >>> 8 = valueLE r := by
        rw [Nat.shiftRight_eq_div_pow]
        show (x.toNat + 256 * valueLE r) / 256 = valueLE r
        omega
      simp only [byteAt, valueLE]
      rw [Nat.mul_add, Nat.mul_one, Nat.add_comm (8 * i), Nat.shiftRight_add, hdrop]

/-- Every byte array is the denotation of the blob `ofBytes` builds. -/
theorem bytes_ofBytes (b : Bytes) : (ofBytes b).bytes = b := by
  apply Array.ext'
  simp only [bytes, ofBytes, toList_bytesOf]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [byteAt_valueLE _ _ (by simpa using h2)]

end Silmaril.Machine.Link.Blob
