module

public import Silmaril.Proofs.Formats.Tar.Octal

/-! Proofs for `Silmaril.Formats.Tar.Thms`: header records. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Tar

open Silmaril.Formats.Tar

section Record

variable (e : Entry) (pre name chk : List UInt8)

theorem headerRecord_length (h : chk.length = 8) : (headerRecord e pre name chk).length = 512 := by
  simp [headerRecord, ustarMagic, ustarVersion, h]

/-- The checksum does not depend on the contents of the `chksum` field. -/
theorem headerChecksum_headerRecord (h : chk.length = 8) :
    headerChecksum (headerRecord e pre name chk) =
      headerChecksum (headerRecord e pre name (List.replicate 8 0x20)) := by
  simp [headerChecksum, headerRecord, List.drop_append, List.take_append,
    List.drop_of_length_le, List.take_of_length_le, h]

theorem headerRecord_chksum (h : chk.length = 8) :
    ((headerRecord e pre name chk).drop 148).take 8 = chk := by
  simp [headerRecord, List.drop_append, List.drop_of_length_le, h]

end Record

theorem sum_toNat_le (bytes : List UInt8) : (bytes.map UInt8.toNat).sum ≤ 255 * bytes.length := by
  induction bytes with
  | nil => simp
  | cons b t ih =>
    have : b.toNat < 256 := b.toNat_lt
    simp only [List.map_cons, List.sum_cons, List.length_cons]; omega

/-- The checksum of a record fits the six octal digits of `chksum`. -/
theorem headerChecksum_lt {record : List UInt8} (h : record.length = 512) :
    headerChecksum record < 8 ^ 6 := by
  have h1 := sum_toNat_le (record.take 148)
  have h2 := sum_toNat_le (record.drop 156)
  simp only [List.length_take, List.length_drop, h] at h1 h2
  unfold headerChecksum; omega

/-- `parseHeader` reads back every field of a header record, given that each
field fits and the `chksum` field holds the record's checksum. -/
theorem parseHeader_headerRecord {e : Entry} {pre name : List UInt8} {c : Nat}
    (hc : c < 8 ^ 6) (hsum : headerChecksum (headerRecord e pre name (checksumField c)) = c)
    (hname : name.length ≤ 100) (hnameN : name.all nonNul = true)
    (hpre : pre.length ≤ 155) (hpreN : pre.all nonNul = true)
    (hpath : readText (joinPath pre name) = some e.name)
    (hlnk : (utf8 e.linkname).length ≤ 100) (hlnkN : (utf8 e.linkname).all nonNul = true)
    (hun : (utf8 e.uname).length ≤ 32) (hunN : (utf8 e.uname).all nonNul = true)
    (hgn : (utf8 e.gname).length ≤ 32) (hgnN : (utf8 e.gname).all nonNul = true)
    (hmode : e.mode < 8 ^ 7) (huid : e.uid < 8 ^ 7) (hgid : e.gid < 8 ^ 7)
    (hsize : e.data.length < 8 ^ 11) (hmtime : e.mtime < 8 ^ 11)
    (hmaj : e.devmajor < 8 ^ 7) (hmin : e.devminor < 8 ^ 7)
    (hdev : e.typeflag.isDevice = false → e.devmajor = 0 ∧ e.devminor = 0)
    (htf : TypeFlag.ofByte e.typeflag.toByte = e.typeflag) :
    parseHeader (headerRecord e pre name (checksumField c)) =
      some ({ e with data := [] }, e.data.length) := by
  generalize hR : headerRecord e pre name (checksumField c) = R at hsum
  have hlen : R.length = 512 := hR ▸ headerRecord_length _ _ _ _ (by simp)
  have hd : ∀ l : List UInt8, l.headD 0 = (l.take 1).headD 0 := fun l => by cases l <;> rfl
  obtain ⟨f0, f100, f108, f116, f124, f136, f148, f156, f157, f257, f263, f265, f297, f329, f337,
      f345⟩ :
      R.take 100 = padTo name 100 ∧
      (R.drop 100).take 8 = encodeOctal e.mode 8 ∧
      (R.drop 108).take 8 = encodeOctal e.uid 8 ∧
      (R.drop 116).take 8 = encodeOctal e.gid 8 ∧
      (R.drop 124).take 12 = encodeOctal e.data.length 12 ∧
      (R.drop 136).take 12 = encodeOctal e.mtime 12 ∧
      (R.drop 148).take 8 = checksumField c ∧
      (R.drop 156).take 1 = [e.typeflag.toByte] ∧
      (R.drop 157).take 100 = padTo (utf8 e.linkname) 100 ∧
      (R.drop 257).take 6 = ustarMagic ∧
      (R.drop 263).take 2 = ustarVersion ∧
      (R.drop 265).take 32 = padTo (utf8 e.uname) 32 ∧
      (R.drop 297).take 32 = padTo (utf8 e.gname) 32 ∧
      (R.drop 329).take 8 = deviceField e.typeflag e.devmajor ∧
      (R.drop 337).take 8 = deviceField e.typeflag e.devminor ∧
      (R.drop 345).take 155 = padTo pre 155 := by
    rw [← hR]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [headerRecord, List.drop_append, List.drop_of_length_le, ustarMagic, ustarVersion]
  have hmag : isUstarMagic ustarMagic ustarVersion = true := by decide
  simp only [parseHeader, hlen, List.drop_zero, f0, f100, f108, f116, f124, f136, f148, f157, f257, f263, f265,
    f297, f329, f337, f345, hd (R.drop 156), f156, hmag,
    decodeOctal_encodeOctal (w := 8) (by decide) hmode,
    decodeOctal_encodeOctal (w := 8) (by decide) huid,
    decodeOctal_encodeOctal (w := 8) (by decide) hgid,
    decodeOctal_encodeOctal (w := 12) (by decide) hsize,
    decodeOctal_encodeOctal (w := 12) (by decide) hmtime,
    decodeOctal_checksumField hc,
    decodeOctalOrZero_deviceField hmaj (fun h => (hdev h).1),
    decodeOctalOrZero_deviceField hmin (fun h => (hdev h).2),
    hsum, fieldBytes_padTo hname hnameN, fieldBytes_padTo hpre hpreN,
    fieldBytes_padTo hlnk hlnkN, fieldBytes_padTo hun hunN, fieldBytes_padTo hgn hgnN,
    hpath, readText_utf8]
  simp [htf, guard]

/-! ## Pathnames -/

theorem splitPath_spec {path pre name : List UInt8} (h : splitPath path = some (pre, name)) :
    joinPath pre name = path ∧ name.length ≤ 100 ∧ pre.length ≤ 155 ∧
      (∀ b ∈ pre, b ∈ path) ∧ (∀ b ∈ name, b ∈ path) := by
  unfold splitPath at h
  split at h
  · cases h
    exact ⟨rfl, by omega, by simp, by simp, fun _ hb => hb⟩
  · obtain ⟨i, hi, hpair⟩ := Option.map_eq_some_iff.mp h
    cases hpair
    have hmem : i ∈ splitPoints path := List.mem_of_getLast? hi
    simp only [splitPoints, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at hmem
    obtain ⟨hlt, ⟨⟨hpos, hslash⟩, _⟩, h100⟩ := hmem
    have hilt : i < path.length := by omega
    rw [List.getElem?_eq_getElem hilt, Option.some.injEq] at hslash
    refine ⟨?_, by rw [List.length_drop]; omega, by rw [List.length_take]; omega, fun _ hb => List.mem_of_mem_take hb,
      fun _ hb => List.mem_of_mem_drop hb⟩
    have hne : (path.take i).isEmpty = false := by
      cases hx : path.take i with
      | nil => have := congrArg List.length hx; rw [List.length_take, List.length_nil] at this; omega
      | cons _ _ => rfl
    simp only [joinPath, hne, Bool.false_eq_true, ite_false]
    rw [← hslash, ← List.drop_eq_getElem_cons hilt, List.take_append_drop]

/-! ## Encoded headers -/

theorem encodeHeader_eq_some {e : Entry} {h : List UInt8} (he : encodeHeader e = some h) :
    e.admissible = true ∧ ∃ pre name, splitPath (utf8 e.name) = some (pre, name) ∧
      h = headerRecord e pre name
        (checksumField (headerChecksum (headerRecord e pre name (List.replicate 8 0x20)))) := by
  unfold encodeHeader at he
  split at he
  · obtain ⟨⟨pre, name⟩, hs, rfl⟩ := Option.map_eq_some_iff.mp he
    exact ⟨by assumption, pre, name, hs, rfl⟩
  · cases he

theorem encodeHeader_length {e : Entry} {h : List UInt8} (he : encodeHeader e = some h) :
    h.length = 512 := by
  obtain ⟨-, pre, name, -, rfl⟩ := encodeHeader_eq_some he
  exact headerRecord_length _ _ _ _ (by simp)

theorem encodeHeader_isSome {e : Entry} (h : e.admissible = true) : (encodeHeader e).isSome := by
  have hs : (splitPath (utf8 e.name)).isSome := by
    unfold Entry.admissible at h
    simp only [Bool.and_eq_true, and_assoc] at h
    exact h.1
  unfold encodeHeader
  rw [ite_eq_left h]
  cases hp : splitPath (utf8 e.name) with
  | none => rw [hp] at hs; cases hs
  | some p => rfl

theorem encodeHeader_eq_none {e : Entry} (h : e.admissible = false) : encodeHeader e = none := by
  simp [encodeHeader, h]

theorem decodeOctal_chksum_headerRecord {e : Entry} {pre name : List UInt8} {k : Nat}
    (hk : k < 8 ^ 6) (hs : headerChecksum (headerRecord e pre name (checksumField k)) = k) :
    decodeOctal (((headerRecord e pre name (checksumField k)).drop 148).take 8) =
      some (headerChecksum (headerRecord e pre name (checksumField k))) := by
  rw [hs, headerRecord_chksum _ _ _ _ (checksumField_length k)]
  exact decodeOctal_checksumField hk

/-- The `chksum` field of an encoded header holds its POSIX checksum. -/
theorem encodeHeader_checksum {e : Entry} {h : List UInt8} (he : encodeHeader e = some h) :
    decodeOctal ((h.drop 148).take 8) = some (headerChecksum h) := by
  obtain ⟨-, pre, name, -, rfl⟩ := encodeHeader_eq_some he
  exact decodeOctal_chksum_headerRecord
    (headerChecksum_lt (headerRecord_length _ _ _ _ (by simp)))
    (headerChecksum_headerRecord _ _ _ _ (by simp))

/-- **The header round trip.** -/
theorem parseHeader_encodeHeader {e : Entry} {h : List UInt8} (he : encodeHeader e = some h) :
    parseHeader h = some ({ e with data := [] }, e.data.length) := by
  obtain ⟨hadm, pre, name, hs, rfl⟩ := encodeHeader_eq_some he
  obtain ⟨hjoin, hnl, hpl, hpm, hnm⟩ := splitPath_spec hs
  simp only [Entry.admissible, fitsOctal, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    Bool.or_eq_true, List.isEmpty_iff, and_assoc] at hadm
  obtain ⟨-, hnul, -, hlnk, hlnkN, hun, hunN, hgn, hgnN, hmode, huid, hgid, hmaj, hmin, hmtime,
    hsize, htf, -, hdev⟩ := hadm
  have hall : ∀ {xs : List UInt8}, (∀ b ∈ xs, b ∈ utf8 e.name) → xs.all nonNul = true :=
    fun hx => List.all_eq_true.mpr fun b hb => List.all_eq_true.mp hnul b (hx b hb)
  refine parseHeader_headerRecord (headerChecksum_lt (headerRecord_length _ _ _ _ (by simp)))
    (headerChecksum_headerRecord _ _ _ _ (by simp)) hnl (hall hnm) hpl (hall hpm)
    (by rw [hjoin]; exact readText_utf8 _) hlnk hlnkN hun hunN hgn hgnN hmode huid hgid hsize
    hmtime hmaj hmin ?_ htf
  intro hd
  rcases hdev with hd' | hd'
  · rw [hd] at hd'; cases hd'
  · exact hd'

/-- An encoded header is not a zero-filled record: it holds the magic. -/
theorem encodeHeader_not_zero {e : Entry} {h : List UInt8} (he : encodeHeader e = some h) :
    (h.all (· == 0)) = false := by
  obtain ⟨-, pre, name, -, rfl⟩ := encodeHeader_eq_some he
  have h257 : ((headerRecord e pre name (checksumField
      (headerChecksum (headerRecord e pre name (List.replicate 8 0x20))))).drop 257).take 6 =
      ustarMagic := by
    simp [headerRecord, List.drop_append, List.drop_of_length_le, ustarMagic, ustarVersion]
  rw [Bool.eq_false_iff]
  intro hall
  have hmem : (0x75 : UInt8) ∈ headerRecord e pre name (checksumField
      (headerChecksum (headerRecord e pre name (List.replicate 8 0x20)))) := by
    have : (0x75 : UInt8) ∈ ustarMagic := by simp [ustarMagic]
    rw [← h257] at this
    exact List.mem_of_mem_drop (List.mem_of_mem_take this)
  have := List.all_eq_true.mp hall _ hmem
  simp at this

end Silmaril.Proofs.Formats.Tar
