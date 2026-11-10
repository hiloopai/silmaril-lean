module

public import Silmaril.Formats.Compression.Inflate.Stream.ContainerFields
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.Parser
public import Silmaril.Raw.Formats.Compression.Bits.Bit
public import Silmaril.Formats.Compression.Bits.Bitstream
public import Silmaril.Raw.Formats.Compression.Deflate.Huffman
public import Silmaril.Formats.Compression.Deflate.Decompress
public import Silmaril.Raw.Formats.Compression.Deflate.Stored
public import Silmaril.Raw.Formats.Compression.Deflate.WithHistory
public import Silmaril.Formats.Compression.Deflate.Compress
public import Silmaril.Raw.Formats.Compression.Deflate.LZ77
public import Silmaril.Raw.Formats.Compression.Bits.ByteFields
public import Silmaril.Raw.Formats.Compression.Checksum.Adler32
public import Silmaril.Raw.Formats.Compression.Checksum.CRC32
public import Silmaril.Raw.Formats.Compression.Zlib.Basic
public import Silmaril.Raw.Formats.Compression.Zlib.Take
public import Silmaril.Raw.Formats.Compression.Zlib.Dictionary
public import Silmaril.Raw.Formats.Compression.Gzip.Basic

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Stream.ContainerFields`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.ContainerFields

open Silmaril.Formats.Compression

theorem readBits_byte_cons (first : UInt8) (rest : List UInt8) (total : Nat) :
    (alignedReader (first :: rest) total).readBits 8 =
      some (first.toNat, alignedReader rest (total + 8)) :=
  Deflate.readBits8_aligned first rest total

@[simp] theorem eval_byte_cons (first : UInt8) (rest : List UInt8) (total : Nat) :
    byte.eval (alignedReader (first :: rest) total) =
      .ok (first, alignedReader rest (total + 8)) := by
  simp only [byte, Parser.eval, readBits_byte_cons, UInt8.ofNat_toNat]

@[simp] theorem eval_byte_nil (total : Nat) :
    byte.eval (alignedReader [] total) = .error .decodeOverrun := rfl

theorem eval_bytes (count : Nat) (input : List UInt8) (total : Nat) :
    (bytes count).eval (alignedReader input total) =
      if count ≤ input.length then
        .ok (input.take count, alignedReader (input.drop count) (total + 8 * count))
      else .error .decodeOverrun := by
  induction count generalizing input total with
  | zero => simp [bytes, Parser.eval]
  | succ count ih =>
    cases input with
    | nil => simp [bytes, Parser.eval_bind]
    | cons first rest =>
      simp only [bytes, Parser.eval_bind, eval_byte_cons]
      rw [ih]
      by_cases hcount : count ≤ rest.length
      · simp only [hcount, ite_true, Parser.eval, List.length_cons,
          Nat.add_le_add_iff_right, List.take_succ_cons, List.drop_succ_cons]
        congr 3 <;> omega
      · simp only [hcount, ite_false, List.length_cons, Nat.add_le_add_iff_right]

theorem validationReader_eq_some
    (result : Except Deflate.DecompressError (Option Unit × LSBReader)) (reader : LSBReader) :
    validationReader result = some reader ↔ result = .ok (some (), reader) := by
  cases result with
  | error error => simp [validationReader]
  | ok pair =>
    obtain ⟨valid, actual⟩ := pair
    cases valid with
    | none => simp [validationReader]
    | some value => cases value; simp [validationReader]

@[simp] theorem eval_quad_cons {α : Type} (field : UInt8 → UInt8 → UInt8 → UInt8 → α)
    (b0 b1 b2 b3 : UInt8) (rest : List UInt8) (total : Nat) :
    (quad field).eval (alignedReader (b0 :: b1 :: b2 :: b3 :: rest) total) =
      .ok (field b0 b1 b2 b3, alignedReader rest (total + 32)) := by
  simp only [quad, Parser.eval_bind, eval_byte_cons, Parser.eval]

@[simp] theorem eval_zlibTrailerValue_cons (check : Nat) (a0 a1 a2 a3 : UInt8)
    (rest : List UInt8) (total : Nat) :
    (zlibTrailerValue check).eval (alignedReader (a0 :: a1 :: a2 :: a3 :: rest) total) =
      .ok ((if be32Val a0 a1 a2 a3 = check then some () else none),
        alignedReader rest (total + 32)) := by
  simp only [zlibTrailerValue, Parser.eval_bind, be32, eval_quad_cons, Parser.eval]

@[simp] theorem eval_gzipTrailerValue_cons (check size : Nat)
    (c0 c1 c2 c3 i0 i1 i2 i3 : UInt8) (rest : List UInt8) (total : Nat) :
    (gzipTrailerValue check size).eval
        (alignedReader (c0 :: c1 :: c2 :: c3 :: i0 :: i1 :: i2 :: i3 :: rest) total) =
      .ok ((if le32Val c0 c1 c2 c3 = check ∧
          le32Val i0 i1 i2 i3 = size % 4294967296 then some () else none),
        alignedReader rest (total + 64)) := by
  simp only [gzipTrailerValue, Parser.eval_bind, le32, eval_quad_cons, Parser.eval]

theorem zlibTrailer_eq_value (data : List UInt8) :
    zlibTrailer data = zlibTrailerValue (adler32 ⟨data.toArray⟩).toNat := rfl

theorem gzipTrailer_eq_value (data : List UInt8) :
    gzipTrailer data = gzipTrailerValue (crc32 ⟨data.toArray⟩).toNat data.length := rfl

theorem validationReader_zlibHeader (input : List UInt8) (total : Nat) :
    validationReader (zlibHeader.eval (alignedReader input total)) =
      (zlibCheckHeader input).map (fun rest => alignedReader rest (total + 16)) := by
  match input with
  | [] => rfl
  | [_] => simp [zlibHeader, Parser.eval_bind, validationReader, zlibCheckHeader]
  | cmf :: flg :: rest =>
    simp only [zlibHeader, Parser.eval_bind, eval_byte_cons, Parser.eval, zlibCheckHeader]
    split <;> rfl

theorem validationReader_zlibTrailer (data input : List UInt8) (total : Nat) :
    validationReader ((zlibTrailer data).eval (alignedReader input total)) =
      (zlibCheckTrailer data input).map (fun rest => alignedReader rest (total + 32)) := by
  match input with
  | [] | [_] | [_, _] | [_, _, _] =>
    simp [zlibTrailer, zlibTrailerValue, be32, quad, Parser.eval_bind, validationReader,
      zlibCheckTrailer]
  | a0 :: a1 :: a2 :: a3 :: rest =>
    simp only [zlibTrailer, eval_zlibTrailerValue_cons, zlibCheckTrailer]
    split <;> rfl

theorem validationReader_gzipTrailer (data input : List UInt8) (total : Nat) :
    validationReader ((gzipTrailer data).eval (alignedReader input total)) =
      (gzipCheckTrailer data input).map (fun rest => alignedReader rest (total + 64)) := by
  match input with
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] |
      [_, _, _, _, _, _] | [_, _, _, _, _, _, _] =>
    simp [gzipTrailer, gzipTrailerValue, le32, quad, Parser.eval_bind, Parser.eval, validationReader,
      gzipCheckTrailer]
  | c0 :: c1 :: c2 :: c3 :: i0 :: i1 :: i2 :: i3 :: rest =>
    simp only [gzipTrailer, eval_gzipTrailerValue_cons, gzipCheckTrailer]
    split <;> rfl

theorem observe_zlibHeader (input : List UInt8) (total : Nat) :
    observeValidation (zlibHeader.eval (alignedReader input total)) = zlibCheckHeader input := by
  simp only [observeValidation, validationReader_zlibHeader, Option.map_map]
  cases zlibCheckHeader input <;> rfl

theorem observe_zlibTrailer (data input : List UInt8) (total : Nat) :
    observeValidation ((zlibTrailer data).eval (alignedReader input total)) =
      zlibCheckTrailer data input := by
  simp only [observeValidation, validationReader_zlibTrailer, Option.map_map]
  cases zlibCheckTrailer data input <;> rfl

theorem observe_gzipTrailer (data input : List UInt8) (total : Nat) :
    observeValidation ((gzipTrailer data).eval (alignedReader input total)) =
      gzipCheckTrailer data input := by
  simp only [observeValidation, validationReader_gzipTrailer, Option.map_map]
  cases gzipCheckTrailer data input <;> rfl

theorem eval_zlibHeader_of_check (input rest : List UInt8) (total : Nat)
    (hcheck : zlibCheckHeader input = some rest) :
    zlibHeader.eval (alignedReader input total) =
      .ok (some (), alignedReader rest (total + 16)) := by
  apply (validationReader_eq_some _ _).mp
  rw [validationReader_zlibHeader, hcheck]
  rfl

theorem eval_zlibTrailer_of_check (data input rest : List UInt8) (total : Nat)
    (hcheck : zlibCheckTrailer data input = some rest) :
    (zlibTrailer data).eval (alignedReader input total) =
      .ok (some (), alignedReader rest (total + 32)) := by
  apply (validationReader_eq_some _ _).mp
  rw [validationReader_zlibTrailer, hcheck]
  rfl

theorem eval_gzipTrailer_of_check (data input rest : List UInt8) (total : Nat)
    (hcheck : gzipCheckTrailer data input = some rest) :
    (gzipTrailer data).eval (alignedReader input total) =
      .ok (some (), alignedReader rest (total + 64)) := by
  apply (validationReader_eq_some _ _).mp
  rw [validationReader_gzipTrailer, hcheck]
  rfl

/-! ## Checks distinguish valid, invalid and incomplete fields -/

/-- A split header genuinely suspends, then resumes with the same continuation
and leaves the following byte untouched. -/
theorem zlibHeader_split :
    match Parser.run 8 zlibHeader (Reservoir.ofBytes [0x78]) with
    | .needInput continuation state =>
      Parser.run 8 continuation (state.feed [0x01, 0xaa]) =
        .done (some ()) ⟨0, 0, [0xaa], 16⟩
    | _ => False := by
  rfl

theorem zlibHeader_rejects_dictionary (tail : List UInt8) (total : Nat) :
    zlibHeader.eval (alignedReader (0x78 :: 0x20 :: tail) total) =
      .ok (none, alignedReader tail (total + 16)) := by
  simp only [zlibHeader, Parser.eval_bind, eval_byte_cons, Parser.eval]
  rfl

theorem gzipTrailerValue_accepts_correct_isize (tail : List UInt8) (total : Nat) :
    (gzipTrailerValue 0 1).eval (alignedReader (0 :: 0 :: 0 :: 0 :: 1 :: 0 :: 0 :: 0 :: tail) total) =
      .ok (some (), alignedReader tail (total + 64)) := by
  rw [eval_gzipTrailerValue_cons]
  rfl

/-- CRC matches, but ISIZE is wrong: the length condition is independent of
the checksum condition and compares the parsed value with the caller's size. -/
theorem gzipTrailerValue_rejects_wrong_isize (tail : List UInt8) (total : Nat) :
    (gzipTrailerValue 0 1).eval (alignedReader (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: tail) total) =
      .ok (none, alignedReader tail (total + 64)) := by
  rw [eval_gzipTrailerValue_cons]
  rfl

end Silmaril.Formats.Compression.Inflate.Stream.ContainerFields
