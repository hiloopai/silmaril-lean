module

public import Silmaril.Raw.Formats.Compression.Inflate.Stream.Blocks

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream

open Silmaril.Formats.Compression

/-- An eight-bit reservoir read is exactly a byte read of the normalized
canonical reader. The resulting reservoir and reader remain related. -/
theorem Reservoir.Normalizes.readByte {state after : Reservoir} {reader : LSBReader} {value : Nat}
    (h : Reservoir.Normalizes state reader)
    (hread : Reservoir.readBits 8 state = .value value after) :
    ∃ rest, reader.readByte = some (UInt8.ofNat value, rest) ∧
      Reservoir.Normalizes after rest := by
  obtain ⟨rest, hr, hrest⟩ := h.readBits hread
  exact ⟨rest, by simp only [LSBReader.readByte, hr], hrest⟩

namespace StoredContinuation

/-!
# Stored-block continuations and output framing

A controller can validate a stored header, retain its
remaining byte count across resumptions, and append its bytes to existing output.
The framing laws below connect that continuation directly to the existing raw
block-body specification, preserving every error and the entire final reader.
The earlier stored-parser equality already accounts for LEN/NLEN validation and
the verified array/list copy correspondence. No C memory theorem is claimed.
-/

/-! Check satisfiable success, suffix preservation, and failure before proving
the general framing law. -/

theorem framed_byte_checked :
    Deflate.readStoredBytes [65, 66] ⟨0, 0, [67, 68], 0⟩ 1 =
      .ok ([65, 66, 67], ⟨0, 0, [68], 8⟩) := rfl

theorem framed_short_input_checked :
    Deflate.readStoredBytes [65, 66] ⟨0, 0, [], 0⟩ 1 = .error .decodeOverrun := rfl

/-- A fixed prefix of the output is framed around the byte-copy operation. -/
theorem readStoredBytes_frame (framed acc : List UInt8) (reader : LSBReader) (count : Nat) :
    Deflate.readStoredBytes (framed ++ acc) reader count =
      (Deflate.readStoredBytes acc reader count).map
        (fun pair => (framed ++ pair.1, pair.2)) := by
  induction count generalizing acc reader with
  | zero => rfl
  | succ count ih =>
    rw [Deflate.readStoredBytes, Deflate.readStoredBytes]
    cases reader.readByte with
    | none => rfl
    | some pair =>
      obtain ⟨byte, rest⟩ := pair
      simpa only [List.append_assoc] using ih (acc ++ [byte]) rest

/-- In particular, copying directly into the old output is equivalent to
copying into an empty accumulator and then prepending the old output. -/
theorem readStoredBytes_append (output : List UInt8) (reader : LSBReader) (count : Nat) :
    Deflate.readStoredBytes output reader count =
      (Deflate.readStoredBytes [] reader count).map
        (fun pair => (output ++ pair.1, pair.2)) := by
  simpa only [List.append_nil] using readStoredBytes_frame output [] reader count

/-- Header validation followed by byte copying, exposed without the array
representation hidden behind the already proved stored phase. -/
theorem decompressStored_header_eval (reader : LSBReader) :
    Deflate.decompressStored reader =
      match ParserPhases.storedHeader.eval reader with
      | .error err => .error err
      | .ok (count, rest) => Deflate.readStoredBytes [] rest count := by
  rw [← Manual.decompressStored_eq, ← ParserPhases.stored_eval]
  simp only [ParserPhases.stored, Parser.eval_bind, ParserPhases.storedBytes_eval]
  cases ParserPhases.storedHeader.eval reader with
  | error err => rfl
  | ok pair => cases pair; rfl

/-- The stored-header/copy controller appends to its accumulated output and
implements precisely the independently expressed stored parsing program. -/
theorem storedHeader_copy_eq_storedBody (output : List UInt8) (reader : LSBReader) :
    (match ParserPhases.storedHeader.eval reader with
      | .error err => .error err
      | .ok (count, rest) => Deflate.readStoredBytes output rest count) =
      (Blocks.storedBody output).eval reader := by
  rw [Blocks.storedBody_eval, decompressStored_header_eval]
  cases hh : ParserPhases.storedHeader.eval reader with
  | error err => rfl
  | ok pair =>
    obtain ⟨count, rest⟩ := pair
    have hf := readStoredBytes_append output rest count
    cases hr : Deflate.readStoredBytes [] rest count with
    | error err => simpa only [hr, Except.map] using hf
    | ok pair =>
      obtain ⟨bytes, next⟩ := pair
      simpa only [hr, Except.map] using hf

/-- The same continuation equals BTYPE=00 in the canonical block-body decoder. -/
theorem storedHeader_copy_eq_blockBody (output : List UInt8) (reader : LSBReader) :
    (match ParserPhases.storedHeader.eval reader with
      | .error err => .error err
      | .ok (count, rest) => Deflate.readStoredBytes output rest count) =
      Deflate.decompressBlockBody 0 reader output := by
  rw [storedHeader_copy_eq_storedBody, Blocks.storedBody_eval]
  rfl

theorem storedBody_after_header (output : List UInt8) (reader : LSBReader) (count : Nat)
    (rest : LSBReader) (hheader : ParserPhases.storedHeader.eval reader = .ok (count, rest)) :
    (Blocks.storedBody output).eval reader = Deflate.readStoredBytes output rest count := by
  rw [← storedHeader_copy_eq_storedBody, hheader]

theorem blockBody_after_header (output : List UInt8) (reader : LSBReader) (count : Nat)
    (rest : LSBReader) (hheader : ParserPhases.storedHeader.eval reader = .ok (count, rest)) :
    Deflate.decompressBlockBody 0 reader output = Deflate.readStoredBytes output rest count := by
  rw [← storedHeader_copy_eq_blockBody, hheader]

end StoredContinuation
end Silmaril.Formats.Compression.Inflate.Stream
