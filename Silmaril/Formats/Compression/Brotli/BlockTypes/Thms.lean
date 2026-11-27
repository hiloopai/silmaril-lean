module

public import Silmaril.Formats.Compression.Brotli.BlockTypes.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.BlockTypes.Contracts

public section

namespace Silmaril.Formats.Compression.Brotli.BlockTypes

/-- One NBLTYPES field occupies 1–11 bits and declares 1–256 types. -/
theorem CountWire.bounds {bits : List Bool} {types : Nat} (wire : CountWire bits types) :
    1 ≤ types ∧ types ≤ 256 ∧ 1 ≤ bits.length ∧ bits.length ≤ 11 :=
  Proofs.Formats.Compression.Brotli.BlockTypes.CountWire.bounds wire

theorem CountWire.bits_of_one {bits : List Bool} (wire : CountWire bits 1) : bits = [false] :=
  Proofs.Formats.Compression.Brotli.BlockTypes.CountWire.bits_of_one wire rfl

/-- The shared count field advances to its exact following bit. -/
theorem readCount_sound {bitLimit types : Nat} {before after : LSBReader} {input : List Bool}
    (rep : before.Rep input) (count : before.count < 8)
    (read : readCount bitLimit before = .ok (types, after)) :
    ∃ used suffix, CountWire used types ∧ input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ bitLimit :=
  Proofs.Formats.Compression.Brotli.BlockTypes.readCount_sound rep count read

theorem LengthWire.bounds {table : Huffman.Description.Table} {bits : List Bool} {length : Nat}
    (wire : LengthWire table bits length) : 1 ≤ length ∧ length ≤ 16793840 :=
  Proofs.Formats.Compression.Brotli.BlockTypes.LengthWire.bounds wire

/-- The same exact count reader serves both initial runs and switches. -/
theorem readLength_sound {table : Huffman.Description.Table} {bitLimit length : Nat} {before after : LSBReader}
    {input : List Bool} (rep : before.Rep input) (count : before.count < 8)
    (read : readLength table bitLimit before = .ok (length, after)) :
    ∃ used suffix, LengthWire table used length ∧ input = used ++ suffix ∧ after.Rep suffix ∧
      after.count < 8 ∧ after.totalRead = before.totalRead + used.length ∧ used.length ≤ bitLimit :=
  Proofs.Formats.Compression.Brotli.BlockTypes.readLength_sound rep count read

/-- Section 6 bounds the finite count for a multi-type initial block. -/
theorem ControlWire.bounds {bits : List Bool} {control : Control} (wire : ControlWire bits control) :
    1 ≤ control.typeCount ∧ control.typeCount ≤ 256 ∧
      match control with
      | .single => True
      | .multiple _ _ _ initial => 1 ≤ initial ∧ initial ≤ 16793840 :=
  Proofs.Formats.Compression.Brotli.BlockTypes.ControlWire.bounds wire

/-- The three controls come from the original bits in RFC category order.
    The result preserves the untouched suffix under one caller bit cap. -/
theorem read_sound {bitLimit : Nat} {before after : LSBReader} {input : List Bool} {controls : Controls}
    (rep : before.Rep input) (count : before.count < 8)
    (read : read bitLimit before = .ok (controls, after)) :
    ∃ used suffix, Wire used controls ∧ input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ bitLimit :=
  Proofs.Formats.Compression.Brotli.BlockTypes.read_sound rep count read

end Silmaril.Formats.Compression.Brotli.BlockTypes
