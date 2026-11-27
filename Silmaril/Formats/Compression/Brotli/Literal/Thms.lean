module

public import Silmaril.Formats.Compression.Brotli.Literal.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Literal.Contracts

public section

namespace Silmaril.Formats.Compression.Brotli.Literal

theorem History.advance_append (history : History) (prefixBytes suffix : List UInt8) :
    history.advance (prefixBytes ++ suffix) = (history.advance prefixBytes).advance suffix :=
  List.foldl_append

theorem source_sound {header : CompressedHeader.Header} {tables : Source}
    (read : source header = .ok tables) : FromHeader header tables :=
  Proofs.Formats.Compression.Brotli.Literal.source_sound read

theorem Wire.history {source : Source} {start final : History} {bits : List Bool} {bytes : List UInt8}
    (wire : Wire source start bits bytes final) : final = start.advance bytes :=
  Proofs.Formats.Compression.Brotli.Literal.Wire.history wire

theorem Wire.bit_bound {source : Source} {start final : History} {bits : List Bool} {bytes : List UInt8}
    (wire : Wire source start bits bytes final) : bits.length ≤ 15 * bytes.length :=
  Proofs.Formats.Compression.Brotli.Literal.Wire.bit_bound wire

theorem readByte_sound {table : Huffman.Description.Table} {bitLimit : Nat} {before after : LSBReader}
    {byte : UInt8} {input : List Bool} (rep : before.Rep input) (count : before.count < 8)
    (read : readByte table bitLimit before = .ok (byte, after)) :
    table.alphabetSize = 256 ∧
    ∃ code width suffix, table.codeFor byte.toNat = some (code, width) ∧ width ≤ 15 ∧ width ≤ bitLimit ∧
      input = msbBits code width ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + width :=
  Proofs.Formats.Compression.Brotli.Literal.readByte_sound rep count read

/-- The header-selected trees witness each original code. The exact
    returned cursor still holds all bits after the insertion. -/
theorem read_sound {header : CompressedHeader.Header} {command : Command.Value} {metaLength : Nat}
    {limits : Limits} {state : State} {before after : LSBReader} {input : List Bool} {result : Result}
    (rep : before.Rep input) (count : before.count < 8)
    (read : read header command metaLength limits state before = .ok (result, after)) :
    state.produced < metaLength ∧ result.bytes.length = command.insertLength ∧
    result.state.produced = state.produced + result.bytes.length ∧
    result.state.produced ≤ metaLength ∧ result.state.produced ≤ limits.output ∧
    result.state.history = state.history.advance result.bytes ∧
    (result.next = .endOfMetaBlock ↔ result.state.produced = metaLength) ∧
    (result.next = .copyPending ↔ result.state.produced < metaLength) ∧
    ∃ tables used suffix, FromHeader header tables ∧
      Wire tables state.history used result.bytes result.state.history ∧ input = used ++ suffix ∧
      after.Rep suffix ∧ after.count < 8 ∧ after.totalRead = before.totalRead + used.length ∧
      used.length ≤ limits.bits :=
  Proofs.Formats.Compression.Brotli.Literal.read_sound rep count read

end Silmaril.Formats.Compression.Brotli.Literal
