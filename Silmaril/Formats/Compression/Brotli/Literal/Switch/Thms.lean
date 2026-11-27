module

public import Silmaril.Formats.Compression.Brotli.Literal.Switch.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Literal.Switch.Contracts

public section

namespace Silmaril.Formats.Compression.Brotli.Literal.Switch

theorem tableFor_sound {header : CompressedHeader.Header} {history : History} {type : Nat}
    {table : Huffman.Description.Table} (read : tableFor header history type = .ok table) :
    TableWire header history type table :=
  Proofs.Formats.Compression.Brotli.Literal.Switch.tableFor_sound read

theorem readOne_sound {header : CompressedHeader.Header} {limit : Nat} {initial final : State}
    {before after : LSBReader} {input : List Bool} {byte : UInt8}
    (rep : before.Rep input) (count : before.count < 8)
    (read : readOne header limit initial before = .ok (byte, final, after)) :
    ∃ used suffix, StepWire header initial used byte final ∧
      Source before after input used suffix ∧ used.length ≤ limit :=
  Proofs.Formats.Compression.Brotli.Literal.Switch.readOne_sound rep count read

theorem Source.trans {before middle after : LSBReader} {input a rest b suffix : List Bool}
    (first : Source before middle input a rest) (second : Source middle after rest b suffix) :
    Source before after input (a ++ b) suffix :=
  Proofs.Formats.Compression.Brotli.Literal.Switch.Source.trans first second

theorem Wire.carry {header : CompressedHeader.Header} {initial final : State}
    {bits : List Bool} {bytes : List UInt8} (wire : Wire header initial bits bytes final) :
    final.history = initial.history.advance bytes ∧ final.runs.insertCopy = initial.runs.insertCopy ∧
    final.runs.distance = initial.runs.distance :=
  Proofs.Formats.Compression.Brotli.Literal.Switch.Wire.carry wire

theorem read_sound {header : CompressedHeader.Header} {amount limit : Nat} {initial final : State}
    {before after : LSBReader} {input : List Bool} {bytes : List UInt8}
    (rep : before.Rep input) (count : before.count < 8)
    (read : read header amount limit initial before = .ok (bytes, final, after)) :
    bytes.length = amount ∧ ∃ used suffix, Wire header initial used bytes final ∧
      Source before after input used suffix ∧ used.length ≤ limit :=
  Proofs.Formats.Compression.Brotli.Literal.Switch.read_sound rep count read

theorem read_error {header : CompressedHeader.Header} {amount limit : Nat} {initial : State}
    {before : LSBReader} {input : List Bool} {error : Error} (rep : before.Rep input) (count : before.count < 8)
    (read : read header amount limit initial before = .error error) :
    Failure header amount 0 limit initial before input error :=
  Proofs.Formats.Compression.Brotli.Literal.Switch.read_error rep count read

theorem Failure.index_bounds {header : CompressedHeader.Header} {amount index limit : Nat} {state : State}
    {before : LSBReader} {input : List Bool} {error : Error}
    (failure : Failure header amount index limit state before input error) :
    index ≤ error.index ∧ error.index < index + amount :=
  Proofs.Formats.Compression.Brotli.Literal.Switch.Failure.index_bounds failure

theorem Failure.offset {header : CompressedHeader.Header} {amount index limit : Nat} {state : State}
    {before : LSBReader} {input : List Bool} {error : Error}
    (failure : Failure header amount index limit state before input error) :
    ∃ used suffix, input = used ++ suffix ∧ error.bit = before.totalRead + used.length :=
  Proofs.Formats.Compression.Brotli.Literal.Switch.Failure.offset failure

end Silmaril.Formats.Compression.Brotli.Literal.Switch
