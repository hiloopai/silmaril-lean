module

public import Silmaril.Formats.Compression.Brotli.Stream.Dictionary.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Stream.Dictionary.Contracts

public section

namespace Silmaril.Formats.Compression.Brotli.Stream.Dictionary

/-- A meta-block contributes its declared bytes and exact charge to the shared command budget. -/
theorem BodyWire.output {limits : Stream.Limits} {window position : Nat} {frame : Header}
    {initial final : State} {bits : List Bool} {chunk : List UInt8} {charge : Nat}
    (wire : BodyWire limits window position frame initial bits chunk charge final) :
    final.execution.output.toList = initial.execution.output.toList ++ chunk ∧
    chunk.length = frame.outputSize ∧ charge + final.remainingCommands = initial.remainingCommands :=
  Proofs.Formats.Compression.Brotli.Stream.Dictionary.BodyWire.output wire

/-- The original window and meta-block walk justify the decoder outcome. -/
theorem decode_wire (limits : Limits) (input : List UInt8) :
    Wire limits input (decode limits input) :=
  Proofs.Formats.Compression.Brotli.Stream.Dictionary.decode_wire limits input

/-- Success consumes exactly one stream and accounts for the global output, bit, block and command caps. -/
theorem decode_sound {limits : Limits} {input : List UInt8} {final : State}
    (decoded : decode limits input = .ok final) :
    Wire limits input (.ok final) ∧ input.length ≤ limits.framing.input ∧
    8 * input.length ≤ limits.framing.bits ∧ final.execution.output.size ≤ limits.framing.output ∧
    ∃ (window : Nat) (chunks : List (List UInt8)) (charges : List Nat),
      10 ≤ window ∧ window ≤ 24 ∧ windowSize window ≤ limits.framing.window ∧
      0 < chunks.length ∧ chunks.length ≤ limits.framing.blocks ∧ charges.length = chunks.length ∧
      final.execution.output.toList = chunks.flatten ∧ charges.sum + final.remainingCommands = limits.commands :=
  Proofs.Formats.Compression.Brotli.Stream.Dictionary.decode_sound decoded

/-- The first failing operation is located at an exact suffix of the original input. -/
theorem decode_error {limits : Limits} {input : List UInt8} {error : Stream.DistanceSwitch.Error}
    (decoded : decode limits input = .error error) :
    Wire limits input (.error error) ∧ ∃ used suffix, bytesBits input = used ++ suffix ∧ error.bit = used.length :=
  Proofs.Formats.Compression.Brotli.Stream.Dictionary.decode_error decoded

end Silmaril.Formats.Compression.Brotli.Stream.Dictionary
