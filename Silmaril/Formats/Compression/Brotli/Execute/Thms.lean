module

public import Silmaril.Formats.Compression.Brotli.Execute.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Execute.Contracts

public section

namespace Silmaril.Formats.Compression.Brotli.Execute

theorem State.literalHistory_spec (state : State) :
    state.literalHistory =
      ⟨if state.output.toList.length = 0 then 0 else
        state.output.toList[state.output.toList.length - 1]?.getD 0,
       if state.output.toList.length < 2 then 0 else
        state.output.toList[state.output.toList.length - 2]?.getD 0⟩ := by
  simp [State.literalHistory]

theorem Wire.output_count {header : CompressedHeader.Header} {block : Block} {initial : State}
    {bits : List Bool} {result : Result} (wire : Wire header block initial bits result) :
    result.state.output.size = initial.output.size + result.command.insertLength +
      (if result.distance.isSome then result.command.copyLength else 0) :=
  Proofs.Formats.Compression.Brotli.Execute.Wire.output_count wire

/-- An overrun on the admitted copy path returns an error before
    extending the history. -/
theorem copyTail_rejects_overrun {header : CompressedHeader.Header} {block : Block} {limits : Limits}
    {initial : State} {command : Command.Value} {literals : List UInt8} {bitLimit distance : Nat}
    {before after : LSBReader} {resolved : Distance.Result}
    (parsed : Distance.read header command ⟨block.windowBits, initial.output.size + literals.length⟩
      initial.ring bitLimit before = .ok (resolved, after))
    (target : resolved.target = .backReference distance) :
    let finish := initial.output.size + literals.length + command.copyLength
    (block.endOutput < finish →
      Internal.copyTail header block limits initial command literals bitLimit before = .error .metaBlockExtent) ∧
    (finish ≤ block.endOutput → limits.output < finish →
      Internal.copyTail header block limits initial command literals bitLimit before = .error .outputLimit) :=
  Proofs.Formats.Compression.Brotli.Execute.copyTail_rejects_overrun parsed target

/-- An accepted command appends the exact literal and overlap-copy
    sequence, with the resolved ring and original source suffix. -/
theorem read_sound {header : CompressedHeader.Header} {block : Block} {limits : Limits}
    {initial : State} {before after : LSBReader} {input : List Bool} {result : Result}
    (rep : before.Rep input) (count : before.count < 8)
    (read : read header block limits initial before = .ok (result, after)) :
    oneType header = true ∧ 10 ≤ block.windowBits ∧ block.windowBits ≤ 24 ∧
    block.start ≤ initial.output.size ∧ initial.output.size < result.state.output.size ∧
    result.state.output.size ≤ block.endOutput ∧ result.state.output.size ≤ limits.output ∧
    ∃ used suffix, Wire header block initial used result ∧
      input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ limits.bits :=
  Proofs.Formats.Compression.Brotli.Execute.read_sound rep count read

end Silmaril.Formats.Compression.Brotli.Execute
