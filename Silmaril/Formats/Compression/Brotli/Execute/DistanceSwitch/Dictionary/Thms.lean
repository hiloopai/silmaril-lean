module

public import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.Contracts

public section

namespace Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary

open Literal.Switch (Source)
open Execute.LiteralSwitch (remainingBits)
open StaticDictionary (lookup splitAddress)

/-- A resolved copy emits the exact backward-reference or transformed dictionary bytes. -/
theorem finishCopy_sound {block : Block} {limits : Execute.Limits} {initial : Execute.State} {command : Command.Value}
    {literals : List UInt8} {resolved : Distance.Result} {result : Execute.Result}
    (checked : Distance.Resolved ⟨block.windowBits, initial.output.size + literals.length⟩ initial.ring
      command.copyLength resolved.code resolved.target.distance resolved.target resolved.ring)
    (finished : Internal.finishCopy block limits initial command literals resolved = .ok result) :
    result.state.output.size ≤ block.endOutput ∧ result.state.output.size ≤ limits.output ∧
      CopyWire initial command literals resolved result :=
  Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.finishCopy_sound checked finished

/-- MLEN takes precedence over the caller output cap. Both use the transformed extent. -/
theorem dictionary_budget {block : Block} {limits : Execute.Limits} {initial : Execute.State} {command : Command.Value}
    {literals : List UInt8} {resolved : Distance.Result} {distance length wordId : Nat} {word : ByteArray}
    (target : resolved.target = .staticDictionary distance length wordId)
    (rendered : StaticDictionary.Transform.materialize command.copyLength wordId = .ok word) :
    let extent := initial.output.size + literals.length + word.size
    (Internal.finishCopy block limits initial command literals resolved = .error .metaBlockExtent ↔
      block.endOutput < extent) ∧
    (Internal.finishCopy block limits initial command literals resolved = .error .outputLimit ↔
      extent ≤ block.endOutput ∧ limits.output < extent) :=
  Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.dictionary_budget target rendered

/-- Distance resolution refuses any dictionary word ID outside the selected bucket. -/
theorem invalid_dictionary_id {bounds : Distance.Bounds} {ring : Distance.Ring}
    {length code extra distance : Nat} (dictionary : bounds.maxBackward < distance)
    (lengthFits : StaticDictionary.WordLength length)
    (invalid : 121 * Distance.dictionaryWordCount length ≤ distance - (bounds.maxBackward + 1)) :
    Distance.Internal.route bounds ring length code extra distance = .error .dictionaryWord :=
  Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.invalid_dictionary_id dictionary lengthFits invalid

/-- The parsed copy length selects the word. The returned ring is the incoming ring. -/
theorem copy_dictionary {block : Block} {limits : Execute.Limits} {initial : Execute.State} {command : Command.Value}
    {literals : List UInt8} {resolved : Distance.Result} {result : Execute.Result} {distance length wordId : Nat}
    (target : resolved.target = .staticDictionary distance length wordId)
    (checked : Distance.Resolved ⟨block.windowBits, initial.output.size + literals.length⟩ initial.ring
      command.copyLength resolved.code resolved.target.distance resolved.target resolved.ring)
    (finished : Internal.finishCopy block limits initial command literals resolved = .ok result) :
    length = command.copyLength ∧ result.state.ring = initial.ring ∧
    ∃ address base word, splitAddress command.copyLength wordId = .ok address ∧
      lookup command.copyLength address.index = .ok base ∧
      StaticDictionary.Transform.Wire address.transform base word ∧
      result.state.output = initial.output ++ literals.toArray ++ word.data ∧
      result.state.output.size = initial.output.size + literals.length + word.size :=
  Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.copy_dictionary target checked finished

/-- After a witnessed prefix and insertion, the public reader propagates the
    typed distance refusal or the copy refusal at the original post-distance bit. -/
theorem read_pending {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {initial : Execute.InsertCopy.State} {before atDistance : LSBReader} {input tail : List Bool}
    {pref : Execute.LiteralSwitch.Prefix} {literals : List UInt8} {state : Literal.Switch.State}
    (path : LiteralPath header block limits initial before atDistance input tail pref literals state) :
    read header block limits initial before = (do
      let (resolved, runs, after) ← Execute.DistanceSwitch.Internal.resolve header pref.command
        ⟨block.windowBits, initial.execution.output.size + literals.length⟩ initial.execution.ring
        (remainingBits limits.bits before atDistance) state.runs atDistance
      let executed ← (Internal.finishCopy block limits initial.execution pref.command literals resolved).mapError
        (Execute.DistanceSwitch.Error.copy after.totalRead)
      pure (⟨executed, runs⟩, after)) :=
  Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.read_pending path

/-- The original command bits, unread suffix and both output bounds hold together. -/
theorem read_sound {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {initial : Execute.InsertCopy.State} {before after : LSBReader} {input : List Bool}
    {result : Execute.InsertCopy.Result} (rep : before.Rep input) (count : before.count < 8)
    (parsed : read header block limits initial before = .ok (result, after)) :
    initial.execution.output.size ≤ result.execution.state.output.size ∧
    result.execution.state.output.size ≤ block.endOutput ∧ result.execution.state.output.size ≤ limits.output ∧
    ∃ used suffix, Wire header block limits initial used result ∧
      Source before after input used suffix ∧ used.length ≤ limits.bits :=
  Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.read_sound rep count parsed

/-- A following command uses the returned cursor, output, run state, ring and residual bit budget. -/
theorem read_pair_sound {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {initial : Execute.InsertCopy.State} {before middle after : LSBReader} {input : List Bool}
    {first second : Execute.InsertCopy.Result} (rep : before.Rep input) (count : before.count < 8)
    (firstRead : read header block limits initial before = .ok (first, middle))
    (nextRead : read header block {limits with bits := remainingBits limits.bits before middle}
      first.state middle = .ok (second, after)) :
    first.execution.state.output.size ≤ second.execution.state.output.size ∧
    second.execution.state.output.size ≤ block.endOutput ∧ second.execution.state.output.size ≤ limits.output ∧
    ∃ firstBits nextBits suffix,
      Wire header block limits initial firstBits first ∧
      Wire header block {limits with bits := remainingBits limits.bits before middle} first.state nextBits second ∧
      Source before after input (firstBits ++ nextBits) suffix ∧ (firstBits ++ nextBits).length ≤ limits.bits :=
  Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.read_pair_sound rep count firstRead nextRead

end Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary
