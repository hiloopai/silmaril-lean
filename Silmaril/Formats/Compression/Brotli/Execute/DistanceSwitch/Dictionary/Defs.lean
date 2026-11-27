module

public import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Defs
public import Silmaril.Formats.Compression.Brotli.StaticDictionary.Transform.Defs

/-! RFC 7932 §8 and §9.2 command execution with the standard static dictionary. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary

open StaticDictionary (Address lookup splitAddress)

namespace Internal

def dictionaryError : StaticDictionary.Transform.Error → Execute.Error
  | .address .wordLength | .baseLength => .distance .dictionaryLength
  | .address .wordId | .address .wordIndex | .transformOrdinal => .distance .dictionaryWord

/-- The parsed copy length selects the base word bucket. Only the
    transformed bytes are debited before committing the destination. -/
def finishCopy : DistanceSwitch.Internal.FinishCopy := fun block limits initial command literals resolved =>
  match resolved.target with
  | .backReference _ => Execute.Internal.applyCopy block limits initial command literals resolved
  | .staticDictionary distance _ wordId => do
    let word ← (StaticDictionary.Transform.materialize command.copyLength wordId).mapError dictionaryError
    let extent := initial.output.size + literals.length + word.size
    if block.endOutput < extent then .error .metaBlockExtent
    else if limits.output < extent then .error .outputLimit
    else
      let output := initial.output ++ literals.toArray ++ word.data
      .ok ⟨⟨output, initial.ring⟩, command, some distance⟩

end Internal

/-- Opt in to standard static-dictionary command execution. The result
    can be fed straight to the next call with the residual bit budget. -/
def read (header : CompressedHeader.Header) (block : Block) (limits : Limits)
    (initial : InsertCopy.State) (before : LSBReader) : Except DistanceSwitch.Error (InsertCopy.Result × LSBReader) :=
  DistanceSwitch.Internal.readWith Internal.finishCopy header block limits initial before

inductive CopyBytes (command : Command.Value) (history : List UInt8) : Distance.Target → List UInt8 → Prop where
  | back {distance : Nat} {bytes : List UInt8} :
      HistoryCopy.Wire distance history bytes → bytes.length = command.copyLength →
      CopyBytes command history (.backReference distance) bytes
  | dictionary {distance wordId : Nat} {address : Address} {base word : ByteArray} :
      splitAddress command.copyLength wordId = .ok address →
      lookup command.copyLength address.index = .ok base →
      StaticDictionary.Transform.Wire address.transform base word →
      CopyBytes command history (.staticDictionary distance command.copyLength wordId) word.data.toList

structure CopyWire (initial : Execute.State) (command : Command.Value) (literals : List UInt8)
    (resolved : Distance.Result) (result : Execute.Result) : Prop where
  commandExact : result.command = command
  distance : result.distance = some resolved.target.distance
  ring : result.state.ring = resolved.ring
  parts : ∃ bytes, CopyBytes command (initial.output.toList ++ literals) resolved.target bytes ∧
    result.state.output.toList = initial.output.toList ++ literals ++ bytes

abbrev Wire := ReadWire Internal.finishCopy

end Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary
