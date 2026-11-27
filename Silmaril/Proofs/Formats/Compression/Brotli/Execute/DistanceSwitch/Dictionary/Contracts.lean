module

public import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.Defs
import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Thms
import Silmaril.Formats.Compression.Brotli.Execute.Thms
import Silmaril.Formats.Compression.Brotli.Distance.Thms
import Silmaril.Formats.Compression.Brotli.Literal.Switch.Thms
import Silmaril.Formats.Compression.Brotli.StaticDictionary.Transform.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Execute (Block)
open Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch
open Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary
open Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch (remainingBits)
open Silmaril.Formats.Compression.Brotli.Literal.Switch (Source)
open Silmaril.Formats.Compression.Brotli.StaticDictionary (lookup splitAddress)

theorem finishCopy_sound {block : Block} {limits : Execute.Limits} {initial : Execute.State} {command : Command.Value}
    {literals : List UInt8} {resolved : Distance.Result} {result : Execute.Result}
    (checked : Distance.Resolved ⟨block.windowBits, initial.output.size + literals.length⟩ initial.ring
      command.copyLength resolved.code resolved.target.distance resolved.target resolved.ring)
    (finished : Internal.finishCopy block limits initial command literals resolved = .ok result) :
    result.state.output.size ≤ block.endOutput ∧ result.state.output.size ≤ limits.output ∧
      CopyWire initial command literals resolved result := by
  cases target : resolved.target with
  | backReference distance =>
    simp only [Internal.finishCopy, target] at finished
    obtain ⟨same, ring, extent, cap, distance', bytes, target', observed, copied, size, output⟩ :=
      Execute.applyCopy_sound finished
    rw [target] at target'
    cases target'
    exact ⟨extent, cap, ⟨same, by simpa [target, Distance.Target.distance] using observed,
      ring, bytes, by rw [target]; exact .back copied size, output⟩⟩
  | staticDictionary distance length wordId =>
    rw [target] at checked
    obtain ⟨_, _, _, lengthEq, _, _, _, _, sameRing⟩ := checked.valid
    subst length
    obtain ⟨address, base, row, word, split, lookup, _, rendered, wire, _, _⟩ :=
      StaticDictionary.Transform.materialize_resolved checked
    simp only [Internal.finishCopy, target, rendered, Except.mapError, bind, Except.bind] at finished
    split at finished
    · cases finished
    · rename_i blockFits
      split at finished
      · cases finished
      · rename_i outputFits
        cases finished
        refine ⟨?_, ?_, ⟨rfl, by rw [target]; rfl, sameRing.symm, word.data.toList,
          ?_, by simp⟩⟩
        · simpa only [Array.size_append, List.size_toArray, ByteArray.size] using Nat.le_of_not_gt blockFits
        · simpa only [Array.size_append, List.size_toArray, ByteArray.size] using Nat.le_of_not_gt outputFits
        · rw [target]; exact .dictionary split lookup wire

theorem dictionary_budget {block : Block} {limits : Execute.Limits} {initial : Execute.State} {command : Command.Value}
    {literals : List UInt8} {resolved : Distance.Result} {distance length wordId : Nat} {word : ByteArray}
    (target : resolved.target = .staticDictionary distance length wordId)
    (rendered : StaticDictionary.Transform.materialize command.copyLength wordId = .ok word) :
    let extent := initial.output.size + literals.length + word.size
    (Internal.finishCopy block limits initial command literals resolved = .error .metaBlockExtent ↔
      block.endOutput < extent) ∧
    (Internal.finishCopy block limits initial command literals resolved = .error .outputLimit ↔
      extent ≤ block.endOutput ∧ limits.output < extent) := by
  simp only [Internal.finishCopy, target, rendered, Except.mapError, bind, Except.bind]
  split <;> rename_i extent
  · simp [extent, Nat.not_le_of_gt extent]
  · split <;> simp_all

theorem invalid_dictionary_id {bounds : Distance.Bounds} {ring : Distance.Ring}
    {length code extra distance : Nat} (dictionary : bounds.maxBackward < distance)
    (lengthFits : StaticDictionary.WordLength length)
    (invalid : 121 * Distance.dictionaryWordCount length ≤ distance - (bounds.maxBackward + 1)) :
    Distance.Internal.route bounds ring length code extra distance = .error .dictionaryWord := by
  obtain ⟨minimum, maximum⟩ := lengthFits
  have positive : distance ≠ 0 := by omega
  simp [Distance.Internal.route, positive, Nat.not_le_of_gt dictionary,
    Nat.not_lt_of_ge minimum, Nat.not_lt_of_ge maximum, invalid]

private theorem copy_extent {initial : Execute.State} {command : Command.Value} {literals : List UInt8}
    {resolved : Distance.Result} {result : Execute.Result} (wire : CopyWire initial command literals resolved result) :
    initial.output.size ≤ result.state.output.size := by
  obtain ⟨bytes, _, joined⟩ := wire.parts
  have extent := congrArg List.length joined
  simp only [Array.length_toList, List.length_append] at extent
  omega

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
      result.state.output.size = initial.output.size + literals.length + word.size := by
  have wire := (finishCopy_sound checked finished).2.2
  rw [target] at checked
  obtain ⟨_, _, _, lengthEq, _, _, _, _, sameRing⟩ := checked.valid
  refine ⟨lengthEq, wire.ring.trans sameRing, ?_⟩
  obtain ⟨bytes, effect, joined⟩ := wire.parts
  rw [target] at effect
  cases effect with
  | @dictionary _ _ address base word split found transformed =>
    have output : result.state.output = initial.output ++ literals.toArray ++ word.data := by
      apply Array.toList_inj.mp
      simpa using joined
    exact ⟨address, base, word, split, found, transformed, output,
      by rw [output]; simp only [Array.size_append, List.size_toArray, ByteArray.size]⟩

theorem read_pending {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {initial : Execute.InsertCopy.State} {before atDistance : LSBReader} {input tail : List Bool}
    {pref : Execute.LiteralSwitch.Prefix} {literals : List UInt8} {state : Literal.Switch.State}
    (path : LiteralPath header block limits initial before atDistance input tail pref literals state) :
    Dictionary.read header block limits initial before = (do
      let (resolved, runs, after) ← Execute.DistanceSwitch.Internal.resolve header pref.command
        ⟨block.windowBits, initial.execution.output.size + literals.length⟩ initial.execution.ring
        (remainingBits limits.bits before atDistance) state.runs atDistance
      let executed ← (Internal.finishCopy block limits initial.execution pref.command literals resolved).mapError
        (Execute.DistanceSwitch.Error.copy after.totalRead)
      pure (⟨executed, runs⟩, after)) := by
  obtain ⟨_, _, _, prefixRead, literalRead, _, pending⟩ := path.parts
  simp only [Dictionary.read, Execute.DistanceSwitch.Internal.readWith, prefixRead.parsed, literalRead,
    Except.mapError, bind, Except.bind, pending, ite_false]

theorem read_sound {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {initial : Execute.InsertCopy.State} {before after : LSBReader} {input : List Bool}
    {result : Execute.InsertCopy.Result} (rep : before.Rep input) (count : before.count < 8)
    (parsed : Dictionary.read header block limits initial before = .ok (result, after)) :
    initial.execution.output.size ≤ result.execution.state.output.size ∧
    result.execution.state.output.size ≤ block.endOutput ∧ result.execution.state.output.size ≤ limits.output ∧
    ∃ used suffix, Wire header block limits initial used result ∧
      Source before after input used suffix ∧ used.length ≤ limits.bits := by
  obtain ⟨used, suffix, wire, source, fits⟩ := Execute.DistanceSwitch.readWith_sound rep count parsed
  have bounds : initial.execution.output.size ≤ result.execution.state.output.size ∧
      result.execution.state.output.size ≤ block.endOutput ∧ result.execution.state.output.size ≤ limits.output := by
    obtain ⟨_, _, _, _, _, literals, _, _, _, _, _, blockFits, outputFits, finish⟩ := wire
    cases finish with
    | terminal =>
      simp only [Array.size_append, List.size_toArray]
      omega
    | copy _ _ _ distanceRead copied =>
      obtain ⟨extent, cap, effect⟩ := finishCopy_sound distanceRead.resolved copied
      exact ⟨copy_extent effect, extent, cap⟩
  exact ⟨bounds.1, bounds.2.1, bounds.2.2, used, suffix, wire, source, fits⟩

theorem read_pair_sound {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {initial : Execute.InsertCopy.State} {before middle after : LSBReader} {input : List Bool}
    {first second : Execute.InsertCopy.Result} (rep : before.Rep input) (count : before.count < 8)
    (firstRead : Dictionary.read header block limits initial before = .ok (first, middle))
    (nextRead : Dictionary.read header block {limits with bits := remainingBits limits.bits before middle}
      first.state middle = .ok (second, after)) :
    first.execution.state.output.size ≤ second.execution.state.output.size ∧
    second.execution.state.output.size ≤ block.endOutput ∧ second.execution.state.output.size ≤ limits.output ∧
    ∃ firstBits nextBits suffix,
      Wire header block limits initial firstBits first ∧
      Wire header block {limits with bits := remainingBits limits.bits before middle} first.state nextBits second ∧
      Source before after input (firstBits ++ nextBits) suffix ∧ (firstBits ++ nextBits).length ≤ limits.bits := by
  obtain ⟨_, _, _, firstBits, rest, firstWire, firstSource, firstCap⟩ := read_sound rep count firstRead
  obtain ⟨grows, extent, cap, nextBits, suffix, nextWire, nextSource, nextCap⟩ :=
    read_sound firstSource.rep firstSource.count nextRead
  have position := firstSource.position
  exact ⟨grows, extent, cap, firstBits, nextBits, suffix, firstWire, nextWire, firstSource.trans nextSource,
    by simp only [remainingBits, List.length_append] at nextCap ⊢; omega⟩

end Silmaril.Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary
