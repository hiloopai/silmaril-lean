module

public import Silmaril.Formats.Compression.Brotli.Execute.Defs
import Silmaril.Formats.Compression.Brotli.Command.Thms
import Silmaril.Formats.Compression.Brotli.Literal.Thms
import Silmaril.Formats.Compression.Brotli.Distance.Thms
import Silmaril.Formats.Compression.HistoryCopy.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Execute

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Execute
open Silmaril.Formats.Compression.Brotli.Execute.Internal

private theorem bind_ok {α β : Type} {action : Except Execute.Error α}
    {next : α → Except Execute.Error β} {value : β} (read : (action >>= next) = .ok value) :
    ∃ result, action = .ok result ∧ next result = .ok value := by
  cases action with
  | error _ => cases read
  | ok result => exact ⟨result, rfl, read⟩

private theorem mapError_ok {ε α : Type} {action : Except ε α}
    {f : ε → Execute.Error} {value : α} (read : action.mapError f = .ok value) :
    action = .ok value := by
  cases action <;> cases read <;> rfl

theorem applyCopy_sound {block : Block} {limits : Execute.Limits} {initial : State}
    {command : Command.Value} {literals : List UInt8} {resolved : Distance.Result} {result : Result}
    (read : applyCopy block limits initial command literals resolved = .ok result) :
    result.command = command ∧ result.state.ring = resolved.ring ∧
    result.state.output.size ≤ block.endOutput ∧ result.state.output.size ≤ limits.output ∧
    ∃ distance matched, resolved.target = .backReference distance ∧ result.distance = some distance ∧
      HistoryCopy.Wire distance (initial.output.toList ++ literals) matched ∧ matched.length = command.copyLength ∧
      result.state.output.toList = initial.output.toList ++ literals ++ matched := by
  unfold applyCopy at read
  dsimp only at read
  split at read <;> try contradiction
  rename_i distance target
  split at read <;> try contradiction
  rename_i blockCap
  split at read <;> try contradiction
  rename_i outputCap
  split at read <;> try contradiction
  rename_i fits
  cases read
  let history := initial.output ++ literals.toArray
  have inHistory : distance ≤ history.size := by simpa [history] using fits.2
  obtain ⟨matched, output, length, copied⟩ :=
    HistoryCopy.copy_sound fits.1 command.copyLength history inHistory
  have rendered : history.toList = initial.output.toList ++ literals := by simp [history]
  rw [rendered] at output copied
  have outputSize := congrArg List.length output
  simp only [Array.length_toList, List.length_append, length] at outputSize
  refine ⟨rfl, rfl, ?_, ?_, distance, matched, target, rfl, copied, length, output⟩
  · change (HistoryCopy.copy distance fits.1 command.copyLength history inHistory).size ≤ block.endOutput
    omega
  · change (HistoryCopy.copy distance fits.1 command.copyLength history inHistory).size ≤ limits.output
    omega

theorem copyTail_sound {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {initial : State} {command : Command.Value} {literals : List UInt8} {bitLimit : Nat}
    {before after : LSBReader} {input : List Bool} {result : Result}
    (pending : initial.output.size + literals.length < block.endOutput)
    (rep : before.Rep input) (count : before.count < 8)
    (read : copyTail header block limits initial command literals bitLimit before = .ok (result, after)) :
    result.command = command ∧ initial.output.size < result.state.output.size ∧
    result.state.output.size ≤ block.endOutput ∧ result.state.output.size ≤ limits.output ∧
    ∃ used matched suffix,
      TailWire header block command initial.ring (initial.output.toList ++ literals)
        used matched result.distance result.state.ring ∧
      result.state.output.toList = initial.output.toList ++ literals ++ matched ∧
      input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ bitLimit := by
  unfold copyTail at read
  obtain ⟨⟨resolved, cursor⟩, distanceRead, done⟩ := bind_ok read
  obtain ⟨executed, copied, done⟩ := bind_ok done
  cases done
  obtain ⟨_, _, minCopy, _, used, suffix, wire, split, rep', count', offset, bitCap⟩ :=
    Distance.read_sound rep count (mapError_ok distanceRead)
  obtain ⟨same, ring, extent, cap, distance, matched, target, observed, copied, length, output⟩ := applyCopy_sound copied
  have sourceLength : (initial.output.toList ++ literals).length = initial.output.size + literals.length := by simp
  have tail : TailWire header block command initial.ring (initial.output.toList ++ literals)
      used matched result.distance result.state.ring := by
    rw [observed, ring]
    exact .copy (sourceLength ▸ pending) (by simpa only [sourceLength] using wire) target copied length
  have outputSize := congrArg List.length output
  simp only [Array.length_toList, List.length_append, length] at outputSize
  exact ⟨same, by omega, extent, cap, used, matched, suffix, tail, output, split, rep', count', offset, bitCap⟩

private theorem TailWire.length {header : CompressedHeader.Header} {block : Block} {command : Command.Value}
    {ring afterRing : Distance.Ring} {beforeCopy matched : List UInt8} {bits : List Bool} {distance : Option Nat}
    (wire : TailWire header block command ring beforeCopy bits matched distance afterRing) :
    matched.length = (if distance.isSome then command.copyLength else 0) := by
  cases wire with
  | terminal => rfl
  | copy _ _ _ _ length => exact length

theorem Wire.output_count {header : CompressedHeader.Header} {block : Block} {initial : State}
    {bits : List Bool} {result : Result} (wire : Wire header block initial bits result) :
    result.state.output.size = initial.output.size + result.command.insertLength +
      (if result.distance.isSome then result.command.copyLength else 0) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, size, tail, shape⟩ := wire.parts
  simpa only [Array.length_toList, List.length_append, size, TailWire.length tail] using congrArg List.length shape

theorem copyTail_rejects_overrun {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {initial : State} {command : Command.Value} {literals : List UInt8} {bitLimit distance : Nat}
    {before after : LSBReader} {resolved : Distance.Result}
    (parsed : Distance.read header command ⟨block.windowBits, initial.output.size + literals.length⟩
      initial.ring bitLimit before = .ok (resolved, after))
    (target : resolved.target = .backReference distance) :
    let finish := initial.output.size + literals.length + command.copyLength
    (block.endOutput < finish →
      copyTail header block limits initial command literals bitLimit before = .error .metaBlockExtent) ∧
    (finish ≤ block.endOutput → limits.output < finish →
      copyTail header block limits initial command literals bitLimit before = .error .outputLimit) := by
  dsimp only
  constructor
  · intro exceeds
    simp [copyTail, applyCopy, parsed, target, bind, Except.bind, exceeds, Except.mapError]
  · intro fits exceeds
    simp [copyTail, applyCopy, parsed, target, bind, Except.bind, Nat.not_lt.mpr fits, exceeds, Except.mapError]

theorem read_sound {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {initial : State} {before after : LSBReader} {input : List Bool} {result : Result}
    (rep : before.Rep input) (count : before.count < 8)
    (read : Silmaril.Formats.Compression.Brotli.Execute.read header block limits initial before =
      .ok (result, after)) :
    oneType header = true ∧ 10 ≤ block.windowBits ∧ block.windowBits ≤ 24 ∧
    block.start ≤ initial.output.size ∧ initial.output.size < result.state.output.size ∧
    result.state.output.size ≤ block.endOutput ∧ result.state.output.size ≤ limits.output ∧
    ∃ used suffix, Wire header block initial used result ∧
      input = used ++ suffix ∧ after.Rep suffix ∧ after.count < 8 ∧
      after.totalRead = before.totalRead + used.length ∧ used.length ≤ limits.bits := by
  unfold Silmaril.Formats.Compression.Brotli.Execute.read at read
  split at read <;> try contradiction
  rename_i profile
  split at read <;> try contradiction
  rename_i window
  split at read <;> try contradiction
  rename_i blockBound
  split at read <;> try contradiction
  rename_i initialCap
  obtain ⟨⟨command, atLiterals⟩, commandRead, next⟩ := bind_ok read
  obtain ⟨⟨inserted, atDistance⟩, literalRead, done⟩ := bind_ok next
  obtain ⟨_, tree, commandBits, rest, selected, commandWire, splitCommand, rep', count', commandOffset, commandCap⟩ :=
    Command.readSingle_sound rep count (mapError_ok commandRead)
  obtain ⟨_, size, produced, metaCap, literalOutCap, _, terminal, pending, tables, literalBits, tail,
      source, literalWire, splitLiteral, rep'', count'', literalOffset, literalCap⟩ :=
    Literal.read_sound rep' count' (mapError_ok literalRead)
  have literalBudget : literalBits.length ≤ limits.bits - commandBits.length := by
    change literalBits.length ≤ limits.bits - (atLiterals.totalRead - before.totalRead) at literalCap
    rw [commandOffset] at literalCap
    omega
  have starts : block.start ≤ initial.output.size := by omega
  have profile : oneType header = true := by simpa using profile
  refine ⟨profile, by omega, by omega, starts, ?_⟩
  simp only [] at produced metaCap literalOutCap
  simp only [] at done
  split at done
  · rename_i isTerminal
    cases done
    have finalPos := terminal.mp isTerminal
    have exactSize : initial.output.size + inserted.bytes.length = block.endOutput := by
      simp only [Block.endOutput]
      omega
    have outputShape : (initial.output ++ inserted.bytes.toArray).toList =
        initial.output.toList ++ inserted.bytes := by simp
    refine ⟨?_, ?_, ?_, commandBits ++ literalBits, tail, ?_, ?_, rep'', count'', ?_, ?_⟩
    · change initial.output.size < (initial.output ++ inserted.bytes.toArray).size
      simp only [Array.size_append, List.size_toArray]
      omega
    · simpa only [Array.size_append, List.size_toArray] using Nat.le_of_eq exactSize
    · change (initial.output ++ inserted.bytes.toArray).size ≤ limits.output
      simp only [Array.size_append, List.size_toArray]
      omega
    · exact ⟨commandBits, literalBits, [], tree, tables, inserted.bytes, inserted.state.history, [],
        by simp, selected, commandWire, source, literalWire, size,
        .terminal (by simpa using exactSize), by simp [outputShape]⟩
    · rw [splitCommand, splitLiteral, List.append_assoc]
    · simp only [List.length_append, literalOffset, commandOffset]
      omega
    · simp only [List.length_append]
      omega
  · rename_i copy
    have room : initial.output.size + inserted.bytes.length < block.endOutput := by
      have := pending.mp copy
      simp only [Block.endOutput]
      omega
    obtain ⟨rfl, grows, blockCap, outputCap, distanceBits, matched, suffix, tailWire, output,
      splitTail, rep''', count''', distanceOffset, distanceCap⟩ :=
      copyTail_sound room rep'' count'' done
    have debit : atDistance.totalRead - before.totalRead = commandBits.length + literalBits.length := by omega
    rw [debit] at distanceCap
    refine ⟨grows, blockCap, outputCap, commandBits ++ literalBits ++ distanceBits, suffix, ?_, ?_,
      rep''', count''', ?_, ?_⟩
    · exact ⟨commandBits, literalBits, distanceBits, tree, tables, inserted.bytes, inserted.state.history,
        matched, rfl, selected, commandWire, source, literalWire, size, tailWire, output⟩
    · simp only [splitCommand, splitLiteral, splitTail, List.append_assoc]
    · simp only [List.length_append, distanceOffset, literalOffset, commandOffset]
      omega
    · simp only [List.length_append]
      omega

end Silmaril.Proofs.Formats.Compression.Brotli.Execute
