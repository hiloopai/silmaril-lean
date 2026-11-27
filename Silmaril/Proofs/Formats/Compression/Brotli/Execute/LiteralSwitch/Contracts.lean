module

public import Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch.Defs
import Silmaril.Formats.Compression.Brotli.Execute.Thms
import Silmaril.Formats.Compression.Brotli.Literal.Switch.Thms
import Silmaril.Formats.Compression.Brotli.BlockTypes.Switch.Thms
import Silmaril.Formats.Compression.Brotli.Command.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Execute.LiteralSwitch

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Execute (Block)
open Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch
open Silmaril.Formats.Compression.Brotli.Literal.Switch (Source)

theorem bind_ok {ε α β : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (parsed : (action >>= next) = .ok value) :
    ∃ result, action = .ok result ∧ next result = .ok value := by
  cases action with
  | error _ => cases parsed
  | ok result => exact ⟨result, rfl, parsed⟩

theorem bind_mapped_ok {ε δ α β : Type} {action : Except ε α} {next : α → Except δ β}
    {map : ε → δ} {value : β} (parsed : (action.mapError map >>= next) = .ok value) :
    ∃ result, action = .ok result ∧ next result = .ok value := by
  cases action with
  | error _ => cases parsed
  | ok result => exact ⟨result, rfl, parsed⟩

theorem readPrefixCore_sound {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {initial : Execute.InsertCopy.State} {before after : LSBReader} {input : List Bool} {pref : Prefix}
    (rep : before.Rep input) (count : before.count < 8)
    (parsed : readPrefixCore header block limits initial before = .ok (pref, after)) :
    10 ≤ block.windowBits ∧ block.windowBits ≤ 24 ∧
    block.start ≤ initial.execution.output.size ∧ initial.execution.output.size < block.endOutput ∧
    initial.execution.output.size + pref.command.insertLength ≤ block.endOutput ∧
    initial.execution.output.size + pref.command.insertLength ≤ limits.output ∧
    ∃ used suffix, PrefixWire header initial used pref ∧ Source before after input used suffix ∧
      used.length ≤ limits.bits := by
  unfold readPrefixCore at parsed
  split at parsed
  · cases parsed
  rename_i window
  split at parsed
  · cases parsed
  rename_i blockBounds
  split at parsed
  · cases parsed
  obtain ⟨⟨runs, atCommand⟩, switched, parsed⟩ := bind_mapped_ok parsed
  dsimp only at parsed
  split at parsed
  · rename_i table selected
    obtain ⟨⟨command, atLiterals⟩, commandRead, parsed⟩ := bind_mapped_ok parsed
    dsimp only at parsed
    split at parsed
    · cases parsed
    rename_i blockCap
    split at parsed
    · cases parsed
    rename_i outputCap
    cases parsed
    obtain ⟨_, other, switchBits, tail, wire, split, tailRep, tailCount, position, cap⟩ :=
      BlockTypes.Switch.select_sound rep count switched
    obtain ⟨commandBits, suffix, commandWire, commandSplit, afterRep, afterCount, offset, bitCap⟩ :=
      Command.read_sound tailRep tailCount commandRead
    have first : Source before atCommand input switchBits tail := ⟨split, tailRep, tailCount, position⟩
    have second : Source atCommand after tail commandBits suffix :=
      ⟨commandSplit, afterRep, afterCount, offset⟩
    have firstBound : block.start ≤ initial.execution.output.size := by omega
    have room : initial.execution.output.size < block.endOutput := by omega
    refine ⟨by omega, by omega, firstBound, room, Nat.le_of_not_gt blockCap, Nat.le_of_not_gt outputCap,
      switchBits ++ commandBits, suffix, ⟨other .literal (by decide), other .distance (by decide),
        switchBits, commandBits, table, rfl, wire, selected, commandWire⟩,
      Literal.Switch.Source.trans first second, ?_⟩
    change commandBits.length ≤ limits.bits - (atCommand.totalRead - before.totalRead) at bitCap
    simp only [List.length_append]
    omega
  · cases parsed

private theorem readPrefix_sound {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {initial : Execute.InsertCopy.State} {before after : LSBReader} {input : List Bool} {pref : Prefix}
    (rep : before.Rep input) (count : before.count < 8)
    (parsed : readPrefix header block limits initial before = .ok (pref, after)) :
    header.initial.controls.distance = .single ∧ 10 ≤ block.windowBits ∧ block.windowBits ≤ 24 ∧
    block.start ≤ initial.execution.output.size ∧ initial.execution.output.size < block.endOutput ∧
    initial.execution.output.size + pref.command.insertLength ≤ block.endOutput ∧
    initial.execution.output.size + pref.command.insertLength ≤ limits.output ∧
    ∃ used suffix, PrefixWire header initial used pref ∧ Source before after input used suffix ∧
      used.length ≤ limits.bits := by
  unfold readPrefix at parsed
  split at parsed
  · cases parsed
  · rename_i single
    exact ⟨single, readPrefixCore_sound rep count parsed⟩

theorem Wire.distance_preserved {header : CompressedHeader.Header} {block : Block} {initial : Execute.InsertCopy.State}
    {bits : List Bool} {result : Execute.InsertCopy.Result} (wire : Wire header block initial bits result) :
    result.runs.distance = initial.runs.distance := by
  obtain ⟨_, _, _, pref, state, _, _, _, prefixWitness, literals, _, _, runs, _, _⟩ := wire.parts
  rw [runs]
  exact (Literal.Switch.Wire.carry literals).2.2.trans prefixWitness.distance

theorem read_sound {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {initial : Execute.InsertCopy.State} {before after : LSBReader} {input : List Bool}
    {result : Execute.InsertCopy.Result} (rep : before.Rep input) (count : before.count < 8)
    (parsed : Execute.LiteralSwitch.read header block limits initial before = .ok (result, after)) :
    initial.execution.output.size < result.execution.state.output.size ∧
    result.execution.state.output.size ≤ block.endOutput ∧ result.execution.state.output.size ≤ limits.output ∧
    ∃ used suffix, Wire header block initial used result ∧ Source before after input used suffix ∧
      used.length ≤ limits.bits := by
  unfold Execute.LiteralSwitch.read at parsed
  obtain ⟨⟨pref, atLiterals⟩, prefixRead, parsed⟩ := bind_ok parsed
  obtain ⟨⟨bytes, state, atTail⟩, literalRead, parsed⟩ := bind_mapped_ok parsed
  obtain ⟨distance, _, _, _, room, blockCap, outCap, prefixBits, tail, prefixWire, first, prefixCap⟩ :=
    readPrefix_sound rep count prefixRead
  obtain ⟨size, literalBits, suffix, wire, second, literalCap⟩ :=
    Literal.Switch.read_sound first.rep first.count literalRead
  have literalSource := Literal.Switch.Source.trans first second
  have beforeTail := literalSource.position
  have beforeLiterals := first.position
  rw [← size] at blockCap outCap
  have bitsFit : (prefixBits ++ literalBits).length ≤ limits.bits := by
    change literalBits.length ≤ limits.bits - (atLiterals.totalRead - before.totalRead) at literalCap
    simp only [List.length_append]
    omega
  dsimp only at parsed
  split at parsed
  · rename_i terminal
    cases parsed
    have outputShape : (initial.execution.output ++ bytes.toArray).toList = initial.execution.output.toList ++ bytes := by simp
    refine ⟨?_, ?_, ?_, prefixBits ++ literalBits, suffix, ⟨distance, prefixBits, literalBits, [], pref, state, bytes, [],
      by simp, prefixWire, wire, size, rfl, rfl, .terminal (by simpa using terminal), by simp [outputShape]⟩,
      literalSource, bitsFit⟩
    · simp only [Array.size_append, List.size_toArray]
      omega
    · simpa only [Array.size_append, List.size_toArray] using blockCap
    · simpa only [Array.size_append, List.size_toArray] using outCap
  · rename_i pending
    obtain ⟨⟨executed, after⟩, tailRead, done⟩ := bind_mapped_ok parsed
    cases done
    have pending : initial.execution.output.size + bytes.length < block.endOutput := by omega
    obtain ⟨same, grows, extent, cap, tailBits, matched, rest, tailWire, append,
      tailSplit, afterRep, afterCount, position, tailCap⟩ :=
      Execute.copyTail_sound pending second.rep second.count tailRead
    have finalSource : Source atTail after suffix tailBits rest := ⟨tailSplit, afterRep, afterCount, position⟩
    refine ⟨grows, extent, cap, (prefixBits ++ literalBits) ++ tailBits, rest,
      ⟨distance, prefixBits, literalBits, tailBits, pref, state, bytes, matched, rfl, prefixWire, wire, size,
        same, rfl, tailWire, append⟩,
      Literal.Switch.Source.trans literalSource finalSource, ?_⟩
    change tailBits.length ≤ limits.bits - (atTail.totalRead - before.totalRead) at tailCap
    simp only [List.length_append] at beforeTail bitsFit ⊢
    omega

private theorem CommandPrefix.ofRead {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {initial : Execute.InsertCopy.State} {before atLiterals : LSBReader} {input : List Bool} {pref : Prefix}
    (rep : before.Rep input) (count : before.count < 8)
    (parsed : readPrefix header block limits initial before = .ok (pref, atLiterals)) :
    ∃ used suffix, CommandPrefix header block limits initial before atLiterals input suffix pref ∧
      Source before atLiterals input used suffix := by
  obtain ⟨_, _, _, _, _, _, _, used, suffix, wire, source, cap⟩ := readPrefix_sound rep count parsed
  exact ⟨used, suffix, ⟨parsed, used, wire, source, cap⟩, source⟩

theorem read_error {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {initial : Execute.InsertCopy.State} {before : LSBReader} {input : List Bool} {error : Execute.LiteralSwitch.Error}
    (rep : before.Rep input) (count : before.count < 8)
    (parsed : Execute.LiteralSwitch.read header block limits initial before = .error error) :
    Failure header block limits initial before input error := by
  unfold Execute.LiteralSwitch.read at parsed
  cases prefixRead : readPrefix header block limits initial before with
  | error reason =>
    simp only [prefixRead, bind, Except.bind] at parsed
    cases parsed
    exact .beforeLiterals prefixRead
  | ok pair =>
    obtain ⟨pref, atLiterals⟩ := pair
    simp only [prefixRead, bind, Except.bind] at parsed
    obtain ⟨used, suffix, prefixWitness, first⟩ := CommandPrefix.ofRead rep count prefixRead
    cases literalRead : Literal.Switch.read header pref.command.insertLength
        (remainingBits limits.bits before atLiterals) (pref.literalState initial) atLiterals with
    | error reason =>
      simp only [literalRead, Except.mapError] at parsed
      cases parsed
      exact .literal prefixWitness (Literal.Switch.read_error first.rep first.count literalRead)
    | ok triple =>
      obtain ⟨bytes, state, atTail⟩ := triple
      simp only [literalRead, Except.mapError] at parsed
      split at parsed
      · cases parsed
      · rename_i pending
        cases tailRead : Execute.Internal.copyTail header block limits initial.execution pref.command bytes
            (remainingBits limits.bits before atTail) atTail with
        | error reason =>
          simp only [tailRead] at parsed
          cases parsed
          obtain ⟨_, used, tail, _, source, _⟩ := Literal.Switch.read_sound first.rep first.count literalRead
          exact .tail prefixWitness literalRead source pending tailRead
        | ok pair =>
          obtain ⟨_, _⟩ := pair
          simp only [tailRead] at parsed
          cases parsed

private def Offset (before : LSBReader) (input : List Bool) (bit : Nat) : Prop :=
  ∃ used suffix, input = used ++ suffix ∧ bit = before.totalRead + used.length

private theorem Offset.here (before : LSBReader) (input : List Bool) : Offset before input before.totalRead :=
  ⟨[], input, rfl, by simp⟩

private theorem Offset.prepend {before after : LSBReader} {input used tail : List Bool} {bit : Nat}
    (first : Source before after input used tail) (offset : Offset after tail bit) :
    Offset before input bit := by
  obtain ⟨read, suffix, split, position⟩ := offset
  exact ⟨used ++ read, suffix, by rw [first.split, split, List.append_assoc],
    by rw [position, first.position, List.length_append, Nat.add_assoc]⟩

theorem readPrefixCore_error_offset {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {initial : Execute.InsertCopy.State} {before : LSBReader} {input : List Bool} {error : Execute.LiteralSwitch.Error}
    (rep : before.Rep input) (count : before.count < 8)
    (parsed : readPrefixCore header block limits initial before = .error error) :
    ∃ used suffix, input = used ++ suffix ∧ error.bit = before.totalRead + used.length := by
  unfold readPrefixCore at parsed
  split at parsed
  · cases parsed
    exact Offset.here before input
  split at parsed
  · cases parsed
    exact Offset.here before input
  split at parsed
  · cases parsed
    exact Offset.here before input
  cases switchRead : BlockTypes.Switch.select header.initial.controls .insertCopy limits.bits initial.runs before with
  | error reason =>
    simp only [switchRead, Except.mapError, bind, Except.bind] at parsed
    cases parsed
    exact (BlockTypes.Switch.select_error rep count switchRead).offset
  | ok pair =>
    obtain ⟨runs, atCommand⟩ := pair
    simp only [switchRead, Except.mapError, bind, Except.bind] at parsed
    obtain ⟨_, _, used, suffix, _, split, nextRep, nextCount, position, _⟩ :=
      BlockTypes.Switch.select_sound rep count switchRead
    have first : Source before atCommand input used suffix := ⟨split, nextRep, nextCount, position⟩
    cases treeRead : header.insertCopyTrees[runs.insertCopy.current]? with
    | none =>
      simp only [treeRead] at parsed
      cases parsed
      exact Offset.prepend first (Offset.here atCommand suffix)
    | some tree =>
      simp only [treeRead] at parsed
      cases commandRead : Command.read tree (remainingBits limits.bits before atCommand) atCommand with
      | error reason =>
        simp only [commandRead] at parsed
        cases parsed
        exact Offset.prepend first (Offset.here atCommand suffix)
      | ok pair =>
        obtain ⟨command, atLiterals⟩ := pair
        simp only [commandRead] at parsed
        obtain ⟨commandBits, rest, _, commandSplit, afterRep, afterCount, offset, _⟩ :=
          Command.read_sound nextRep nextCount commandRead
        have second : Source atCommand atLiterals suffix commandBits rest :=
          ⟨commandSplit, afterRep, afterCount, offset⟩
        split at parsed
        · cases parsed
          exact Offset.prepend first (Offset.prepend second (Offset.here atLiterals rest))
        · split at parsed
          · cases parsed
            exact Offset.prepend first (Offset.prepend second (Offset.here atLiterals rest))
          · cases parsed

private theorem prefix_offset {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {initial : Execute.InsertCopy.State} {before : LSBReader} {input : List Bool} {error : Execute.LiteralSwitch.Error}
    (rep : before.Rep input) (count : before.count < 8)
    (parsed : readPrefix header block limits initial before = .error error) :
    Offset before input error.bit := by
  unfold readPrefix at parsed
  split at parsed
  · cases parsed
    exact Offset.here before input
  · exact readPrefixCore_error_offset rep count parsed

theorem Failure.offset {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {initial : Execute.InsertCopy.State} {before : LSBReader} {input : List Bool} {error : Execute.LiteralSwitch.Error}
    (rep : before.Rep input) (count : before.count < 8)
    (failure : Failure header block limits initial before input error) :
    ∃ used suffix, input = used ++ suffix ∧ error.bit = before.totalRead + used.length := by
  cases failure with
  | beforeLiterals parsed => exact prefix_offset rep count parsed
  | literal prefixWitness failure =>
    obtain ⟨_, _, source, _⟩ := prefixWitness.extent
    exact Offset.prepend source failure.offset
  | tail prefixWitness _ second _ _ =>
    obtain ⟨_, _, first, _⟩ := prefixWitness.extent
    exact Offset.prepend first (Offset.prepend second (Offset.here _ _))

end Silmaril.Proofs.Formats.Compression.Brotli.Execute.LiteralSwitch
