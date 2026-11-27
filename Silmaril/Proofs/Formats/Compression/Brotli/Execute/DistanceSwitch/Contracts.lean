module

public import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Defs
import Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch.Thms
import Silmaril.Formats.Compression.Brotli.Execute.Thms
import Silmaril.Formats.Compression.Brotli.Literal.Switch.Thms
import Silmaril.Formats.Compression.Brotli.BlockTypes.Switch.Thms
import Silmaril.Formats.Compression.Brotli.Distance.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Execute (Block)
open Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch
open Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Internal
open Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch (remainingBits)
open Silmaril.Formats.Compression.Brotli.Literal.Switch (Source)
open Silmaril.Formats.Compression.Brotli.BlockTypes.Switch (State)

private theorem bind_mapped_ok {ε δ α β : Type} {action : Except ε α} {next : α → Except δ β}
    {map : ε → δ} {value : β} (parsed : (action.mapError map >>= next) = .ok value) :
    ∃ result, action = .ok result ∧ next result = .ok value := by
  cases action with
  | error _ => cases parsed
  | ok result => exact ⟨result, rfl, parsed⟩

private theorem bind_ok {ε α β : Type} {action : Except ε α} {next : α → Except ε β}
    {value : β} (parsed : (action >>= next) = .ok value) :
    ∃ result, action = .ok result ∧ next result = .ok value := by
  cases action with
  | error _ => cases parsed
  | ok result => exact ⟨result, rfl, parsed⟩

private theorem select_sound {header : CompressedHeader.Header} {command : Command.Value} {bitLimit : Nat}
    {runs next : State} {before after : LSBReader} {input : List Bool}
    (rep : before.Rep input) (count : before.count < 8)
    (parsed : select header command bitLimit runs before = .ok (next, after)) :
    ∃ used suffix, SelectionWire header.initial.controls.distance command runs used next ∧
      Source before after input used suffix ∧ used.length ≤ bitLimit := by
  unfold select at parsed
  split at parsed
  · rename_i implicit
    cases parsed
    exact ⟨[], input, .implicit implicit, ⟨by simp, rep, count, by simp⟩, by simp⟩
  · rename_i explicit
    obtain ⟨valid, stable, used, suffix, wire, split, rep', count', offset, fit⟩ :=
      BlockTypes.Switch.select_sound rep count parsed
    exact ⟨used, suffix, .explicit explicit valid wire (stable .literal (by decide))
      (stable .insertCopy (by decide)), ⟨split, rep', count', offset⟩, fit⟩

private theorem resolve_sound {header : CompressedHeader.Header} {command : Command.Value}
    {bounds : Distance.Bounds} {ring : Distance.Ring} {bitLimit : Nat} {runs next : State}
    {before after : LSBReader} {input : List Bool} {resolved : Distance.Result}
    (rep : before.Rep input) (count : before.count < 8)
    (parsed : resolve header command bounds ring bitLimit runs before = .ok (resolved, next, after)) :
    2 ≤ command.copyLength ∧
    ∃ switchBits distanceBits suffix,
      SelectionWire header.initial.controls.distance command runs switchBits next ∧
      Distance.WireAt header command bounds ring next.distance.current distanceBits resolved ∧
      Source before after input (switchBits ++ distanceBits) suffix ∧
      (switchBits ++ distanceBits).length ≤ bitLimit := by
  unfold resolve at parsed
  obtain ⟨⟨chosen, atCode⟩, selected, parsed⟩ := bind_mapped_ok parsed
  obtain ⟨⟨value, stop⟩, decoded, parsed⟩ := bind_mapped_ok parsed
  cases parsed
  obtain ⟨control, tail, selection, first, controlFits⟩ := select_sound rep count selected
  obtain ⟨_, copyLength, _, bits, suffix, wire, split, rep', count', offset, valueFits⟩ :=
    Distance.readAt_sound first.rep first.count decoded
  have second : Source atCode after tail bits suffix := ⟨split, rep', count', offset⟩
  have position := first.position
  change bits.length ≤ bitLimit - (atCode.totalRead - before.totalRead) at valueFits
  exact ⟨copyLength, control, bits, suffix, selection, wire, first.trans second,
    by simp only [List.length_append]; omega⟩

theorem readWith_sound {finishCopy : Internal.FinishCopy} {header : CompressedHeader.Header}
    {block : Block} {limits : Execute.Limits} {initial : Execute.InsertCopy.State}
    {before after : LSBReader} {input : List Bool} {result : Execute.InsertCopy.Result}
    (rep : before.Rep input) (count : before.count < 8)
    (parsed : readWith finishCopy header block limits initial before = .ok (result, after)) :
    ∃ used suffix, ReadWire finishCopy header block limits initial used result ∧
      Source before after input used suffix ∧ used.length ≤ limits.bits := by
  unfold readWith at parsed
  obtain ⟨⟨pref, atLiterals⟩, prefixRead, parsed⟩ := bind_mapped_ok parsed
  obtain ⟨⟨literals, state, atDistance⟩, literalRead, parsed⟩ := bind_mapped_ok parsed
  obtain ⟨_, _, _, room, blockFit, outFit, prefixBits, tail, prefixWire, first, prefixFit⟩ :=
    Execute.LiteralSwitch.readPrefixCore_sound rep count prefixRead
  obtain ⟨length, literalBits, suffix, literalWire, second, literalFit⟩ :=
    Literal.Switch.read_sound first.rep first.count literalRead
  have insertion := first.trans second
  have afterPrefix := first.position
  have afterInsert := insertion.position
  rw [← length] at blockFit outFit
  have insertBitsFit : (prefixBits ++ literalBits).length ≤ limits.bits := by
    change literalBits.length ≤ limits.bits - (atLiterals.totalRead - before.totalRead) at literalFit
    simp only [List.length_append]
    omega
  dsimp only at parsed
  split at parsed
  · rename_i terminal
    cases parsed
    exact ⟨prefixBits ++ literalBits, suffix,
      ⟨prefixBits, literalBits, [], pref, state, literals, by simp, prefixWire, literalWire, length,
        room, blockFit, outFit, .terminal terminal⟩, insertion, insertBitsFit⟩
  · rename_i pending
    obtain ⟨⟨resolved, runs, stop⟩, distanceRead, parsed⟩ := bind_ok parsed
    obtain ⟨executed, copied, parsed⟩ := bind_mapped_ok parsed
    cases parsed
    obtain ⟨copyLength, switchBits, distanceBits, rest, selection, distanceWire, source, distanceFit⟩ :=
      resolve_sound second.rep second.count distanceRead
    refine ⟨(prefixBits ++ literalBits) ++ (switchBits ++ distanceBits), rest,
      ⟨prefixBits, literalBits, switchBits ++ distanceBits, pref, state, literals, rfl, prefixWire,
        literalWire, length, room, blockFit, outFit, .copy (by omega) copyLength selection distanceWire copied⟩,
      insertion.trans source, ?_⟩
    change (switchBits ++ distanceBits).length ≤
      limits.bits - (atDistance.totalRead - before.totalRead) at distanceFit
    simp only [List.length_append] at afterInsert insertBitsFit distanceFit ⊢
    omega

theorem read_sound {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {initial : Execute.InsertCopy.State} {before after : LSBReader} {input : List Bool}
    {result : Execute.InsertCopy.Result} (rep : before.Rep input) (count : before.count < 8)
    (parsed : Execute.DistanceSwitch.read header block limits initial before = .ok (result, after)) :
    initial.execution.output.size < result.execution.state.output.size ∧
    result.execution.state.output.size ≤ block.endOutput ∧ result.execution.state.output.size ≤ limits.output ∧
    ∃ used suffix, Wire header block initial used result ∧
      Source before after input used suffix ∧ used.length ≤ limits.bits := by
  obtain ⟨used, suffix, wire, source, fits⟩ := readWith_sound rep count parsed
  obtain ⟨prefixBits, literalBits, tailBits, pref, state, literals, rfl, prefixWire, literalWire, length,
    room, blockFit, outFit, finish⟩ := wire
  cases finish with
  | terminal terminal =>
    refine ⟨?_, ?_, ?_, _, suffix, ⟨prefixBits, literalBits, [], pref, state, literals, [],
      rfl, prefixWire, literalWire, length, rfl, .terminal (by simpa using terminal), by simp⟩,
      source, fits⟩
    · simp only [Array.size_append, List.size_toArray]; omega
    · simpa only [Array.size_append, List.size_toArray] using blockFit
    · simpa only [Array.size_append, List.size_toArray] using outFit
  | copy pending copyLength selection value copied =>
    obtain ⟨same, ring, extent, cap, distance, bytes, target, observed, copied, size, output⟩ :=
      Execute.applyCopy_sound copied
    have outputSize := congrArg List.length output
    rw [List.length_append, size, Array.length_toList] at outputSize
    have sourceLength : (initial.execution.output.toList ++ literals).length =
        initial.execution.output.size + literals.length := by simp
    rw [sourceLength] at outputSize
    refine ⟨by dsimp; omega, extent, cap, _, suffix,
      ⟨prefixBits, literalBits, _, pref, state, literals, bytes, rfl, prefixWire, literalWire, length,
        same, ?_, output⟩, source, fits⟩
    dsimp
    rw [observed, ring]
    refine .copy (by simpa only [sourceLength] using pending) selection ?_ target copied size
    simpa only [sourceLength] using value

private theorem TailWire.copy_length {header : CompressedHeader.Header} {block : Block}
    {command : Command.Value} {ring after : Distance.Ring} {beforeCopy matched : List UInt8}
    {initial final : State} {bits : List Bool} {distance : Option Nat}
    (wire : TailWire header block command ring beforeCopy initial bits matched distance after final) :
    matched.length = (if distance.isSome then command.copyLength else 0) := by
  cases wire with
  | terminal => rfl
  | copy _ _ _ _ _ length => exact length

theorem Wire.output_count {header : CompressedHeader.Header} {block : Block}
    {initial : Execute.InsertCopy.State} {bits : List Bool} {result : Execute.InsertCopy.Result}
    (wire : Wire header block initial bits result) :
    result.execution.state.output.size = initial.execution.output.size + result.execution.command.insertLength +
      (if result.execution.distance.isSome then result.execution.command.copyLength else 0) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, length, command, tail, output⟩ := wire.parts
  simpa only [Array.length_toList, List.length_append, length, command, TailWire.copy_length tail]
    using congrArg List.length output

theorem SelectionWire.other_runs {control : BlockTypes.Control} {command : Command.Value}
    {initial final : State} {bits : List Bool} (wire : SelectionWire control command initial bits final) :
    final.literal = initial.literal ∧ final.insertCopy = initial.insertCopy := by
  cases wire with
  | implicit _ => exact ⟨rfl, rfl⟩
  | explicit _ _ _ literal insert => exact ⟨literal, insert⟩

theorem SelectionWire.implicit_preserved {control : BlockTypes.Control} {command : Command.Value}
    {initial final : State} {bits : List Bool} (wire : SelectionWire control command initial bits final)
    (implicit : command.distance = .implicitZero) : bits = [] ∧ final = initial := by
  cases wire with
  | implicit _ => exact ⟨rfl, rfl⟩
  | explicit explicit => rw [implicit] at explicit; cases explicit

private theorem TailWire.no_distance_symbol {header : CompressedHeader.Header} {block : Block}
    {command : Command.Value} {ring after : Distance.Ring} {beforeCopy matched : List UInt8}
    {initial final : State} {bits : List Bool} {distance : Option Nat}
    (wire : TailWire header block command ring beforeCopy initial bits matched distance after final)
    (absent : distance = none ∨ command.distance = .implicitZero) :
    final.distance = initial.distance ∧ after = ring := by
  cases wire with
  | terminal => exact ⟨rfl, rfl⟩
  | copy _ selection value _ _ _ =>
    have implicit : command.distance = .implicitZero := by
      rcases absent with impossible | implicit
      · cases impossible
      · exact implicit
    have runs := (SelectionWire.implicit_preserved selection implicit).2
    cases value with
    | explicit mode => rw [implicit] at mode; cases mode
    | implicit _ resolved =>
      cases resolved <;> exact ⟨by rw [runs], rfl⟩

theorem Wire.no_distance_symbol {header : CompressedHeader.Header} {block : Block}
    {initial : Execute.InsertCopy.State} {bits : List Bool} {result : Execute.InsertCopy.Result}
    (wire : Wire header block initial bits result)
    (absent : result.execution.distance = none ∨ result.execution.command.distance = .implicitZero) :
    result.runs.distance = initial.runs.distance ∧ result.execution.state.ring = initial.execution.ring := by
  obtain ⟨_, _, _, pref, _, _, _, _, prefixWitness, literal, _, command, tail, _⟩ := wire.parts
  have prior := (Literal.Switch.Wire.carry literal).2.2.trans prefixWitness.distance
  rw [command] at absent
  obtain ⟨preserved, ring⟩ := TailWire.no_distance_symbol tail absent
  exact ⟨preserved.trans prior, ring⟩

private theorem resolve_error {header : CompressedHeader.Header} {command : Command.Value}
    {bounds : Distance.Bounds} {ring : Distance.Ring} {bitLimit : Nat} {runs : State}
    {before : LSBReader} {input : List Bool} {error : Execute.DistanceSwitch.Error}
    (rep : before.Rep input) (count : before.count < 8)
    (parsed : resolve header command bounds ring bitLimit runs before = .error error) :
    ResolveFailure header command bounds ring bitLimit runs before input error := by
  unfold resolve at parsed
  cases selected : select header command bitLimit runs before with
  | error reason =>
    simp only [selected, Except.mapError, bind, Except.bind] at parsed
    cases parsed
    unfold select at selected
    split at selected
    · cases selected
    · rename_i explicit
      exact .switch explicit (BlockTypes.Switch.select_error rep count selected)
  | ok pair =>
    obtain ⟨next, atCode⟩ := pair
    simp only [selected, Except.mapError, bind, Except.bind] at parsed
    cases readValue : Distance.Internal.readAt header next.distance.current command bounds ring
        (remainingBits bitLimit before atCode) atCode with
    | error reason =>
      simp only [readValue] at parsed
      cases parsed
      obtain ⟨used, suffix, wire, source, _⟩ := select_sound rep count selected
      exact .value selected wire source readValue
    | ok pair =>
      obtain ⟨_, _⟩ := pair
      simp only [readValue] at parsed
      cases parsed

theorem readWith_error {finishCopy : Internal.FinishCopy} {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {initial : Execute.InsertCopy.State} {before : LSBReader} {input : List Bool} {error : Execute.DistanceSwitch.Error}
    (rep : before.Rep input) (count : before.count < 8)
    (parsed : Internal.readWith finishCopy header block limits initial before = .error error) :
    Failure header block limits initial before input error finishCopy := by
  unfold Internal.readWith at parsed
  cases prefixRead : Execute.LiteralSwitch.readPrefixCore header block limits initial before with
  | error reason =>
    simp only [prefixRead, Except.mapError, bind, Except.bind] at parsed
    cases parsed
    exact .commandPrefix prefixRead
  | ok pair =>
    obtain ⟨pref, atLiterals⟩ := pair
    simp only [prefixRead, Except.mapError, bind, Except.bind] at parsed
    obtain ⟨_, _, _, _, _, _, used, suffix, wire, source, _⟩ :=
      Execute.LiteralSwitch.readPrefixCore_sound rep count prefixRead
    have prefixWitness : PrefixPath header block limits initial before atLiterals input suffix pref :=
      ⟨prefixRead, used, wire, source⟩
    cases literalRead : Literal.Switch.read header pref.command.insertLength
        (remainingBits limits.bits before atLiterals) (pref.literalState initial) atLiterals with
    | error reason =>
      simp only [literalRead] at parsed
      cases parsed
      exact .literal prefixWitness (Literal.Switch.read_error source.rep source.count literalRead)
    | ok triple =>
      obtain ⟨literals, state, atDistance⟩ := triple
      simp only [literalRead] at parsed
      split at parsed
      · cases parsed
      · rename_i pending
        obtain ⟨_, bits, tail, _, second, _⟩ := Literal.Switch.read_sound source.rep source.count literalRead
        have path : LiteralPath header block limits initial before atDistance input tail pref literals state :=
          ⟨atLiterals, suffix, bits, prefixWitness, literalRead, second, pending⟩
        cases distanceRead : resolve header pref.command ⟨block.windowBits, initial.execution.output.size + literals.length⟩
            initial.execution.ring (remainingBits limits.bits before atDistance) state.runs atDistance with
        | error reason =>
          simp only [distanceRead] at parsed
          cases parsed
          exact .resolve path (resolve_error second.rep second.count distanceRead)
        | ok triple =>
          obtain ⟨resolved, runs, after⟩ := triple
          simp only [distanceRead] at parsed
          cases copied : finishCopy block limits initial.execution pref.command literals resolved with
          | error reason =>
            simp only [copied] at parsed
            cases parsed
            obtain ⟨_, switchBits, distanceBits, rest, _, _, third, _⟩ :=
              resolve_sound second.rep second.count distanceRead
            exact .copy path distanceRead third copied
          | ok result =>
            simp only [copied] at parsed
            cases parsed

theorem read_error {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {initial : Execute.InsertCopy.State} {before : LSBReader} {input : List Bool} {error : Execute.DistanceSwitch.Error}
    (rep : before.Rep input) (count : before.count < 8)
    (parsed : Execute.DistanceSwitch.read header block limits initial before = .error error) :
    Failure header block limits initial before input error :=
  readWith_error rep count parsed

private def Offset (before : LSBReader) (input : List Bool) (bit : Nat) : Prop :=
  ∃ used suffix, input = used ++ suffix ∧ bit = before.totalRead + used.length

private theorem Offset.prepend {before after : LSBReader} {input used tail : List Bool} {bit : Nat}
    (prefixWitness : Source before after input used tail) (offset : Offset after tail bit) :
    Offset before input bit := by
  obtain ⟨read, suffix, split, position⟩ := offset
  exact ⟨used ++ read, suffix, by rw [prefixWitness.split, split, List.append_assoc],
    by rw [position, prefixWitness.position, List.length_append, Nat.add_assoc]⟩

private theorem ResolveFailure.offset {header : CompressedHeader.Header} {command : Command.Value}
    {bounds : Distance.Bounds} {ring : Distance.Ring} {bitLimit : Nat} {runs : State}
    {before : LSBReader} {input : List Bool} {error : Execute.DistanceSwitch.Error}
    (failed : ResolveFailure header command bounds ring bitLimit runs before input error) :
    Offset before input error.bit := by
  cases failed with
  | switch _ reason => exact reason.offset
  | value _ _ source _ => exact ⟨_, _, source.split, source.position⟩

theorem Failure.offset {finishCopy : Internal.FinishCopy} {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {initial : Execute.InsertCopy.State} {before : LSBReader} {input : List Bool}
    {error : Execute.DistanceSwitch.Error} (rep : before.Rep input) (count : before.count < 8)
    (failed : Failure header block limits initial before input error finishCopy) :
    ∃ used suffix, input = used ++ suffix ∧ error.bit = before.totalRead + used.length := by
  cases failed with
  | commandPrefix parsed => exact Execute.LiteralSwitch.readPrefixCore_error_offset rep count parsed
  | literal prefixWitness reason =>
    obtain ⟨_, _, source⟩ := prefixWitness.extent
    exact Offset.prepend source reason.offset
  | resolve path reason =>
    obtain ⟨_, _, _, prefixWitness, _, second, _⟩ := path.parts
    obtain ⟨_, _, first⟩ := prefixWitness.extent
    exact Offset.prepend (first.trans second) (ResolveFailure.offset reason)
  | copy path _ third _ =>
    obtain ⟨_, _, _, prefixWitness, _, second, _⟩ := path.parts
    obtain ⟨_, _, first⟩ := prefixWitness.extent
    exact Offset.prepend (first.trans second) ⟨_, _, third.split, third.position⟩

end Silmaril.Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch
