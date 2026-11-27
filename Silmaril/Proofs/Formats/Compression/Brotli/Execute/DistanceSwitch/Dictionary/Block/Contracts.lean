module

public import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.Block.Defs
import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.Thms
import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Thms
import Silmaril.Formats.Compression.Brotli.Distance.Thms
import Silmaril.Formats.Compression.Brotli.Literal.Switch.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.Block

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Execute (Block)
open Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch
open Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary
open Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch (remainingBits)
open Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch.Internal (runWithResult)
open Silmaril.Formats.Compression.Brotli.Literal.Switch (Source)

private theorem appended {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {initial : Execute.InsertCopy.State} {used : List Bool} {result : Execute.InsertCopy.Result}
    (wire : Dictionary.Wire header block limits initial used result) :
    ∃ chunk, result.execution.state.output.toList = initial.execution.output.toList ++ chunk := by
  obtain ⟨_, _, _, _, _, literals, _, _, _, _, _, _, _, finish⟩ := wire
  cases finish with
  | terminal => exact ⟨literals, by simp⟩
  | copy _ _ _ target copied =>
    have effect := (finishCopy_sound target.resolved copied).2.2
    obtain ⟨bytes, _, emitted⟩ := effect.parts
    exact ⟨literals ++ bytes, by simpa only [List.append_assoc] using emitted⟩

theorem CommandsWire.output {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {origin before after : LSBReader} {initial final : Execute.InsertCopy.State} {input suffix : List Bool}
    {chunks : List (List UInt8)} (wire : CommandsWire header block limits origin initial before input suffix chunks final after) :
    final.execution.output.size = block.endOutput ∧
    final.execution.output.toList = initial.execution.output.toList ++ chunks.flatten := by
  induction wire with
  | done size => exact ⟨size, by simp⟩
  | step _ _ _ emitted _ ih =>
    exact ⟨ih.1, by simp [ih.2, Execute.InsertCopy.Result.state, emitted, List.append_assoc]⟩

private theorem run_sound {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {origin before : LSBReader} {fuel index : Nat} {initial : Execute.InsertCopy.State} {final : BlockResult} {input : List Bool}
    (rep : before.Rep input) (count : before.count < 8)
    (afterOrigin : origin.totalRead ≤ before.totalRead) (bitFit : before.totalRead ≤ origin.totalRead + limits.bits)
    (outFit : initial.execution.output.size ≤ limits.output)
    (parsed : runWithResult (fun remaining state cursor => ⟨state, cursor, remaining⟩) (Dictionary.read header block) BlockError.command BlockError.fuel block limits origin
      fuel index initial before = .ok final) :
    final.state.execution.output.size ≤ limits.output ∧ final.cursor.totalRead ≤ origin.totalRead + limits.bits ∧
    ∃ used suffix chunks, CommandsWire header block limits origin initial before input suffix chunks final.state final.cursor ∧
      chunks.length + final.remainingCommands = fuel ∧ Source before final.cursor input used suffix := by
  induction fuel generalizing index initial final before input with
  | zero =>
    unfold runWithResult at parsed
    split at parsed
    · rename_i done
      cases parsed
      exact ⟨outFit, bitFit, [], input, [], .done done, by simp, ⟨rfl, rep, count, by simp⟩⟩
    · cases parsed
  | succ fuel ih =>
    unfold runWithResult at parsed
    split at parsed
    · rename_i done
      cases parsed
      exact ⟨outFit, bitFit, [], input, [], .done done, by simp, ⟨rfl, rep, count, by simp⟩⟩
    · cases commandRead : Dictionary.read header block {limits with bits := remainingBits limits.bits origin before}
        initial before with
      | error reason => simp [commandRead, Except.mapError, bind, Except.bind] at parsed
      | ok pair =>
        obtain ⟨result, next⟩ := pair
        simp only [commandRead, Except.mapError, bind, Except.bind] at parsed
        obtain ⟨_, _, nextFit, used, tail, wire, first, fits⟩ := Dictionary.read_sound rep count commandRead
        obtain ⟨chunk, output⟩ := appended wire
        have shifted := first.position
        change used.length ≤ limits.bits - (before.totalRead - origin.totalRead) at fits
        obtain ⟨outFits, bitFits, rest, suffix, chunks, chain, steps, second⟩ :=
          ih first.rep first.count (by omega) (by omega) nextFit parsed
        exact ⟨outFits, bitFits, used ++ rest, suffix, chunk :: chunks,
          .step commandRead wire first output chain, by simp only [List.length_cons]; omega, first.trans second⟩

theorem readBlockCounted_sound {header : CompressedHeader.Header} {window length commandCap : Nat} {limits : Execute.Limits}
    {initial : Execute.State} {final : BlockResult} {before : LSBReader} {input : List Bool}
    (rep : before.Rep input) (count : before.count < 8)
    (parsed : Dictionary.readBlockCounted header window length commandCap limits initial before = .ok final) :
    final.state.execution.output.size = initial.output.size + length ∧ final.state.execution.output.size ≤ limits.output ∧
    ∃ used suffix chunks,
      CommandsWire header ⟨window, initial.output.size, length⟩ limits before
        (Execute.InsertCopy.State.start header initial) before input suffix chunks final.state final.cursor ∧
      final.state.execution.output.toList = initial.output.toList ++ chunks.flatten ∧
      chunks.length + final.remainingCommands = commandCap ∧ Source before final.cursor input used suffix ∧ used.length ≤ limits.bits := by
  unfold Dictionary.readBlockCounted at parsed
  split at parsed
  · cases parsed
  rename_i exceeded
  obtain ⟨outFit, bitFit, used, suffix, chunks, wire, steps, source⟩ :=
    run_sound rep count (Nat.le_refl _) (by omega) (Nat.le_of_not_gt exceeded) parsed
  obtain ⟨size, output⟩ := CommandsWire.output wire
  have position := source.position
  exact ⟨size, outFit, used, suffix, chunks, wire, output, steps, source, by omega⟩

theorem readBlock_sound {header : CompressedHeader.Header} {window length commandCap : Nat} {limits : Execute.Limits}
    {initial : Execute.State} {final : Execute.InsertCopy.State} {before after : LSBReader} {input : List Bool}
    (rep : before.Rep input) (count : before.count < 8)
    (parsed : Dictionary.readBlock header window length commandCap limits initial before = .ok (final, after)) :
    final.execution.output.size = initial.output.size + length ∧ final.execution.output.size ≤ limits.output ∧
    ∃ used suffix chunks,
      CommandsWire header ⟨window, initial.output.size, length⟩ limits before
        (Execute.InsertCopy.State.start header initial) before input suffix chunks final after ∧
      final.execution.output.toList = initial.output.toList ++ chunks.flatten ∧
      chunks.length ≤ commandCap ∧ Source before after input used suffix ∧ used.length ≤ limits.bits := by
  unfold Dictionary.readBlock at parsed
  cases counted : Dictionary.readBlockCounted header window length commandCap limits initial before with
  | error reason => simp [counted, Except.map] at parsed
  | ok result =>
    simp only [counted, Except.map, Except.ok.injEq, Prod.mk.injEq] at parsed
    obtain ⟨rfl, rfl⟩ := parsed
    obtain ⟨extent, outFits, used, suffix, chunks, commandWire, output, slots, source, bitFits⟩ :=
      readBlockCounted_sound rep count counted
    exact ⟨extent, outFits, used, suffix, chunks, commandWire, output, by omega, source, bitFits⟩

private theorem run_error {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {origin before : LSBReader} {fuel index : Nat} {state : Execute.InsertCopy.State} {input : List Bool}
    {error : BlockError} (rep : before.Rep input) (count : before.count < 8)
    (parsed : runWithResult (fun remaining state cursor => (⟨state, cursor, remaining⟩ : BlockResult)) (Dictionary.read header block) BlockError.command BlockError.fuel block limits origin
      fuel index state before = .error error) :
    FailurePath header block limits origin fuel index state before input error := by
  induction fuel generalizing index state before input with
  | zero =>
    unfold runWithResult at parsed
    split at parsed
    · cases parsed
    · rename_i pending
      cases parsed
      exact .fuel pending
  | succ fuel ih =>
    unfold runWithResult at parsed
    split at parsed
    · cases parsed
    · rename_i pending
      cases commandRead : Dictionary.read header block {limits with bits := remainingBits limits.bits origin before}
          state before with
      | error reason =>
        simp only [commandRead, Except.mapError, bind, Except.bind] at parsed
        cases parsed
        exact .command pending commandRead (Execute.DistanceSwitch.readWith_error rep count commandRead)
      | ok pair =>
        obtain ⟨result, after⟩ := pair
        simp only [commandRead, Except.mapError, bind, Except.bind] at parsed
        obtain ⟨_, _, _, used, tail, wire, source, _⟩ := Dictionary.read_sound rep count commandRead
        exact .next pending commandRead wire source (ih source.rep source.count parsed)

theorem FailurePath.locate {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {origin before : LSBReader} {fuel index : Nat} {state : Execute.InsertCopy.State} {input : List Bool}
    {error : BlockError} (rep : before.Rep input) (count : before.count < 8)
    (failed : FailurePath header block limits origin fuel index state before input error) :
    (∃ used suffix, input = used ++ suffix ∧ error.bit = before.totalRead + used.length) ∧
    match error with
    | .initialOutput _ => False
    | .fuel exhausted _ => exhausted = index + fuel
    | .command failedIndex _ => index ≤ failedIndex ∧ failedIndex < index + fuel := by
  induction failed with
  | @fuel index state before input pending =>
    exact ⟨⟨[], input, rfl, by simp [BlockError.bit]⟩, by simp⟩
  | command _ _ reason =>
    exact ⟨Execute.DistanceSwitch.Failure.offset rep count reason, ⟨Nat.le_refl _, by omega⟩⟩
  | @next fuel index state result before after input previous tail error pending parsed wire source earlier ih =>
    obtain ⟨⟨used, suffix, split, bit⟩, slot⟩ := ih source.rep source.count
    refine ⟨⟨_, suffix, by rw [source.split, split, List.append_assoc],
      by rw [bit, source.position, List.length_append, Nat.add_assoc]⟩, ?_⟩
    cases error <;> (first | exact slot | omega)

theorem readBlockCounted_error {header : CompressedHeader.Header} {window length commandCap : Nat}
    {limits : Execute.Limits} {initial : Execute.State} {before : LSBReader} {input : List Bool}
    {error : BlockError} (rep : before.Rep input) (count : before.count < 8)
    (parsed : Dictionary.readBlockCounted header window length commandCap limits initial before = .error error) :
    (∃ used suffix, input = used ++ suffix ∧ error.bit = before.totalRead + used.length) ∧
      match error with
      | .initialOutput bit => limits.output < initial.output.size ∧ bit = before.totalRead
      | .fuel .. | .command .. =>
        FailurePath header ⟨window, initial.output.size, length⟩ limits before commandCap 0
          (Execute.InsertCopy.State.start header initial) before input error := by
  unfold Dictionary.readBlockCounted at parsed
  split at parsed
  · rename_i initialCap
    cases parsed
    exact ⟨⟨[], input, rfl, by simp [BlockError.bit]⟩, initialCap, rfl⟩
  · rename_i admits
    dsimp only at parsed
    have found := run_error rep count parsed
    obtain ⟨offset, slot⟩ := FailurePath.locate rep count found
    cases error with
    | initialOutput _ => exact False.elim slot
    | fuel | command => exact ⟨offset, found⟩

theorem readBlock_error {header : CompressedHeader.Header} {window length commandCap : Nat}
    {limits : Execute.Limits} {initial : Execute.State} {before : LSBReader} {input : List Bool}
    {error : BlockError} (rep : before.Rep input) (count : before.count < 8)
    (parsed : Dictionary.readBlock header window length commandCap limits initial before = .error error) :
    (∃ used suffix, input = used ++ suffix ∧ error.bit = before.totalRead + used.length) ∧
      match error with
      | .initialOutput bit => limits.output < initial.output.size ∧ bit = before.totalRead
      | .fuel .. | .command .. =>
        FailurePath header ⟨window, initial.output.size, length⟩ limits before commandCap 0
          (Execute.InsertCopy.State.start header initial) before input error := by
  unfold Dictionary.readBlock at parsed
  cases counted : Dictionary.readBlockCounted header window length commandCap limits initial before with
  | error reason =>
    simp only [counted, Except.map, Except.error.injEq] at parsed
    subst error
    have observed := readBlockCounted_error rep count counted
    cases reason <;> exact observed
  | ok result => simp [counted, Except.map] at parsed

end Silmaril.Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.Block
