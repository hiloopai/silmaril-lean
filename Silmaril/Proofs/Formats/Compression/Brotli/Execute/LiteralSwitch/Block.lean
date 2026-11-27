module

public import Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Execute.LiteralSwitch.Contracts
import Silmaril.Formats.Compression.Brotli.Literal.Switch.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Execute.LiteralSwitch

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Execute (Block)
open Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch
open Silmaril.Formats.Compression.Brotli.Literal.Switch (Source)

theorem CommandsWire.output {header : CompressedHeader.Header} {block : Block}
    {initial final : Execute.InsertCopy.State} {bits : List Bool} {chunks : List (List UInt8)}
    (wire : CommandsWire header block initial bits chunks final) :
    final.execution.output.size = block.endOutput ∧
    final.execution.output.toList = initial.execution.output.toList ++ chunks.flatten ∧
    chunks.length ≤ chunks.flatten.length := by
  induction wire with
  | done size => exact ⟨size, by simp, by simp⟩
  | step _ appended grows _ ih =>
    have remaining := ih.2.2
    refine ⟨ih.1, ?_, ?_⟩
    · simp [ih.2.1, Execute.InsertCopy.Result.state, appended, List.append_assoc]
    · simp only [List.length_cons, List.flatten_cons, List.length_append]
      omega

private theorem run_sound {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {origin before after : LSBReader} {fuel index : Nat} {initial final : Execute.InsertCopy.State} {input : List Bool}
    (rep : before.Rep input) (count : before.count < 8)
    (afterOrigin : origin.totalRead ≤ before.totalRead) (bitFit : before.totalRead ≤ origin.totalRead + limits.bits)
    (outFit : initial.execution.output.size ≤ limits.output)
    (parsed : Execute.LiteralSwitch.Internal.run header block limits origin fuel index initial before = .ok (final, after)) :
    final.execution.output.size ≤ limits.output ∧ after.totalRead ≤ origin.totalRead + limits.bits ∧
    ∃ used suffix chunks, CommandsWire header block initial used chunks final ∧ chunks.length ≤ fuel ∧
      Source before after input used suffix := by
  induction fuel generalizing index initial final before after input with
  | zero =>
    unfold Execute.LiteralSwitch.Internal.run Execute.LiteralSwitch.Internal.runWith at parsed
    split at parsed
    · rename_i done
      cases parsed
      exact ⟨outFit, bitFit, [], input, [], .done done, by simp, ⟨rfl, rep, count, by simp⟩⟩
    · cases parsed
  | succ fuel ih =>
    unfold Execute.LiteralSwitch.Internal.run Execute.LiteralSwitch.Internal.runWith at parsed
    split at parsed
    · rename_i done
      cases parsed
      exact ⟨outFit, bitFit, [], input, [], .done done, by simp, ⟨rfl, rep, count, by simp⟩⟩
    · obtain ⟨⟨result, next⟩, stepRead, rest⟩ := bind_mapped_ok parsed
      obtain ⟨grows, _, outputFits, used, tail, wire, first, bits⟩ := read_sound rep count stepRead
      have shifted := first.position
      change used.length ≤ limits.bits - (before.totalRead - origin.totalRead) at bits
      obtain ⟨outFits, bitsFit, restBits, suffix, chunks, chain, steps, second⟩ :=
        ih first.rep first.count (by omega) (by omega) outputFits rest
      obtain ⟨_, _, _, _, _, literals, matched, _, _, _, _, _, _, _, appended⟩ := wire.parts
      have shape : result.execution.state.output.toList =
          initial.execution.output.toList ++ (literals ++ matched) := by simpa only [List.append_assoc] using appended
      have size := congrArg List.length shape
      simp only [Array.length_toList, List.length_append] at size
      refine ⟨outFits, bitsFit, used ++ restBits, suffix, (literals ++ matched) :: chunks,
        .step wire shape (by simp only [List.length_append]; omega) chain, ?_, Literal.Switch.Source.trans first second⟩
      simp only [List.length_cons]
      omega

theorem readBlock_sound {header : CompressedHeader.Header} {window length : Nat} {limits : Execute.Limits}
    {initial : Execute.State} {final : Execute.InsertCopy.State} {before after : LSBReader} {input : List Bool}
    (rep : before.Rep input) (count : before.count < 8)
    (parsed : readBlock header window length limits initial before = .ok (final, after)) :
    final.execution.output.size = initial.output.size + length ∧ final.execution.output.size ≤ limits.output ∧
    ∃ used suffix chunks,
      CommandsWire header ⟨window, initial.output.size, length⟩
        (Execute.InsertCopy.State.start header initial) used chunks final ∧
      final.execution.output.toList = initial.output.toList ++ chunks.flatten ∧
      chunks.length ≤ length ∧ Source before after input used suffix ∧ used.length ≤ limits.bits := by
  unfold readBlock at parsed
  split at parsed
  · cases parsed
  rename_i exceeded
  obtain ⟨outFit, bitFit, used, suffix, chunks, wire, steps, source⟩ :=
    run_sound rep count (Nat.le_refl _) (by omega) (Nat.le_of_not_gt exceeded) parsed
  obtain ⟨size, output, _⟩ := CommandsWire.output wire
  have position := source.position
  exact ⟨size, outFit, used, suffix, chunks, wire, output, steps, source, by omega⟩

private theorem run_command_error {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {origin before : LSBReader} {fuel index command : Nat} {state : Execute.InsertCopy.State} {input : List Bool}
    {reason : Execute.LiteralSwitch.Error}
    (rep : before.Rep input) (count : before.count < 8)
    (parsed : Execute.LiteralSwitch.Internal.run header block limits origin fuel index state before =
      .error (.command command reason)) :
    BlockFailure header block limits origin command reason fuel index state before input := by
  induction fuel generalizing index state before input with
  | zero => unfold Execute.LiteralSwitch.Internal.run Execute.LiteralSwitch.Internal.runWith at parsed; split at parsed <;> cases parsed
  | succ fuel ih =>
    unfold Execute.LiteralSwitch.Internal.run Execute.LiteralSwitch.Internal.runWith at parsed
    split at parsed
    · cases parsed
    cases step : Execute.LiteralSwitch.read header block {limits with bits := remainingBits limits.bits origin before}
        state before with
    | error reason =>
      simp only [step, Except.mapError, bind, Except.bind] at parsed
      cases parsed
      exact .here step (read_error rep count step)
    | ok pair =>
      obtain ⟨result, after⟩ := pair
      simp only [step, Except.mapError, bind, Except.bind] at parsed
      obtain ⟨_, _, _, used, suffix, wire, source, _⟩ := read_sound rep count step
      exact .next step wire source (ih source.rep source.count parsed)

theorem readBlock_command_error {header : CompressedHeader.Header} {window length command : Nat}
    {limits : Execute.Limits} {initial : Execute.State} {before : LSBReader} {input : List Bool}
    {reason : Execute.LiteralSwitch.Error}
    (rep : before.Rep input) (count : before.count < 8)
    (parsed : readBlock header window length limits initial before = .error (.command command reason)) :
    BlockFailure header ⟨window, initial.output.size, length⟩ limits before command reason length 0
      (Execute.InsertCopy.State.start header initial) before input := by
  unfold readBlock at parsed
  split at parsed
  · cases parsed
  exact run_command_error rep count parsed

theorem BlockFailure.offset {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {origin before : LSBReader} {fuel index command : Nat} {state : Execute.InsertCopy.State} {input : List Bool}
    {reason : Execute.LiteralSwitch.Error} (rep : before.Rep input) (count : before.count < 8)
    (failure : BlockFailure header block limits origin command reason fuel index state before input) :
    command < index + fuel ∧
    ∃ used suffix, input = used ++ suffix ∧ reason.bit = before.totalRead + used.length := by
  induction failure with
  | here _ first =>
    exact ⟨by omega, Failure.offset rep count first⟩
  | next _ _ source _ ih =>
    obtain ⟨fits, used, suffix, read, bit⟩ := ih source.rep source.count
    exact ⟨by omega, _, suffix, by rw [source.split, read, List.append_assoc],
      by rw [bit, source.position, List.length_append, Nat.add_assoc]⟩

end Silmaril.Proofs.Formats.Compression.Brotli.Execute.LiteralSwitch
