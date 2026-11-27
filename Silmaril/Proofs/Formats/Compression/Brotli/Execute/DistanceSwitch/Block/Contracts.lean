module

public import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Block.Defs
import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Thms
import Silmaril.Formats.Compression.Brotli.Literal.Switch.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Block

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Execute (Block)
open Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch (remainingBits)
open Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch.Internal (runWith runWithResult)
open Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch
open Silmaril.Formats.Compression.Brotli.Literal.Switch (Source)

private theorem bind_mapped_ok {ε δ α β : Type} {action : Except ε α} {next : α → Except δ β}
    {map : ε → δ} {value : β} (parsed : (action.mapError map >>= next) = .ok value) :
    ∃ result, action = .ok result ∧ next result = .ok value := by
  cases action with
  | error _ => cases parsed
  | ok result => exact ⟨result, rfl, parsed⟩

theorem CommandsWire.output {header : CompressedHeader.Header} {block : Block}
    {initial final : Execute.InsertCopy.State} {bits : List Bool} {chunks : List (List UInt8)}
    (wire : CommandsWire header block initial bits chunks final) :
    final.execution.output.size = block.endOutput ∧
    final.execution.output.toList = initial.execution.output.toList ++ chunks.flatten ∧
    chunks.length ≤ chunks.flatten.length := by
  induction wire with
  | done exactSize => exact ⟨exactSize, by simp, by simp⟩
  | step _ appended progress _ ih =>
    have remaining := ih.2.2
    have length := congrArg List.length appended
    simp only [Array.length_toList, List.length_append] at length
    refine ⟨ih.1, ?_, ?_⟩
    · simp [ih.2.1, Execute.InsertCopy.Result.state, appended, List.append_assoc]
    · simp only [List.length_cons, List.flatten_cons, List.length_append]
      omega

private theorem run_sound {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {origin before after : LSBReader} {fuel index : Nat} {initial final : Execute.InsertCopy.State} {input : List Bool}
    (rep : before.Rep input) (count : before.count < 8)
    (afterOrigin : origin.totalRead ≤ before.totalRead) (bitFit : before.totalRead ≤ origin.totalRead + limits.bits)
    (outFit : initial.execution.output.size ≤ limits.output)
    (parsed : runWith (read header block) BlockError.command BlockError.fuel block limits origin
      fuel index initial before = .ok (final, after)) :
    final.execution.output.size ≤ limits.output ∧ after.totalRead ≤ origin.totalRead + limits.bits ∧
    ∃ used suffix chunks, CommandsWire header block initial used chunks final ∧
      chunks.length ≤ fuel ∧ Source before after input used suffix := by
  induction fuel generalizing index initial final before after input with
  | zero =>
    unfold runWith runWithResult at parsed
    split at parsed
    · rename_i done
      cases parsed
      exact ⟨outFit, bitFit, [], input, [], .done done, by simp, ⟨rfl, rep, count, by simp⟩⟩
    · cases parsed
  | succ fuel ih =>
    unfold runWith runWithResult at parsed
    split at parsed
    · rename_i done
      cases parsed
      exact ⟨outFit, bitFit, [], input, [], .done done, by simp, ⟨rfl, rep, count, by simp⟩⟩
    · obtain ⟨⟨result, next⟩, commandRead, rest⟩ := bind_mapped_ok parsed
      obtain ⟨grows, extent, outputFit, used, tail, command, first, bits⟩ :=
        Execute.DistanceSwitch.read_sound rep count commandRead
      have shifted := first.position
      change used.length ≤ limits.bits - (before.totalRead - origin.totalRead) at bits
      obtain ⟨outFits, bitFits, restBits, suffix, chunks, chain, steps, second⟩ :=
        ih first.rep first.count (by omega) (by omega) outputFit rest
      obtain ⟨_, _, _, _, _, literals, copied, _, _, _, _, _, _, output⟩ := command.parts
      have shape : result.execution.state.output.toList =
          initial.execution.output.toList ++ (literals ++ copied) := by
        simpa only [List.append_assoc] using output
      have progress : block.endOutput - result.execution.state.output.size <
          block.endOutput - initial.execution.output.size := by omega
      exact ⟨outFits, bitFits, used ++ restBits, suffix, (literals ++ copied) :: chunks,
        .step command shape progress chain, by simp only [List.length_cons]; omega, first.trans second⟩

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

/-- Remaining output is an upper bound on the number of successful
    commands still needed, so MLEN fuel cannot mask a command failure. -/
private theorem run_failure {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {origin before : LSBReader} {fuel index : Nat} {state : Execute.InsertCopy.State} {input : List Bool}
    {error : BlockError} (rep : before.Rep input) (count : before.count < 8)
    (extent : state.execution.output.size ≤ block.endOutput)
    (remaining : block.endOutput ≤ state.execution.output.size + fuel)
    (parsed : runWith (read header block) BlockError.command BlockError.fuel block limits origin
      fuel index state before = .error error) :
    ∃ command reason, error = .command command reason ∧
      BlockFailure header block limits origin command reason fuel index state before input := by
  induction fuel generalizing index state before input with
  | zero =>
    have done : state.execution.output.size = block.endOutput := by omega
    simp [runWith, runWithResult, done] at parsed
  | succ fuel ih =>
    unfold runWith runWithResult at parsed
    split at parsed
    · cases parsed
    · rename_i pending
      cases commandRead : read header block {limits with bits := remainingBits limits.bits origin before}
          state before with
      | error reason =>
        simp only [commandRead, Except.mapError, bind, Except.bind] at parsed
        cases parsed
        exact ⟨index, reason, rfl, .here pending commandRead (Execute.DistanceSwitch.read_error rep count commandRead)⟩
      | ok pair =>
        obtain ⟨result, after⟩ := pair
        simp only [commandRead, Except.mapError, bind, Except.bind] at parsed
        obtain ⟨grows, upper, _, used, suffix, wire, source, _⟩ :=
          Execute.DistanceSwitch.read_sound rep count commandRead
        have next : block.endOutput ≤ result.state.execution.output.size + fuel := by
          change block.endOutput ≤ result.execution.state.output.size + fuel
          omega
        obtain ⟨command, reason, exactError, path⟩ := ih source.rep source.count upper next parsed
        exact ⟨command, reason, exactError, .next pending commandRead wire source path⟩

theorem BlockFailure.offset {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {origin before : LSBReader} {fuel index command : Nat} {state : Execute.InsertCopy.State} {input : List Bool}
    {reason : Execute.DistanceSwitch.Error} (rep : before.Rep input) (count : before.count < 8)
    (failure : BlockFailure header block limits origin command reason fuel index state before input) :
    command < index + fuel ∧
    ∃ used suffix, input = used ++ suffix ∧ reason.bit = before.totalRead + used.length := by
  induction failure with
  | here _ _ first => exact ⟨by omega, Execute.DistanceSwitch.Failure.offset rep count first⟩
  | next _ _ _ source _ ih =>
    obtain ⟨fits, used, suffix, read, bit⟩ := ih source.rep source.count
    exact ⟨by omega, _, suffix, by rw [source.split, read, List.append_assoc],
      by rw [bit, source.position, List.length_append, Nat.add_assoc]⟩

theorem readBlock_error {header : CompressedHeader.Header} {window length : Nat}
    {limits : Execute.Limits} {initial : Execute.State} {before : LSBReader} {input : List Bool}
    {error : BlockError} (rep : before.Rep input) (count : before.count < 8)
    (parsed : readBlock header window length limits initial before = .error error) :
    (∃ used suffix, input = used ++ suffix ∧ error.bit = before.totalRead + used.length) ∧
      match error with
      | .initialOutput _ => limits.output < initial.output.size
      | .fuel .. => False
      | .command command reason =>
        BlockFailure header ⟨window, initial.output.size, length⟩ limits before command reason length 0
          (Execute.InsertCopy.State.start header initial) before input := by
  unfold readBlock at parsed
  split at parsed
  · rename_i initialCap
    cases parsed
    exact ⟨⟨[], input, rfl, by simp [BlockError.bit]⟩, initialCap⟩
  · dsimp only at parsed
    have extent : (Execute.InsertCopy.State.start header initial).execution.output.size ≤
        (⟨window, initial.output.size, length⟩ : Block).endOutput := Nat.le_add_right _ _
    obtain ⟨command, reason, rfl, failure⟩ :=
      run_failure (fuel := length) rep count extent (Nat.le_refl _) parsed
    exact ⟨(BlockFailure.offset rep count failure).2, failure⟩

end Silmaril.Proofs.Formats.Compression.Brotli.Execute.DistanceSwitch.Block
