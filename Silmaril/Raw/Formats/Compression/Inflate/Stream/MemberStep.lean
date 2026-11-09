module

public import Silmaril.Raw.Formats.Compression.Inflate.Stream.MemberGzipStep

/-!
# Incremental member-step preservation

Every physical header, raw-body and trailer step preserves the same complete
member observation under every future input extension. Suspension is a saved
continuation, rather than a failed canonical decode. Data checksum and size
invariants justify entering the trailer with the incrementally stored values.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.MemberMachine

open Silmaril.Formats.Compression
open MemberSemantics

private theorem body_step_correct_feed (kind : Kind) (version : Version)
    (checked : CheckedRaw.State) (reader : LSBReader) (fuel capacity : Nat)
    (hnorm : Reservoir.Normalizes checked.reservoir reader)
    (hwf : WellFormed (.body kind checked) reader) :
    ∃ rest, Reservoir.Normalizes
        (MemberMachine.body kind (CheckedRaw.step kind.checksumKind version checked fuel capacity)).reservoir rest ∧
      WellFormed (.body kind (CheckedRaw.step kind.checksumKind version checked fuel capacity)) rest ∧
      ∀ future, denote (.body kind checked) (Reservoir.readerFeed reader future) =
        denote (.body kind (CheckedRaw.step kind.checksumKind version checked fuel capacity))
          (Reservoir.readerFeed rest future) := by
  obtain ⟨rest, hn, hw, hi, observations⟩ :=
    CheckedRaw.step_correct_feed kind.checksumKind version checked reader fuel capacity hwf.1 hnorm hwf.2
  exact ⟨rest, hn, ⟨hi, hw⟩, fun future => congrArg (afterRaw kind) (observations future)⟩

theorem step_correct_feed (version : Version) (machine : MemberMachine)
    (reader : LSBReader) (fuel capacity : Nat)
    (hnorm : Reservoir.Normalizes machine.reservoir reader)
    (hwf : machine.WellFormed reader) :
    ∃ rest, Reservoir.Normalizes (step version machine fuel capacity).reservoir rest ∧
      WellFormed (step version machine fuel capacity) rest ∧
      ∀ future, denote machine (Reservoir.readerFeed reader future) =
        denote (step version machine fuel capacity) (Reservoir.readerFeed rest future) := by
  cases machine with
  | header kind parser reservoir =>
    obtain ⟨rest, hn, observations⟩ := Parser.run_correct_feed fuel parser
      (show Reservoir.Normalizes reservoir reader from hnorm)
    cases hp : Parser.run fuel parser reservoir with
    | done valid physical =>
      rw [hp] at hn observations
      simp only [RunResult.state, RunResult.observe] at hn observations
      cases valid with
      | none =>
        simp only [step, hp]
        exact ⟨rest, hn, trivial, fun future => by simp only [denote, observations future,
          ContainerFields.validationReader, Option.bind_none]⟩
      | some value =>
        cases value
        simp only [step, hp]
        refine ⟨rest, hn, enterBody_wellFormed kind physical rest, ?_⟩
        intro future
        rw [enterBody_denote]
        simp only [denote, observations future, ContainerFields.validationReader, Option.bind_some]
    | error err physical =>
      rw [hp] at hn observations
      simp only [RunResult.state, RunResult.observe] at hn observations
      simp only [step, hp]
      exact ⟨rest, hn, trivial, fun future => by simp only [denote, observations future,
        ContainerFields.validationReader, Option.bind_none]⟩
    | needInput next physical =>
      rw [hp] at hn observations
      simp only [RunResult.state, RunResult.observe] at hn observations
      simp only [step, hp]
      exact ⟨rest, hn, trivial, fun future => by simp only [denote, observations future]⟩
    | yield next physical =>
      rw [hp] at hn observations
      simp only [RunResult.state, RunResult.observe] at hn observations
      simp only [step, hp]
      exact ⟨rest, hn, trivial, fun future => by simp only [denote, observations future]⟩
  | gzipHeader header => exact MemberGzipStep.step_correct_feed version header reader fuel capacity hnorm hwf
  | body kind checked =>
    change Reservoir.Normalizes checked.machine.reservoir reader at hnorm
    cases hm : checked.machine with
    | done state =>
      rw [hm] at hnorm
      simp only [step, hm]
      refine ⟨reader, hnorm, trivial, ?_⟩
      intro future
      simp only [denote, hm, RawSemantics.denote, afterRaw, checkedTrailer_eq kind checked hwf.1]
      simp only [CheckedRaw.State.output, hm, RawMachine.output, RawMachine.state]
    | bad err state =>
      rw [hm] at hnorm
      simp only [step, hm]
      exact ⟨reader, hnorm, trivial, fun _ => by simp only [denote, hm, RawSemantics.denote, afterRaw]⟩
    | header _ _ | storedHeader _ _ _ | storedCopy _ _ _ | dynamicTables _ _ _ | symbols _ _ _ _ =>
      simpa only [step, hm] using body_step_correct_feed kind version checked reader fuel capacity hnorm hwf
  | trailer parser state =>
    obtain ⟨rest, hn, observations⟩ := Parser.run_correct_feed fuel parser
      (show Reservoir.Normalizes state.reservoir reader from hnorm)
    cases hp : Parser.run fuel parser state.reservoir with
    | done valid physical =>
      rw [hp] at hn observations
      simp only [RunResult.state, RunResult.observe] at hn observations
      cases valid with
      | none =>
        simp only [step, hp]
        exact ⟨rest, hn, trivial, fun future => by simp only [denote, observations future,
          ContainerFields.validationReader, Option.map_none]⟩
      | some value =>
        cases value
        simp only [step, hp]
        exact ⟨rest, hn, trivial, fun future => by simp only [denote, observations future,
          ContainerFields.validationReader, Option.map_some]⟩
    | error err physical =>
      rw [hp] at hn observations
      simp only [RunResult.state, RunResult.observe] at hn observations
      simp only [step, hp]
      exact ⟨rest, hn, trivial, fun future => by simp only [denote, observations future,
        ContainerFields.validationReader, Option.map_none]⟩
    | needInput next physical =>
      rw [hp] at hn observations
      simp only [RunResult.state, RunResult.observe] at hn observations
      simp only [step, hp]
      exact ⟨rest, hn, trivial, fun future => by simp only [denote, observations future]⟩
    | yield next physical =>
      rw [hp] at hn observations
      simp only [RunResult.state, RunResult.observe] at hn observations
      simp only [step, hp]
      exact ⟨rest, hn, trivial, fun future => by simp only [denote, observations future]⟩
  | done state => exact ⟨reader, hnorm, trivial, fun _ => rfl⟩
  | bad error state => exact ⟨reader, hnorm, trivial, fun _ => rfl⟩

end Silmaril.Formats.Compression.Inflate.Stream.MemberMachine
