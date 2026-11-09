module

public import Silmaril.Formats.Compression.Inflate.Stream.MemberSpec
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.MemberRuns
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.GzipHeaderSpec

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Stream.MemberSpec`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.MemberMachine

open Silmaril.Formats.Compression
open MemberSemantics

theorem start_denote_inputView (kind : Kind) (initial input : List UInt8) :
    inputView ((start kind initial).denote (ContainerFields.alignedReader input)) = shared kind input := by
  cases kind with
  | zlib =>
    simp only [start, denote, ContainerFields.validationReader_zlibHeader]
    cases hh : zlibCheckHeader input with
    | none => simp only [Option.map_none, Option.bind_none, inputView]; simp [shared, zlibTake, hh]
    | some body =>
      simp only [Option.map_some, Option.bind_some]
      exact body_zlib_eq_spec input body 16 hh
  | gzip =>
    change inputView ((GzipHeader.Machine.denoteReader
      ⟨GzipHeader.initialControl, Reservoir.ofBytes initial⟩ (ContainerFields.alignedReader input)).bind
        (MemberSemantics.body .gzip)) = _
    rw [GzipHeaderSpec.denoteReader_initial]
    cases hh : RawContainers.gzipBody input with
    | none =>
      simp only [Option.map_none, Option.bind_none, inputView]
      simp [shared, RawContainers.gzipMember_eq_body, hh]
    | some body =>
      simp only [Option.map_some, Option.bind_some]
      exact body_gzip_eq_spec input body _ hh

/-- No completion assumption: even suspended member schedules retain exactly
the shared specification on all delivered input and every future extension. -/
theorem start_runCalls_correct_feed (version : Version) (kind : Kind)
    (initial : List UInt8) (calls : List RawMachine.Call) :
    ∃ rest, Reservoir.Normalizes (runCalls version (start kind initial) calls).reservoir rest ∧
      WellFormed (runCalls version (start kind initial) calls) rest ∧ ∀ future,
      shared kind (initial ++ RawRuns.deliveredInput calls ++ future) =
        inputView ((runCalls version (start kind initial) calls).denote
          (Reservoir.readerFeed rest future)) := by
  obtain ⟨rest, hr, hwr, observations⟩ := runCalls_correct_feed version (start kind initial)
    (ContainerFields.alignedReader initial) calls (start_normalizes kind initial) (start_wellFormed kind initial)
  refine ⟨rest, hr, hwr, ?_⟩
  intro future
  have observed := congrArg inputView (observations future)
  change inputView ((start kind initial).denote
      (ContainerFields.alignedReader (initial ++ (RawRuns.deliveredInput calls ++ future)))) = _ at observed
  simpa only [start_denote_inputView, List.append_assoc] using observed

theorem start_done_correct_feed (version : Version) (kind : Kind) (initial : List UInt8)
    (calls : List RawMachine.Call) (completed : RawState)
    (hdone : runCalls version (start kind initial) calls = .done completed) :
    ∃ rest, Reservoir.Normalizes completed.reservoir rest ∧ ∀ future,
      shared kind (initial ++ RawRuns.deliveredInput calls ++ future) =
        some (completed.output, rest.input ++ future) := by
  obtain ⟨rest, hr, _, observations⟩ := start_runCalls_correct_feed version kind initial calls
  rw [hdone] at hr observations
  exact ⟨rest, hr, observations⟩

theorem start_bad_correct_feed (version : Version) (kind : Kind) (initial : List UInt8)
    (calls : List RawMachine.Call) (error : MemberError) (failed : RawState)
    (hbad : runCalls version (start kind initial) calls = .bad error failed) :
    ∀ future, shared kind (initial ++ RawRuns.deliveredInput calls ++ future) = none := by
  obtain ⟨_, _, _, observations⟩ := start_runCalls_correct_feed version kind initial calls
  rw [hbad] at observations
  exact observations

theorem completed_schedules_agree (firstVersion secondVersion : Version) (kind : Kind)
    (firstInitial secondInitial : List UInt8) (firstCalls secondCalls : List RawMachine.Call)
    (firstState secondState : RawState)
    (firstDone : runCalls firstVersion (start kind firstInitial) firstCalls = .done firstState)
    (secondDone : runCalls secondVersion (start kind secondInitial) secondCalls = .done secondState)
    (sameInput : firstInitial ++ RawRuns.deliveredInput firstCalls =
      secondInitial ++ RawRuns.deliveredInput secondCalls) :
    ∃ firstRest secondRest, Reservoir.Normalizes firstState.reservoir firstRest ∧
      Reservoir.Normalizes secondState.reservoir secondRest ∧
      firstState.output = secondState.output ∧ firstRest.input = secondRest.input := by
  obtain ⟨firstRest, hn₁, observations₁⟩ :=
    start_done_correct_feed firstVersion kind firstInitial firstCalls firstState firstDone
  obtain ⟨secondRest, hn₂, observations₂⟩ :=
    start_done_correct_feed secondVersion kind secondInitial secondCalls secondState secondDone
  have h₁ := observations₁ []
  have h₂ := observations₂ []
  simp only [List.append_nil] at h₁ h₂
  rw [sameInput, h₂] at h₁
  have equality : (firstState.output, firstRest.input) = (secondState.output, secondRest.input) :=
    (Option.some.inj h₁).symm
  exact ⟨firstRest, secondRest, hn₁, hn₂, congrArg Prod.fst equality, congrArg Prod.snd equality⟩

end Silmaril.Formats.Compression.Inflate.Stream.MemberMachine
