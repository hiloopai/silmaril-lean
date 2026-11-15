module

public import Silmaril.Semantics.Accept.Verdict.Thms

/-! # Combined verdicts: worked examples and regression tests

An execution outcome records whether the run called `accept` and whether it called `reject`
(`Bool × Bool`). The accept and reject predicates overlap at `(true, true)`, a run that calls
both. Every `example` is checked when the library builds.
-/

@[expose] public section

namespace Silmaril.Accept.VerdictExamples

open Silmaril.Accept

/-- Runs that called `accept`. -/
def calledAccept : Set (Bool × Bool) := {o | o.1 = true}

/-- Runs that called `reject`. -/
def calledReject : Set (Bool × Bool) := {o | o.2 = true}

/-- The predicates are not disjoint. -/
example : (true, true) ∈ conflicts calledAccept calledReject := ⟨rfl, rfl⟩

/-- Five inputs: accepts only; accepts in one run and rejects in another; one run calls both;
no run; only silent runs. -/
def run : Fin 5 → Set (Bool × Bool)
  | 0 => {(true, false)}
  | 1 => {(true, false), (false, true)}
  | 2 => {(true, true)}
  | 3 => ∅
  | 4 => {(false, false)}

example : (0 : Fin 5) ∈ acceptsSafely run calledAccept calledReject := by
  simp [run, calledAccept, calledReject]

/-- Some run accepts, but another rejects. -/
example : (1 : Fin 5) ∈ acceptsSome run calledAccept ∧
    (1 : Fin 5) ∉ acceptsSafely run calledAccept calledReject :=
  ⟨⟨(true, false), by simp [run], rfl⟩, fun h => h.2 (false, true) (by simp [run]) rfl⟩

/-- A run that calls both verdicts excludes the input. -/
example : (2 : Fin 5) ∉ acceptsSafely run calledAccept calledReject :=
  not_mem_acceptsSafely_of_conflict (o := (true, true)) rfl ⟨rfl, rfl⟩

/-- No run: never rejects, but is not accepted. -/
example : (3 : Fin 5) ∈ neverRejects run calledReject ∧
    (3 : Fin 5) ∉ acceptsSafely run calledAccept calledReject :=
  ⟨mem_neverRejects_of_eq_empty rfl, not_mem_acceptsSafely_of_eq_empty rfl⟩

/-- Silent runs: never rejects, never accepts. -/
example : (4 : Fin 5) ∉ acceptsSafely run calledAccept calledReject := by
  simp [run, calledAccept]

/-- Restricting the executions of `1` to its accepting run makes it accepted: the combined
language is not antitone in the executions. -/
example : (1 : Fin 5) ∈ acceptsSafely (fun _ => {(true, false)}) calledAccept calledReject := by
  simp [calledAccept, calledReject]

/-! ## Deterministic components -/

example : acceptsSafely (detRun fun n : ℕ => (n % 2 == 0, n % 3 == 0)) calledAccept calledReject =
    (fun n : ℕ => (n % 2 == 0, n % 3 == 0)) ⁻¹' (calledAccept \ calledReject) :=
  acceptsSafely_detRun

/-! ## Environment classes -/

/-- Two environments: in `false` the component accepts, in `true` it rejects. -/
def envRunner (e : Bool) (_ : Unit) : Set (Bool × Bool) :=
  if e then {(false, true)} else {(true, false)}

/-- Under the class `{false}` it is accepted; under `{false, true}` it is not. -/
example : () ∈ acceptsSafely (envRun envRunner {false}) calledAccept calledReject :=
  mem_acceptsSafely_envRun.2 ⟨⟨false, rfl, (true, false), by simp [envRunner], rfl⟩,
    fun e he o ho => by simp at he; subst he; simp [envRunner] at ho; simp [ho, calledReject]⟩

example : () ∉ acceptsSafely (envRun envRunner Set.univ) calledAccept calledReject := fun h =>
  (mem_acceptsSafely_envRun.1 h).2 true trivial (false, true) (by simp [envRunner]) rfl

end Silmaril.Accept.VerdictExamples
