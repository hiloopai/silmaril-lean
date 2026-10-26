module

public import Silmaril.Problems.Basic
public import Silmaril.Problems.Compose
public import Silmaril.Process.LPS.Problems.Sha256Cli.Fetchable

/-! # The `sha256` filter as problems

Five problems in the family `sha256`, all about the pinned ELF `apps/sha256-cli/build/sha256`
(`Sha256Cli.elfBytes`, 2368 bytes, SHA-256 `6eaae149…89e1f7`); `problems/sha256/sha256-cli-x86-64/`
holds their `problem.toml` files. All five are solved, VERIFIED (standard axioms only).

* `sha256/sha256-cli-x86-64/cli-total`: total correctness in the CLI process model
  (`Process.CLI.X86Linux`, reliable environment): `cliTotal_solution` (`EndToEnd.cli_total`).
* `sha256/sha256-cli-x86-64/lps-launch`: the loader correspondence of the CLI-to-LPS bridge
  (`LaunchObligation`): `lpsLaunch_solution` (`Launch.launchObligation`).
* `sha256/sha256-cli-x86-64/lps-total`: total correctness in LPS (`TotalGoal`), every flag
  oracle, refusal configuration, budget and finite stdin: `lpsTotal_solution`, composed by
  `lpsTotal_link : All [cliTotal, lpsLaunch] → lpsTotal`.
* `sha256/sha256-cli-x86-64/lps-bounded-1024`: `BoundedGoal 1024`, via `lpsBounded_link`.
* `sha256/sha256-cli-x86-64/lps-partial`: `PartialGoal` (safety only), via `lpsPartial_link`.

Everything in this file is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.Sha256Cli.Registry

open Silmaril.Problems

/-- The pinned binary's bytes: the artifact every problem here is about. The LPS statements
mention it through `snapshot`; the CLI statement through the chain's transcribed image
(equality of the two images is part of `lps-launch`). -/
abbrev elf : List Byte := Sha256Cli.elfBytes

/-- Total correctness of the pinned `sha256` filter in the CLI process model. -/
@[problem "sha256/sha256-cli-x86-64/cli-total"]
def cliTotal : Prop := CliTotalOn fun _ => True

/-- The open part of the bridge from the CLI model to LPS: the loader correspondence. -/
@[problem "sha256/sha256-cli-x86-64/lps-launch"]
def lpsLaunch : Prop := LaunchObligation

/-- Total correctness of the pinned ELF in LPS on every finite stdin. -/
@[problem "sha256/sha256-cli-x86-64/lps-total"]
def lpsTotal : Prop := TotalGoal

/-- Total correctness of the pinned ELF in LPS on stdin of at most 1024 bytes. -/
@[problem "sha256/sha256-cli-x86-64/lps-bounded-1024"]
def lpsBounded : Prop := BoundedGoal 1024

/-- Partial correctness (safety) of the pinned ELF in LPS on every finite stdin. -/
@[problem "sha256/sha256-cli-x86-64/lps-partial"]
def lpsPartial : Prop := PartialGoal

/-- Solution of `cli-total` (VERIFIED). -/
@[solves "sha256/sha256-cli-x86-64/cli-total"]
theorem cliTotal_solution : cliTotal := cli_total

/-- Non-vacuity of `cli-total` (VERIFIED): its hypotheses hold on every stdin. -/
theorem cliTotal_hypotheses (message : List Byte) :
    ∃ (input : CLI.ProcInput) (x : PS),
      input.stdin = .ofList message ∧ input.Valid ∧ Launch input x := by
  obtain ⟨x, launch⟩ := launch_exists message
  exact ⟨_, x, rfl, ⟨by simp [CLI.Sha256Cli.inputOf], by simp [CLI.Sha256Cli.inputOf]⟩, launch⟩

/-- Solution of `lps-launch` (VERIFIED). -/
@[solves "sha256/sha256-cli-x86-64/lps-launch"]
theorem lpsLaunch_solution : lpsLaunch := launchObligation

/-- Link of `lps-total` (VERIFIED): CLI total correctness and the launch correspondence give
LPS total correctness. -/
theorem lpsTotal_link : All [cliTotal, lpsLaunch] → lpsTotal := fun ⟨cli, launch, _⟩ =>
  bridge_of_readSim (readSim_of_launch launch) _ cli

/-- Link of `lps-bounded-1024` (VERIFIED). -/
theorem lpsBounded_link : All [lpsTotal] → lpsBounded := fun ⟨total, _⟩ =>
  boundedGoal_of_totalGoal total 1024

/-- Link of `lps-partial` (VERIFIED). -/
theorem lpsPartial_link : All [lpsTotal] → lpsPartial := fun ⟨total, _⟩ =>
  partialGoal_of_totalGoal total

/-- `lps-total` modulo `lps-launch`, through the proved `cli-total` (VERIFIED). -/
theorem lpsTotal_of_launch (launch : lpsLaunch) : lpsTotal :=
  compose (components := [cliTotal, lpsLaunch]) ⟨cliTotal_solution, launch, trivial⟩
    lpsTotal_link

theorem lpsBounded_of_launch (launch : lpsLaunch) : lpsBounded :=
  compose (components := [lpsTotal]) ⟨lpsTotal_of_launch launch, trivial⟩ lpsBounded_link

theorem lpsPartial_of_launch (launch : lpsLaunch) : lpsPartial :=
  compose (components := [lpsTotal]) ⟨lpsTotal_of_launch launch, trivial⟩ lpsPartial_link

/-- Non-vacuity of the LPS problems (VERIFIED): every message has an admissible launch for every
flag oracle, and the ideal trace occurs on it. -/
theorem lps_nonvacuous (oracle : Nat → Silmaril.Process.LPS.Machines.X86FlagChoices.Choice) (refusals : SpuriousCfg)
    (limit : Int) (message : List Byte) :
    ∃ en inp, Admissible oracle en inp message ∧
      (behaviour oracle refusals limit en inp).traces (idealTrace message inp.fs) :=
  ideal_trace_occurs oracle refusals limit message

/-- Solution of `lps-total` (VERIFIED): composed from `cli-total` and `lps-launch`. -/
@[solves "sha256/sha256-cli-x86-64/lps-total"]
theorem lpsTotal_solution : lpsTotal := lpsTotal_of_launch lpsLaunch_solution

/-- Solution of `lps-bounded-1024` (VERIFIED). -/
@[solves "sha256/sha256-cli-x86-64/lps-bounded-1024"]
theorem lpsBounded_solution : lpsBounded := lpsBounded_of_launch lpsLaunch_solution

/-- Solution of `lps-partial` (VERIFIED). -/
@[solves "sha256/sha256-cli-x86-64/lps-partial"]
theorem lpsPartial_solution : lpsPartial := lpsPartial_of_launch lpsLaunch_solution

end Silmaril.Process.LPS.Problems.Sha256Cli.Registry
