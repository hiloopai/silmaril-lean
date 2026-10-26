module

public import Silmaril.Problems.Basic
public import Silmaril.Process.LPS.Problems.CoreutilsLite.Probes

/-! # Core utilities, simplified, as problems (part A: probes, `true`, `false`)

Each problem is `CoreutilsLite.Total snapshot spec` for one pinned binary (its bytes are the
generated probe data module named in `problem.toml`): total correctness in LPS on every valid
launch, every flag oracle and every allocation limit. A mutant's problem states the original's
spec of the mutant's bytes; it is a negative control (`expect = "refutable"`), refuted by
`@[refutes]`.

| problem | binary | spec | result |
|---|---|---|---|
| `lps/exit42` | probe `exit42` | `exitSpec 42` | solved |
| `lps/exit42/mutant-exit43` | probe `exit43` | `exitSpec 42` | refuted |
| `lps/hello` | probe `write_hello` | `helloProbeSpec` | solved |
| `lps/hello/mutant-write-hello5` | probe `write_hello5` | `helloProbeSpec` | refuted |
| `lps/hello/strict` | probe `write_hello` | `helloStrictSpec` | refuted (no retry) |
| `coreutils-lite/true` | GCC `true.c` | `trueSpec` | solved |
| `coreutils-lite/true/mutant-exit1` | GCC `false.c` | `trueSpec` | refuted |
| `coreutils-lite/true/mutant-stderr` | GCC `true_stderr.c` | `trueSpec` | refuted |
| `coreutils-lite/false` | GCC `false.c` | `falseSpec` | solved |
| `coreutils-lite/false/mutant-exit0` | GCC `true.c` | `falseSpec` | refuted |
| `coreutils-lite/false/mutant-stdout` | GCC `false_stdout.c` | `falseSpec` | refuted |

Everything in this file is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.CoreutilsLite.Registry

open Silmaril.Process.LPS.Probes
open Silmaril.Process.LPS.Problems.CoreutilsLite

/-! ## The probes of #3554 -/

@[problem "lps/exit42"]
def exit42 : Prop := Total Data.Exit42.probe.snapshot (exitSpec 42)

@[solves "lps/exit42"]
theorem exit42_solution : exit42 := exit42_total

@[problem "lps/exit42/mutant-exit43"]
def exit42MutantExit43 : Prop := Total Data.Exit43.probe.snapshot (exitSpec 42)

@[refutes "lps/exit42/mutant-exit43"]
theorem exit42MutantExit43_refuted : ¬ exit42MutantExit43 := exit43_refuted

@[problem "lps/hello"]
def hello : Prop := Total Data.WriteHello.probe.snapshot helloProbeSpec

@[solves "lps/hello"]
theorem hello_solution : hello := write_hello_total

@[problem "lps/hello/mutant-write-hello5"]
def helloMutantWriteHello5 : Prop := Total Data.WriteHello5.probe.snapshot helloProbeSpec

@[refutes "lps/hello/mutant-write-hello5"]
theorem helloMutantWriteHello5_refuted : ¬ helloMutantWriteHello5 := write_hello5_refuted

@[problem "lps/hello/strict"]
def helloStrict : Prop := Total Data.WriteHello.probe.snapshot helloStrictSpec

@[refutes "lps/hello/strict"]
theorem helloStrict_refuted : ¬ helloStrict := write_hello_not_strict

/-! ## `true` and `false` -/

@[problem "coreutils-lite/true"]
def «true» : Prop := Total Data.LiteTrue.probe.snapshot trueSpec

@[solves "coreutils-lite/true"]
theorem true_solution : «true» := true_total

@[problem "coreutils-lite/true/mutant-exit1"]
def trueMutantExit1 : Prop := Total Data.LiteFalse.probe.snapshot trueSpec

@[refutes "coreutils-lite/true/mutant-exit1"]
theorem trueMutantExit1_refuted : ¬ trueMutantExit1 := true_mutant_exit1

@[problem "coreutils-lite/true/mutant-stderr"]
def trueMutantStderr : Prop := Total Data.LiteTrueStderr.probe.snapshot trueSpec

@[refutes "coreutils-lite/true/mutant-stderr"]
theorem trueMutantStderr_refuted : ¬ trueMutantStderr := true_mutant_stderr

@[problem "coreutils-lite/false"]
def «false» : Prop := Total Data.LiteFalse.probe.snapshot falseSpec

@[solves "coreutils-lite/false"]
theorem false_solution : «false» := false_total

@[problem "coreutils-lite/false/mutant-exit0"]
def falseMutantExit0 : Prop := Total Data.LiteTrue.probe.snapshot falseSpec

@[refutes "coreutils-lite/false/mutant-exit0"]
theorem falseMutantExit0_refuted : ¬ falseMutantExit0 := false_mutant_exit0

@[problem "coreutils-lite/false/mutant-stdout"]
def falseMutantStdout : Prop := Total Data.LiteFalseStdout.probe.snapshot falseSpec

@[refutes "coreutils-lite/false/mutant-stdout"]
theorem falseMutantStdout_refuted : ¬ falseMutantStdout := false_mutant_stdout

/-! ## The statements are not vacuous (VERIFIED)

Each binary has an admissible launch (the harness's) for every oracle, and on it the ideal trace
is observable (`TotalAt.complete`), so `Total` is neither vacuously true (the hypotheses hold) nor
trivially met (a binary that never exits, or exits otherwise, is refuted above). -/

theorem true_nonvacuous (oracle : Nat → Silmaril.Process.LPS.Machines.X86FlagChoices.Choice) :
    Admissible oracle Data.LiteTrue.probe.snapshot Data.LiteTrue.probe.entry
      Data.LiteTrue.probe.input :=
  admissible_harness _ oracle

theorem false_nonvacuous (oracle : Nat → Silmaril.Process.LPS.Machines.X86FlagChoices.Choice) :
    Admissible oracle Data.LiteFalse.probe.snapshot Data.LiteFalse.probe.entry
      Data.LiteFalse.probe.input :=
  admissible_harness _ oracle

end Silmaril.Process.LPS.Problems.CoreutilsLite.Registry
