module

public import Silmaril.Process.LPS.Problems.CoreutilsLite.Spec
public import Silmaril.Process.LPS.Probes.Data.LiteTrue
public import Silmaril.Process.LPS.Probes.Data.LiteFalse
public import Silmaril.Process.LPS.Probes.Data.LiteTrueStderr
public import Silmaril.Process.LPS.Probes.Data.LiteFalseStdout

/-! # `true` and `false` (GCC -O2, freestanding), total in LPS, with refuted mutants

The binaries are `examples/coreutils-lite/{true,false}.c` compiled by GCC 13.3.0 `-O2`
(`gen-probes.sh`) and linked by the LPS probe harness; their bytes are the generated data
modules `Probes.Data.LiteTrue` / `LiteFalse` (pinned in the harness's `SHA256SUMS`, recorded
on Linux: exit 0 / exit 1, no other system call).

```
true:   b8 3c 00 00 00   mov $60,%eax        false:  b8 3c 00 00 00   mov $60,%eax
        31 ff            xor %edi,%edi               bf 01 00 00 00   mov $1,%edi
        0f 05            syscall                     0f 05            syscall
```

`true`'s `xor` leaves AF undefined, so it is unmodelled under the deterministic adapter; the
statements are over every flag oracle (`CoreutilsLite.Total`).

* `trueSpec` / `falseSpec`: on every input, the only complete trace is the exit with status
  0 / 1 and the initial file system (nothing read, nothing written).
* `true_total`, `false_total` (VERIFIED): each binary meets its spec on every launch.
* Mutants, refuted (VERIFIED): `false` is the "exits 1" mutant of `true` and `true` the
  "exits 0" mutant of `false`; `lite_true_stderr` writes one byte to stderr and exits 0;
  `lite_false_stdout` writes `false\n` to stdout and exits 1.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Problems.CoreutilsLite

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Process.LPS.Probes

/-- Exit with `status` and nothing else. -/
def exitSpec (status : Word) : Spec where
  domain _ := True
  allowed inp trace code := trace = [.exitEv status inp.fs] ∧ code = status
  ideal inp := [.exitEv status inp.fs]

/-- `true`: exit 0, observing nothing. -/
abbrev trueSpec : Spec := exitSpec 0

/-- `false`: exit 1, observing nothing. -/
abbrev falseSpec : Spec := exitSpec 1

namespace LiteTrue
open Data.LiteTrue
theorem layout : probe.Layout := by probe_layout
instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩
end LiteTrue

namespace LiteFalse
open Data.LiteFalse
theorem layout : probe.Layout := by probe_layout
instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩
end LiteFalse

namespace LiteTrueStderr
open Data.LiteTrueStderr
theorem layout : probe.Layout := by probe_layout
instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩
end LiteTrueStderr

namespace LiteFalseStdout
open Data.LiteFalseStdout
theorem layout : probe.Layout := by probe_layout
instance checked : probe.Checked :=
  ⟨layout, harnessInput_valid, probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩
end LiteFalseStdout

/-! ## `true` -/

theorem true_exec (oracle : Nat → X86FlagChoices.Choice) (limit : Int) (en : ExecEntry)
    (inp : ProcInput) [Probe.Checked (Data.LiteTrue.probe.launchAt en inp)] :
    Omni.Exec (Data.LiteTrue.probe.launchAt en inp).segs spec noFilter
      ((Data.LiteTrue.probe.launchAt en inp).oinitial oracle limit)
      (Ends (trueSpec.allowed inp)) := by
  rw [Probe.oinitial_at]
  oprobe_instr 128 5 _
  oprobe_instr 133 2 _
  oprobe_trap 135
  oprobe_exit 0
  refine ⟨_, rfl, rfl, _, rfl, ?_⟩
  exact ⟨rfl, rfl⟩

theorem true_complete (oracle : Nat → X86FlagChoices.Choice) (limit : Int) (en : ExecEntry)
    (inp : ProcInput) [Probe.Checked (Data.LiteTrue.probe.launchAt en inp)] :
    ∃ final, Star (Data.LiteTrue.probe.launchAt en inp).segs spec noFilter
      ((Data.LiteTrue.probe.launchAt en inp).oinitial oracle limit) (trueSpec.ideal inp) final := by
  rw [Probe.oinitial_at]
  apply Exists.intro
  oprobe_instr 128 5 _
  oprobe_instr 133 2 _
  oprobe_trap 135
  oprobe_exit 0

/-- `true` meets `trueSpec` on every launch (VERIFIED). -/
theorem true_total : Total Data.LiteTrue.probe.snapshot trueSpec := by
  intro oracle limit en inp _ admissible
  have := Data.LiteTrue.probe.checkedAt LiteTrue.layout.static admissible.1 admissible.2
  exact ⟨true_exec oracle limit en inp, _, _, (true_complete oracle limit en inp).choose_spec, List.prefix_refl _⟩

/-! ## `false` -/

theorem false_exec (oracle : Nat → X86FlagChoices.Choice) (limit : Int) (en : ExecEntry)
    (inp : ProcInput) [Probe.Checked (Data.LiteFalse.probe.launchAt en inp)] :
    Omni.Exec (Data.LiteFalse.probe.launchAt en inp).segs spec noFilter
      ((Data.LiteFalse.probe.launchAt en inp).oinitial oracle limit)
      (Ends (falseSpec.allowed inp)) := by
  rw [Probe.oinitial_at]
  oprobe_instr 128 5 _
  oprobe_instr 133 5 _
  oprobe_trap 138
  oprobe_exit 1
  refine ⟨_, rfl, rfl, _, rfl, ?_⟩
  exact ⟨rfl, rfl⟩

theorem false_complete (oracle : Nat → X86FlagChoices.Choice) (limit : Int) (en : ExecEntry)
    (inp : ProcInput) [Probe.Checked (Data.LiteFalse.probe.launchAt en inp)] :
    ∃ final, Star (Data.LiteFalse.probe.launchAt en inp).segs spec noFilter
      ((Data.LiteFalse.probe.launchAt en inp).oinitial oracle limit) (falseSpec.ideal inp) final := by
  rw [Probe.oinitial_at]
  apply Exists.intro
  oprobe_instr 128 5 _
  oprobe_instr 133 5 _
  oprobe_trap 138
  oprobe_exit 1

/-- `false` meets `falseSpec` on every launch (VERIFIED). -/
theorem false_total : Total Data.LiteFalse.probe.snapshot falseSpec := by
  intro oracle limit en inp _ admissible
  have := Data.LiteFalse.probe.checkedAt LiteFalse.layout.static admissible.1 admissible.2
  exact ⟨false_exec oracle limit en inp, _, _, (false_complete oracle limit en inp).choose_spec, List.prefix_refl _⟩

/-! ## Mutants -/

/-- The harness launch of a checked probe, as a `launchAt`. -/
instance harnessChecked (P : Probe) [checked : Probe.Checked P] :
    Probe.Checked (P.launchAt P.entry P.input) := checked

theorem exitSpec_ends_ne {s t : Word} {inp : ProcInput} {trace : List Event}
    {outcome : Omni.Outcome (machine (fun _ => clearChoice))} (differ : s ≠ t) :
    Ends ((exitSpec s).allowed inp) trace outcome → ¬ Ends ((exitSpec t).allowed inp) trace outcome := by
  rintro ⟨final, rfl, _, code, halted, rfl, rfl⟩ ⟨final', same, _, code', halted', trace', rfl⟩
  cases same
  rw [halted] at halted'
  exact differ (Option.some.inj halted')

/-- Mutant "exits 1" of `true` (the `false` binary) is refuted (VERIFIED). -/
theorem true_mutant_exit1 : ¬ Total Data.LiteFalse.probe.snapshot trueSpec :=
  not_total_of_exec (oracle := (fun _ => clearChoice)) (limit := sourceAllocLimit) trivial
    (admissible_harness Data.LiteFalse.probe (fun _ => clearChoice))
    (false_exec (fun _ => clearChoice) sourceAllocLimit Data.LiteFalse.probe.entry Data.LiteFalse.probe.input)
    (fun _ _ ends => exitSpec_ends_ne (by decide) ends)

/-- Mutant "exits 0" of `false` (the `true` binary) is refuted (VERIFIED). -/
theorem false_mutant_exit0 : ¬ Total Data.LiteTrue.probe.snapshot falseSpec :=
  not_total_of_exec (oracle := (fun _ => clearChoice)) (limit := sourceAllocLimit) trivial
    (admissible_harness Data.LiteTrue.probe (fun _ => clearChoice))
    (true_exec (fun _ => clearChoice) sourceAllocLimit Data.LiteTrue.probe.entry Data.LiteTrue.probe.input)
    (fun _ _ ends => exitSpec_ends_ne (by decide) ends)

/-- Every execution starts with an event on descriptor `ch`'s channel. -/
def WritesFirst {isa : UserIsa} (ch : Word) : Omni.Post isa :=
  fun trace _ => ∃ b rest, trace = .writeEv ch b :: rest

theorem writesFirst_append {isa : UserIsa} {ch : Word} {ds : List Byte} (nonempty : ds ≠ [])
    (trace : List Event) (outcome : Omni.Outcome isa) :
    WritesFirst ch (ds.map (.writeEv ch) ++ trace) outcome := by
  cases ds with
  | nil => exact absurd rfl nonempty
  | cons b rest => exact ⟨b, _, rfl⟩

theorem exitSpec_not_writesFirst {s ch : Word} {inp : ProcInput} {trace : List Event}
    {outcome : Omni.Outcome (machine (fun _ => clearChoice))} :
    WritesFirst ch trace outcome → ¬ Ends ((exitSpec s).allowed inp) trace outcome := by
  rintro ⟨b, rest, rfl⟩ ⟨_, _, _, _, _, same, _⟩
  cases same

/-- `lite_true_stderr` writes to stderr first, on every execution. -/
theorem trueStderr_exec (oracle : Nat → X86FlagChoices.Choice) (limit : Int) (en : ExecEntry)
    (inp : ProcInput) [Probe.Checked (Data.LiteTrueStderr.probe.launchAt en inp)] :
    Omni.Exec (Data.LiteTrueStderr.probe.launchAt en inp).segs spec noFilter
      ((Data.LiteTrueStderr.probe.launchAt en inp).oinitial oracle limit) (WritesFirst 2) := by
  rw [Probe.oinitial_at]
  oprobe_instr 128 5 _
  oprobe_instr 133 5 _
  oprobe_instr 138 5 _
  oprobe_instr 143 3 _
  oprobe_trap 146
  oprobe_write 157 1
  intro ds delivered
  oprobe_instr 148 5 _
  oprobe_instr 153 2 _
  oprobe_trap 155
  oprobe_exit 0
  exact writesFirst_append delivered.1 _ _

/-- Mutant "writes to stderr" of `true` is refuted (VERIFIED). -/
theorem true_mutant_stderr : ¬ Total Data.LiteTrueStderr.probe.snapshot trueSpec :=
  not_total_of_exec (oracle := (fun _ => clearChoice)) (limit := sourceAllocLimit) trivial
    (admissible_harness Data.LiteTrueStderr.probe (fun _ => clearChoice))
    (trueStderr_exec (fun _ => clearChoice) sourceAllocLimit Data.LiteTrueStderr.probe.entry
      Data.LiteTrueStderr.probe.input)
    (fun _ _ first => exitSpec_not_writesFirst first)

/-- `lite_false_stdout` writes to stdout first, on every execution. -/
theorem falseStdout_exec (oracle : Nat → X86FlagChoices.Choice) (limit : Int) (en : ExecEntry)
    (inp : ProcInput) [Probe.Checked (Data.LiteFalseStdout.probe.launchAt en inp)] :
    Omni.Exec (Data.LiteFalseStdout.probe.launchAt en inp).segs spec noFilter
      ((Data.LiteFalseStdout.probe.launchAt en inp).oinitial oracle limit) (WritesFirst 1) := by
  rw [Probe.oinitial_at]
  oprobe_instr 128 5 _
  oprobe_instr 133 5 _
  oprobe_instr 138 5 _
  oprobe_instr 143 3 _
  oprobe_trap 146
  oprobe_write 155 6
  intro ds delivered
  oprobe_instr 148 5 _
  oprobe_trap 153
  oprobe_exit 1
  exact writesFirst_append delivered.1 _ _

/-- Mutant "writes to stdout" of `false` is refuted (VERIFIED). -/
theorem false_mutant_stdout : ¬ Total Data.LiteFalseStdout.probe.snapshot falseSpec :=
  not_total_of_exec (oracle := (fun _ => clearChoice)) (limit := sourceAllocLimit) trivial
    (admissible_harness Data.LiteFalseStdout.probe (fun _ => clearChoice))
    (falseStdout_exec (fun _ => clearChoice) sourceAllocLimit Data.LiteFalseStdout.probe.entry
      Data.LiteFalseStdout.probe.input)
    (fun _ _ first => exitSpec_not_writesFirst first)

end Silmaril.Process.LPS.Problems.CoreutilsLite
