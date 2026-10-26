module

public import Silmaril.Process.LPS.Problems.CoreutilsLite.TrueFalse
public import Silmaril.Process.LPS.Probes.Exit42
public import Silmaril.Process.LPS.Probes.WriteHello

/-! # The LPS reality probes `exit42` and `write_hello` as problems (VERIFIED)

The hand-written probes of #3554 (`examples/verification-projects/theorem-dev/lps-probes`),
restated in the `CoreutilsLite.Total` shape: every valid launch (not only the harness's), every
flag oracle and allocation limit.

* `exit42`: `exitSpec 42`. `exit42_total`; the mutant `exit43` is refuted (`exit43_refuted`).
* `write_hello`: `write(1, "hello\n", 6); exit(0)`, ignoring the return value. Its spec
  `helloProbeSpec` is what the probe claims: some non-empty prefix of `hello\n` is written to
  stdout (the reference short write) and the process exits 0, and the full `hello\n` then exit
  0 is observable. `write_hello_total`. The mutant `write_hello5` (length 5) is refuted
  (`write_hello5_refuted`): it can never write the newline, so the ideal trace is not
  observable.
* The strict spec `helloStrictSpec` (the ladder's `helloSpec` reading, #3543, with the message
  `hello\n`: exit 0 only after the **whole** message) is refuted by `write_hello` itself
  (`write_hello_not_strict`): LPS may accept one byte, and the probe exits 0 without retrying.
  A conforming `hello` must loop on short writes (the write-all stencil, `docs/X86Stencils.md`).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Problems.CoreutilsLite

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Process.LPS.Probes

/-! ## `exit42` -/

theorem exit42_exec (oracle : Nat → X86FlagChoices.Choice) (limit : Int) (en : ExecEntry)
    (inp : ProcInput) [Probe.Checked (Data.Exit42.probe.launchAt en inp)] :
    Omni.Exec (Data.Exit42.probe.launchAt en inp).segs spec noFilter
      ((Data.Exit42.probe.launchAt en inp).oinitial oracle limit)
      (Ends ((exitSpec 42).allowed inp)) := by
  rw [Probe.oinitial_at]
  oprobe_instr 120 5 _
  oprobe_instr 125 5 _
  oprobe_trap 130
  oprobe_exit 42
  refine ⟨_, rfl, rfl, _, rfl, ?_⟩
  exact ⟨rfl, rfl⟩

theorem exit42_complete (oracle : Nat → X86FlagChoices.Choice) (limit : Int) (en : ExecEntry)
    (inp : ProcInput) [Probe.Checked (Data.Exit42.probe.launchAt en inp)] :
    ∃ final, Star (Data.Exit42.probe.launchAt en inp).segs spec noFilter
      ((Data.Exit42.probe.launchAt en inp).oinitial oracle limit) ((exitSpec 42).ideal inp) final := by
  rw [Probe.oinitial_at]
  apply Exists.intro
  oprobe_instr 120 5 _
  oprobe_instr 125 5 _
  oprobe_trap 130
  oprobe_exit 42

/-- `exit42` meets `exitSpec 42` on every launch (VERIFIED). -/
theorem exit42_total : Total Data.Exit42.probe.snapshot (exitSpec 42) := by
  intro oracle limit en inp _ admissible
  have := Data.Exit42.probe.checkedAt Exit42.layout.static admissible.1 admissible.2
  exact ⟨exit42_exec oracle limit en inp, _, _, (exit42_complete oracle limit en inp).choose_spec,
    List.prefix_refl _⟩

theorem exit43_exec (oracle : Nat → X86FlagChoices.Choice) (limit : Int) (en : ExecEntry)
    (inp : ProcInput) [Probe.Checked (Data.Exit43.probe.launchAt en inp)] :
    Omni.Exec (Data.Exit43.probe.launchAt en inp).segs spec noFilter
      ((Data.Exit43.probe.launchAt en inp).oinitial oracle limit)
      (Ends ((exitSpec 43).allowed inp)) := by
  rw [Probe.oinitial_at]
  oprobe_instr 120 5 _
  oprobe_instr 125 5 _
  oprobe_trap 130
  oprobe_exit 43
  refine ⟨_, rfl, rfl, _, rfl, ?_⟩
  exact ⟨rfl, rfl⟩

/-- The mutant `exit43` does not meet `exitSpec 42` (VERIFIED). -/
theorem exit43_refuted : ¬ Total Data.Exit43.probe.snapshot (exitSpec 42) :=
  not_total_of_exec (oracle := fun _ => clearChoice) (limit := sourceAllocLimit) trivial
    (admissible_harness Data.Exit43.probe _)
    (exit43_exec _ sourceAllocLimit Data.Exit43.probe.entry Data.Exit43.probe.input)
    (fun _ _ ends => exitSpec_ends_ne (by decide) ends)

/-! ## `write_hello` -/

/-- `hello\n`. -/
def helloMessage : List Byte := [104, 101, 108, 108, 111, 10]

/-- What the probe claims: a non-empty prefix of `hello\n` on stdout, then exit 0; the full
message then exit 0 is observable. -/
abbrev helloProbeSpec : Spec where
  domain _ := True
  allowed inp trace code := code = 0 ∧
    ∃ ds, Probe.WritePrefix helloMessage ds ∧ trace = ds.map (.writeEv 1) ++ [.exitEv 0 inp.fs]
  ideal inp := helloMessage.map (.writeEv 1) ++ [.exitEv 0 inp.fs]

/-- The strict reading (the ladder's `helloSpec` with `hello\n`): exit 0 only after the whole
message, and nothing else. -/
abbrev helloStrictSpec : Spec where
  domain _ := True
  allowed inp trace code := code = 0 ∧ trace = helloMessage.map (.writeEv 1) ++ [.exitEv 0 inp.fs]
  ideal inp := helloMessage.map (.writeEv 1) ++ [.exitEv 0 inp.fs]

theorem helloMessage_eq : (Data.WriteHello.probe.bytes.drop 154).take 6 = helloMessage :=
  WriteHello.message

theorem write_hello_exec (oracle : Nat → X86FlagChoices.Choice) (limit : Int) (en : ExecEntry)
    (inp : ProcInput) [Probe.Checked (Data.WriteHello.probe.launchAt en inp)] :
    Omni.Exec (Data.WriteHello.probe.launchAt en inp).segs spec noFilter
      ((Data.WriteHello.probe.launchAt en inp).oinitial oracle limit)
      (Ends (helloProbeSpec.allowed inp)) := by
  rw [Probe.oinitial_at]
  oprobe_instr 120 5 _
  oprobe_instr 125 5 _
  oprobe_instr 130 5 _
  oprobe_instr 135 5 _
  oprobe_trap 140
  oprobe_write 154 6
  intro ds delivered
  oprobe_instr 142 5 _
  oprobe_instr 147 5 _
  oprobe_trap 152
  oprobe_exit 0
  rw [Probe.launchAt_bytes, helloMessage_eq] at delivered
  refine ⟨_, rfl, rfl, _, rfl, ?_⟩
  exact ⟨rfl, ds, delivered, rfl⟩

theorem write_hello_complete (oracle : Nat → X86FlagChoices.Choice) (limit : Int) (en : ExecEntry)
    (inp : ProcInput) [Probe.Checked (Data.WriteHello.probe.launchAt en inp)] :
    ∃ final, Star (Data.WriteHello.probe.launchAt en inp).segs spec noFilter
      ((Data.WriteHello.probe.launchAt en inp).oinitial oracle limit) (helloProbeSpec.ideal inp)
      final := by
  rw [Probe.oinitial_at]
  apply Exists.intro
  show Star _ _ _ _ (helloMessage.map (.writeEv 1) ++ [.exitEv 0 inp.fs]) _
  oprobe_instr 120 5 _
  oprobe_instr 125 5 _
  oprobe_instr 130 5 _
  oprobe_instr 135 5 _
  oprobe_trap 140
  oprobe_write 154 6 with helloMessage
  oprobe_instr 142 5 _
  oprobe_instr 147 5 _
  oprobe_trap 152
  oprobe_exit 0

/-- `write_hello` meets its probe spec on every launch (VERIFIED). -/
theorem write_hello_total : Total Data.WriteHello.probe.snapshot helloProbeSpec := by
  intro oracle limit en inp _ admissible
  have := Data.WriteHello.probe.checkedAt WriteHello.layout.static admissible.1 admissible.2
  exact ⟨write_hello_exec oracle limit en inp, _, _,
    (write_hello_complete oracle limit en inp).choose_spec, List.prefix_refl _⟩

/-- The mutant writes at most five bytes, then exits 0. -/
def AtMostFive {isa : UserIsa} (fs : Fs.FileSystem) : Omni.Post isa := fun trace _ =>
  ∃ ds : List Byte, ds.length ≤ 5 ∧ trace = ds.map (.writeEv 1) ++ [.exitEv 0 fs]

theorem write_hello5_exec (oracle : Nat → X86FlagChoices.Choice) (limit : Int) (en : ExecEntry)
    (inp : ProcInput) [Probe.Checked (Data.WriteHello5.probe.launchAt en inp)] :
    Omni.Exec (Data.WriteHello5.probe.launchAt en inp).segs spec noFilter
      ((Data.WriteHello5.probe.launchAt en inp).oinitial oracle limit) (AtMostFive inp.fs) := by
  rw [Probe.oinitial_at]
  oprobe_instr 120 5 _
  oprobe_instr 125 5 _
  oprobe_instr 130 5 _
  oprobe_instr 135 5 _
  oprobe_trap 140
  oprobe_write 154 5
  intro ds delivered
  oprobe_instr 142 5 _
  oprobe_instr 147 5 _
  oprobe_trap 152
  oprobe_exit 0
  have short := delivered.2.length_le
  simp only [List.length_take] at short
  exact ⟨ds, by omega, rfl⟩

/-- The mutant `write_hello5` does not meet the probe spec of `write_hello` (VERIFIED): the
full message is never observable. -/
theorem write_hello5_refuted : ¬ Total Data.WriteHello5.probe.snapshot helloProbeSpec := by
  intro total
  have := total (fun _ => clearChoice) sourceAllocLimit Data.WriteHello5.probe.entry
    Data.WriteHello5.probe.input trivial
    (admissible_harness Data.WriteHello5.probe _)
  obtain ⟨rest, _, pre, ds, short, rfl⟩ := Omni.Exec.obsTrace
    (write_hello5_exec (fun _ => clearChoice) sourceAllocLimit Data.WriteHello5.probe.entry
      Data.WriteHello5.probe.input) this.complete
  have long := pre.length_le
  simp only [helloMessage, List.length_append, List.length_map,
    List.length_cons, List.length_nil] at long
  omega

/-- `write_hello` does not meet the strict spec (VERIFIED): a one-byte write followed by exit 0
is one of its executions. -/
theorem write_hello_not_strict : ¬ Total Data.WriteHello.probe.snapshot helloStrictSpec := by
  intro total
  have run : ∃ final, Star (Data.WriteHello.probe.launchAt Data.WriteHello.probe.entry
      Data.WriteHello.probe.input).segs spec noFilter
      ((Data.WriteHello.probe.launchAt Data.WriteHello.probe.entry Data.WriteHello.probe.input).oinitial
        (fun _ => clearChoice) sourceAllocLimit)
      ([104].map (.writeEv 1) ++ [.exitEv 0 Data.WriteHello.probe.input.fs]) final ∧
        final.model.halted ≠ none := by
    rw [Probe.oinitial_at]
    apply Exists.intro
    apply And.intro
    · oprobe_instr 120 5 _
      oprobe_instr 125 5 _
      oprobe_instr 130 5 _
      oprobe_instr 135 5 _
      oprobe_trap 140
      oprobe_write 154 6 with [104]
      oprobe_instr 142 5 _
      oprobe_instr 147 5 _
      oprobe_trap 152
      oprobe_exit 0
    · simp [Model.withHalted, Model.halted]
  obtain ⟨final, path, halted⟩ := run
  have finite := Omni.star_finiteExec path (.halt halted)
  rw [List.append_nil] at finite
  obtain ⟨_, _, _, _, _, _, bad⟩ :=
    (total (fun _ => clearChoice) sourceAllocLimit Data.WriteHello.probe.entry
      Data.WriteHello.probe.input trivial
      (admissible_harness Data.WriteHello.probe _)).exec.sound finite
  simp [helloMessage] at bad

end Silmaril.Process.LPS.Problems.CoreutilsLite
