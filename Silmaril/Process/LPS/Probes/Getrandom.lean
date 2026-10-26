module

public import Silmaril.Process.LPS.Probes.KitMisc
public import Silmaril.Process.LPS.Probes.Data.Getrandom8
public import Silmaril.Process.LPS.Probes.Data.GetrandomBadflags

/-! # Probe `getrandom8` and its mutant `getrandom_badflags`

`getrandom8.s` is `getrandom(rsp, 8, 0); exit(its return value)`: the buffer is
the entry stack pointer. On Linux the harness recorded
`getrandom(0x7fffffffee20, 8, 0) = 8` and exit status 8
(`Data.Getrandom8.observed`). The stack pointer is a launch parameter
(`ExecEntry.sp`); the native backend disables address randomization, so it is
reproducible, and the proofs launch the probe at Linux's value (`linuxProbe`).
Linux's eight random bytes are not recorded: they differ on every run.

* `Getrandom.determined`, `Getrandom.sound`: every execution exits 8, whatever
  bytes the environment delivers. There is no alternative: a request of at most
  256 bytes is delivered in full and is not interruptible (LPS
  `getrandom_small_max`).
* `Getrandom.every_bytes`: for *every* eight-byte string there is a run of the
  model that delivers exactly those bytes at the buffer (the final memory is
  the initial one with them installed at the stack pointer), with the recorded
  raw calls and exit. So the model is not "lucky": admitting Linux's run does
  not depend on which bytes Linux chose.
* `Getrandom.admits`: the recorded run is admitted (a corollary).

The mutant `getrandom_badflags.s` changes the flags immediate to 0xdead. Linux
returns `-EINVAL` and exits 234. LPS fails closed on unknown flag bits
(`getrandom_spec`: "GRND_RANDOM and any unknown flag bit are unmodeled"): every
execution, under every refusal filter, stops at the call in an unmodeled
configuration (`GetrandomBadflags.unmodeled_at_call`). This is a
reference-faithful design choice, not a translation bug. The recorded run is not
admitted, and the original's universal claim is false of the mutant
(`GetrandomBadflags.not_determined_original`).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Machines.X86Launch

namespace Getrandom

open Data.Getrandom8

/-- The entry stack pointer Linux ran the probe with: `getrandom`'s recorded buffer. -/
def linuxSp : Word := BitVec.ofInt 64 ((((observed.syscalls[0]?).map (·.args)).bind (·[0]?)).getD 0)

theorem linuxSp_eq : linuxSp = 0x7fffffffee20 := by decide

/-- The probe, launched at Linux's stack pointer. -/
def linuxProbe : Probe := { probe with entry := { X86Launch.Controls.entry with sp := linuxSp } }

theorem layout : linuxProbe.Layout := by probe_layout

instance checked : linuxProbe.Checked :=
  ⟨layout, harnessInput_valid, linuxProbe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

theorem writable : ∀ k < 8, linuxProbe.mem0.permits .write (linuxProbe.entry.sp.toNat + k) = true := by
  decide +kernel

/-- The postcondition with the delivered bytes: exit 8, and the memory is the
initial memory with `bs` at the stack pointer. -/
def Delivers (bs : List Byte) : Omni.Post x86ExtNative := fun trace outcome =>
  ∃ final, outcome = .halt final ∧ trace = observed.events final.model.fs ∧ observed.Ends final ∧
    final.ms.m.memory = { linuxProbe.mem0 with bytes := installWrapping linuxProbe.mem0.bytes linuxSp.toNat bs }

theorem exec : Omni.Exec linuxProbe.segs spec noFilter linuxProbe.initial
    (fun trace outcome => ∃ bs : List Byte, bs.length = 8 ∧ Delivers bs trace outcome) := by
  rw [Probe.initial_at]
  probe_instr 120 3 (.mov .q (.reg .rdi) .rsp)
  probe_instr 123 5 (.movI32 .rsi 8)
  probe_instr 128 5 (.movI32 .rdx 0)
  probe_instr 133 5 (.movI32 .rax 318)
  probe_trap 138
  apply Probe.exec_retH (by decide) rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (Probe.getrandom_stack_outcomes (count := 8) rfl rfl rfl rfl (by decide) (by decide)
      (by decide +kernel) writable (by decide +kernel)) ⟨List.replicate 8 0, rfl⟩
  intro bs length
  match bs, length with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
  rw [Probe.applyMemoryEffect_write]
  have holds := linuxProbe.holds_write linuxProbe.holds_mem0 linuxSp.toNat [b0, b1, b2, b3, b4, b5, b6, b7]
    (show linuxSp.toNat + 8 ≤ 2 ^ 64 by decide +kernel) (by decide +kernel) layout
  apply Probe.exec_instrH holds (off := 140) (len := 3) (instruction := .mov .q (.reg .rdi) .rax) <;>
    probe_sides
  apply Probe.exec_instrH holds (off := 143) (len := 5) (instruction := .movI32 .rax 60) <;> probe_sides
  apply Probe.exec_trapH holds (off := 148) <;> probe_sides
  apply Probe.exec_exitH (Or.inl rfl) (status := 8) rfl rfl (by probe_clear)
  exact ⟨_, rfl, _, rfl, rfl, ⟨rfl, rfl, rfl⟩, rfl⟩

/-- The universal statement: every execution exits 8. -/
theorem determined : linuxProbe.Determined noFilter observed :=
  exec.consequence fun _ _ ⟨_, _, final, outcome, events, ends, _⟩ => ⟨final, outcome, events, ends⟩

theorem sound (refused : RefusalFilter) {trace : List Event} {outcome : Omni.Outcome x86ExtNative}
    (finite : Omni.FiniteExec linuxProbe.segs spec refused linuxProbe.initial trace outcome) :
    Probe.Exactly observed trace outcome :=
  Omni.Exec.sound_any determined finite

/-- The model is not lucky: every eight-byte string is delivered by some run with
the recorded raw calls and exit. -/
theorem every_bytes (bs : List Byte) (length : bs.length = 8) :
    ∃ calls trace final, Run linuxProbe.segs spec noFilter linuxProbe.initial calls trace (.halt final) ∧
      observed.MatchesCalls linuxProbe.entry.sp calls = true ∧ trace = observed.events final.model.fs ∧
      observed.Ends final ∧
      final.ms.m.memory = { linuxProbe.mem0 with bytes := installWrapping linuxProbe.mem0.bytes linuxSp.toNat bs } := by
  match bs, length with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
  have holds := linuxProbe.holds_write linuxProbe.holds_mem0 linuxSp.toNat [b0, b1, b2, b3, b4, b5, b6, b7]
    (show linuxSp.toNat + 8 ≤ 2 ^ 64 by decide +kernel) (by decide +kernel) layout
  apply Exists.intro
  apply Exists.intro
  apply Exists.intro
  refine ⟨?run, ?raw, ?events, ?ends, ?memory⟩
  case run =>
    rw [Probe.initial_at]
    probe_instr 120 3 (.mov .q (.reg .rdi) .rsp)
    probe_instr 123 5 (.movI32 .rsi 8)
    probe_instr 128 5 (.movI32 .rdx 0)
    probe_instr 133 5 (.movI32 .rax 318)
    probe_trap 138
    apply Probe.run_retH (by decide) rfl (fun _ _ => rfl) (fun _ _ => rfl)
      (Probe.getrandom_stack_outcomes (count := 8) rfl rfl rfl rfl (by decide) (by decide)
        (by decide +kernel) writable (by decide +kernel)) [b0, b1, b2, b3, b4, b5, b6, b7] rfl (fun h => h)
    rw [Probe.applyMemoryEffect_write]
    apply Probe.run_instrH holds (off := 140) (len := 3) (instruction := .mov .q (.reg .rdi) .rax) <;>
      probe_sides
    apply Probe.run_instrH holds (off := 143) (len := 5) (instruction := .movI32 .rax 60) <;> probe_sides
    apply Probe.run_trapH holds (off := 148) <;> probe_sides
    apply Probe.run_exitH (Or.inl rfl) (status := 8) <;> rfl
  all_goals first | rfl | exact ⟨rfl, rfl, rfl⟩

/-- Reality is admitted (any delivered bytes will do; `every_bytes`). -/
theorem admits : linuxProbe.Admits noFilter observed := by
  obtain ⟨_, _, _, run, raw, events, ends, _⟩ := every_bytes (List.replicate 8 0) rfl
  exact Probe.admits_of _ run raw events ends

theorem no_error (refused : RefusalFilter) : ¬ (linuxProbe.behavior refused).errors :=
  Probe.Determined.no_error _ determined

end Getrandom

namespace GetrandomBadflags

open Data.GetrandomBadflags

def linuxProbe : Probe := { probe with entry := { X86Launch.Controls.entry with sp := Getrandom.linuxSp } }

theorem layout : linuxProbe.Layout := by probe_layout

instance checked : linuxProbe.Checked :=
  ⟨layout, harnessInput_valid, linuxProbe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

/-- The model's actual behaviour, under every refusal filter: every execution
stops at `getrandom(sp, 8, 0xdead)`, which is unmodeled (fail closed). -/
theorem unmodeled_at_call (refused : RefusalFilter) :
    Omni.Exec linuxProbe.segs spec refused linuxProbe.initial (linuxProbe.StopsUnmodeled 318) := by
  rw [Probe.initial_at]
  probe_instr 120 3 (.mov .q (.reg .rdi) .rsp)
  probe_instr 123 5 (.movI32 .rsi 8)
  probe_instr 128 5 (.movI32 .rdx 0xdead)
  probe_instr 133 5 (.movI32 .rax 318)
  probe_trap 138
  exact Probe.exec_stops rfl (fun outcome => (Probe.native_getrandom _ _ outcome rfl (by decide +kernel)).trans
    (Probe.getrandom_badflags_iff _ _ outcome (by decide)))

theorem unmodeled (refused : RefusalFilter) : (linuxProbe.behavior refused).unmodeled :=
  Probe.unmodeled_of_stops (unmodeled_at_call refused)

/-- Linux's run (`-EINVAL`, exit 234) is not a run of the model. -/
theorem not_admits (refused : RefusalFilter) : ¬ linuxProbe.Admits refused observed :=
  Probe.not_admits_of_stops (unmodeled_at_call refused)

/-- What Linux did instead, from the fixture: `-EINVAL` (-22), exit 234. -/
theorem linux_einval :
    ((observed.syscalls[0]?).bind (·.ret)) = some (-22) ∧ observed.outcome = .exited 234 := by
  decide

/-- Mutation: the original's "every execution exits 8" is false of the mutant. -/
theorem not_determined_original : ¬ linuxProbe.Determined noFilter Data.Getrandom8.observed := by
  intro determined
  obtain ⟨_, _, finite, final, rfl, _⟩ := Omni.Exec.realizes determined
  obtain ⟨_, _, impossible, _⟩ := (unmodeled_at_call noFilter).sound finite
  cases impossible

end GetrandomBadflags

end Silmaril.Process.LPS.Probes
