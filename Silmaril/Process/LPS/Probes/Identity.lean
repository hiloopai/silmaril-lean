module

public import Silmaril.Process.LPS.Probes.KitMisc
public import Silmaril.Process.LPS.Probes.Data.Identity
public import Silmaril.Process.LPS.Probes.Data.Identity1

/-! # Probe `identity` and its mutant `identity1`

`identity.s` calls `getpid`, `gettid`, `set_tid_address(NULL)`, `getuid` and
`geteuid`, and exits with `(tid - pid) + (set_tid_address - pid) + (euid - uid)`:
status 0 exactly when the identities agree. On Linux the harness recorded the
same id from the first three calls, uid = euid = 1000, and exit status 0
(`Data.Identity.observed`). The ids differ from run to run; the fixture marks
them host-dependent, and the proofs take them from the JSON.

How the model gets these values:

* LPS answers `getpid`, `gettid` and `set_tid_address` all with
  `set_tid_address_spec` (`Probe.native_tid_iff`): the thread id is chosen by the
  environment at its first observation (any id in `(0, PID_MAX_ENVELOPE)`) and
  pinned thereafter (`Probe.TidChoice`), so all three calls return the same id.
* `getuid` and `geteuid` return the credentials, which the launch fixes from the
  launch input (`ProcInput.uid`, real = effective). The proofs launch the probe as
  Linux's user (`linuxProbe`, uid from the recorded `getuid` return).

* `Identity.determined`, `Identity.sound`: every execution of that launch exits 0,
  *whatever id the model chooses*: the id is universally quantified, and pinning
  makes the three answers agree. Nothing errors (`no_error`).
* `Identity.admits`: the recorded run is admitted, with Linux's id as the choice,
  every raw return matching the strace line.

The mutant `identity1.s` changes the immediate of the final `add $0, %rdi` to 1:
Linux exits 1, the model admits that (`Identity1.admits`), and the original's
"every execution exits 0" is false of it (`Identity1.not_determined_original`).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Machines.X86Launch

namespace Identity

open Data.Identity

/-- The user id Linux ran the probe as: `getuid`'s recorded return. -/
def linuxUid : Word := BitVec.ofInt 64 (((observed.syscalls[3]?).bind (·.ret)).getD 0)

/-- The probe, launched as Linux's user. -/
def linuxProbe : Probe := { probe with input := harnessInputAs linuxUid }

theorem layout : linuxProbe.Layout := by probe_layout

instance checked : linuxProbe.Checked :=
  ⟨layout, harnessInputAs_valid linuxUid (by unfold ValidId; decide +kernel),
    linuxProbe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

/-- The thread id Linux chose: `getpid`'s recorded return. -/
def linuxTid : Word := BitVec.ofInt 64 (((observed.syscalls[0]?).bind (·.ret)).getD 0)

/-- The universal statement: every execution exits 0, for every thread id the
model chooses. -/
theorem determined : linuxProbe.Determined noFilter observed := by
  unfold Probe.Determined
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 39)
  probe_trap 125
  apply Probe.exec_retH (by decide) rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun outcome => Probe.native_tid_iff _ _ outcome (Or.inl rfl) (by probe_clear)) ⟨1, by decide⟩
  intro tid choice
  simp only [Probe.cfgM, Probe.resume, Silmaril.X86.Ext.Sz.write, Silmaril.X86.State.write_flags, Silmaril.X86.State.write_fsBase]
  probe_instr 127 3 (.mov .q (.reg .rbx) .rax)
  probe_instr 130 5 (.movI32 .rax 186)
  probe_trap 135
  apply Probe.exec_retH (by decide) rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun outcome => Probe.native_tid_iff _ _ outcome (Or.inr (Or.inl rfl)) (by probe_clear)) (by exact ⟨tid, rfl⟩)
  intro tid' pinned
  obtain rfl : tid = tid' := pinned.symm
  simp only [Probe.cfgM, Probe.resume, Silmaril.X86.Ext.Sz.write, Silmaril.X86.State.write_flags, Silmaril.X86.State.write_fsBase]
  probe_instr 137 3 (.alu .q .sub (.reg .rax) .rbx)
  probe_instr 140 3 (.mov .q (.reg .r12) .rax)
  probe_instr 143 5 (.movI32 .rax 218)
  probe_instr 148 5 (.movI32 .rdi 0)
  probe_trap 153
  apply Probe.exec_retH (by decide) rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun outcome => Probe.native_tid_iff _ _ outcome (Or.inr (Or.inr rfl)) (by probe_clear)) (by exact ⟨tid, rfl⟩)
  intro tid' pinned
  obtain rfl : tid = tid' := pinned.symm
  simp only [Probe.cfgM, Probe.resume, Silmaril.X86.Ext.Sz.write, Silmaril.X86.State.write_flags, Silmaril.X86.State.write_fsBase]
  probe_instr 155 3 (.alu .q .sub (.reg .rax) .rbx)
  probe_instr 158 3 (.alu .q .add (.reg .r12) .rax)
  probe_instr 161 5 (.movI32 .rax 102)
  probe_trap 166
  apply Probe.exec_retH (by decide) rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (Probe.outcomes_unique (fun outcome => Probe.native_getuid_iff _ _ outcome rfl (by probe_clear))) ⟨(), trivial⟩
  intro _ _
  simp only [Probe.cfgM, Probe.resume, Silmaril.X86.Ext.Sz.write, Silmaril.X86.State.write_flags, Silmaril.X86.State.write_fsBase]
  probe_instr 168 3 (.mov .q (.reg .rbx) .rax)
  probe_instr 171 5 (.movI32 .rax 107)
  probe_trap 176
  apply Probe.exec_retH (by decide) rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (Probe.outcomes_unique (fun outcome => Probe.native_geteuid_iff _ _ outcome rfl (by probe_clear))) ⟨(), trivial⟩
  intro _ _
  simp only [Probe.cfgM, Probe.resume, Silmaril.X86.Ext.Sz.write, Silmaril.X86.State.write_flags, Silmaril.X86.State.write_fsBase]
  probe_instr 178 3 (.alu .q .sub (.reg .rax) .rbx)
  probe_instr 181 3 (.alu .q .add (.reg .rax) .r12)
  probe_instr 184 3 (.mov .q (.reg .rdi) .rax)
  probe_instr 187 4 (.aluI8 .q .add (.reg .rdi) 0)
  probe_instr 191 5 (.movI32 .rax 60)
  probe_trap 196
  refine Probe.exec_exit _ (status := 0) rfl ?rdi rfl ?clear ?done
  case done => exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
  case clear =>
    rw [Probe.boundarySuspect_regs _ (by decide +kernel)]
    simp only [List.any_cons, List.any_nil, Bool.or_false, Silmaril.X86.State.read,
      Silmaril.X86.State.write, Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read,
      Silmaril.Machine.RegisterFile.write, Silmaril.X86.Ext.AluOp.resultN, mkEffect]
    simp [show ∀ (m : Model) (t : Word), (m.withTid t).creds = m.creds from fun _ _ => rfl,
      show linuxProbe.model0.creds.euid = linuxProbe.model0.creds.uid from rfl]
    refine ⟨?_, by decide +kernel⟩
    generalize linuxProbe.model0.creds.uid = uid
    change NativeX86.All.inGuardWindow (uid - uid + (tid - tid + (tid - tid)) + 0 : BitVec 64) = false
    simp only [BitVec.sub_self, BitVec.add_zero]
    decide
  case rdi =>
    simp only [Silmaril.X86.State.read, Silmaril.X86.State.write, Silmaril.X86.Ext.Sz.write,
      Silmaril.X86.Ext.Sz.read, Silmaril.Machine.RegisterFile.write, Silmaril.X86.Ext.AluOp.resultN, mkEffect]
    simp [show ∀ (m : Model) (t : Word), (m.withTid t).creds = m.creds from fun _ _ => rfl,
      show linuxProbe.model0.creds.euid = linuxProbe.model0.creds.uid from rfl]
    generalize linuxProbe.model0.creds.uid = uid
    change (uid - uid + (tid - tid + (tid - tid)) + 0 : BitVec 64) = 0
    simp

theorem sound (refused : RefusalFilter) {trace : List Event} {outcome : Omni.Outcome x86ExtNative}
    (finite : Omni.FiniteExec linuxProbe.segs spec refused linuxProbe.initial trace outcome) :
    Probe.Exactly observed trace outcome :=
  Omni.Exec.sound_any determined finite

theorem no_error (refused : RefusalFilter) : ¬ (linuxProbe.behavior refused).errors :=
  Probe.Determined.no_error _ determined

/-- Reality is admitted: Linux's id as the model's thread-id choice. -/
theorem admits : linuxProbe.Admits noFilter observed := by
  apply Probe.admits_of
  case run =>
    rw [Probe.initial_at]
    probe_instr 120 5 (.movI32 .rax 39)
    probe_trap 125
    apply Probe.run_retH (by decide) rfl (fun _ _ => rfl) (fun _ _ => rfl)
      (fun outcome => Probe.native_tid_iff _ _ outcome (Or.inl rfl) (by probe_clear)) linuxTid (by decide +kernel)
      (fun h => h)
    probe_instr 127 3 (.mov .q (.reg .rbx) .rax)
    probe_instr 130 5 (.movI32 .rax 186)
    probe_trap 135
    apply Probe.run_retH (by decide) rfl (fun _ _ => rfl) (fun _ _ => rfl)
      (fun outcome => Probe.native_tid_iff _ _ outcome (Or.inr (Or.inl rfl)) (by probe_clear)) linuxTid
      (by decide +kernel) (fun h => h)
    probe_instr 137 3 (.alu .q .sub (.reg .rax) .rbx)
    probe_instr 140 3 (.mov .q (.reg .r12) .rax)
    probe_instr 143 5 (.movI32 .rax 218)
    probe_instr 148 5 (.movI32 .rdi 0)
    probe_trap 153
    apply Probe.run_retH (by decide) rfl (fun _ _ => rfl) (fun _ _ => rfl)
      (fun outcome => Probe.native_tid_iff _ _ outcome (Or.inr (Or.inr rfl)) (by probe_clear)) linuxTid
      (by decide +kernel) (fun h => h)
    probe_instr 155 3 (.alu .q .sub (.reg .rax) .rbx)
    probe_instr 158 3 (.alu .q .add (.reg .r12) .rax)
    probe_instr 161 5 (.movI32 .rax 102)
    probe_trap 166
    apply Probe.run_retH (by decide) rfl (fun _ _ => rfl) (fun _ _ => rfl)
      (Probe.outcomes_unique (fun outcome => Probe.native_getuid_iff _ _ outcome rfl (by probe_clear))) () trivial
      (fun h => h)
    probe_instr 168 3 (.mov .q (.reg .rbx) .rax)
    probe_instr 171 5 (.movI32 .rax 107)
    probe_trap 176
    apply Probe.run_retH (by decide) rfl (fun _ _ => rfl) (fun _ _ => rfl)
      (Probe.outcomes_unique (fun outcome => Probe.native_geteuid_iff _ _ outcome rfl (by probe_clear))) () trivial
      (fun h => h)
    probe_instr 178 3 (.alu .q .sub (.reg .rax) .rbx)
    probe_instr 181 3 (.alu .q .add (.reg .rax) .r12)
    probe_instr 184 3 (.mov .q (.reg .rdi) .rax)
    probe_instr 187 4 (.aluI8 .q .add (.reg .rdi) 0)
    probe_instr 191 5 (.movI32 .rax 60)
    probe_trap 196
    probe_exit 0
  all_goals probe_side

end Identity

namespace Identity1

open Data.Identity1

def linuxUid : Word := BitVec.ofInt 64 (((observed.syscalls[3]?).bind (·.ret)).getD 0)
def linuxTid : Word := BitVec.ofInt 64 (((observed.syscalls[0]?).bind (·.ret)).getD 0)

def linuxProbe : Probe := { probe with input := harnessInputAs linuxUid }

theorem layout : linuxProbe.Layout := by probe_layout

instance checked : linuxProbe.Checked :=
  ⟨layout, harnessInputAs_valid linuxUid (by unfold ValidId; decide +kernel),
    linuxProbe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

/-- The mutant's own observation (exit 1) is admitted. -/
theorem admits : linuxProbe.Admits noFilter observed := by
  apply Probe.admits_of
  case run =>
    rw [Probe.initial_at]
    probe_instr 120 5 (.movI32 .rax 39)
    probe_trap 125
    apply Probe.run_retH (by decide) rfl (fun _ _ => rfl) (fun _ _ => rfl)
      (fun outcome => Probe.native_tid_iff _ _ outcome (Or.inl rfl) (by probe_clear)) linuxTid (by decide +kernel)
      (fun h => h)
    probe_instr 127 3 (.mov .q (.reg .rbx) .rax)
    probe_instr 130 5 (.movI32 .rax 186)
    probe_trap 135
    apply Probe.run_retH (by decide) rfl (fun _ _ => rfl) (fun _ _ => rfl)
      (fun outcome => Probe.native_tid_iff _ _ outcome (Or.inr (Or.inl rfl)) (by probe_clear)) linuxTid
      (by decide +kernel) (fun h => h)
    probe_instr 137 3 (.alu .q .sub (.reg .rax) .rbx)
    probe_instr 140 3 (.mov .q (.reg .r12) .rax)
    probe_instr 143 5 (.movI32 .rax 218)
    probe_instr 148 5 (.movI32 .rdi 0)
    probe_trap 153
    apply Probe.run_retH (by decide) rfl (fun _ _ => rfl) (fun _ _ => rfl)
      (fun outcome => Probe.native_tid_iff _ _ outcome (Or.inr (Or.inr rfl)) (by probe_clear)) linuxTid
      (by decide +kernel) (fun h => h)
    probe_instr 155 3 (.alu .q .sub (.reg .rax) .rbx)
    probe_instr 158 3 (.alu .q .add (.reg .r12) .rax)
    probe_instr 161 5 (.movI32 .rax 102)
    probe_trap 166
    apply Probe.run_retH (by decide) rfl (fun _ _ => rfl) (fun _ _ => rfl)
      (Probe.outcomes_unique (fun outcome => Probe.native_getuid_iff _ _ outcome rfl (by probe_clear))) () trivial
      (fun h => h)
    probe_instr 168 3 (.mov .q (.reg .rbx) .rax)
    probe_instr 171 5 (.movI32 .rax 107)
    probe_trap 176
    apply Probe.run_retH (by decide) rfl (fun _ _ => rfl) (fun _ _ => rfl)
      (Probe.outcomes_unique (fun outcome => Probe.native_geteuid_iff _ _ outcome rfl (by probe_clear))) () trivial
      (fun h => h)
    probe_instr 178 3 (.alu .q .sub (.reg .rax) .rbx)
    probe_instr 181 3 (.alu .q .add (.reg .rax) .r12)
    probe_instr 184 3 (.mov .q (.reg .rdi) .rax)
    probe_instr 187 4 (.aluI8 .q .add (.reg .rdi) 1)
    probe_instr 191 5 (.movI32 .rax 60)
    probe_trap 196
    probe_exit 1
  all_goals probe_side

/-- Mutation: the original's "every execution exits 0" is false of the mutant. -/
theorem not_determined_original : ¬ linuxProbe.Determined noFilter Data.Identity.observed :=
  Probe.not_determined_of_admits _ admits (by
    intro fs fs' same
    simp [Observed.events, Observed.terminal, observed, Data.Identity.observed] at same)

end Identity1

end Silmaril.Process.LPS.Probes
