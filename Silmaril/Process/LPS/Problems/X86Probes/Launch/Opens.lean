module

public import Silmaril.Process.LPS.Problems.X86Probes.Basic
public import Silmaril.Process.LPS.Probes.OpenLegacy
public import Silmaril.Process.LPS.Probes.OpenCreate
public import Silmaril.Process.LPS.Probes.OpenMissing

/-! # The opening probes: runs that leave Linux's exit status

Linux's run of an opening probe is one execution; the published `halts_may_fail` reads every
injected failure as an outcome and every valid input as a launch. Three runs separate the
probes from Linux's single status:

* `open_legacy` (`open("in.txt")`, then `exit(fd)`): an injected `ENOMEM` makes it exit
  `-ENOMEM & 255 = 244` at its own launch (`openLegacy_enomem`).
* `open_create` and `open_create_ko` (`openat(…, O_CREAT)`, `write`, `close`,
  `exit(write's return)`): an injected `ENOMEM` makes the write fail with `EBADF`, and the
  probe exits `247` at its own launch (`openCreate_enomem`, `openCreateKo_enomem`).
* `open_missing` (`openat("nofile")`, then `exit(-ret)`): at a launch whose file system holds
  `nofile` the open succeeds with descriptor 3 and the probe exits `-3 & 255 = 253`
  (`openMissing_present`).

`run_openFailed` is the kit's `run_opened` for an injected errno.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Machines.X86Launch

namespace Probe

variable (P : Probe) {refused : RefusalFilter} {memory : Memory}

/-- The injected-failure alternative `e` of a descriptor-allocating open. -/
theorem run_openFailed {core : Silmaril.X86.State} {n : Word} {model success : Model} {fd : Word}
    {copyins : List (Word × Nat)} {calls : List Call} {trace : List Event}
    {outcome : Omni.Outcome x86ExtNative} (e : Int) (member : e ∈ openatErrnos) (other : n ≠ 158)
    (running : model.halted = none)
    (outcomes : ∀ o, spec (P.sysInM core memory n) model o ↔ ∃ r, OpenAllowed r ∧
      o = .ok ((mkEffect (openRet fd r) [] []).withCopyins copyins) (openModel model success r) [])
    (live : success.halted = none) (lazy : success.vmLazy = []) (lazy₀ : model.vmLazy = [])
    (accepted : ¬ refused (P.sysInM core memory n) model ((mkEffect (errnoRet e) [] []).withCopyins copyins))
    (rest : Run P.segs spec refused (cfgM (resume core (errnoRet e)) memory none model) calls trace outcome) :
    Run P.segs spec refused (cfgM core memory (some n) model)
      (⟨n, x86ExtNative.syscallArgs (⟨⟨core, memory⟩, some n⟩ : X86State), some (errnoRet e)⟩ :: calls)
      ([] ++ trace) outcome :=
  P.run_sys (allowed := OpenAllowed)
    (effect := fun r => (mkEffect (openRet fd r) [] []).withCopyins copyins)
    (model' := openModel model success) (events := fun _ => []) (memory' := fun _ => memory)
    other running outcomes
    (fun r _ => by cases r with | none => exact live | some _ => exact running)
    (fun r _ => by cases r with | none => exact lazy | some _ => exact lazy₀)
    (fun _ _ => rfl) (some e) member accepted rest

end Probe

/-- `open_legacy` with an injected `ENOMEM`: it exits 244. -/
theorem openLegacy_enomem : ∃ calls trace final,
    Run Data.OpenLegacy.probe.segs spec noFilter Data.OpenLegacy.probe.initial calls trace (.halt final) ∧
      final.model.halted = some 244 := by
  apply Exists.intro
  apply Exists.intro
  apply Exists.intro
  constructor
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 2)
  probe_instr 125 5 (.movI32 .rdi 0x400093)
  probe_instr 130 5 (.movI32 .rsi 0)
  probe_trap 135
  apply Probe.run_openFailed _ ENOMEM (by decide) ?_ ?_
    (spec_open_read (clear := ?_) (path := OpenLegacy.name) ?_ ?_ ?_
      (readCstr_image (off := 147) ?_ ?_ ?_ OpenLegacy.name_read) ?_ ?_ ?_ ?_ ?_) <;> probe_sides
  probe_instr 137 3 (.mov .q (.reg .rdi) .rax)
  probe_instr 140 5 (.movI32 .rax 60)
  probe_trap 145
  probe_exit _
  rfl

/-- `open_create`, `open_create_ko` with an injected `ENOMEM`: they exit 247. -/
theorem openCreate_enomem : ∃ calls trace final,
    Run Data.OpenCreate.probe.segs spec noFilter Data.OpenCreate.probe.initial calls trace (.halt final) ∧
      final.model.halted = some 247 := by
  apply Exists.intro
  apply Exists.intro
  apply Exists.intro
  constructor
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 257)
  probe_instr 125 5 (.movI32 .rdi 0xffffff9c)
  probe_instr 130 5 (.movI32 .rsi 0x4000c2)
  probe_instr 135 5 (.movI32 .rdx 0x241)
  probe_instr 140 6 (.movI32 .r10 0x1a4)
  probe_trap 146
  apply Probe.run_openFailed _ ENOMEM (by decide) ?_ ?_
    (spec_openat_create (clear := ?_) (path := outName) ?_ ?_ ?_ ?_ ?_
      (readCstr_image (off := 194) ?_ ?_ ?_ OpenCreate.name_read) ?_ ?_ ?_ ?_ ?_) <;> probe_sides
  probe_instr 148 3 (.mov .q (.reg .rbx) .rax)
  probe_instr 151 5 (.movI32 .rax 1)
  probe_instr 156 3 (.mov .q (.reg .rdi) .rbx)
  probe_instr 159 5 (.movI32 .rsi 0x4000ca)
  probe_instr 164 5 (.movI32 .rdx 2)
  probe_trap 169
  probe_call (spec_write_badfd (clear := ?_) ?_ ?_)
  probe_instr 171 3 (.mov .q (.reg .rbp) .rax)
  probe_instr 174 5 (.movI32 .rax 3)
  probe_instr 179 3 (.mov .q (.reg .rdi) .rbx)
  probe_trap 182
  probe_call (spec_close_badfd (clear := ?_) ?_ ?_)
  probe_instr 184 5 (.movI32 .rax 60)
  probe_instr 189 3 (.mov .q (.reg .rdi) .rbp)
  probe_trap 192
  probe_exit _
  rfl

theorem openCreateKo_enomem : ∃ calls trace final,
    Run Data.OpenCreateKo.probe.segs spec noFilter Data.OpenCreateKo.probe.initial calls trace (.halt final) ∧
      final.model.halted = some 247 := by
  apply Exists.intro
  apply Exists.intro
  apply Exists.intro
  constructor
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 257)
  probe_instr 125 5 (.movI32 .rdi 0xffffff9c)
  probe_instr 130 5 (.movI32 .rsi 0x4000c2)
  probe_instr 135 5 (.movI32 .rdx 0x241)
  probe_instr 140 6 (.movI32 .r10 0x1a4)
  probe_trap 146
  apply Probe.run_openFailed _ ENOMEM (by decide) ?_ ?_
    (spec_openat_create (clear := ?_) (path := outName) ?_ ?_ ?_ ?_ ?_
      (readCstr_image (off := 194) ?_ ?_ ?_ OpenCreateKo.name_read) ?_ ?_ ?_ ?_ ?_) <;> probe_sides
  probe_instr 148 3 (.mov .q (.reg .rbx) .rax)
  probe_instr 151 5 (.movI32 .rax 1)
  probe_instr 156 3 (.mov .q (.reg .rdi) .rbx)
  probe_instr 159 5 (.movI32 .rsi 0x4000ca)
  probe_instr 164 5 (.movI32 .rdx 2)
  probe_trap 169
  probe_call (spec_write_badfd (clear := ?_) ?_ ?_)
  probe_instr 171 3 (.mov .q (.reg .rbp) .rax)
  probe_instr 174 5 (.movI32 .rax 3)
  probe_instr 179 3 (.mov .q (.reg .rdi) .rbx)
  probe_trap 182
  probe_call (spec_close_badfd (clear := ?_) ?_ ?_)
  probe_instr 184 5 (.movI32 .rax 60)
  probe_instr 189 3 (.mov .q (.reg .rdi) .rbp)
  probe_trap 192
  probe_exit _
  rfl

/-! ## `open_missing` at a launch that holds `nofile` -/

namespace OpenMissing

/-- The launch file system with `nofile` (one byte, `x`). -/
def presentFiles : Fs.FileSystem := [(name, [0x78])]

/-- `open_missing` launched with `nofile` present. -/
def present : Probe := { Data.OpenMissing.probe with input := harnessInputFiles presentFiles }

theorem present_layout : present.Layout := by probe_layout

theorem present_name_read : cstrOfList (present.bytes.drop 155) pathMax = .ok name := by decide +kernel

instance present_checked : present.Checked :=
  ⟨present_layout, harnessInputFiles_valid _ (by unfold Fs.ValidFs; decide) (by decide),
    present.snapshot_valid present_layout, by unfold ValidBrk; decide +kernel⟩

/-- With `nofile` present the open returns descriptor 3 and the probe exits 253. -/
theorem present_opens : ∃ calls trace final,
    Run present.segs spec noFilter present.initial calls trace (.halt final) ∧
      final.model.halted = some 253 := by
  apply Exists.intro
  apply Exists.intro
  apply Exists.intro
  constructor
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 257)
  probe_instr 125 5 (.movI32 .rdi 0xffffff9c)
  probe_instr 130 5 (.movI32 .rsi 0x40009b)
  probe_instr 135 5 (.movI32 .rdx 0)
  probe_trap 140
  probe_open (spec_openat_read (clear := ?_) (path := name) ?_ ?_ ?_ ?_
    (readCstr_image (off := 155) ?_ ?_ ?_ present_name_read) ?_ ?_ ?_ ?_ ?_)
  probe_instr 142 3 (.mov .q (.reg .rdi) .rax)
  probe_instr 145 3 (.unary .q .neg (.reg .rdi))
  probe_instr 148 5 (.movI32 .rax 60)
  probe_trap 153
  probe_exit _
  rfl

end OpenMissing

end Silmaril.Process.LPS.Probes

namespace Silmaril.Process.LPS.Problems.X86Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Probes

/-- A path read from an address below the image and the stack faults, given the launch's
`ValidEntry` in the context. -/
macro_rules
  | `(tactic| probe_side) => `(tactic| ((with_reducible show readCstr _ _ = .fault); refine readCstr_view_unmapped _ _ (Probe.permits_launched_low ?_ ?_ ?_) <;> first | assumption | probe_reg_ne))

/-- `open_efault` at every native launch: the path pointer `0x1000` is below the image and
the stack at every launch, so `openat` faults with `EFAULT` and the probe exits 14. -/
theorem openEfault_exec (en : ExecEntry) (inp : ProcInput) (launch : NativeLaunch Data.OpenEfault.probe en inp) :
    Omni.Exec Data.OpenEfault.probe.segs spec noFilter (Data.OpenEfault.probe.launchedAt en inp).initial
      (Emits Data.OpenEfault.observed) := by
  have := Probe.checked_launchedAt (P := Data.OpenEfault.probe) launch.entry launch.input
  have valid := launch.entry
  show Omni.Exec (Data.OpenEfault.probe.launchedAt en inp).segs spec noFilter _ _
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rax 257)
  probe_instr 125 5 (.movI32 .rdi 0xffffff9c)
  probe_instr 130 5 (.movI32 .rsi 0x1000)
  probe_instr 135 5 (.movI32 .rdx 0)
  probe_trap 140
  probe_call (spec_openat_fault (clear := ?_) ?_ ?_ ?_)
  probe_instr 142 3 (.mov .q (.reg .rdi) .rax)
  probe_instr 145 3 (.unary .q .neg (.reg .rdi))
  probe_instr 148 5 (.movI32 .rax 60)
  probe_trap 153
  probe_exit 14
  exact ⟨_, rfl, rfl, rfl, rfl⟩

end Silmaril.Process.LPS.Problems.X86Probes
