module

public import Silmaril.Process.LPS.Machines.X86MuslRunSteps0
public import Silmaril.Process.LPS.Machines.X86MuslRunSteps1
public import Silmaril.Process.LPS.Machines.X86MuslRunSteps2
public import Silmaril.Process.LPS.Machines.X86MuslRunSteps3
public import Silmaril.Process.LPS.Machines.X86MuslRunSteps4
public import Silmaril.Process.LPS.Machines.X86MuslRunSteps5
public import Silmaril.Process.LPS.Machines.X86MuslRunSteps6
public import Silmaril.Process.LPS.Machines.X86MuslRunSteps7
public import Silmaril.Process.LPS.Machines.X86MuslRunSteps8
public import Silmaril.Process.LPS.Machines.X86MuslRunSteps9
public import Silmaril.Process.LPS.Machines.X86MuslRunSteps10
public import Silmaril.Process.LPS.Machines.X86ArchPrctl

/-! # The pinned static-musl executable reaches `main` under the LPS semantics

`reaches_main`: for every CPUID platform, every flag oracle and every spurious
refusal configuration, the actual LPS run relation (`Star` of `SStep`) takes
the flag-oracle Wire+REP STOSQ launch of the exact pinned bytes
(`X86MuslStartup.initialOracle`: `ELFImage.loadX86` of the 16,256-byte file,
argv `checksum`, empty environment) to a running state at `main` (0x401030)
with an empty event trace.

The run has 542 transitions: 538 instruction steps (including 38 REP STOSQ
microsteps in `__init_libc`), the two SYSCALL instruction steps, and two
syscall transitions under the native table with the `arch_prctl` extension
(`NativeX86.extendedSyscallSpec`):

* `arch_prctl(ARCH_SET_FS, 0x404138)` returns 0 (`Machines/X86ArchPrctl.lean`;
  Linux `arch/x86/kernel/process_64.c:898-923`), and sets the FS base;
* `set_tid_address(0x404270)` returns the thread id the environment chooses
  (LPS `Sys/Kernel/Fork.v:123`), any id in `(0, 2^22)` (`ValidTid`).
  `star_main` is proved for every such id: the states after the call are
  functions of a symbolic `tid`, which flows only into RAX (overwritten two
  instructions later) and into the four bytes of `td->tid`; every later step
  is checked with `tid` symbolic, so the path to `main` does not depend on it.
  `reaches_main` instantiates it at 7.

The flags SYSCALL saves in R11 are completed by the oracle; at
`set_tid_address` only AF is undefined (left by `test %eax,%eax`), and the
run is proved for both choices. Nothing on the path is pending or unmodeled
on this base.

`star_main` holds under any refusal filter that refuses neither startup
syscall (`StartupNotRefused`), which covers LPS's `run` reading (`noFilter`)
and every native `run_scfg` reading. That *every* execution takes this path
is `X86MuslRunUniversal.funnel_main`.

The run's states were found by evaluating the same Lean step function
(`lps-run.trace`); each step is nonetheless a theorem about the actual
`stepUsing (X86RepStosq.step platform) oracle` or `SStep`.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 100000

namespace Silmaril.Process.LPS.Machines.X86MuslRun

open Silmaril.Process (Memory ByteMemory Region)
open Silmaril.Process.LPS.Machines.X86MuslStartup


/-! ## `arch_prctl(ARCH_SET_FS, 0x404138)` -/

theorem next447 (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) (segments : List Segment) :
    Next (Isa platform oracle) segments (running c447 R M84 0)
      ⟨⟨⟨c448, ⟨R, M84⟩⟩, some (c447.read .rax)⟩, 1⟩ :=
  syscall_step realizes84 (by decide +kernel)
    (X86FlagChoices.completeFlags_eq_self _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) rfl

/-- `arch_prctl(ARCH_SET_FS, base)` with a valid base has exactly one
specified outcome: 0, with the model unchanged. -/
theorem archSetFs_outcomes (input : SyscallInput) (model : Model) (outcome : Outcome SyscallEffect)
    (number : input.sysno = 158) (operation : input.arg 0 = NativeX86.archSetFs)
    (valid : uns (input.arg 1) < x86AddressSpace.taskSize) :
    NativeX86.extendedSyscallSpec input model outcome ↔
      outcome = .ok (mkEffect 0 [] []) model [] := by
  rw [NativeX86.archPrctl_dispatch _ _ _ number, operation]
  exact NativeX86.archPrctl_success _ _ _ _ valid

open Silmaril.X86 in
/-- `archSetFs_outcomes` at the input of a pending SYSCALL of the run. -/
theorem archSetFs_pending_outcomes {platform : Ext.Wire.Platform}
    {oracle : Nat → X86FlagChoices.Choice} {segments : List Segment} {core : State}
    {R : List Region} {B : ByteMemory} {c : Nat} {x8 : Word} {model : Model}
    (number : x8 = 158) (operation : core.read .rdi = NativeX86.archSetFs)
    (valid : uns (core.read .rsi) < x86AddressSpace.taskSize) (outcome : Outcome SyscallEffect) :
    NativeX86.extendedSyscallSpec (sysInput (Isa platform oracle) segments
      ⟨⟨⟨core, ⟨R, B⟩⟩, some x8⟩, c⟩ x8) model outcome ↔
        outcome = .ok (mkEffect 0 [] []) model [] := by
  generalize input : sysInput (Isa platform oracle) segments
    ⟨⟨⟨core, ⟨R, B⟩⟩, some x8⟩, c⟩ x8 = sysin
  have sysno : sysin.sysno = 158 := by rw [← input]; exact number
  have first : sysin.arg 0 = NativeX86.archSetFs := by rw [← input]; exact operation
  have second : sysin.arg 1 = core.read .rsi := by rw [← input]; rfl
  exact archSetFs_outcomes sysin model outcome sysno first (second ▸ valid)

open Silmaril.X86 in
/-- A pending `arch_prctl(ARCH_SET_FS, base)` with a valid base succeeds with 0,
under any refusal filter that does not refuse it; the architectural FS-base
update is part of the state the run continues from. -/
theorem star_archSetFs' {platform : Ext.Wire.Platform} {oracle : Nat → X86FlagChoices.Choice}
    {segments : List Segment} {refused : RefusalFilter} {core core' : State}
    {R : List Region} {B : ByteMemory} {c : Nat} {x8 : Word} {model : Model}
    {trace : List Event} {final : Config (Isa platform oracle)}
    (halted : model.halted = none) (lazy : model.vmLazy = []) (number : x8 = 158)
    (operation : core.read .rdi = NativeX86.archSetFs)
    (valid : uns (core.read .rsi) < x86AddressSpace.taskSize)
    (notRefused : ∀ input model effect, input.sysno = 158 → ¬ refused input model effect)
    (next : normCore (x86AdvancePastSvc (x86ApplyEffectNative ⟨⟨core, ⟨R, B⟩⟩, some x8⟩
      (mkEffect 0 [] []))).m.core = core')
    (rest : Star segments NativeX86.extendedSyscallSpec refused
      (cfg platform oracle (running core' R B c) model) trace final) :
    Star segments NativeX86.extendedSyscallSpec refused
      (cfg platform oracle ⟨⟨⟨core, ⟨R, B⟩⟩, some x8⟩, c⟩ model) trace final := by
  have specified : NativeX86.extendedSyscallSpec (sysInput (Isa platform oracle) segments
      ⟨⟨⟨core, ⟨R, B⟩⟩, some x8⟩, c⟩ x8) model (.ok (mkEffect 0 [] []) model []) :=
    (archSetFs_pending_outcomes number operation valid _).mpr rfl
  exact star_syscall halted specified (notRefused _ _ _ number) halted
    (Progress.materializeModelAccesses_noLazy _ _ lazy) rfl next rest

open Silmaril.X86 in
/-- `star_archSetFs'` under the default native refusal filter. -/
theorem star_archSetFs {platform : Ext.Wire.Platform} {oracle : Nat → X86FlagChoices.Choice}
    {segments : List Segment} {cfgRefusal : SpuriousCfg} {core core' : State}
    {R : List Region} {B : ByteMemory} {c : Nat} {x8 : Word} {model : Model}
    {trace : List Event} {final : Config (Isa platform oracle)}
    (halted : model.halted = none) (lazy : model.vmLazy = []) (number : x8 = 158)
    (operation : core.read .rdi = NativeX86.archSetFs)
    (valid : uns (core.read .rsi) < x86AddressSpace.taskSize)
    (next : normCore (x86AdvancePastSvc (x86ApplyEffectNative ⟨⟨core, ⟨R, B⟩⟩, some x8⟩
      (mkEffect 0 [] []))).m.core = core')
    (rest : Star segments NativeX86.extendedSyscallSpec (NativeX86.defaultRefusalFilter cfgRefusal)
      (cfg platform oracle (running core' R B c) model) trace final) :
    Star segments NativeX86.extendedSyscallSpec (NativeX86.defaultRefusalFilter cfgRefusal)
      (cfg platform oracle ⟨⟨⟨core, ⟨R, B⟩⟩, some x8⟩, c⟩ model) trace final :=
  star_archSetFs' halted lazy number operation valid
    (fun _ _ _ number => NativeX86.archPrctl_not_spuriously_refused _ _ _ _ number) next rest

theorem advance448 : normCore (x86AdvancePastSvc (x86ApplyEffectNative
    ⟨⟨c448, ⟨R, M84⟩⟩, some (c447.read .rax)⟩ (mkEffect 0 [] []))).m.core = c449 := rfl

theorem advance458 (tid : Silmaril.X86.Word) (b : Bool) : normCore (x86AdvancePastSvc
    (x86ApplyEffectNative ⟨⟨c458 b, ⟨R, M86⟩⟩, some (c457.read .rax)⟩ (mkEffect tid [] []))).m.core =
      c459 tid b := by
  cases b <;> rfl

/-! ## `set_tid_address(0x404270)` -/

theorem next457 (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) (segments : List Segment) (b : Bool)
    (choice : (oracle 1).adjust = b) :
    Next (Isa platform oracle) segments (running c457 R M86 1)
      ⟨⟨⟨c458 b, ⟨R, M86⟩⟩, some (c457.read .rax)⟩, 2⟩ := by
  apply syscall_step realizes86 (by decide +kernel)
    (flags := ⟨some false, some true, some b, some true, some false, some false⟩)
  · simp [X86FlagChoices.completeFlags, X86FlagChoices.completeFlag, c457, choice]
  · cases b <;> rfl

theorem setTid_not_refused (cfg : SpuriousCfg) (input : SyscallInput) (model : Model)
    (effect : SyscallEffect) (number : input.sysno = 218) :
    ¬ NativeX86.defaultRefusalFilter cfg input model effect := by
  have off : injectedArm 96 = none := rfl
  simp [NativeX86.defaultRefusalFilter, NativeX86.refusalFilter, NativeX86.referenceInput,
    number, NativeX86.byNative, NativeX86.numbers, spuriousRefusalCfg, injectedFamilyOff,
    NativeX86.referenceInputFor, zw, off]

/-- The thread ids `set_tid_address` may return at the first observation
(LPS `Sys/Kernel/Fork.v:123`): `(0, PID_MAX_ENVELOPE)`, `PID_MAX_ENVELOPE = 2^22`. -/
def ValidTid (tid : Silmaril.X86.Word) : Prop := 0 < uns tid ∧ uns tid < PID_MAX_ENVELOPE

theorem validTid_seven : ValidTid 7 := ⟨by decide, by decide⟩

/-- `extendedSyscallSpec` at `set_tid_address` is the reference arm on the
reference input. -/
theorem setTid_dispatch (input : SyscallInput) (model : Model)
    (outcome : Outcome SyscallEffect) (number : input.sysno = 218) :
    NativeX86.extendedSyscallSpec input model outcome =
      setTidAddressSpec (NativeX86.referenceInputFor ⟨96, 218, "set_tid_address"⟩ input) model
        outcome := by
  unfold NativeX86.extendedSyscallSpec dispatch
  rw [number]
  rfl

/-- At the first thread-id observation, `set_tid_address` returns some id in
range and records it; nothing else is specified. -/
theorem setTid_outcomes (input : SyscallInput) (model : Model) (fresh : model.tid = none)
    (outcome : Outcome SyscallEffect) :
    setTidAddressSpec input model outcome ↔
      ∃ tid, ValidTid tid ∧ outcome = .ok (mkEffect tid [] []) (model.withTid tid) [] := by
  constructor
  · intro spec
    cases outcome with
    | ok eff model' evs =>
      obtain ⟨x, m₁, evs₁, evs₂, get, rest, events⟩ := spec
      cases get
      simp only [fresh] at rest
      obtain ⟨tid, m₂, evs₃, evs₄, ⟨t, valid, chosen⟩, rest, events'⟩ := rest
      cases chosen
      obtain ⟨u, m₃, evs₅, evs₆, modified, returned, events''⟩ := rest
      cases modified
      cases returned
      subst events events' events''
      exact ⟨_, valid, rfl⟩
    | unmodeled =>
      rcases spec with get | ⟨x, m₁, evs₁, get, rest⟩
      · cases get
      · cases get
        simp only [fresh] at rest
        rcases rest with ⟨t, _, chosen⟩ | ⟨tid, m₂, evs₃, ⟨t, _, chosen⟩, rest⟩
        · cases chosen
        · cases chosen
          rcases rest with modified | ⟨u, m₃, evs₅, modified, returned⟩
          · cases modified
          · cases returned
  · rintro ⟨tid, valid, rfl⟩
    refine ⟨model, model, [], [], rfl, ?_, rfl⟩
    simp only [fresh]
    exact ⟨tid, model, [], [], ⟨tid, valid, rfl⟩,
      ⟨(), model.withTid tid, [], [], rfl, rfl, rfl⟩, rfl⟩

open Silmaril.X86 in
/-- A pending `set_tid_address` at the first thread-id observation returns
the chosen id `tid` (any id in `(0, 2^22)`) and records it in the model. -/
theorem star_setTid {platform : Ext.Wire.Platform} {oracle : Nat → X86FlagChoices.Choice}
    {segments : List Segment} {refused : RefusalFilter} {core core' : State}
    {R : List Region} {B : ByteMemory} {c : Nat} {x8 : Word} {model : Model}
    {trace : List Event} {final : Config (Isa platform oracle)} {tid : Word}
    (halted : model.halted = none) (lazy : model.vmLazy = []) (fresh : model.tid = none)
    (number : x8 = 218) (valid : ValidTid tid)
    (notRefused : ∀ input model effect, input.sysno = 218 → ¬ refused input model effect)
    (next : normCore (x86AdvancePastSvc (x86ApplyEffectNative ⟨⟨core, ⟨R, B⟩⟩, some x8⟩
      (mkEffect tid [] []))).m.core = core')
    (rest : Star segments NativeX86.extendedSyscallSpec refused
      (cfg platform oracle (running core' R B c) (model.withTid tid)) trace final) :
    Star segments NativeX86.extendedSyscallSpec refused
      (cfg platform oracle ⟨⟨⟨core, ⟨R, B⟩⟩, some x8⟩, c⟩ model) trace final := by
  have specified : NativeX86.extendedSyscallSpec (sysInput (Isa platform oracle) segments
      ⟨⟨⟨core, ⟨R, B⟩⟩, some x8⟩, c⟩ x8) model
      (.ok (mkEffect tid [] []) (model.withTid tid) []) := by
    rw [setTid_dispatch _ _ _ number, setTid_outcomes _ _ fresh]
    exact ⟨tid, valid, rfl⟩
  exact star_syscall halted specified (notRefused _ _ _ number) halted
    (Progress.materializeModelAccesses_noLazy _ _ lazy) rfl next rest

/-! ## The whole run -/

theorem initial_cfg (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) :
    initialOracle platform oracle =
      cfg platform oracle (running c0 R M0 0) (initialOracle platform oracle).model := by
  rw [← initial_ms]

/-- The configuration in which the run enters `main`, for the returned thread
id `tid` and the oracle's adjust-flag choice `b`. -/
def mainCfg (platform : Silmaril.X86.Ext.Wire.Platform) (oracle : Nat → X86FlagChoices.Choice)
    (tid : Silmaril.X86.Word) (b : Bool) : Config (Isa platform oracle) :=
  cfg platform oracle (running (c542 b) R (M104 tid) 2)
    ((initialOracle platform oracle).model.withTid tid)

/-- No startup syscall outcome is refused: neither `arch_prctl` (158) nor
`set_tid_address` (218) has an injected-failure family. -/
def StartupNotRefused (refused : RefusalFilter) : Prop :=
  ∀ input model effect, (input.sysno = 158 ∨ input.sysno = 218) → ¬ refused input model effect

theorem startupNotRefused_default (cfgRefusal : SpuriousCfg) :
    StartupNotRefused (NativeX86.defaultRefusalFilter cfgRefusal) := by
  rintro input model effect (number | number)
  · exact NativeX86.archPrctl_not_spuriously_refused _ _ _ _ number
  · exact setTid_not_refused _ _ _ _ number

/-- LPS's `run` reading (`Reading = none`): no outcome is filtered. -/
theorem startupNotRefused_noFilter : StartupNotRefused noFilter := fun _ _ _ _ refused => refused

/-- For every thread id `set_tid_address` may return, the actual LPS run
relation takes the launch to `mainCfg … tid b` with no events, in 542
transitions. -/
theorem star_main (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) {refused : RefusalFilter}
    (notRefused : StartupNotRefused refused) (tid : Silmaril.X86.Word) (valid : ValidTid tid) :
    Star snapshot.image.segments NativeX86.extendedSyscallSpec refused
      (initialOracle platform oracle) [] (mainCfg platform oracle tid (oracle 1).adjust) := by
  generalize choice : (oracle 1).adjust = b
  let model := (initialOracle platform oracle).model
  have halted : model.halted = none := initial_halted platform oracle
  have lazy : model.vmLazy = [] := initial_lazy platform oracle
  have fresh : model.tid = none := initial_tid platform oracle
  have halted' : (model.withTid tid).halted = none := halted
  have lazy' : (model.withTid tid).vmLazy = [] := lazy
  rw [initial_cfg]
  refine star_append (run0_60 platform oracle model halted lazy) ?_
  refine star_append (run60_120 platform oracle model halted lazy) ?_
  refine star_append (run120_180 platform oracle model halted lazy) ?_
  refine star_append (run180_240 platform oracle model halted lazy) ?_
  refine star_append (run240_300 platform oracle model halted lazy) ?_
  refine star_append (run300_360 platform oracle model halted lazy) ?_
  refine star_append (run360_420 platform oracle model halted lazy) ?_
  refine star_append (run420_447 platform oracle model halted lazy) ?_
  refine star_instr halted lazy rfl (next447 platform oracle _) ?_
  refine star_archSetFs' halted lazy rfl rfl (by decide +kernel)
    (fun input model effect number => notRefused input model effect (.inl number)) advance448 ?_
  refine star_append (run449_457 platform oracle model halted lazy) ?_
  refine star_instr halted lazy rfl (next457 platform oracle _ b choice) ?_
  refine star_setTid halted lazy fresh rfl valid
    (fun input model effect number => notRefused input model effect (.inr number))
    (advance458 tid b) ?_
  refine star_append (run459_519 platform oracle (model.withTid tid) tid b halted' lazy') ?_
  exact run519_542 platform oracle (model.withTid tid) tid b halted' lazy'

/-- The actual LPS run relation takes the launch of the pinned musl executable
to a running state whose next instruction is `main`'s, with no events. -/
theorem reaches_main (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) (cfgRefusal : SpuriousCfg) :
    ∃ final : Config (x86WireDf0RepStosqWithFlagOracle platform oracle),
      Star snapshot.image.segments NativeX86.extendedSyscallSpec
          (NativeX86.defaultRefusalFilter cfgRefusal) (initialOracle platform oracle) [] final ∧
        final.ms.native.m.core.rip.toNat = mainAddress ∧ final.ms.native.pending = none ∧
        final.model.halted = none :=
  ⟨_, star_main platform oracle (startupNotRefused_default cfgRefusal) 7 validTid_seven,
    by cases (oracle 1).adjust <;> rfl, rfl, initial_halted platform oracle⟩

end Silmaril.Process.LPS.Machines.X86MuslRun
