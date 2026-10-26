module

public import Silmaril.Process.LPS.Machines.X86MuslRunMainFacts

/-! # Every execution of the pinned static-musl launch enters `main`

`X86MuslRun.reaches_main` says that *some* execution of the LPS launch of the
pinned executable reaches `main`. Here: *every* execution does, in the same
way, for every thread id `set_tid_address` may return.

`funnel_main`: from the launch, every execution under `extendedSyscallSpec`
reaches `mainCfg … tid (oracle 1).adjust` for some valid thread id `tid`, with
no events, and before that no configuration is stuck, errors (`SError`,
including unmodeled instructions and syscalls) or diverges. The proof is the
run itself, read as a `Funnel`:

* each of the 540 instruction steps (538 Wire and REP STOSQ steps, the two
  SYSCALL instruction steps) is the unique `SStep` of its configuration: the
  machine step is a function and succeeds, so `instrFault` and
  `instrUnmodeled` are excluded and the syscall rules need a pending number
  (`funnel_instr`);
* at the two syscall transitions every outcome the specification allows is
  enumerated (`funnel_syscall`): `arch_prctl(ARCH_SET_FS, 0x404138)` has
  exactly one, 0 (`archSetFs_outcomes`); `set_tid_address` at the first
  observation has one per thread id in `(0, 2^22)` (`setTid_outcomes`), and
  the run after it is proved for a symbolic `tid`.

`every_execution` then classifies every finite execution: it is a silent
prefix of this path (and still funneled), or it passed through `mainCfg … tid
b`, where `MainFacts tid` holds (argc, argv, envp, alignment, return address,
FS, `td->tid`). `errors_after_main`, `unmodeled_after_main` and
`no_divergence_before_main` are the three "nothing else happens before `main`"
corollaries.

## Readings of the environment

The statements take any refusal filter that does not refuse the two startup
syscalls (`StartupNotRefused`). Three readings are instantiated: LPS's `run`
reading (`noFilter`, every injected failure possible;
`every_execution_run`), the native reference filter
`NativeX86.defaultRefusalFilter cfg` (reference numbers through
`referenceInput`; `every_execution_default`), and `nativeScfgFilter cfg`, LPS's
`spuriousRefusalCfg` over `extendedSyscallSpec` read on native numbers
(`every_execution_scfg`; `startupNotRefused_spurious` covers every
specification). No Lean definition names one of these as *the* native x86
`run_scfg`. A filter that refuses a startup outcome is outside these theorems.
The *named
alternatives* to reaching `main` are empty under both, for two reasons that
are proved, not assumed: neither number has an injected-failure family
(`injectedArm 96 = none` for `set_tid_address`; `arch_prctl` has no reference
number, so the native filter never refuses it), and the specification itself
has no failure outcome here (`ARCH_SET_FS` with a base below `TASK_SIZE_MAX`
answers only 0; `set_tid_address` answers only a thread id). In particular
musl's failure branch after `__set_thread_area` (`js` at `0x401746`, into
`a_crash`) is never taken.

Under the plain native table `NativeX86.syscallSpec`, which has no
`arch_prctl` arm (`extendedSyscallSpec` adds exactly that arm,
`extended_agrees`), the same launch has one ending: every execution is
silent and reaches the pending `arch_prctl`, whose only step is to `SError`
as unmodeled (`native_funnel`, `native_archPrctl_only_unmodeled`,
`native_every_execution`, `native_reaches_unmodeled`).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 100000

namespace Silmaril.Process.LPS.Machines.X86MuslRun

open Silmaril.Process (Memory ByteMemory Region)
open Silmaril.Process.LPS.Machines.X86MuslStartup

/-! ## The two syscall transitions, as funnels -/

open Silmaril.X86 in
theorem syscall_next {platform : Ext.Wire.Platform} {oracle : Nat → X86FlagChoices.Choice}
    {core core' : State} {R : List Region} {B : ByteMemory} {c : Nat} {x8 : Word}
    {eff : SyscallEffect} (memoryEffect : applyMemoryEffect ⟨R, B⟩ eff = ⟨R, B⟩)
    (next : normCore (x86AdvancePastSvc
      (x86ApplyEffectNative ⟨⟨core, ⟨R, B⟩⟩, some x8⟩ eff)).m.core = core') :
    (Isa platform oracle).advancePastSvc ((Isa platform oracle).applyEffect
      ⟨⟨⟨core, ⟨R, B⟩⟩, some x8⟩, c⟩ eff) = running core' R B c := by
  rw [← next, normCore_eq]
  change (⟨x86AdvancePastSvc (x86ApplyEffectNative ⟨⟨core, ⟨R, B⟩⟩, some x8⟩ eff), c⟩ :
    X86FlagChoices.State) = _
  simp only [x86AdvancePastSvc, x86ApplyEffectNative, memoryEffect, running]

open Silmaril.X86 in
/-- The pending `arch_prctl(ARCH_SET_FS, base)` with a valid base: its only
outcome is 0. -/
theorem funnel_archSetFs {platform : Ext.Wire.Platform} {oracle : Nat → X86FlagChoices.Choice}
    {segments : List Segment} {refused : RefusalFilter} {T : Config (Isa platform oracle) → Prop}
    {core core' : State} {R : List Region} {B : ByteMemory} {c : Nat} {x8 : Word}
    {model : Model}
    (halted : model.halted = none) (lazy : model.vmLazy = []) (number : x8 = 158)
    (operation : core.read .rdi = NativeX86.archSetFs)
    (valid : uns (core.read .rsi) < x86AddressSpace.taskSize)
    (notRefused : ∀ input model effect, input.sysno = 158 → ¬ refused input model effect)
    (next : normCore (x86AdvancePastSvc (x86ApplyEffectNative ⟨⟨core, ⟨R, B⟩⟩, some x8⟩
      (mkEffect 0 [] []))).m.core = core')
    (rest : Funnel segments NativeX86.extendedSyscallSpec refused T
      (cfg platform oracle (running core' R B c) model)) :
    Funnel segments NativeX86.extendedSyscallSpec refused T
      (cfg platform oracle ⟨⟨⟨core, ⟨R, B⟩⟩, some x8⟩, c⟩ model) := by
  have outcome : ∀ o, NativeX86.extendedSyscallSpec (sysInput (Isa platform oracle) segments
      ⟨⟨⟨core, ⟨R, B⟩⟩, some x8⟩, c⟩ x8) model o ↔ o = .ok (mkEffect 0 [] []) model [] :=
    archSetFs_pending_outcomes number operation valid
  refine funnel_syscall halted rfl ⟨_, (outcome _).mpr rfl⟩ ?_
  intro o so
  refine ⟨_, _, (outcome o).mp so, halted, lazy, notRefused _ _ _ number, ?_⟩
  rw [syscall_next rfl next]
  exact rest

open Silmaril.X86 in
/-- The pending `set_tid_address` at the first thread-id observation: its
outcomes are exactly the thread ids in `(0, 2^22)`. -/
theorem funnel_setTid {platform : Ext.Wire.Platform} {oracle : Nat → X86FlagChoices.Choice}
    {segments : List Segment} {refused : RefusalFilter} {T : Config (Isa platform oracle) → Prop}
    {core : State} {core' : Word → State} {R : List Region} {B : ByteMemory} {c : Nat}
    {x8 : Word} {model : Model}
    (halted : model.halted = none) (lazy : model.vmLazy = []) (fresh : model.tid = none)
    (number : x8 = 218)
    (notRefused : ∀ input model effect, input.sysno = 218 → ¬ refused input model effect)
    (next : ∀ tid, normCore (x86AdvancePastSvc (x86ApplyEffectNative ⟨⟨core, ⟨R, B⟩⟩, some x8⟩
      (mkEffect tid [] []))).m.core = core' tid)
    (rest : ∀ tid, ValidTid tid → Funnel segments NativeX86.extendedSyscallSpec refused T
      (cfg platform oracle (running (core' tid) R B c) (model.withTid tid))) :
    Funnel segments NativeX86.extendedSyscallSpec refused T
      (cfg platform oracle ⟨⟨⟨core, ⟨R, B⟩⟩, some x8⟩, c⟩ model) := by
  have outcome : ∀ o, NativeX86.extendedSyscallSpec (sysInput (Isa platform oracle) segments
      ⟨⟨⟨core, ⟨R, B⟩⟩, some x8⟩, c⟩ x8) model o ↔
        ∃ tid, ValidTid tid ∧ o = .ok (mkEffect tid [] []) (model.withTid tid) [] := by
    intro o
    rw [setTid_dispatch _ _ _ number, setTid_outcomes _ _ fresh]
  refine funnel_syscall halted rfl ⟨_, (outcome _).mpr ⟨7, validTid_seven, rfl⟩⟩ ?_
  intro o so
  obtain ⟨tid, valid, rfl⟩ := (outcome o).mp so
  refine ⟨_, _, rfl, halted, lazy, notRefused _ _ _ number, ?_⟩
  rw [syscall_next rfl (next tid)]
  exact rest tid valid

/-! ## Every execution reaches `main` -/

/-- The configurations at `main`'s entry: one per valid thread id. -/
def AtMain (platform : Silmaril.X86.Ext.Wire.Platform) (oracle : Nat → X86FlagChoices.Choice)
    (c : Config (Isa platform oracle)) : Prop :=
  ∃ tid, ValidTid tid ∧ c = mainCfg platform oracle tid (oracle 1).adjust

/-- Every execution from the launch reaches `main` silently, and before that
none is stuck, errors or diverges. -/
theorem funnel_main (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) {refused : RefusalFilter}
    (notRefused : StartupNotRefused refused) :
    Funnel snapshot.image.segments NativeX86.extendedSyscallSpec refused (AtMain platform oracle)
      (initialOracle platform oracle) := by
  generalize choice : (oracle 1).adjust = b
  let model := (initialOracle platform oracle).model
  have halted : model.halted = none := initial_halted platform oracle
  have lazy : model.vmLazy = [] := initial_lazy platform oracle
  have fresh : model.tid = none := initial_tid platform oracle
  rw [initial_cfg]
  refine funnel0_60 platform oracle model halted lazy ?_
  refine funnel60_120 platform oracle model halted lazy ?_
  refine funnel120_180 platform oracle model halted lazy ?_
  refine funnel180_240 platform oracle model halted lazy ?_
  refine funnel240_300 platform oracle model halted lazy ?_
  refine funnel300_360 platform oracle model halted lazy ?_
  refine funnel360_420 platform oracle model halted lazy ?_
  refine funnel420_447 platform oracle model halted lazy ?_
  refine funnel_instr halted lazy rfl (next447 platform oracle _) ?_
  refine funnel_archSetFs halted lazy rfl rfl (by decide +kernel)
    (fun input model effect number => notRefused input model effect (.inl number)) advance448 ?_
  refine funnel449_457 platform oracle model halted lazy ?_
  refine funnel_instr halted lazy rfl (next457 platform oracle _ b choice) ?_
  refine funnel_setTid halted lazy fresh rfl
    (fun input model effect number => notRefused input model effect (.inr number))
    (fun tid => advance458 tid b) ?_
  intro tid valid
  have halted' : (model.withTid tid).halted = none := halted
  have lazy' : (model.withTid tid).vmLazy = [] := lazy
  refine funnel459_519 platform oracle (model.withTid tid) tid b halted' lazy' ?_
  refine funnel519_542 platform oracle (model.withTid tid) tid b halted' lazy' ?_
  exact Funnel.done ⟨tid, valid, by rw [choice]; rfl⟩

/-- **Every execution from the pinned launch** either is a silent prefix of
the path to `main` (and every execution extending it still reaches `main`),
or has entered `main` with exactly `MainFacts tid` for the thread id `tid` it
was given and continued from there. -/
theorem every_execution (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) {refused : RefusalFilter}
    (notRefused : StartupNotRefused refused) {trace : List Event}
    {final : Config (Isa platform oracle)}
    (run : Star snapshot.image.segments NativeX86.extendedSyscallSpec refused
      (initialOracle platform oracle) trace final) :
    (trace = [] ∧ Funnel snapshot.image.segments NativeX86.extendedSyscallSpec refused
        (AtMain platform oracle) final) ∨
      ∃ tid, ValidTid tid ∧
        Star snapshot.image.segments NativeX86.extendedSyscallSpec refused
          (initialOracle platform oracle) [] (mainCfg platform oracle tid (oracle 1).adjust) ∧
        MainFacts tid (mainCfg platform oracle tid (oracle 1).adjust) ∧
        Star snapshot.image.segments NativeX86.extendedSyscallSpec refused
          (mainCfg platform oracle tid (oracle 1).adjust) trace final := by
  rcases (funnel_main platform oracle notRefused).cover run with before | ⟨m, ⟨tid, valid, rfl⟩,
    first, second⟩
  · exact .inl before
  · exact .inr ⟨tid, valid, first, mainCfg_facts platform oracle tid _, second⟩

/-- Every reachable `SError` is reached after `main`. -/
theorem errors_after_main (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) {refused : RefusalFilter}
    (notRefused : StartupNotRefused refused) {trace evs : List Event}
    {final : Config (Isa platform oracle)}
    (run : Star snapshot.image.segments NativeX86.extendedSyscallSpec refused
      (initialOracle platform oracle) trace final)
    (error : SStep snapshot.image.segments NativeX86.extendedSyscallSpec refused final evs .error) :
    ∃ tid, ValidTid tid ∧
      Star snapshot.image.segments NativeX86.extendedSyscallSpec refused
        (mainCfg platform oracle tid (oracle 1).adjust) trace final := by
  obtain ⟨m, ⟨tid, valid, rfl⟩, _, second⟩ := (funnel_main platform oracle notRefused).error_after
    run error
  exact ⟨tid, valid, second⟩

/-- Every reachable unmodeled instruction or syscall is reached after `main`. -/
theorem unmodeled_after_main (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) {refused : RefusalFilter}
    (notRefused : StartupNotRefused refused) {trace : List Event}
    {final : Config (Isa platform oracle)}
    (run : Star snapshot.image.segments NativeX86.extendedSyscallSpec refused
      (initialOracle platform oracle) trace final)
    (unmodeled : UnmodeledAt snapshot.image.segments NativeX86.extendedSyscallSpec final) :
    ∃ tid, ValidTid tid ∧
      Star snapshot.image.segments NativeX86.extendedSyscallSpec refused
        (mainCfg platform oracle tid (oracle 1).adjust) trace final := by
  obtain ⟨halted, ⟨pending, account⟩ | ⟨x8, pending, spec⟩⟩ := unmodeled
  · exact errors_after_main platform oracle notRefused run (SStep.instrUnmodeled halted pending account)
  · exact errors_after_main platform oracle notRefused run (SStep.syscallUnmodeled halted pending spec)

/-- No infinite execution from the launch avoids `main`. -/
theorem no_divergence_before_main (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) {refused : RefusalFilter}
    (notRefused : StartupNotRefused refused) (seq : Nat → Config (Isa platform oracle))
    (start : seq 0 = initialOracle platform oracle)
    (steps : ∀ n, ∃ evs, SStep snapshot.image.segments NativeX86.extendedSyscallSpec refused
      (seq n) evs (.next (seq (n + 1)))) :
    ∃ n tid, ValidTid tid ∧ seq n = mainCfg platform oracle tid (oracle 1).adjust := by
  obtain ⟨n, tid, valid, at_⟩ := (funnel_main platform oracle notRefused).no_divergence seq start
    steps
  exact ⟨n, tid, valid, at_⟩

/-- `every_execution` under the native reference refusal filter
(LPS `run_scfg`, every `SpuriousCfg`). -/
theorem every_execution_default (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) (cfgRefusal : SpuriousCfg) {trace : List Event}
    {final : Config (Isa platform oracle)}
    (run : Star snapshot.image.segments NativeX86.extendedSyscallSpec
      (NativeX86.defaultRefusalFilter cfgRefusal) (initialOracle platform oracle) trace final) :
    (trace = [] ∧ Funnel snapshot.image.segments NativeX86.extendedSyscallSpec
        (NativeX86.defaultRefusalFilter cfgRefusal) (AtMain platform oracle) final) ∨
      ∃ tid, ValidTid tid ∧
        Star snapshot.image.segments NativeX86.extendedSyscallSpec
          (NativeX86.defaultRefusalFilter cfgRefusal)
          (initialOracle platform oracle) [] (mainCfg platform oracle tid (oracle 1).adjust) ∧
        MainFacts tid (mainCfg platform oracle tid (oracle 1).adjust) ∧
        Star snapshot.image.segments NativeX86.extendedSyscallSpec
          (NativeX86.defaultRefusalFilter cfgRefusal)
          (mainCfg platform oracle tid (oracle 1).adjust) trace final :=
  every_execution platform oracle (startupNotRefused_default cfgRefusal) run

/-- `every_execution` under LPS's `run` reading: no outcome filtered, every
injected failure possible. -/
theorem every_execution_run (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) {trace : List Event}
    {final : Config (Isa platform oracle)}
    (run : Star snapshot.image.segments NativeX86.extendedSyscallSpec noFilter
      (initialOracle platform oracle) trace final) :
    (trace = [] ∧ Funnel snapshot.image.segments NativeX86.extendedSyscallSpec noFilter
        (AtMain platform oracle) final) ∨
      ∃ tid, ValidTid tid ∧
        Star snapshot.image.segments NativeX86.extendedSyscallSpec noFilter
          (initialOracle platform oracle) [] (mainCfg platform oracle tid (oracle 1).adjust) ∧
        MainFacts tid (mainCfg platform oracle tid (oracle 1).adjust) ∧
        Star snapshot.image.segments NativeX86.extendedSyscallSpec noFilter
          (mainCfg platform oracle tid (oracle 1).adjust) trace final :=
  every_execution platform oracle startupNotRefused_noFilter run

/-- LPS's `spurious_refusal_cfg` classifier applied directly to native
numbers refuses neither startup syscall, for every specification and every
`SpuriousCfg`: neither 158 nor 218 is in `injectedTable`, so
`injectedFamilyOff` is false at both. -/
theorem startupNotRefused_spurious (spec : Sys SyscallEffect) (cfgRefusal : SpuriousCfg) :
    StartupNotRefused (spuriousRefusalCfg spec cfgRefusal) := by
  rintro input model effect (number | number) ⟨off, _⟩
  · have none_ : injectedArm input.sysno.toNat = none := by rw [number]; rfl
    simp [injectedFamilyOff, none_] at off
  · have none_ : injectedArm input.sysno.toNat = none := by rw [number]; rfl
    simp [injectedFamilyOff, none_] at off

/-- The `run_scfg` filter read over native numbers: `Run.runScfg`'s
`spuriousRefusalCfg`, taken over `extendedSyscallSpec` instead of the
reference table. This and `NativeX86.defaultRefusalFilter` (reference numbers
through `referenceInput`) are the two native `run_scfg` readings instantiated
here; no Lean definition fixes either one as *the* native x86 `run_scfg`. -/
def nativeScfgFilter (cfgRefusal : SpuriousCfg) : RefusalFilter :=
  spuriousRefusalCfg NativeX86.extendedSyscallSpec cfgRefusal

/-- `every_execution` under the native-number `run_scfg` reading. -/
theorem every_execution_scfg (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) (cfgRefusal : SpuriousCfg) {trace : List Event}
    {final : Config (Isa platform oracle)}
    (run : Star snapshot.image.segments NativeX86.extendedSyscallSpec
      (nativeScfgFilter cfgRefusal) (initialOracle platform oracle) trace final) :
    (trace = [] ∧ Funnel snapshot.image.segments NativeX86.extendedSyscallSpec
        (nativeScfgFilter cfgRefusal) (AtMain platform oracle) final) ∨
      ∃ tid, ValidTid tid ∧
        Star snapshot.image.segments NativeX86.extendedSyscallSpec
          (nativeScfgFilter cfgRefusal)
          (initialOracle platform oracle) [] (mainCfg platform oracle tid (oracle 1).adjust) ∧
        MainFacts tid (mainCfg platform oracle tid (oracle 1).adjust) ∧
        Star snapshot.image.segments NativeX86.extendedSyscallSpec
          (nativeScfgFilter cfgRefusal)
          (mainCfg platform oracle tid (oracle 1).adjust) trace final :=
  every_execution platform oracle
    (startupNotRefused_spurious NativeX86.extendedSyscallSpec cfgRefusal) run

/-- Neither startup syscall has an injected-failure family: `set_tid_address`
(reference number 96) is not in `injectedTable`, and `arch_prctl` has no
reference number, so the native filter has no input to classify. -/
theorem startup_no_injected_family :
    injectedArm 96 = none ∧ (NativeX86.byNative 158).isNone = true := ⟨rfl, by decide⟩

/-! ## The plain native table: unmodeled at `arch_prctl` -/

/-- `extendedSyscallSpec` is the plain native table with the `arch_prctl` arm
added, and agrees with it at every other number. -/
theorem extended_agrees (input : SyscallInput) (model : Model) (outcome : Outcome SyscallEffect)
    (other : input.sysno.toNat ≠ 158) :
    NativeX86.extendedSyscallSpec input model outcome ↔
      NativeX86.syscallSpec input model outcome := by
  have ne : ¬ (158 = input.sysno.toNat) := fun h => other h.symm
  simp [NativeX86.extendedSyscallSpec, NativeX86.extendedTable, NativeX86.syscallSpec, dispatch,
    lookupArm, NativeX86.archPrctlArm, arm, ne]

theorem native_lookup_archPrctl : (lookupArm (NativeX86.table specTable) 158).isNone = true := by
  decide +kernel

/-- The plain native table has no `arch_prctl` arm: its only outcome is
`unmodeled`. -/
theorem native_archPrctl_unmodeled (input : SyscallInput) (model : Model)
    (outcome : Outcome SyscallEffect) (number : input.sysno = 158) :
    NativeX86.syscallSpec input model outcome ↔ outcome = .unmodeled := by
  have none_ : lookupArm (NativeX86.table specTable) 158 = none :=
    Option.isNone_iff_eq_none.mp native_lookup_archPrctl
  unfold NativeX86.syscallSpec dispatch
  rw [number]
  change (match lookupArm (NativeX86.table specTable) 158 with
    | some a => a.spec input model outcome
    | none => Sys.unmodeled input model outcome) ↔ _
  rw [none_]
  rfl

/-- The configuration with `arch_prctl(ARCH_SET_FS, 0x404138)` pending. -/
def archPending (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) : Config (Isa platform oracle) :=
  cfg platform oracle ⟨⟨⟨c448, ⟨R, M84⟩⟩, some (c447.read .rax)⟩, 1⟩
    (initialOracle platform oracle).model

/-- Under the plain native table every execution reaches the pending
`arch_prctl` silently; the first 448 steps are the same as under the
extension. -/
theorem native_funnel (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) (refused : RefusalFilter) :
    Funnel snapshot.image.segments NativeX86.syscallSpec refused
      (· = archPending platform oracle) (initialOracle platform oracle) := by
  let model := (initialOracle platform oracle).model
  have halted : model.halted = none := initial_halted platform oracle
  have lazy : model.vmLazy = [] := initial_lazy platform oracle
  rw [initial_cfg]
  refine funnel0_60 platform oracle model halted lazy ?_
  refine funnel60_120 platform oracle model halted lazy ?_
  refine funnel120_180 platform oracle model halted lazy ?_
  refine funnel180_240 platform oracle model halted lazy ?_
  refine funnel240_300 platform oracle model halted lazy ?_
  refine funnel300_360 platform oracle model halted lazy ?_
  refine funnel360_420 platform oracle model halted lazy ?_
  refine funnel420_447 platform oracle model halted lazy ?_
  refine funnel_instr halted lazy rfl (next447 platform oracle _) ?_
  exact Funnel.done rfl

/-- At the pending `arch_prctl` the plain native table's only step is to
`SError`, as unmodeled. -/
theorem native_archPrctl_only_unmodeled (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) (refused : RefusalFilter) :
    UnmodeledAt snapshot.image.segments NativeX86.syscallSpec (archPending platform oracle) ∧
      ∀ evs st, SStep snapshot.image.segments NativeX86.syscallSpec refused
        (archPending platform oracle) evs st → evs = [] ∧ st = .error := by
  have number : ∀ segments, (sysInput (Isa platform oracle) segments
      ⟨⟨⟨c448, ⟨R, M84⟩⟩, some (c447.read .rax)⟩, 1⟩ (c447.read .rax)).sysno = 158 :=
    fun _ => rfl
  refine ⟨⟨initial_halted platform oracle, .inr ⟨_, rfl,
    (native_archPrctl_unmodeled _ _ _ (number _)).mpr rfl⟩⟩, ?_⟩
  intro evs st step
  cases step with
  | instr _ p => cases p
  | instrFault _ p => cases p
  | instrUnmodeled _ p => cases p
  | syscall _ p so =>
    cases p
    cases (native_archPrctl_unmodeled _ _ _ (number _)).mp so
  | syscallMaterializationFault _ p so =>
    cases p
    cases (native_archPrctl_unmodeled _ _ _ (number _)).mp so
  | exit _ p so =>
    cases p
    cases (native_archPrctl_unmodeled _ _ _ (number _)).mp so
  | killed _ p so =>
    cases p
    cases (native_archPrctl_unmodeled _ _ _ (number _)).mp so
  | syscallUnmodeled => exact ⟨rfl, rfl⟩

/-- Under the plain native table every execution from the launch is silent
and is a prefix of the path to the pending `arch_prctl`, or is exactly that
configuration, whose only step is the unmodeled `SError`. -/
theorem native_every_execution (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) (refused : RefusalFilter) {trace : List Event}
    {final : Config (Isa platform oracle)}
    (run : Star snapshot.image.segments NativeX86.syscallSpec refused
      (initialOracle platform oracle) trace final) :
    trace = [] ∧ Funnel snapshot.image.segments NativeX86.syscallSpec refused
      (· = archPending platform oracle) final := by
  rcases (native_funnel platform oracle refused).cover run with before | ⟨m, rfl, _, second⟩
  · exact before
  · cases second with
    | refl => exact ⟨rfl, Funnel.done rfl⟩
    | step st _ =>
      cases ((native_archPrctl_only_unmodeled platform oracle refused).2 _ _ st).2

/-- Under the plain native table the launch reaches an unmodeled syscall. -/
theorem native_reaches_unmodeled (platform : Silmaril.X86.Ext.Wire.Platform)
    (oracle : Nat → X86FlagChoices.Choice) (refused : RefusalFilter) :
    ReachesUnmodeled snapshot.image.segments NativeX86.syscallSpec refused
      (initialOracle platform oracle) := by
  obtain ⟨m, rfl, run⟩ := (native_funnel platform oracle refused).reaches
  exact ⟨[], _, run, (native_archPrctl_only_unmodeled platform oracle refused).1⟩

end Silmaril.Process.LPS.Machines.X86MuslRun
