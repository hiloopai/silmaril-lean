module

public import Silmaril.Process.LPS.Probes.Kit

/-! # Probe kit rules for identities, `getrandom`, `arch_prctl`, `exit_group` and unknown calls

Additions to `Probes.Kit` for the probes of `Probes.Identity`, `Probes.Getrandom`,
`Probes.UnknownSyscall` and `Probes.ArchPrctl`:

* a configuration over any memory that still holds the loaded segment
  (`Probe.Holds`, `Probe.cfgM`), with instruction, `syscall` and exit rules, for the
  instructions after a call that wrote user memory (`getrandom`);
* a step rule for calls that return to the program, possibly changing the model
  (`Probe.sstep_retH_iff`), and the outcomes of the native `getpid`, `gettid`,
  `set_tid_address` (the thread id is chosen at its first observation and fixed
  thereafter), `getuid`, `geteuid`, `getrandom` (a small request delivers exactly
  the requested number of environment-chosen bytes) and `arch_prctl(ARCH_SET_FS)`;
* the fail-closed calls: a pending call whose only outcome is `unmodeled` steps to
  an error under every refusal filter (`Probe.sstep_unmodeled_iff`). The native
  table does this for a number it does not know (999), for `getrandom` with flag
  bits other than `GRND_NONBLOCK`, and for every `arch_prctl` other than
  `ARCH_SET_FS`;
* `exit_group` has exactly the specification of `exit` (`native_exit_group_iff_exit`).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines
open Silmaril.Process.LPS.Machines.X86Launch
open Silmaril.Process (Memory Access Region Permissions)

/-- The harness launch input with another user id: the id Linux ran the probe as
is a launch parameter of the model (`ProcInput.uid`; LPS launches with
real = effective = saved id). -/
def harnessInputAs (uid : Word) : ProcInput := { harnessInput with uid := uid }

theorem harnessInputAs_valid (uid : Word) (valid : ValidId uid) :
    X86Launch.ValidInput (harnessInputAs uid) := by
  have base := harnessInput_valid
  obtain ⟨⟨argv, envp, fs, keys, ⟨_, gid⟩, nofile, sigmask, rest⟩, hwcap⟩ := base
  exact ⟨⟨argv, envp, fs, keys, ⟨valid, gid⟩, nofile, sigmask, rest⟩, hwcap⟩

namespace Probe

variable (P : Probe)

/-! ## Memories that still hold the loaded segment -/

/-- The memory still has the segment's region and bytes. -/
structure Holds (memory : Memory) : Prop where
  region : segmentRegion P.segment ∈ memory.regions
  installed : ∀ index (bound : index < P.bytes.length),
    memory.bytes.get? (P.base + index) = some P.bytes[index]

theorem holds_mem0 [Checked P] : P.Holds P.mem0 := ⟨P.mem0_region, P.mem0_get⟩

/-- A write of user memory outside the segment keeps it. -/
theorem holds_write {memory : Memory} (holds : P.Holds memory) (address : Nat) (bytes : List Byte)
    (nowrap : address + bytes.length ≤ 2 ^ 64) (above : P.base + P.size ≤ address) (layout : P.Layout) :
    P.Holds { memory with bytes := installWrapping memory.bytes address bytes } := by
  refine ⟨holds.region, fun index bound => ?_⟩
  have sizes := layout.sizes
  rw [installWrapping_outside _ _ _ _ nowrap (Or.inl (by omega))]
  exact holds.installed index bound

section Rules

variable {P} {refused : RefusalFilter}

theorem accountStep_instrH [checked : Checked P] {memory : Memory} (holds : P.Holds memory)
    {off len : Nat} {instruction : Silmaril.X86.Ext.Instr}
    {core core' : Silmaril.X86.State} {model : Model} (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (fits : off + len ≤ P.size) (two : off + 2 ≤ P.size)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core memory len = .ok core' memory) :
    accountStep x86ExtNative P.segs ⟨⟨core, memory⟩, none⟩ model =
      .ok (⟨⟨core', memory⟩, none⟩, model) := by
  have fetched := window_of memory holds.region holds.installed checked.layout .execute (by decide)
    off len (by omega) fits
  have prefix2 := window_of memory holds.region holds.installed checked.layout .execute (by decide)
    off 2 (by omega) two
  apply Progress.accountStep_of_noLazy _ _ model _ lazy
  change x86NativeStep ⟨⟨core, memory⟩, none⟩ = _
  rw [x86NativeStep_of_fetch (s := ⟨⟨core, memory⟩, none⟩)
    (show memory.fetchBytes core.rip.toNat 2 ≠ some [0x0f, 0x05] by
      rw [rip, Memory.fetchBytes, prefix2]
      exact fun h => notSyscall (Option.some.inj h))
    (show memory.fetchBytes core.rip.toNat len = some _ by rw [rip, Memory.fetchBytes, fetched])
    decoded]
  change x86ExecResult _ (Silmaril.X86.Ext.exec instruction core memory len) = _
  rw [exec]
  rfl

theorem sstep_instr_iffH [Checked P] {memory : Memory} (holds : P.Holds memory)
    {off len : Nat} {instruction : Silmaril.X86.Ext.Instr}
    {core core' : Silmaril.X86.State} {model : Model}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (fits : off + len ≤ P.size) (two : off + 2 ≤ P.size)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core memory len = .ok core' memory)
    (evs : List Event) (target : StepTo x86ExtNative) :
    SStep P.segs spec refused (cfgM core memory none model) evs target ↔
      evs = [] ∧ target = .next (cfgM core' memory none model) := by
  have account := accountStep_instrH holds lazy rip fits two notSyscall decoded exec
  constructor
  · intro step
    cases step with
    | instr _ _ h => rw [account] at h; cases h; exact ⟨rfl, rfl⟩
    | instrFault _ _ h => rw [account] at h; cases h
    | instrUnmodeled _ _ h => rw [account] at h; cases h
    | syscall _ p => cases p
    | syscallMaterializationFault _ p => cases p
    | exit _ p => cases p
    | killed _ p => cases p
    | syscallUnmodeled _ p => cases p
  · rintro ⟨rfl, rfl⟩
    exact .instr running rfl account

theorem sstep_trap_iffH [checked : Checked P] {memory : Memory} (holds : P.Holds memory) {off : Nat}
    {core : Silmaril.X86.State} {model : Model}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (two : off + 2 ≤ P.size)
    (isSyscall : (P.bytes.drop off).take 2 = [0x0f, 0x05])
    (defined : (rflagsImage core.flags).isSome = true)
    (evs : List Event) (target : StepTo x86ExtNative) :
    SStep P.segs spec refused (cfgM core memory none model) evs target ↔
      evs = [] ∧ target = .next (cfgM core memory (some (core.read .rax)) model) := by
  have prefix2 := window_of memory holds.region holds.installed checked.layout .execute (by decide)
    off 2 (by omega) two
  have account : accountStep x86ExtNative P.segs ⟨⟨core, memory⟩, none⟩ model =
      .ok (⟨⟨core, memory⟩, some (core.read .rax)⟩, model) := by
    apply Progress.accountStep_of_noLazy _ _ model _ lazy
    exact x86NativeStep_syscall ⟨⟨core, memory⟩, none⟩
      (by rw [show core.rip.toNat = P.base + off from rip, Memory.fetchBytes, prefix2, isSyscall])
      defined
  constructor
  · intro step
    cases step with
    | instr _ _ h => rw [account] at h; cases h; exact ⟨rfl, rfl⟩
    | instrFault _ _ h => rw [account] at h; cases h
    | instrUnmodeled _ _ h => rw [account] at h; cases h
    | syscall _ p => cases p
    | syscallMaterializationFault _ p => cases p
    | exit _ p => cases p
    | killed _ p => cases p
    | syscallUnmodeled _ p => cases p
  · rintro ⟨rfl, rfl⟩
    exact .instr running rfl account

/-- A pending call whose only outcome halts normally, over any memory. -/
theorem sstep_halt_iffH {core : Silmaril.X86.State} {memory : Memory} {n : Word} {model model' : Model}
    {effect : SyscallEffect} {code : Word} (running : model.halted = none)
    (outcomes : ∀ outcome, spec (P.sysInM core memory n) model outcome ↔ outcome = .ok effect model' [])
    (halted : model'.halted = some code) (unkilled : model'.killedBy = none)
    (evs : List Event) (target : StepTo x86ExtNative) :
    SStep P.segs spec refused (cfgM core memory (some n) model) evs target ↔
      evs = [.exitEv code model'.fs] ∧ target = .next (cfgM core memory (some n) model') := by
  constructor
  · intro step
    cases step with
    | instr _ p => cases p
    | instrFault _ p => cases p
    | instrUnmodeled _ p => cases p
    | syscall _ p s _ live =>
      cases p
      cases (outcomes _).mp s
      rw [halted] at live
      cases live
    | syscallMaterializationFault _ p s _ live =>
      cases p
      cases (outcomes _).mp s
      rw [halted] at live
      cases live
    | exit _ p s h _ =>
      cases p
      cases (outcomes _).mp s
      rw [halted] at h
      cases h
      exact ⟨rfl, rfl⟩
    | killed _ p s k =>
      cases p
      cases (outcomes _).mp s
      rw [unkilled] at k
      cases k
    | syscallUnmodeled _ p s =>
      cases p
      cases (outcomes _).mp s
  · rintro ⟨rfl, rfl⟩
    exact .exit running rfl ((outcomes _).mpr rfl) halted unkilled

/-- A pending call whose only outcome is `unmodeled` (fail closed) steps to an
error, under every refusal filter. -/
theorem sstep_unmodeled_iff {core : Silmaril.X86.State} {memory : Memory} {n : Word} {model : Model}
    (running : model.halted = none)
    (outcomes : ∀ outcome, spec (P.sysInM core memory n) model outcome ↔ outcome = .unmodeled)
    (evs : List Event) (target : StepTo x86ExtNative) :
    SStep P.segs spec refused (cfgM core memory (some n) model) evs target ↔
      evs = [] ∧ target = .error := by
  constructor
  · intro step
    cases step with
    | instr _ p => cases p
    | instrFault _ p => cases p
    | instrUnmodeled _ p => cases p
    | syscall _ p s => cases p; cases (outcomes _).mp s
    | syscallMaterializationFault _ p s => cases p; cases (outcomes _).mp s
    | exit _ p s => cases p; cases (outcomes _).mp s
    | killed _ p s => cases p; cases (outcomes _).mp s
    | syscallUnmodeled _ p s => exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .syscallUnmodeled running rfl ((outcomes _).mpr rfl)

/-- The machine side of a call other than `arch_prctl` that returns `effect`. -/
theorem resume_effectH (core : Silmaril.X86.State) (memory : Memory) (n : Word) (other : n ≠ 158)
    (effect : SyscallEffect) :
    x86ExtNative.advancePastSvc (x86ExtNative.applyEffect ⟨⟨core, memory⟩, some n⟩ effect) =
      ⟨⟨resume core effect.ret, applyMemoryEffect memory effect⟩, none⟩ := by
  have notArch : ¬ (some n = some (158 : Word) ∧ core.read .rdi = 0x1002 ∧ effect.ret = 0) :=
    fun h => other (Option.some.inj h.1)
  change x86AdvancePastSvc (x86ApplyEffectNative ⟨⟨core, memory⟩, some n⟩ _) = _
  unfold x86ApplyEffectNative
  split
  · next h => exact absurd h notArch
  · rfl

theorem killedBy_none {model : Model} (running : model.halted = none) : model.killedBy = none := by
  simp only [Model.killedBy, Model.halted] at running ⊢
  simp [running]

/-- A pending call (not `arch_prctl`) whose outcomes all return to the program,
over any memory, possibly changing the model (without lazy reservations). -/
theorem sstep_retH_iff {core : Silmaril.X86.State} {memory : Memory} {n : Word} {model : Model}
    {α : Type} {allowed : α → Prop} {effect : α → SyscallEffect} {model' : α → Model}
    {events : α → List Event} (other : n ≠ 158) (running : model.halted = none)
    (running' : ∀ x, allowed x → (model' x).halted = none)
    (lazy' : ∀ x, allowed x → (model' x).vmLazy = [])
    (outcomes : ∀ outcome, spec (P.sysInM core memory n) model outcome ↔
      ∃ x, allowed x ∧ outcome = .ok (effect x) (model' x) (events x))
    (evs : List Event) (target : StepTo x86ExtNative) :
    SStep P.segs spec refused (cfgM core memory (some n) model) evs target ↔
      ∃ x, (allowed x ∧ ¬ refused (P.sysInM core memory n) model (effect x)) ∧ evs = events x ∧
        target = .next (cfgM (resume core (effect x).ret) (applyMemoryEffect memory (effect x)) none
          (model' x)) := by
  constructor
  · intro step
    cases step with
    | instr _ p => cases p
    | instrFault _ p => cases p
    | instrUnmodeled _ p => cases p
    | syscall _ p s notRefused _ m =>
      cases p
      obtain ⟨x, hx, same⟩ := (outcomes _).mp s
      cases same
      rw [Progress.materializeModelAccesses_noLazy _ _ (lazy' x hx)] at m
      cases m
      refine ⟨x, ⟨hx, notRefused⟩, rfl, ?_⟩
      rw [resume_effectH core memory n other]
    | syscallMaterializationFault _ p s _ _ m =>
      cases p
      obtain ⟨x, hx, same⟩ := (outcomes _).mp s
      cases same
      rw [Progress.materializeModelAccesses_noLazy _ _ (lazy' x hx)] at m
      cases m
    | exit _ p s h _ =>
      cases p
      obtain ⟨x, hx, same⟩ := (outcomes _).mp s
      cases same
      rw [running' x hx] at h
      cases h
    | killed _ p s k =>
      cases p
      obtain ⟨x, hx, same⟩ := (outcomes _).mp s
      cases same
      rw [killedBy_none (running' x hx)] at k
      cases k
    | syscallUnmodeled _ p s =>
      cases p
      obtain ⟨x, _, same⟩ := (outcomes _).mp s
      cases same
  · rintro ⟨x, ⟨hx, notRefused⟩, rfl, rfl⟩
    have step := SStep.syscall (segs := P.segs) (spec := spec) (refused := refused)
      (isa := x86ExtNative) (x8 := n)
      (ms := (⟨⟨core, memory⟩, some n⟩ : X86State)) running rfl ((outcomes _).mpr ⟨x, hx, rfl⟩)
      notRefused (running' x hx) (Progress.materializeModelAccesses_noLazy _ _ (lazy' x hx))
    rwa [resume_effectH core memory n other] at step

end Rules

/-! ## Native outcomes -/

section Outcomes

open NativeX86

/-- The thread-id choice of `set_tid_address_spec`: the pinned id, or at the first
observation any id in `(0, PID_MAX_ENVELOPE)`. -/
def TidChoice (model : Model) (tid : Word) : Prop :=
  match model.tid with
  | some pinned => tid = pinned
  | none => 0 < uns tid ∧ uns tid < PID_MAX_ENVELOPE

instance (model : Model) (tid : Word) : Decidable (TidChoice model tid) := by
  unfold TidChoice
  split <;> infer_instance

theorem withTid_pinned {model : Model} {tid : Word} (pinned : model.tid = some tid) :
    model.withTid tid = model := by
  rcases model with ⟨fd, vm, io, fsys, proc, lim, time, profile⟩
  simp only [Model.tid] at pinned
  simp only [Model.withTid, ← pinned]

/-- LPS `set_tid_address_spec` (shared by `getpid` and `gettid`). -/
theorem setTidAddress_iff (input : SyscallInput) (model : Model) (outcome : Outcome SyscallEffect) :
    setTidAddressSpec input model outcome ↔
      ∃ tid, TidChoice model tid ∧ outcome = .ok (mkEffect tid [] []) (model.withTid tid) [] := by
  cases tidOf : model.tid with
  | some pinned =>
    cases outcome with
    | ok effect model' evs =>
      simp [setTidAddressSpec, bind, Sys.bind, Sys.getModel, tidOf, retOnly, Sys.pure, TidChoice,
        withTid_pinned tidOf]
    | unmodeled =>
      simp [setTidAddressSpec, bind, Sys.bind, Sys.getModel, tidOf, retOnly, Sys.pure, TidChoice]
  | none =>
    cases outcome with
    | ok effect model' evs =>
      simp [setTidAddressSpec, bind, Sys.bind, Sys.getModel, tidOf, retOnly, Sys.pure, TidChoice,
        Sys.choose, Sys.modify]
      exact exists_congr fun _ =>
        ⟨fun ⟨⟨a, b⟩, c, d⟩ => ⟨a, d, c, b⟩, fun ⟨a, d, c, b⟩ => ⟨⟨a, b⟩, c, d⟩⟩
    | unmodeled =>
      simp [setTidAddressSpec, bind, Sys.bind, Sys.getModel, tidOf, retOnly, Sys.pure, TidChoice,
        Sys.choose, Sys.modify]

theorem dispatches_getpid : Dispatches 39 (fun _ => getpidSpec) :=
  dispatches_slot ⟨172, 39, "getpid"⟩ (by decide) rfl (by decide)

theorem dispatches_gettid : Dispatches 186 (fun _ => gettidSpec) :=
  dispatches_slot ⟨178, 186, "gettid"⟩ (by decide) rfl (by decide)

theorem dispatches_set_tid_address : Dispatches 218 (fun _ => setTidAddressSpec) :=
  dispatches_slot ⟨96, 218, "set_tid_address"⟩ (by decide) rfl (by decide)

theorem dispatches_getuid : Dispatches 102 (fun _ => getidSpec (·.uid)) :=
  dispatches_slot ⟨174, 102, "getuid"⟩ (by decide) rfl (by decide)

theorem dispatches_geteuid : Dispatches 107 (fun _ => getidSpec (·.euid)) :=
  dispatches_slot ⟨175, 107, "geteuid"⟩ (by decide) rfl (by decide)

theorem dispatches_getrandom :
    Dispatches 318 (fun i => getrandomSpecX86 (i.arg 0) (i.arg 1) (i.arg 2)) :=
  dispatches_slot ⟨278, 318, "getrandom"⟩ (by decide) rfl (by decide)

/-- `arch_prctl` (158) is an extension arm of the hub table. -/
theorem dispatches_arch_prctl :
    Dispatches 158 (fun i => archPrctlSpec (i.arg 0) (i.arg 1)) :=
  dispatches_extension (name := "arch_prctl") rfl (by decide)

/-- Native `getpid` (39), `gettid` (186) and `set_tid_address` (218) are all LPS
`set_tid_address_spec` (`Sys/Kernel/Sys.v:112,173`, `Sys/Kernel/Fork.v:123`), off the
hub's boundary guard. -/
theorem native_tid_iff (input : SyscallInput) (model : Model) (outcome : Outcome SyscallEffect)
    (number : input.sysno = 39 ∨ input.sysno = 186 ∨ input.sysno = 218)
    (clear : NativeX86.All.boundarySuspect input.sysno.toNat input = false) :
    spec input model outcome ↔
      ∃ tid, TidChoice model tid ∧ outcome = .ok (mkEffect tid [] []) (model.withTid tid) [] := by
  rcases number with number | number | number <;> rw [number] at clear
  · rw [dispatches_getpid.spec_iff (by rw [number]; rfl) clear model outcome]
    exact setTidAddress_iff _ model outcome
  · rw [dispatches_gettid.spec_iff (by rw [number]; rfl) clear model outcome]
    exact setTidAddress_iff _ model outcome
  · rw [dispatches_set_tid_address.spec_iff (by rw [number]; rfl) clear model outcome]
    exact setTidAddress_iff _ model outcome

theorem getid_iff (sel : Creds → Word) (input : SyscallInput) (model : Model)
    (outcome : Outcome SyscallEffect) :
    getidSpec sel input model outcome ↔ outcome = .ok (mkEffect (sel model.creds) [] []) model [] := by
  cases outcome with
  | ok effect model' evs =>
    simp [getidSpec, bind, Sys.bind, Sys.getModel, retOnly, Sys.pure]
    tauto
  | unmodeled => simp [getidSpec, bind, Sys.bind, Sys.getModel, retOnly, Sys.pure]

/-- Native `getuid` (102): the real user id of the credentials, which the launch
sets from `ProcInput.uid` (LPS `getid_spec`, `Sys/Kernel/Sys.v:730`). -/
theorem native_getuid_iff (input : SyscallInput) (model : Model) (outcome : Outcome SyscallEffect)
    (number : input.sysno = 102) (clear : NativeX86.All.boundarySuspect 102 input = false) :
    spec input model outcome ↔
      outcome = .ok (mkEffect model.creds.uid [] []) model [] := by
  rw [dispatches_getuid.spec_iff (by rw [number]; rfl) clear model outcome]
  exact getid_iff _ _ model outcome

/-- Native `geteuid` (107). -/
theorem native_geteuid_iff (input : SyscallInput) (model : Model) (outcome : Outcome SyscallEffect)
    (number : input.sysno = 107) (clear : NativeX86.All.boundarySuspect 107 input = false) :
    spec input model outcome ↔
      outcome = .ok (mkEffect model.creds.euid [] []) model [] := by
  rw [dispatches_geteuid.spec_iff (by rw [number]; rfl) clear model outcome]
  exact getid_iff _ _ model outcome

/-- Native `getrandom` (318): the family's x86-64 `getrandom`. -/
theorem native_getrandom (input : SyscallInput) (model : Model) (outcome : Outcome SyscallEffect)
    (number : input.sysno = 318) (clear : NativeX86.All.boundarySuspect 318 input = false) :
    spec input model outcome ↔
      getrandomSpecX86 (input.arg 0) (input.arg 1) (input.arg 2) input model outcome :=
  dispatches_getrandom.spec_iff (by rw [number]; rfl) clear model outcome

/-- LPS `getrandom_spec` with x86-64 `access_ok`, a small request
(`Sys/Drivers/Char/Random.v:90`): exactly `count` environment-chosen bytes are
delivered, and nothing else can happen. -/
theorem getrandom_small_iff (input : SyscallInput) (model : Model) (outcome : Outcome SyscallEffect)
    {buf count flags : Word} (flagsOk : uns flags = 0)
    (modeled : modeledRwCount count = true)
    (writable : (readBytesMap input.wmem buf count).isSome = true)
    (nonzero : wIs0 count = false) (small : uns count ≤ getrandomSmallMax) :
    getrandomSpecX86 buf count flags input model outcome ↔
      ∃ bs : List Byte, (bs.length : Int) = uns count ∧
        outcome = .ok (mkEffect (lenWord bs) [(buf, bs)] []) model [] := by
  obtain ⟨present, read⟩ := Option.isSome_iff_exists.mp writable
  cases outcome with
  | ok effect model' evs =>
    simp [getrandomSpecX86, flagsOk, modeled, bind, Sys.bind, Sys.input, read, nonzero, small,
      Sys.choose, Sys.pure]
    exact exists_congr fun _ => by tauto
  | unmodeled =>
    simp [getrandomSpecX86, flagsOk, modeled, bind, Sys.bind, Sys.input, read, nonzero, small,
      Sys.choose, Sys.pure]

/-- LPS `getrandom_spec` with a flag other than 0 and `GRND_NONBLOCK`: unmodeled
(fail closed), before any other check. Linux returns `-EINVAL`. -/
theorem getrandom_badflags_iff (input : SyscallInput) (model : Model) (outcome : Outcome SyscallEffect)
    {buf count flags : Word} (bad : uns flags ≠ 0 ∧ uns flags ≠ GRND_NONBLOCK) :
    getrandomSpecX86 buf count flags input model outcome ↔ outcome = .unmodeled := by
  simp [getrandomSpecX86, bad.1, bad.2, Sys.unmodeled]

/-- A native number outside the table (here 999) is `unmodeled` (fail closed);
Linux returns `-ENOSYS`. -/
theorem native_unknown_iff (input : SyscallInput) (model : Model) (outcome : Outcome SyscallEffect)
    (number : input.sysno = 999) :
    spec input model outcome ↔ outcome = .unmodeled := by
  have none : lookupArm table 999 = none :=
    NativeX86.All.lookupArm_none_of_not_mem _ _ (by decide +kernel)
  simp only [spec, dispatch, number]
  rw [show (999 : Word).toNat = 999 from rfl, none]
  rfl

/-- Native `exit_group` (231) is LPS `exit_spec`, exactly as `exit` (60) is: a
single-threaded process cannot tell them apart. -/
theorem native_exit_group_iff (input : SyscallInput) (model : Model) (outcome : Outcome SyscallEffect)
    (number : input.sysno = 231) (clear : NativeX86.All.boundarySuspect 231 input = false) :
    spec input model outcome ↔
      outcome = .ok (mkEffect 0 [] []) (model.withHalted (input.arg 0 &&& 255)) [] := by
  rw [dispatches_exit_group.spec_iff (by rw [number]; rfl) clear model outcome]
  cases outcome with
  | ok effect model' evs =>
    simp only [exitSpec, bind, Sys.bind, Sys.modify, retOnly, Sys.pure, Outcome.ok.injEq]
    constructor
    · rintro ⟨_, _, _, _, ⟨_, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl⟩
      exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨rfl, rfl, rfl⟩
      exact ⟨(), _, [], [], ⟨trivial, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl⟩
  | unmodeled =>
    simp only [exitSpec, bind, Sys.bind, Sys.modify, retOnly, Sys.pure, reduceCtorEq, false_or,
      and_false, exists_false]

/-- `exit` and `exit_group` read no pointer, so the hub's boundary guard treats them alike. -/
theorem boundarySuspect_exit_group (input : SyscallInput) :
    NativeX86.All.boundarySuspect 231 input = NativeX86.All.boundarySuspect 60 input := by
  have c231 : NativeX86.All.constPtrArgs 231 = [] := by decide +kernel
  have c60 : NativeX86.All.constPtrArgs 60 = [] := by decide +kernel
  simp only [NativeX86.All.boundarySuspect, c231, c60]

theorem native_exit_group_iff_exit (input : SyscallInput) (model : Model)
    (outcome : Outcome SyscallEffect) :
    spec { input with sysno := 231 } model outcome ↔
      spec { input with sysno := 60 } model outcome := by
  have same : NativeX86.All.boundarySuspect 231 { input with sysno := 231 } =
      NativeX86.All.boundarySuspect 60 { input with sysno := 60 } :=
    boundarySuspect_exit_group _
  cases suspect : NativeX86.All.boundarySuspect 60 { input with sysno := 60 } with
  | true =>
    rw [dispatches_exit_group.suspect_iff rfl (same.trans suspect) model outcome,
      dispatches_exit.suspect_iff rfl suspect model outcome]
  | false =>
    rw [native_exit_group_iff _ model outcome rfl (same.trans suspect),
      native_exit_iff _ model outcome rfl suspect]
    rfl

end Outcomes

/-! ## `arch_prctl(ARCH_SET_FS)` -/

section ArchPrctl

variable {P} {refused : RefusalFilter}

/-- The core after a successful `ARCH_SET_FS`: RAX is 0, the FS base is RSI. -/
def resumeFs (core : Silmaril.X86.State) : Silmaril.X86.State :=
  { resume core 0 with fsBase := core.read .rsi }

theorem setFs_effect (core : Silmaril.X86.State) (memory : Memory) (rdi : core.read .rdi = 0x1002) :
    x86ExtNative.advancePastSvc (x86ExtNative.applyEffect ⟨⟨core, memory⟩, some 158⟩ (mkEffect 0 [] [])) =
      ⟨⟨resumeFs core, memory⟩, none⟩ := by
  have setting : (some (158 : Word) = some 158 ∧ core.read .rdi = 0x1002 ∧ (mkEffect 0 [] []).ret = 0) :=
    ⟨rfl, rdi, rfl⟩
  change x86AdvancePastSvc (x86ApplyEffectNative ⟨⟨core, memory⟩, some 158⟩ _) = _
  unfold x86ApplyEffectNative
  split
  · rfl
  · next h => exact absurd setting h

theorem setFs_outcomes {core : Silmaril.X86.State} {memory : Memory} {model : Model}
    (rdi : core.read .rdi = 0x1002) (valid : uns (core.read .rsi) < x86AddressSpace.taskSize)
    (clear : NativeX86.All.boundarySuspect 158 (P.sysInM core memory 158) = false)
    (outcome : Outcome SyscallEffect) :
    spec (P.sysInM core memory 158) model outcome ↔ outcome = .ok (mkEffect 0 [] []) model [] := by
  rw [dispatches_arch_prctl.spec_iff rfl clear model outcome]
  change NativeX86.archPrctlSpec (core.read .rdi) (core.read .rsi) _ model outcome ↔ _
  rw [rdi]
  exact NativeX86.archPrctl_success _ _ model outcome valid

/-- `arch_prctl(ARCH_SET_FS, base)` below `TASK_SIZE` returns 0 and sets the FS base. -/
theorem sstep_setFs_iff {core : Silmaril.X86.State} {memory : Memory} {model : Model}
    (running : model.halted = none) (lazy : model.vmLazy = []) (rdi : core.read .rdi = 0x1002)
    (valid : uns (core.read .rsi) < x86AddressSpace.taskSize)
    (clear : NativeX86.All.boundarySuspect 158 (P.sysInM core memory 158) = false)
    (evs : List Event) (target : StepTo x86ExtNative) :
    SStep P.segs spec refused (cfgM core memory (some 158) model) evs target ↔
      ¬ refused (P.sysInM core memory 158) model (mkEffect 0 [] []) ∧ evs = [] ∧
        target = .next (cfgM (resumeFs core) memory none model) := by
  have outcomes := setFs_outcomes (P := P) (memory := memory) (model := model) rdi valid clear
  constructor
  · intro step
    cases step with
    | instr _ p => cases p
    | instrFault _ p => cases p
    | instrUnmodeled _ p => cases p
    | syscall _ p s notRefused _ m =>
      cases p
      cases (outcomes _).mp s
      rw [Progress.materializeModelAccesses_noLazy _ _ lazy] at m
      cases m
      refine ⟨notRefused, rfl, ?_⟩
      rw [setFs_effect core memory rdi]
    | syscallMaterializationFault _ p s _ _ m =>
      cases p
      cases (outcomes _).mp s
      rw [Progress.materializeModelAccesses_noLazy _ _ lazy] at m
      cases m
    | exit _ p s h _ =>
      cases p
      cases (outcomes _).mp s
      rw [running] at h
      cases h
    | killed _ p s k =>
      cases p
      cases (outcomes _).mp s
      rw [killedBy_none running] at k
      cases k
    | syscallUnmodeled _ p s =>
      cases p
      cases (outcomes _).mp s
  · rintro ⟨notRefused, rfl, rfl⟩
    have step := SStep.syscall (segs := P.segs) (spec := spec) (refused := refused)
      (isa := x86ExtNative) (x8 := 158)
      (ms := (⟨⟨core, memory⟩, some 158⟩ : X86State)) running rfl ((outcomes _).mpr rfl)
      notRefused running (Progress.materializeModelAccesses_noLazy _ _ lazy)
    rwa [setFs_effect core memory rdi] at step

/-- `arch_prctl` with an operation other than `ARCH_SET_FS` (`ARCH_GET_FS` is
0x1003) is unmodeled: the native adapter does not model it. -/
theorem archOther_outcomes {core : Silmaril.X86.State} {memory : Memory} {model : Model}
    (other : core.read .rdi ≠ 0x1002) (outcome : Outcome SyscallEffect) :
    spec (P.sysInM core memory 158) model outcome ↔ outcome = .unmodeled := by
  rw [dispatches_arch_prctl _ rfl model outcome]
  split
  · exact Iff.rfl
  · exact NativeX86.archPrctl_unsupported _ _ _ model outcome other

end ArchPrctl

/-! ## Execution and run rules -/

section Exec

variable {P} {refused : RefusalFilter}

theorem returnedM {core : Silmaril.X86.State} {memory : Memory} {model : Model} (ret : Word)
    (running : model.halted = none) :
    returned (cfgM (resume core ret) memory none model) = some ret := by
  simp [returned, running, resume]

theorem exec_instrH {checked : Checked P} {post : Omni.Post x86ExtNative} {memory : Memory}
    (holds : P.Holds memory) {off len : Nat}
    {instruction : Silmaril.X86.Ext.Instr} {core core' : Silmaril.X86.State} {model : Model}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (fits : off + len ≤ P.size) (two : off + 2 ≤ P.size)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core memory len = .ok core' memory)
    (rest : Omni.Exec P.segs spec refused (cfgM core' memory none model) post) :
    Omni.Exec P.segs spec refused (cfgM core memory none model) post :=
  Omni.exec_of_unique running (sstep_instr_iffH holds running lazy rip fits two notSyscall decoded exec) rest

theorem run_instrH {checked : Checked P} {memory : Memory} (holds : P.Holds memory) {off len : Nat}
    {instruction : Silmaril.X86.Ext.Instr}
    {core core' : Silmaril.X86.State} {model : Model} {calls : List Call} {trace : List Event}
    {outcome : Omni.Outcome x86ExtNative}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (fits : off + len ≤ P.size) (two : off + 2 ≤ P.size)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core memory len = .ok core' memory)
    (rest : Run P.segs spec refused (cfgM core' memory none model) calls trace outcome) :
    Run P.segs spec refused (cfgM core memory none model) calls trace outcome :=
  .instr rfl ((sstep_instr_iffH holds running lazy rip fits two notSyscall decoded exec _ _).mpr
    ⟨rfl, rfl⟩) rest

theorem exec_trapH {checked : Checked P} {post : Omni.Post x86ExtNative} {memory : Memory}
    (holds : P.Holds memory) {off : Nat} {core : Silmaril.X86.State} {model : Model}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (two : off + 2 ≤ P.size)
    (isSyscall : (P.bytes.drop off).take 2 = [0x0f, 0x05])
    (defined : (rflagsImage core.flags).isSome = true)
    (rest : Omni.Exec P.segs spec refused (cfgM core memory (some (core.read .rax)) model) post) :
    Omni.Exec P.segs spec refused (cfgM core memory none model) post :=
  Omni.exec_of_unique running (sstep_trap_iffH holds running lazy rip two isSyscall defined) rest

theorem run_trapH {checked : Checked P} {memory : Memory} (holds : P.Holds memory) {off : Nat}
    {core : Silmaril.X86.State} {model : Model}
    {calls : List Call} {trace : List Event} {outcome : Omni.Outcome x86ExtNative}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (two : off + 2 ≤ P.size)
    (isSyscall : (P.bytes.drop off).take 2 = [0x0f, 0x05])
    (defined : (rflagsImage core.flags).isSome = true)
    (rest : Run P.segs spec refused (cfgM core memory (some (core.read .rax)) model) calls trace outcome) :
    Run P.segs spec refused (cfgM core memory none model) calls trace outcome :=
  .instr rfl ((sstep_trap_iffH holds running lazy rip two isSyscall defined _ _).mpr ⟨rfl, rfl⟩) rest

theorem exit_outcomes {core : Silmaril.X86.State} {memory : Memory} {n : Word} {model : Model}
    (number : n = 60 ∨ n = 231)
    (clear : NativeX86.All.boundarySuspect 60 (P.sysInM core memory n) = false)
    (outcome : Outcome SyscallEffect) :
    spec (P.sysInM core memory n) model outcome ↔
      outcome = .ok (mkEffect 0 [] []) (model.withHalted (core.read .rdi &&& 255)) [] := by
  rcases number with rfl | rfl
  · exact native_exit_iff _ model outcome rfl clear
  · exact native_exit_group_iff _ model outcome rfl ((boundarySuspect_exit_group _).trans clear)

/-- `exit` (60) or `exit_group` (231) halts with the low byte of RDI, over any memory. -/
theorem exec_exitH {post : Omni.Post x86ExtNative} {core : Silmaril.X86.State} {memory : Memory}
    {n status : Word} {model : Model} (number : n = 60 ∨ n = 231) (rdi : core.read .rdi = status)
    (running : model.halted = none)
    (clear : NativeX86.All.boundarySuspect 60 (P.sysInM core memory n) = false)
    (done : post [.exitEv (status &&& 255) model.fs]
      (.halt (cfgM core memory (some n) (model.withHalted (status &&& 255))))) :
    Omni.Exec P.segs spec refused (cfgM core memory (some n) model) post := by
  subst rdi
  refine Omni.exec_of_unique running
    (sstep_halt_iffH running (exit_outcomes number clear) rfl (by simp [Model.killedBy, Model.withHalted]))
    (.halt (by simp [Model.withHalted, Model.halted]) ?_)
  rw [List.append_nil]
  exact done

theorem run_exitH {core : Silmaril.X86.State} {memory : Memory} {n status : Word} {model : Model}
    (number : n = 60 ∨ n = 231) (rdi : core.read .rdi = status) (running : model.halted = none)
    (clear : NativeX86.All.boundarySuspect 60 (P.sysInM core memory n) = false) :
    Run P.segs spec refused (cfgM core memory (some n) model)
      [⟨n, x86ExtNative.syscallArgs (⟨⟨core, memory⟩, some n⟩ : X86State), none⟩]
      [.exitEv (status &&& 255) model.fs]
      (.halt (cfgM core memory (some n) (model.withHalted (status &&& 255)))) := by
  subst rdi
  exact .sys rfl ((sstep_halt_iffH running (exit_outcomes number clear) rfl
    (by simp [Model.killedBy, Model.withHalted]) _ _).mpr ⟨rfl, rfl⟩)
    (.halt (by simp [Model.withHalted, Model.halted]))

/-- A call with a single outcome, in the shape of `exec_retH` and `run_retH`. -/
theorem outcomes_unique {input : SyscallInput} {model model' : Model} {effect : SyscallEffect}
    {events : List Event}
    (outcomes : ∀ outcome, spec input model outcome ↔ outcome = .ok effect model' events) :
    ∀ outcome, spec input model outcome ↔
      ∃ x : Unit, True ∧ outcome = .ok ((fun _ => effect) x) ((fun _ => model') x) ((fun _ => events) x) :=
  fun outcome => (outcomes outcome).trans ⟨fun h => ⟨(), trivial, h⟩, fun ⟨_, _, h⟩ => h⟩

/-- A call that returns to the program (not `arch_prctl`): every allowed outcome continues. -/
theorem exec_retH {post : Omni.Post x86ExtNative} {core : Silmaril.X86.State} {memory : Memory}
    {n : Word} {model : Model} {α : Type} {allowed : α → Prop} {effect : α → SyscallEffect}
    {model' : α → Model} {events : α → List Event} (other : n ≠ 158) (running : model.halted = none)
    (running' : ∀ x, allowed x → (model' x).halted = none)
    (lazy' : ∀ x, allowed x → (model' x).vmLazy = [])
    (outcomes : ∀ outcome, spec (P.sysInM core memory n) model outcome ↔
      ∃ x, allowed x ∧ outcome = .ok (effect x) (model' x) (events x))
    (inhabited : ∃ x, allowed x)
    (rest : ∀ x, allowed x →
      Omni.Exec P.segs spec noFilter
        (cfgM (resume core (effect x).ret) (applyMemoryEffect memory (effect x)) none (model' x))
        (fun trace outcome => post (events x ++ trace) outcome)) :
    Omni.Exec P.segs spec noFilter (cfgM core memory (some n) model) post :=
  Omni.exec_of_successors running (sstep_retH_iff other running running' lazy' outcomes)
    (inhabited.elim fun x hx => ⟨x, hx, fun h => h⟩) (fun x hx => rest x hx.1)

theorem run_retH {core : Silmaril.X86.State} {memory : Memory}
    {n : Word} {model : Model} {α : Type} {allowed : α → Prop} {effect : α → SyscallEffect}
    {model' : α → Model} {events : α → List Event} {calls : List Call} {trace : List Event}
    {outcome : Omni.Outcome x86ExtNative} (other : n ≠ 158) (running : model.halted = none)
    (running' : ∀ x, allowed x → (model' x).halted = none)
    (lazy' : ∀ x, allowed x → (model' x).vmLazy = [])
    (outcomes : ∀ outcome, spec (P.sysInM core memory n) model outcome ↔
      ∃ x, allowed x ∧ outcome = .ok (effect x) (model' x) (events x))
    (x : α) (chosen : allowed x) (accepted : ¬ refused (P.sysInM core memory n) model (effect x))
    (rest : Run P.segs spec refused
      (cfgM (resume core (effect x).ret) (applyMemoryEffect memory (effect x)) none (model' x))
      calls trace outcome) :
    Run P.segs spec refused (cfgM core memory (some n) model)
      (⟨n, x86ExtNative.syscallArgs (⟨⟨core, memory⟩, some n⟩ : X86State), some (effect x).ret⟩ :: calls)
      (events x ++ trace) outcome :=
  returnedM (memory := applyMemoryEffect memory (effect x)) (core := core) (effect x).ret
      (running' x chosen) ▸
    .sys rfl ((sstep_retH_iff other running running' lazy' outcomes _ _).mpr
      ⟨x, ⟨chosen, accepted⟩, rfl, rfl⟩) rest

theorem exec_setFs {post : Omni.Post x86ExtNative} {core : Silmaril.X86.State} {memory : Memory}
    {model : Model} (running : model.halted = none) (lazy : model.vmLazy = [])
    (rdi : core.read .rdi = 0x1002) (valid : uns (core.read .rsi) < x86AddressSpace.taskSize)
    (clear : NativeX86.All.boundarySuspect 158 (P.sysInM core memory 158) = false)
    (rest : Omni.Exec P.segs spec noFilter (cfgM (resumeFs core) memory none model) post) :
    Omni.Exec P.segs spec noFilter (cfgM core memory (some 158) model) post :=
  Omni.exec_of_unique running (fun evs target => by
    rw [sstep_setFs_iff running lazy rdi valid clear]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨fun impossible => impossible, h⟩⟩)
    (by simpa only [List.nil_append] using rest)

theorem run_setFs {core : Silmaril.X86.State} {memory : Memory} {model : Model}
    {calls : List Call} {trace : List Event} {outcome : Omni.Outcome x86ExtNative}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rdi : core.read .rdi = 0x1002) (valid : uns (core.read .rsi) < x86AddressSpace.taskSize)
    (clear : NativeX86.All.boundarySuspect 158 (P.sysInM core memory 158) = false)
    (accepted : ¬ refused (P.sysInM core memory 158) model (mkEffect 0 [] []))
    (rest : Run P.segs spec refused (cfgM (resumeFs core) memory none model) calls trace outcome) :
    Run P.segs spec refused (cfgM core memory (some 158) model)
      (⟨158, x86ExtNative.syscallArgs (⟨⟨core, memory⟩, some 158⟩ : X86State), some 0⟩ :: calls)
      trace outcome := by
  have returnsZero : returned (cfgM (resumeFs core) memory none model) = some 0 := by
    simp [returned, running, resumeFs, resume]
  have step := Run.sys (segs := P.segs) (spec := spec) (refused := refused) (n := 158) rfl
    ((sstep_setFs_iff running lazy rdi valid clear _ _).mpr ⟨accepted, rfl, rfl⟩) rest
  rw [returnsZero] at step
  simpa only [List.nil_append] using step

/-- A fail-closed call ends every execution in an error, under every filter. -/
theorem exec_unmodeled {post : Omni.Post x86ExtNative} {core : Silmaril.X86.State} {memory : Memory}
    {n : Word} {model : Model} (running : model.halted = none)
    (outcomes : ∀ outcome, spec (P.sysInM core memory n) model outcome ↔ outcome = .unmodeled)
    (done : post [] (.error (cfgM core memory (some n) model))) :
    Omni.Exec P.segs spec refused (cfgM core memory (some n) model) post := by
  have successors := sstep_unmodeled_iff (P := P) (refused := refused) running outcomes
  refine .step running ⟨[], .error, (successors _ _).mpr ⟨rfl, rfl⟩⟩ ?_ ?_
  · intro evs step
    obtain ⟨rfl, _⟩ := (successors _ _).mp step
    exact done
  · intro evs c' step
    cases ((successors _ _).mp step).2

end Exec

/-! ## FS-relative loads from the image -/

/-- `mov %fs:0, dst` with the FS base at segment offset `off` loads the eight
image bytes there, little-endian, from the initialized memory. -/
theorem exec_loadFs [Checked P] (core : Silmaril.X86.State) (dst : Silmaril.X86.Reg) (len off : Nat)
    (base : core.fsBase = BitVec.ofNat 64 (P.base + off)) (start : off < P.size)
    (fits : off + 8 ≤ P.size) :
    Silmaril.X86.Ext.exec (.load .q dst (Silmaril.X86.Ext.Mem.fsAt 0)) core P.mem0 len =
      .ok { Silmaril.X86.Ext.Sz.write .q core dst
          ((BitVec.ofNat 64 (Silmaril.X86.Ext.leValue ((P.bytes.drop off).take 8))).setWidth 64) with
        rip := core.rip + BitVec.ofNat 64 len } P.mem0 := by
  have window := P.mem0_window .read (by decide) off 8 start fits
  have fitsWord := P.size_lt (Checked.layout (P := P))
  have address : (core.fsBase + (0 : BitVec 32).signExtend 64).toNat = P.base + off := by
    have zero : (0 : BitVec 32).signExtend 64 = 0 := by decide
    rw [base, zero, BitVec.toNat_add, BitVec.toNat_ofNat]
    have zeroNat : (0 : Word).toNat = 0 := rfl
    rw [zeroNat, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
  simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.loadN,
    Silmaril.X86.Ext.Mem.addr_fsAt, address, Memory.readBytes]
  rw [show Silmaril.X86.Ext.Sz.q.bytes = 8 from rfl, window]
  rfl

/-! ## Fail-closed executions -/

section Stops

variable {refused : RefusalFilter}

/-- The postcondition of a probe that stops at a fail-closed call: no event, and
the execution ends in an error at a configuration where call `n` is pending and
unmodeled (LPS `unmodeled_at`). -/
def StopsUnmodeled (n : Word) : Omni.Post x86ExtNative := fun trace outcome =>
  trace = [] ∧ ∃ c, outcome = .error c ∧ c.ms.pending = some n ∧ UnmodeledAt P.segs spec c

variable {P}

theorem exec_stops {core : Silmaril.X86.State} {memory : Memory} {n : Word} {model : Model}
    (running : model.halted = none)
    (outcomes : ∀ outcome, spec (P.sysInM core memory n) model outcome ↔ outcome = .unmodeled) :
    Omni.Exec P.segs spec refused (cfgM core memory (some n) model) (P.StopsUnmodeled n) :=
  exec_unmodeled running outcomes ⟨rfl, _, rfl, rfl, running, .inr ⟨n, rfl, (outcomes _).mpr rfl⟩⟩

/-- Such a probe reaches an unmodeled configuration: its behaviour is `unmodeled`. -/
theorem unmodeled_of_stops {n : Word}
    (run : Omni.Exec P.segs spec refused P.initial (P.StopsUnmodeled n)) :
    (P.behavior refused).unmodeled := by
  obtain ⟨_, _, finite, _, c, rfl, _, at_⟩ := run.realizes
  obtain ⟨before, _, _, path, _⟩ := Omni.finiteExec_error_star finite
  exact ⟨before, c, path, at_⟩

/-- No execution of a probe proved to stop halts, so no Linux observation (which
always ends in an exit or a kill) is admitted. -/
theorem not_admits_of_stops {n : Word} {o : Observed}
    (run : Omni.Exec P.segs spec refused P.initial (P.StopsUnmodeled n)) : ¬ P.Admits refused o := by
  rintro ⟨_, _, _, admitted, _⟩
  obtain ⟨_, _, impossible, _⟩ := run.sound admitted.finite
  cases impossible

/-- A probe that admits a halting run is not one that stops at a fail-closed call. -/
theorem not_stops_of_admits {n : Word} {o : Observed} (admits : P.Admits refused o) :
    ¬ Omni.Exec P.segs spec refused P.initial (P.StopsUnmodeled n) :=
  fun run => not_admits_of_stops run admits

end Stops

/-! ## Buffers on the entry stack -/

section Stack

variable {P}

theorem mem0_stack_getH [checked : Checked P] (index : Nat) (bound : index < P.stack.length) :
    P.mem0.bytes.get? (P.entry.sp.toNat + index) = some P.stack[index] := by
  simp only [mem0, initialMemory]
  exact installWrapping_get _ _ _ index bound checked.layout.stackFits

/-- The writable view of the entry block at `sp + off`: the launch's stack bytes. -/
theorem readBytesAux_stack [checked : Checked P] (off count : Nat) (fits : off + count ≤ P.stack.length)
    (writable : ∀ k < count, P.mem0.permits .write (P.entry.sp.toNat + off + k) = true) :
    readBytesAux (viewByte P.mem0 .write) (BitVec.ofNat 64 (P.entry.sp.toNat + off)) count =
      some ((P.stack.drop off).take count) := by
  have stackFits := checked.layout.stackFits
  induction count generalizing off with
  | zero => simp [readBytesAux]
  | succ count ih =>
    have bound : off < P.stack.length := by omega
    have toNat : (BitVec.ofNat 64 (P.entry.sp.toNat + off)).toNat = P.entry.sp.toNat + off := by
      simp only [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have here : viewByte P.mem0 .write (BitVec.ofNat 64 (P.entry.sp.toNat + off)) = some P.stack[off] := by
      unfold viewByte
      have w := writable 0 (by omega)
      rw [Nat.add_zero] at w
      rw [toNat, w]
      simp only [ite_true]
      rw [← Std.ExtHashMap.get?_eq_getElem?, P.mem0_stack_getH off bound]
    have next : BitVec.ofNat 64 (P.entry.sp.toNat + off) + 1 =
        BitVec.ofNat 64 (P.entry.sp.toNat + (off + 1)) := by
      rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    have rest := ih (off + 1) (by omega) (fun k bound' => by
      have shifted := writable (k + 1) (by omega)
      rwa [show P.entry.sp.toNat + off + (k + 1) = P.entry.sp.toNat + (off + 1) + k by omega] at shifted)
    simp only [readBytesAux, here, next, rest, Option.map_some]
    rw [List.drop_eq_getElem_cons bound]
    rfl

/-- A small `getrandom(sp, count, 0)` into the entry stack: exactly `count`
environment-chosen bytes are delivered at `sp`, and nothing else can happen
(LPS `getrandom_spec` with x86-64 `access_ok`, the small-request arm,
`Sys/Drivers/Char/Random.v:90`). -/
theorem getrandom_stack_outcomes [checked : Checked P] {core : Silmaril.X86.State} {model : Model}
    {n : Word} {count : Nat} (number : n = 318) (buf : core.read .rdi = P.entry.sp)
    (length : core.read .rsi = BitVec.ofNat 64 count)
    (flags : core.read .rdx = 0) (positive : 0 < count) (small : count ≤ 256)
    (fits : count ≤ P.stack.length)
    (writable : ∀ k < count, P.mem0.permits .write (P.entry.sp.toNat + k) = true)
    (clear : NativeX86.All.boundarySuspect 318 (P.sysIn core n) = false)
    (outcome : Outcome SyscallEffect) :
    spec (P.sysIn core n) model outcome ↔
      ∃ bs : List Byte, bs.length = count ∧
        outcome = .ok (mkEffect (lenWord bs) [(P.entry.sp, bs)] []) model [] := by
  subst number
  have toNat : (BitVec.ofNat 64 count).toNat = count := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have read := readBytesAux_stack (P := P) 0 count (by omega) (fun k bound => by
    simpa only [Nat.add_zero] using writable k bound)
  rw [show BitVec.ofNat 64 (P.entry.sp.toNat + 0) = P.entry.sp by simp] at read
  rw [native_getrandom _ model outcome rfl clear]
  change getrandomSpecX86 (core.read .rdi) (core.read .rsi) (core.read .rdx) _ model outcome ↔ _
  rw [buf, length, flags]
  rw [getrandom_small_iff _ model outcome rfl
    (by simp [modeledRwCount, uns, toNat, rwBytesMax]; omega)
    (by
      change (readBytesAux (viewByte P.mem0 .write) P.entry.sp (BitVec.ofNat 64 count).toNat).isSome = true
      rw [toNat, read]
      rfl)
    (by simp [wIs0]; intro zero; have := congrArg BitVec.toNat zero; simp [toNat] at this; omega)
    (by simp only [uns, toNat, getrandomSmallMax]; omega)]
  simp only [uns, toNat, Nat.cast_inj]

/-- `applyMemoryEffect` of a single write. -/
theorem applyMemoryEffect_write (memory : Memory) (ret address : Word) (bytes : List Byte) :
    applyMemoryEffect memory (mkEffect ret [(address, bytes)] []) =
      { memory with bytes := installWrapping memory.bytes address.toNat bytes } := rfl

end Stack

end Probe

end Silmaril.Process.LPS.Probes
