module

public import Silmaril.Process.LPS.Probes.Kit
public import Silmaril.Process.LPS.Machines.X86FlagChoices

/-! # The probe kit on every launch and every flag oracle (VERIFIED)

`Probes.Kit` proves facts about one launch of a probe (`Probe.entry`, `Probe.input`, the
harness's `./probe` with an empty environment) on the deterministic adapter `x86ExtNative`.
Compiled code needs two generalizations:

* **Flag oracle.** `x86ExtNative` declines a `syscall` whose RFLAGS image has an undefined
  flag. GCC zeroes registers with `xor %r32,%r32`, which leaves AF undefined, so the GCC
  build of `true` (`mov $60,%eax; xor %edi,%edi; syscall`) is unmodelled at its only system
  call under `x86ExtNative`. Like the `sha256` end-to-end proof
  (`Problems.Sha256Cli.Statement`), this file runs probes on
  `Machines.x86WithFlagOracle oracle`, where the undefined flags at a `syscall` are chosen by
  an oracle; statements quantify over every oracle.
* **Every launch.** `Probe.launchAt P en inp` is the probe launched with any entry and
  input. `Probe.checkedAt` derives the kit's `Checked` instance from the entry-independent
  layout (`Probe.Static`, which follows from the harness `Layout`) and the launch's own
  validity (`ValidInput`, `ValidEntry`).

The transition rules (`Probe.oexec_instr`, `oexec_trap`, `oexec_exit`, `oexec_write`) and the
run rules (`orun_*`, building a `Star`) mirror the kit's, and the tactics `oprobe_instr`,
`oprobe_trap`, `oprobe_exit`, `oprobe_write` apply them. The trap rule completes the flags
with `oracle counter` and advances the counter (`X86FlagChoices.step_syscall`).

No `sorry`, no new axiom.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines
open Silmaril.Process.LPS.Machines.X86Launch
open Silmaril.Process (Memory Access Region Permissions)

namespace Probe

variable (P : Probe)

/-! ## Every launch -/

/-- The probe launched with entry `en` and input `inp`. -/
def launchAt (en : ExecEntry) (inp : ProcInput) : Probe := { P with entry := en, input := inp }

@[simp] theorem launchAt_snapshot (en : ExecEntry) (inp : ProcInput) :
    (P.launchAt en inp).snapshot = P.snapshot := rfl

@[simp] theorem launchAt_size (en : ExecEntry) (inp : ProcInput) :
    (P.launchAt en inp).size = P.size := rfl

@[simp] theorem launchAt_base (en : ExecEntry) (inp : ProcInput) :
    (P.launchAt en inp).base = P.base := rfl

@[simp] theorem launchAt_bytes (en : ExecEntry) (inp : ProcInput) :
    (P.launchAt en inp).bytes = P.bytes := rfl

/-- The entry-independent part of `Layout`. -/
structure Static : Prop where
  parsedHeader : Silmaril.Formats.ELF.readHeader P.fileBytes.toArray = some P.header
  parsedProgram :
    Silmaril.Formats.ELF.readProgramHeaders P.fileBytes.toArray P.header = some [P.programHeader]
  headerMatches : HeaderMatches P.snapshot
  load : P.programHeader.kind = 1
  offsetZero : P.programHeader.offset = 0
  readExecute : P.programHeader.flags = 5 ∨ P.programHeader.flags = 7
  fileBacked : P.programHeader.fileSize = P.programHeader.memorySize
  sizes : P.bytes.length = P.size
  positive : 0 < P.size
  taskBound : (P.base : Int) + P.size ≤ x86AddressSpace.taskSize
  entryInside : P.base ≤ P.header.entry
  entryBelow : P.entryOffset < P.size
  entryDecodes : P.decodesAt P.entryOffset = true
  programHeadersRead :
    (P.imageRead (zw P.image.phdrs.addr) (P.image.phdrs.num * P.image.phdrs.ent)).isSome = true

theorem Layout.static {P : Probe} (layout : P.Layout) : P.Static :=
  ⟨layout.parsedHeader, layout.parsedProgram, layout.headerMatches, layout.load,
    layout.offsetZero, layout.readExecute, layout.fileBacked, layout.sizes, layout.positive,
    layout.taskBound, layout.entryInside, layout.entryBelow, layout.entryDecodes,
    layout.programHeadersRead⟩

theorem pageRoundUp_ge (n : Int) : n ≤ pageRoundUp n := by
  unfold pageRoundUp pageSize; omega

/-- The entry block ends at the page top (as `Sha256Cli.LaunchFacts.block_top`, for any image). -/
theorem entryStack_top (img : Image) (en : ExecEntry) (inp : ProcInput) :
    uns en.sp + (entryStack img en inp).length = entryPageTop en.sp (stackBytes img en inp) := by
  have slack : ∀ (sp : Word) (bytes : List Byte) (f : Word → Byte),
      (entrySlack sp bytes f).length = entrySlackLen sp bytes := by
    intro sp bytes f; simp [entrySlack]
  simp only [entryStack, List.length_append, slack, entrySlackLen]
  have := pageRoundUp_ge (entryBlockTop en.sp (stackBytes img en inp))
  simp only [entryPageTop, entryBlockTop] at this ⊢
  rw [Nat.cast_add, Int.toNat_of_nonneg (by omega)]
  omega

/-- A valid launch of a probe whose static layout holds satisfies the kit's `Checked`. -/
theorem checkedAt (static : P.Static) {en : ExecEntry} {inp : ProcInput}
    (validInput : X86Launch.ValidInput inp)
    (validEntry : X86Launch.ValidEntry x86ExtNative P.snapshot en inp) :
    Checked (P.launchAt en inp) := by
  have top := entryStack_top P.image en inp
  obtain ⟨-, -, -, -, -, -, -, -, pageTop, below⟩ := id validEntry
  change entryPageTop en.sp (stackBytes P.image en inp) ≤ x86AddressSpace.taskSize at pageTop
  have seg := below P.segment (List.mem_singleton_self _)
  simp only [x86AddressSpace, uns] at pageTop seg top
  refine ⟨⟨static.parsedHeader, static.parsedProgram, static.headerMatches, static.load,
    static.offsetZero, static.readExecute, static.fileBacked, static.sizes, static.positive,
    static.taskBound, ?_, ?_, static.entryInside, static.entryBelow, static.entryDecodes,
    static.programHeadersRead⟩, validInput, validEntry⟩
  · change P.base + P.size ≤ en.sp.toNat - stackMaxSize.toNat
    simp only [segment, stackMaxSize] at seg ⊢
    omega
  · change en.sp.toNat + (entryStack P.image en inp).length ≤ 2 ^ 64
    omega

/-! ## Configurations of the flag-oracle machine -/

variable (oracle : Nat → X86FlagChoices.Choice)

/-- The machine: native x86-64 with oracle-chosen undefined flags at `syscall`. -/
abbrev omachine : UserIsa := x86WithFlagOracle oracle

/-- A configuration over the initial memory, with oracle counter `counter`. -/
abbrev ocfg (core : Silmaril.X86.State) (pending : Option Word) (counter : Nat) (model : Model) :
    Config (x86WithFlagOracle oracle) :=
  ⟨⟨⟨⟨core, P.mem0⟩, pending⟩, counter⟩, model⟩

/-- The launch, with allocation limit `limit`. -/
def oinitial (limit : Int) : Config (x86WithFlagOracle oracle) :=
  init (x86WithFlagOracle oracle) P.snapshot P.entry limit P.input

def omodel0 (limit : Int) : Model := (P.oinitial oracle limit).model

theorem oinitial_at (limit : Int) :
    P.oinitial oracle limit = P.ocfg oracle P.core0 none 0 (P.omodel0 oracle limit) := rfl

/-- The core after the oracle completes its undefined flags at a `syscall`. -/
def complete (core : Silmaril.X86.State) (choice : X86FlagChoices.Choice) : Silmaril.X86.State :=
  { core with flags := X86FlagChoices.completeFlags core.flags choice }

@[simp] theorem complete_read (core : Silmaril.X86.State) (choice : X86FlagChoices.Choice)
    (r : Silmaril.X86.Reg) : (complete core choice).read r = core.read r := rfl

@[simp] theorem complete_rip (core : Silmaril.X86.State) (choice : X86FlagChoices.Choice) :
    (complete core choice).rip = core.rip := rfl

/-- The syscall input of a pending configuration. -/
abbrev osysIn (core : Silmaril.X86.State) (n : Word) (counter : Nat) : SyscallInput :=
  sysInput (x86WithFlagOracle oracle) P.segs
    (⟨⟨⟨core, P.mem0⟩, some n⟩, counter⟩ : X86FlagChoices.State) n

theorem osysIn_eq (core : Silmaril.X86.State) (n : Word) (counter : Nat) :
    P.osysIn oracle core n counter = P.sysIn core n := rfl

/-! ## Transition rules -/

section Rules

variable {refused : RefusalFilter}

theorem oresume_effect (core : Silmaril.X86.State) (n : Word) (other : n ≠ 158) (ret : Word)
    (copyins : List (Word × Nat)) (counter : Nat) :
    (x86WithFlagOracle oracle).advancePastSvc ((x86WithFlagOracle oracle).applyEffect
      (⟨⟨⟨core, P.mem0⟩, some n⟩, counter⟩ : X86FlagChoices.State)
      ((mkEffect ret [] []).withCopyins copyins)) = ⟨⟨⟨resume core ret, P.mem0⟩, none⟩, counter⟩ := by
  change (⟨x86ExtNative.advancePastSvc (x86ExtNative.applyEffect ⟨⟨core, P.mem0⟩, some n⟩
    ((mkEffect ret [] []).withCopyins copyins)), counter⟩ : X86FlagChoices.State) = _
  rw [P.resume_effect core n other]

theorem oaccountStep_instr [Checked P] {off len : Nat} {instruction : Silmaril.X86.Ext.Instr}
    {core core' : Silmaril.X86.State} {counter : Nat} {model : Model} (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (fits : off + len ≤ P.size) (two : off + 2 ≤ P.size)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core P.mem0 len = .ok core' P.mem0) :
    accountStep (x86WithFlagOracle oracle) P.segs ⟨⟨⟨core, P.mem0⟩, none⟩, counter⟩ model =
      .ok (⟨⟨⟨core', P.mem0⟩, none⟩, counter⟩, model) := by
  have fetched := P.mem0_window .execute (by decide) off len (by omega) fits
  have prefix2 := P.mem0_window .execute (by decide) off 2 (by omega) two
  have notTwo : P.mem0.fetchBytes core.rip.toNat 2 ≠ some [0x0f, 0x05] := by
    rw [rip, Memory.fetchBytes, prefix2]
    exact fun h => notSyscall (Option.some.inj h)
  apply Progress.accountStep_of_noLazy _ _ model _ lazy
  change X86FlagChoices.step oracle ⟨⟨⟨core, P.mem0⟩, none⟩, counter⟩ = _
  rw [X86FlagChoices.step_not_syscall _ _ notTwo]
  rw [x86NativeStep_of_fetch (s := ⟨⟨core, P.mem0⟩, none⟩) notTwo
    (show P.mem0.fetchBytes core.rip.toNat len = some _ by rw [rip, Memory.fetchBytes, fetched])
    decoded]
  change X86FlagChoices.lift counter
    (x86ExecResult _ (Silmaril.X86.Ext.exec instruction core P.mem0 len)) = _
  rw [exec]
  rfl

/-- An ordinary instruction at segment offset `off` has exactly one successor. -/
theorem osstep_instr_iff [Checked P] {off len : Nat} {instruction : Silmaril.X86.Ext.Instr}
    {core core' : Silmaril.X86.State} {counter : Nat} {model : Model}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (fits : off + len ≤ P.size) (two : off + 2 ≤ P.size)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core P.mem0 len = .ok core' P.mem0)
    (evs : List Event) (target : StepTo (x86WithFlagOracle oracle)) :
    SStep P.segs spec refused (P.ocfg oracle core none counter model) evs target ↔
      evs = [] ∧ target = .next (P.ocfg oracle core' none counter model) := by
  have account := P.oaccountStep_instr oracle (counter := counter) lazy rip fits two notSyscall
    decoded exec
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

/-- `syscall` at offset `off` traps with the pending number from RAX, after the oracle has
completed the undefined flags; the counter advances. -/
theorem osstep_trap_iff [Checked P] {off : Nat} {core : Silmaril.X86.State} {counter : Nat}
    {model : Model} (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (two : off + 2 ≤ P.size)
    (isSyscall : (P.bytes.drop off).take 2 = [0x0f, 0x05])
    (evs : List Event) (target : StepTo (x86WithFlagOracle oracle)) :
    SStep P.segs spec refused (P.ocfg oracle core none counter model) evs target ↔
      evs = [] ∧ target = .next (P.ocfg oracle (complete core (oracle counter))
        (some (core.read .rax)) (counter + 1) model) := by
  have prefix2 := P.mem0_window .execute (by decide) off 2 (by omega) two
  have account : accountStep (x86WithFlagOracle oracle) P.segs ⟨⟨⟨core, P.mem0⟩, none⟩, counter⟩
      model = .ok (⟨⟨⟨complete core (oracle counter), P.mem0⟩, some (core.read .rax)⟩,
        counter + 1⟩, model) := by
    apply Progress.accountStep_of_noLazy _ _ model _ lazy
    exact X86FlagChoices.step_syscall oracle ⟨⟨⟨core, P.mem0⟩, none⟩, counter⟩
      (by rw [show core.rip.toNat = P.base + off from rip, Memory.fetchBytes, prefix2, isSyscall])
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

/-- A pending call whose only outcome halts normally. -/
theorem osstep_halt_iff {core : Silmaril.X86.State} {n : Word} {counter : Nat}
    {model model' : Model} {effect : SyscallEffect} {code : Word} (running : model.halted = none)
    (outcomes : ∀ outcome, spec (P.sysIn core n) model outcome ↔ outcome = .ok effect model' [])
    (halted : model'.halted = some code) (unkilled : model'.killedBy = none)
    (evs : List Event) (target : StepTo (x86WithFlagOracle oracle)) :
    SStep P.segs spec refused (P.ocfg oracle core (some n) counter model) evs target ↔
      evs = [.exitEv code model'.fs] ∧
        target = .next (P.ocfg oracle core (some n) counter model') := by
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
    exact SStep.exit (isa := x86WithFlagOracle oracle)
      (ms := (⟨⟨⟨core, P.mem0⟩, some n⟩, counter⟩ : X86FlagChoices.State))
      running rfl ((outcomes _).mpr rfl) halted unkilled

/-- A pending call whose outcomes return to the program with an unchanged model. -/
theorem osstep_return_iff {core : Silmaril.X86.State} {n : Word} {counter : Nat} {model : Model}
    {α : Type} {allowed : α → Prop} {ret : α → Word} {copyins : α → List (Word × Nat)}
    {events : α → List Event} (other : n ≠ 158)
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (outcomes : ∀ outcome, spec (P.sysIn core n) model outcome ↔
      ∃ x, allowed x ∧ outcome = .ok ((mkEffect (ret x) [] []).withCopyins (copyins x)) model (events x))
    (evs : List Event) (target : StepTo (x86WithFlagOracle oracle)) :
    SStep P.segs spec refused (P.ocfg oracle core (some n) counter model) evs target ↔
      ∃ x, (allowed x ∧ ¬ refused (P.sysIn core n) model
          ((mkEffect (ret x) [] []).withCopyins (copyins x))) ∧
        evs = events x ∧ target = .next (P.ocfg oracle (resume core (ret x)) none counter model) := by
  have materialized (accesses : List (Word × Nat)) :=
    Progress.materializeModelAccesses_noLazy model accesses lazy
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
      rw [materialized] at m
      cases m
      refine ⟨x, ⟨hx, notRefused⟩, rfl, ?_⟩
      rw [P.oresume_effect oracle core n other]
    | syscallMaterializationFault _ p s _ _ m =>
      cases p
      obtain ⟨x, _, same⟩ := (outcomes _).mp s
      cases same
      rw [materialized] at m
      cases m
    | exit _ p s h _ =>
      cases p
      obtain ⟨x, _, same⟩ := (outcomes _).mp s
      cases same
      rw [running] at h
      cases h
    | killed _ p s k =>
      cases p
      obtain ⟨x, _, same⟩ := (outcomes _).mp s
      cases same
      have : model.killedBy = none := by
        simp [Model.killedBy, Model.halted] at running ⊢; simp [running]
      rw [this] at k
      cases k
    | syscallUnmodeled _ p s =>
      cases p
      obtain ⟨x, _, same⟩ := (outcomes _).mp s
      cases same
  · rintro ⟨x, ⟨hx, notRefused⟩, rfl, rfl⟩
    have step := SStep.syscall (segs := P.segs) (spec := spec) (refused := refused)
      (isa := x86WithFlagOracle oracle) (x8 := n)
      (ms := (⟨⟨⟨core, P.mem0⟩, some n⟩, counter⟩ : X86FlagChoices.State)) running rfl
      ((outcomes _).mpr ⟨x, hx, rfl⟩) notRefused running (materialized _)
    rwa [P.oresume_effect oracle core n other] at step

/-- `exit` (60) halts with the low byte of RDI. -/
theorem osstep_exit_iff {core : Silmaril.X86.State} {counter : Nat} {model : Model}
    (running : model.halted = none)
    (clear : NativeX86.All.boundarySuspect 60 (P.sysIn core 60) = false) (evs : List Event)
    (target : StepTo (x86WithFlagOracle oracle)) :
    SStep P.segs spec refused (P.ocfg oracle core (some 60) counter model) evs target ↔
      evs = [.exitEv (core.read .rdi &&& 255) model.fs] ∧
        target = .next (P.ocfg oracle core (some 60) counter
          (model.withHalted (core.read .rdi &&& 255))) :=
  P.osstep_halt_iff oracle running (fun outcome => native_exit_iff _ model outcome rfl clear) rfl
    (by simp [Model.killedBy, Model.withHalted]) evs target

/-- `write` (1) of `count` image bytes at segment offset `off` to a channel. -/
theorem osstep_write_iff [checked : Checked P] {core : Silmaril.X86.State} {n : Word}
    {counter : Nat} {model : Model}
    {off count : Nat} {ch : Word} (number : n = 1)
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (lookup : fdLookup model.fds (fd32 (core.read .rdi)) = some (.channel ch)) (nonzero : ch ≠ 0)
    (buffer : core.read .rsi = BitVec.ofNat 64 (P.base + off))
    (modeled : modeledRwRangeWith accessOkbX86 (core.read .rsi) (core.read .rdx) = true)
    (nonzeroCount : core.read .rdx ≠ 0)
    (clear : NativeX86.All.boundarySuspect 1 (P.sysIn core n) = false)
    (clamp : rwCountClamp (core.read .rdx) = count)
    (clampWord : (zw (rwCountClamp (core.read .rdx))).toNat = count)
    (fits : off + count ≤ P.size) (nonempty : (P.bytes.drop off).take count ≠ [])
    (evs : List Event) (target : StepTo (x86WithFlagOracle oracle)) :
    SStep P.segs spec refused (P.ocfg oracle core (some n) counter model) evs target ↔
      ∃ ds, (WritePrefix ((P.bytes.drop off).take count) ds ∧ ¬ refused (P.sysIn core n) model
          ((mkEffect (lenWord ds) [] []).withCopyins [(core.read .rsi, ds.length)])) ∧
        evs = ds.map (.writeEv ch) ∧
          target = .next (P.ocfg oracle (resume core (lenWord ds)) none counter model) := by
  subst number
  have bounded : (((P.bytes.drop off).take count).length : Int) ≤ rwCountClamp (core.read .rdx) := by
    rw [clamp]
    simp only [List.length_take]
    omega
  refine P.osstep_return_iff oracle (allowed := WritePrefix ((P.bytes.drop off).take count))
    (by decide) running lazy (fun outcome => ?_) evs target
  refine (native_write_iff (P.sysIn core 1) model outcome rfl clear lookup nonzero modeled nonzeroCount
    (bs := (P.bytes.drop off).take count) ?_ nonempty).trans ?_
  · change readableBytesAux (viewByte P.mem0 .read) (core.read .rsi)
      (zw (rwCountClamp (core.read .rdx))).toNat = _
    rw [clampWord, buffer]
    exact P.readableBytesAux_mem0 off count fits
  · exact exists_congr fun ds => and_congr_left fun _ => writePrefix_iff bounded

/-! ### Execution rules -/

theorem oexec_instr {checked : Checked P} {post : Omni.Post (x86WithFlagOracle oracle)} {off len : Nat}
    {instruction : Silmaril.X86.Ext.Instr} {core core' : Silmaril.X86.State} {counter : Nat}
    {model : Model} (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (fits : off + len ≤ P.size) (two : off + 2 ≤ P.size)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core P.mem0 len = .ok core' P.mem0)
    (rest : Omni.Exec P.segs spec refused (P.ocfg oracle core' none counter model) post) :
    Omni.Exec P.segs spec refused (P.ocfg oracle core none counter model) post :=
  Omni.exec_of_unique running
    (P.osstep_instr_iff oracle running lazy rip fits two notSyscall decoded exec) rest

theorem oexec_trap {checked : Checked P} {post : Omni.Post (x86WithFlagOracle oracle)} {off : Nat}
    {core : Silmaril.X86.State} {counter : Nat} {model : Model}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (two : off + 2 ≤ P.size)
    (isSyscall : (P.bytes.drop off).take 2 = [0x0f, 0x05])
    (rest : Omni.Exec P.segs spec refused (P.ocfg oracle (complete core (oracle counter))
      (some (core.read .rax)) (counter + 1) model) post) :
    Omni.Exec P.segs spec refused (P.ocfg oracle core none counter model) post :=
  Omni.exec_of_unique running (P.osstep_trap_iff oracle running lazy rip two isSyscall) rest

theorem oexec_exit {post : Omni.Post (x86WithFlagOracle oracle)} {core : Silmaril.X86.State}
    {n status : Word} {counter : Nat} {model : Model} (number : n = 60)
    (rdi : core.read .rdi = status) (running : model.halted = none)
    (clear : NativeX86.All.boundarySuspect 60 (P.sysIn core n) = false)
    (done : post [.exitEv (status &&& 255) model.fs]
      (.halt (P.ocfg oracle core (some n) counter (model.withHalted (status &&& 255))))) :
    Omni.Exec P.segs spec refused (P.ocfg oracle core (some n) counter model) post := by
  subst number rdi
  refine Omni.exec_of_unique running (P.osstep_exit_iff oracle running clear)
    (.halt (by simp [Model.withHalted, Model.halted]) ?_)
  simpa only [List.append_nil] using done

theorem oexec_write {checked : Checked P} {post : Omni.Post (x86WithFlagOracle oracle)}
    {core : Silmaril.X86.State} {n : Word} {counter : Nat} {model : Model} {off count : Nat}
    {ch : Word} (number : n = 1)
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (lookup : fdLookup model.fds (fd32 (core.read .rdi)) = some (.channel ch)) (nonzero : ch ≠ 0)
    (buffer : core.read .rsi = BitVec.ofNat 64 (P.base + off))
    (modeled : modeledRwRangeWith accessOkbX86 (core.read .rsi) (core.read .rdx) = true)
    (nonzeroCount : core.read .rdx ≠ 0)
    (clear : NativeX86.All.boundarySuspect 1 (P.sysIn core n) = false)
    (clamp : rwCountClamp (core.read .rdx) = count)
    (clampWord : (zw (rwCountClamp (core.read .rdx))).toNat = count)
    (fits : off + count ≤ P.size) (nonempty : (P.bytes.drop off).take count ≠ [])
    (rest : ∀ ds, WritePrefix ((P.bytes.drop off).take count) ds →
      Omni.Exec P.segs spec noFilter (P.ocfg oracle (resume core (lenWord ds)) none counter model)
        (fun trace outcome => post (ds.map (.writeEv ch) ++ trace) outcome)) :
    Omni.Exec P.segs spec noFilter (P.ocfg oracle core (some n) counter model) post :=
  Omni.exec_of_successors running
    (P.osstep_write_iff oracle number running lazy lookup nonzero buffer modeled nonzeroCount
      clear clamp clampWord fits nonempty)
    ⟨_, ⟨nonempty, List.prefix_refl _⟩, fun h => h⟩ (fun ds allowed => rest ds allowed.1)

/-! ### Run rules (one chosen execution, as a `Star`) -/

theorem orun_instr {checked : Checked P} {off len : Nat} {instruction : Silmaril.X86.Ext.Instr}
    {core core' : Silmaril.X86.State} {counter : Nat} {model : Model} {trace : List Event}
    {final : Config (x86WithFlagOracle oracle)}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (fits : off + len ≤ P.size) (two : off + 2 ≤ P.size)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core P.mem0 len = .ok core' P.mem0)
    (rest : Star P.segs spec refused (P.ocfg oracle core' none counter model) trace final) :
    Star P.segs spec refused (P.ocfg oracle core none counter model) trace final :=
  .step ((P.osstep_instr_iff oracle running lazy rip fits two notSyscall decoded exec _ _).mpr
    ⟨rfl, rfl⟩) rest

theorem orun_trap {checked : Checked P} {off : Nat} {core : Silmaril.X86.State} {counter : Nat}
    {model : Model} {trace : List Event} {final : Config (x86WithFlagOracle oracle)}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (two : off + 2 ≤ P.size)
    (isSyscall : (P.bytes.drop off).take 2 = [0x0f, 0x05])
    (rest : Star P.segs spec refused (P.ocfg oracle (complete core (oracle counter))
      (some (core.read .rax)) (counter + 1) model) trace final) :
    Star P.segs spec refused (P.ocfg oracle core none counter model) trace final :=
  .step ((P.osstep_trap_iff oracle running lazy rip two isSyscall _ _).mpr ⟨rfl, rfl⟩) rest

theorem orun_exit {core : Silmaril.X86.State} {n status : Word} {counter : Nat} {model : Model}
    (number : n = 60) (rdi : core.read .rdi = status) (running : model.halted = none)
    (clear : NativeX86.All.boundarySuspect 60 (P.sysIn core n) = false) :
    Star P.segs spec refused (P.ocfg oracle core (some n) counter model)
      [.exitEv (status &&& 255) model.fs]
      (P.ocfg oracle core (some n) counter (model.withHalted (status &&& 255))) := by
  subst number rdi
  exact .step ((P.osstep_exit_iff oracle running clear _ _).mpr ⟨rfl, rfl⟩) (.refl _)

theorem orun_write {checked : Checked P} {core : Silmaril.X86.State} {n : Word} {counter : Nat}
    {model : Model} {off count : Nat} {ch : Word} {ds : List Byte} {trace : List Event}
    {final : Config (x86WithFlagOracle oracle)} (number : n = 1)
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (lookup : fdLookup model.fds (fd32 (core.read .rdi)) = some (.channel ch)) (nonzero : ch ≠ 0)
    (buffer : core.read .rsi = BitVec.ofNat 64 (P.base + off))
    (modeled : modeledRwRangeWith accessOkbX86 (core.read .rsi) (core.read .rdx) = true)
    (nonzeroCount : core.read .rdx ≠ 0)
    (clear : NativeX86.All.boundarySuspect 1 (P.sysIn core n) = false)
    (clamp : rwCountClamp (core.read .rdx) = count)
    (clampWord : (zw (rwCountClamp (core.read .rdx))).toNat = count)
    (fits : off + count ≤ P.size) (nonempty : (P.bytes.drop off).take count ≠ [])
    (delivered : WritePrefix ((P.bytes.drop off).take count) ds)
    (accepted : ¬ noFilter (P.sysIn core n) model
      ((mkEffect (lenWord ds) [] []).withCopyins [(core.read .rsi, ds.length)]))
    (rest : Star P.segs spec noFilter (P.ocfg oracle (resume core (lenWord ds)) none counter model)
      trace final) :
    Star P.segs spec noFilter (P.ocfg oracle core (some n) counter model)
      (ds.map (.writeEv ch) ++ trace) final :=
  .step ((P.osstep_write_iff oracle number running lazy lookup nonzero buffer modeled nonzeroCount
    clear clamp clampWord fits nonempty _ _).mpr ⟨ds, ⟨delivered, accepted⟩, rfl, rfl⟩) rest

end Rules

end Probe

/-! ## Tactics

The side conditions of a launch `P.launchAt en inp` mention the free entry and input, which
`decide` refuses; the static ones are first rewritten to the probe's own bytes. -/

/-- Symbolic evaluation of a register read on a launch core: the free stack pointer only
sits in RSP, so the other registers simplify to literals. -/
macro "oprobe_eval" : tactic =>
  `(tactic| (simp (config := {decide := true}) [Probe.complete, Probe.complete_read, Probe.resume,
      Silmaril.X86.State.read, Silmaril.X86.State.write, Silmaril.Machine.RegisterFile.write,
      Silmaril.X86.Reg.ofBitVec, Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.read,
      Silmaril.X86.Ext.Sz.ofW, Silmaril.X86.Ext.mkReg, Silmaril.X86.Ext.ModRM.ofByte,
      Silmaril.X86.Ext.AluOp.resultN, Silmaril.X86.Ext.Rex.zero, Probe.core0, Probe.initial,
      X86Launch.init, initConfigWithStack, x86ExtNative, x86Ext]; done))

macro "oprobe_side" : tactic =>
  `(tactic| first
    | decide +kernel
    | rfl
    | (simp only [Probe.launchAt_size, Probe.launchAt_base, Probe.launchAt_bytes]
       first | decide +kernel | rfl)
    | exact inferInstance | exact ⟨rfl, rfl⟩ | exact fun h => h
    | probe_clear
    | (show NativeX86.All.boundarySuspect _ _ = false
       rw [Probe.boundarySuspect_regs _ (by decide +kernel)]
       oprobe_eval)
    | oprobe_eval)

macro "oprobe_sides" : tactic => `(tactic| all_goals try oprobe_side)

macro "oprobe_instr " off:term:max len:term:max instr:term:max : tactic =>
  `(tactic| (first
    | apply Probe.oexec_instr _ _ (off := $off) (len := $len) (instruction := $instr)
    | apply Probe.orun_instr _ _ (off := $off) (len := $len) (instruction := $instr)) <;> oprobe_sides)

macro "oprobe_trap " off:term:max : tactic =>
  `(tactic| (first
    | apply Probe.oexec_trap _ _ (off := $off)
    | apply Probe.orun_trap _ _ (off := $off)) <;> oprobe_sides)

macro "oprobe_exit " status:term:max : tactic =>
  `(tactic| (first
    | apply Probe.oexec_exit _ _ (status := $status)
    | apply Probe.orun_exit _ _ (status := $status)) <;> oprobe_sides)

macro "oprobe_write " off:term:max count:term:max : tactic =>
  `(tactic| (apply Probe.oexec_write _ _ (off := $off) (count := $count) <;> oprobe_sides))

macro "oprobe_write " off:term:max count:term:max " with " ds:term : tactic =>
  `(tactic| (apply Probe.orun_write _ _ (off := $off) (count := $count) (ds := $ds) <;> oprobe_sides))

end Silmaril.Process.LPS.Probes
