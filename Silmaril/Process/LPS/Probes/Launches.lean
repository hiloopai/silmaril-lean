module

public import Silmaril.Process.LPS.Probes.Kit
public import Silmaril.Process.LPS.Problems.Profile
public import Silmaril.Process.LPS.Behaviour

/-! # Probes at every valid launch, and the native problem shapes

A probe's universal theorem (`Probe.Determined`, or an `Omni.Exec` with named alternatives)
fixes one launch: `Probe.entry` (stack pointer, break, mmap base and the entry draw) and
`Probe.input` (argv, environment, files, stdin, credentials). An OSS Verify shape quantifies
over every valid entry and every valid input. This file is the bridge.

**Entry independence.** `Probe.launchedAt P en inp` is the same bytes launched at `en` with
`inp`. The kit's rules are stated for every probe with a `Checked` instance and never look
at the stack bytes or the entry draw, only at the loaded segment (`Probe.Intact`), so a proof
script that reads nothing from the stack/auxv region (or only the fixed facts the launch
validity gives, such as `rsp` lying below `TASK_SIZE`) proves the theorem for the symbolic
launch. The launch-dependent part of `Checked` is exactly two layout facts, the image below
the stack reservation and the entry block below `2^64`; `layout_launchedAt` derives both from
`X86Launch.ValidEntry`, and `checked_launchedAt` gives `Checked` at every valid launch. A
probe whose execution depends on the launch (it reads the break, the stack contents or a file)
has a theorem at every launch only in a form that names that dependence.

**Lifting.** `haltsMayFail_of_exec` turns a universal theorem at every valid launch, under no
refusal filter, into the native `haltsMayFail` (`Problems.nativeX86`): the may-fail reading
refuses nothing (`Problems.nativeX86_refusals_mayFail`) and the profile's initial
configuration is the probe's (`initial_launchedAt`). `haltsMayFailWith_of_exec` is the same
for the extended shape. The refutation lemmas go the other way: one valid launch with a
reachable kill, a reachable exit outside the set, or a reachable error refutes `haltsMayFail`.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Machines.X86Launch
open Silmaril.Process.LPS.Problems

namespace Probe

variable (P : Probe)

/-- The probe's bytes launched at entry `en` with input `inp`. -/
def launchedAt (en : ExecEntry) (inp : ProcInput) : Probe := { P with entry := en, input := inp }

variable (en : ExecEntry) (inp : ProcInput)

@[simp] theorem launchedAt_snapshot : (P.launchedAt en inp).snapshot = P.snapshot := rfl
@[simp] theorem launchedAt_segs : (P.launchedAt en inp).segs = P.segs := rfl
@[simp] theorem launchedAt_bytes : (P.launchedAt en inp).bytes = P.bytes := rfl
@[simp] theorem launchedAt_entry : (P.launchedAt en inp).entry = en := rfl
@[simp] theorem launchedAt_input : (P.launchedAt en inp).input = inp := rfl

/-- The probe's initial configuration at allocation limit `lim` (`Probe.initial` is the one
at the source limit). -/
def initialAt (lim : Int) : Config x86ExtNative := init x86ExtNative P.snapshot P.entry lim P.input

/-- The model of `initialAt`: only the allocation limit differs between limits. -/
def modelAt (lim : Int) : Model := (P.initialAt lim).model

theorem initialAt_eq (lim : Int) : P.initialAt lim = P.cfg P.core0 none (P.modelAt lim) := rfl

theorem initialAt_source : P.initialAt sourceAllocLimit = P.initial := rfl

/-- The profile's initial configuration is the launched probe's. -/
theorem initial_launchedAt (lim : Int) :
    nativeX86.initialConfig P.snapshot en lim inp = (P.launchedAt en inp).initialAt lim := rfl

/-- The probe's own launch is `launchedAt` its entry and input. -/
theorem launchedAt_self : P.launchedAt P.entry P.input = P := rfl

theorem entrySlack_length (sp : Word) (bytes : List Byte) (slack : Word → Byte) :
    (entrySlack sp bytes slack).length = entrySlackLen sp bytes := by
  simp [entrySlack]

/-- The entry stack ends at the entry page top. -/
theorem entryStack_end (img : Image) :
    (uns en.sp : Int) + (entryStack img en inp).length = entryPageTop en.sp (stackBytes img en inp) := by
  simp only [entryStack, List.length_append, entrySlack_length, entrySlackLen, entryPageTop,
    entryBlockTop, pageRoundUp, pageSize]
  push_cast
  omega

/-- The entry stack fits below `2^64` when its page top is below the task size. -/
theorem stackFits_of (img : Image)
    (top : entryPageTop en.sp (stackBytes img en inp) ≤ x86AddressSpace.taskSize) :
    en.sp.toNat + (entryStack img en inp).length ≤ 2 ^ 64 := by
  have stackEnd := entryStack_end en inp img
  have top' : (en.sp.toNat : Int) + ((entryStack img en inp).length : Int) ≤ 0x7ffffffff000 := by
    have h : (uns en.sp : Int) + (entryStack img en inp).length ≤ x86AddressSpace.taskSize := by
      rw [stackEnd]; exact top
    exact h
  have pow : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  rw [pow]
  omega

variable {P en inp}

/-- The layout of a probe at a valid launch: the launch-independent facts are the probe's,
the two launch-dependent ones follow from `ValidEntry`. -/
theorem layout_launchedAt (layout : P.Layout) (valid : X86Launch.ValidEntry x86ExtNative P.snapshot en inp) :
    (P.launchedAt en inp).Layout := by
  obtain ⟨_, _, _, _, _, _, _, _, top, below⟩ := valid
  have segment := below P.segment (List.mem_singleton_self _)
  refine ⟨layout.parsedHeader, layout.parsedProgram, layout.headerMatches, layout.load,
    layout.offsetZero, layout.readExecute, layout.fileBacked, layout.sizes, layout.positive,
    layout.taskBound, ?_, ?_, layout.entryInside, layout.entryBelow, layout.entryDecodes,
    layout.programHeadersRead⟩
  · change P.base + P.size ≤ en.sp.toNat - stackMaxSize.toNat
    change (P.base : Int) + P.size ≤ uns en.sp - stackMaxSize at segment
    simp only [uns, stackMaxSize] at segment ⊢
    omega
  · exact stackFits_of en inp P.image top

/-- A checked probe is checked at every valid launch on the kit's input domain. -/
theorem checked_launchedAt [checked : P.Checked] (validEntry : X86Launch.ValidEntry x86ExtNative P.snapshot en inp)
    (validInput : X86Launch.ValidInput inp) : (P.launchedAt en inp).Checked :=
  ⟨layout_launchedAt checked.layout validEntry, validInput, validEntry⟩

end Probe

/-! ## Lifting to the native shapes -/

/-- A launch the native profile admits: valid entry, valid input, `abort()` not modelled. -/
structure NativeLaunch (P : Probe) (en : ExecEntry) (inp : ProcInput) : Prop where
  entry : X86Launch.ValidEntry x86ExtNative P.snapshot en inp
  input : X86Launch.ValidInput inp
  abort : inp.abortTerminal = false

theorem NativeLaunch.of_valid {P : Probe} {en : ExecEntry} {inp : ProcInput}
    (validEntry : nativeX86.validEntry P.snapshot en inp) (validInput : nativeX86.validInput false inp) :
    NativeLaunch P en inp :=
  ⟨validEntry, ((nativeX86_validInput inp).mp validInput).1, ((nativeX86_validInput inp).mp validInput).2⟩

/-- The native must-exit statement at one launch is the probe's must-exit statement under no
refusal filter. -/
theorem mustExitIn_mayFail_iff (P : Probe) (allowed : List Word) (en : ExecEntry) (inp : ProcInput) :
    nativeX86.MustExitIn (some mayFailCfg) allowed P.snapshot sourceAllocLimit en inp ↔
      MustExitInAt P.segs spec noFilter allowed (P.launchedAt en inp).initial := by
  unfold StatementProfile.MustExitIn
  rw [nativeX86_refusals_mayFail]
  exact Iff.rfl

/-- **Lifting.** A universal theorem at every native launch, under no refusal filter, whose
postcondition implies an allowed exit, is the native `haltsMayFail`. -/
theorem haltsMayFail_of_exec (P : Probe) {allowed : List Word} {post : Omni.Post x86ExtNative}
    (exec : ∀ en inp, NativeLaunch P en inp →
      Omni.Exec P.segs spec noFilter (P.launchedAt en inp).initial post)
    (exits : ∀ trace outcome, post trace outcome → Omni.ExitsIn allowed trace outcome) :
    nativeX86.haltsMayFail allowed P.snapshot := by
  intro en inp validEntry validInput
  rw [mustExitIn_mayFail_iff, Omni.mustExitInAt_iff_exec]
  exact (exec en inp (NativeLaunch.of_valid validEntry validInput)).consequence exits

/-- **Lifting**, extended shape. -/
theorem haltsMayFailWith_of_exec (P : Probe) {allowed : List Word} {good : List Event → Prop}
    {post : Omni.Post x86ExtNative}
    (exec : ∀ en inp, NativeLaunch P en inp →
      Omni.Exec P.segs spec noFilter (P.launchedAt en inp).initial post)
    (exits : ∀ trace outcome, post trace outcome → Omni.ExitsIn allowed trace outcome ∧ good trace) :
    nativeX86.haltsMayFailWith allowed good P.snapshot := by
  intro en inp validEntry validInput
  show Omni.Exec P.segs spec (nativeX86.refusals (some mayFailCfg)) (P.launchedAt en inp).initial _
  rw [nativeX86_refusals_mayFail]
  exact (exec en inp (NativeLaunch.of_valid validEntry validInput)).consequence exits

/-! ## Refuting the native shapes at one launch -/

theorem nativeLaunch_valid {P : Probe} {en : ExecEntry} {inp : ProcInput} (launch : NativeLaunch P en inp) :
    nativeX86.validEntry P.snapshot en inp ∧ nativeX86.validInput false inp :=
  ⟨launch.entry, (nativeX86_validInput inp).mpr ⟨launch.input, launch.abort⟩⟩

/-- A reachable kill at one native launch refutes `haltsMayFail` for every exit set. -/
theorem not_haltsMayFail_of_kill (P : Probe) {allowed : List Word} {en : ExecEntry} {inp : ProcInput}
    (launch : NativeLaunch P en inp) {trace : List Event} {final : Config x86ExtNative} {sig : Word}
    (star : Star P.segs spec noFilter (P.launchedAt en inp).initial trace final)
    (killed : final.model.killedBy = some sig) :
    ¬ nativeX86.haltsMayFail allowed P.snapshot := by
  intro h
  have must := (mustExitIn_mayFail_iff P allowed en inp).mp
    (h en inp (nativeLaunch_valid launch).1 (nativeLaunch_valid launch).2)
  exact MustExitInAt.no_kill (h := must) (s := star) killed

/-- A reachable exit with a status outside the set at one native launch refutes
`haltsMayFail`. -/
theorem not_haltsMayFail_of_exit (P : Probe) {allowed : List Word} {en : ExecEntry} {inp : ProcInput}
    (launch : NativeLaunch P en inp) {trace : List Event} {final : Config x86ExtNative} {code : Word}
    (star : Star P.segs spec noFilter (P.launchedAt en inp).initial trace final)
    (halted : final.model.halted = some code) (outside : code ∉ allowed) :
    ¬ nativeX86.haltsMayFail allowed P.snapshot := by
  intro h
  have must := (mustExitIn_mayFail_iff P allowed en inp).mp
    (h en inp (nativeLaunch_valid launch).1 (nativeLaunch_valid launch).2)
  obtain ⟨code', member, exited⟩ :=
    MustExitInAt.exited (h := must) (s := star) (by rw [halted]; exact Option.some_ne_none _)
  have same : some code = some code' := halted.symm.trans exited.1
  cases same
  exact outside member

/-- A reachable error transition at one native launch refutes `haltsMayFail`. -/
theorem not_haltsMayFail_of_error (P : Probe) {allowed : List Word} {en : ExecEntry} {inp : ProcInput}
    (launch : NativeLaunch P en inp) (errors : ReachesError P.segs spec noFilter (P.launchedAt en inp).initial) :
    ¬ nativeX86.haltsMayFail allowed P.snapshot := by
  intro h
  have must := (mustExitIn_mayFail_iff P allowed en inp).mp
    (h en inp (nativeLaunch_valid launch).1 (nativeLaunch_valid launch).2)
  exact MustExitInAt.not_reachesError (h := must) errors

/-- An execution proof at one native launch whose every outcome is outside the exit set
refutes `haltsMayFail`. -/
theorem not_haltsMayFail_of_exec (P : Probe) {allowed : List Word} {en : ExecEntry} {inp : ProcInput}
    (launch : NativeLaunch P en inp) {post : Omni.Post x86ExtNative}
    (exec : Omni.Exec P.segs spec noFilter (P.launchedAt en inp).initial post)
    (bad : ∀ trace outcome, post trace outcome → ¬ Omni.ExitsIn allowed trace outcome) :
    ¬ nativeX86.haltsMayFail allowed P.snapshot := by
  intro h
  have must := (mustExitIn_mayFail_iff P allowed en inp).mp
    (h en inp (nativeLaunch_valid launch).1 (nativeLaunch_valid launch).2)
  obtain ⟨trace, outcome, finite, satisfied⟩ := exec.realizes
  exact bad trace outcome satisfied (((Omni.mustExitInAt_iff_exec allowed _).mp must).sound finite)

/-- A run at one native launch whose trace is not good (or whose outcome is not an allowed
exit) refutes the extended shape. -/
theorem not_haltsMayFailWith_of_run (P : Probe) {allowed : List Word} {good : List Event → Prop}
    {en : ExecEntry} {inp : ProcInput} (launch : NativeLaunch P en inp) {calls : List Call}
    {trace : List Event} {outcome : Omni.Outcome x86ExtNative}
    (run : Run P.segs spec noFilter (P.launchedAt en inp).initial calls trace outcome)
    (bad : ¬ (Omni.ExitsIn allowed trace outcome ∧ good trace)) :
    ¬ nativeX86.haltsMayFailWith allowed good P.snapshot := by
  intro h
  have exec : Omni.Exec P.segs spec (nativeX86.refusals (some mayFailCfg)) (P.launchedAt en inp).initial
      (fun trace outcome => Omni.ExitsIn allowed trace outcome ∧ good trace) :=
    h en inp (nativeLaunch_valid launch).1 (nativeLaunch_valid launch).2
  rw [nativeX86_refusals_mayFail] at exec
  exact bad (exec.sound run.finite)

/-- At a native launch the entry stack pointer is below `TASK_SIZE_MAX`: the entry block (at
least the 16 `AT_RANDOM` bytes) ends below the task size. -/
theorem NativeLaunch.sp_below {P : Probe} {en : ExecEntry} {inp : ProcInput} (launch : NativeLaunch P en inp) :
    uns en.sp < taskSizeMaxX86 := by
  obtain ⟨_, _, _, _, _, _, _, _, top, _⟩ := launch.entry
  have len : 16 ≤ (stackBytes P.snapshot.image en inp).length := by
    simp only [X86Launch.stackBytes, List.length_append, NativeX86.All.atRandomBytes_length]
    omega
  have taskSize : x86AddressSpace.taskSize = 0x7ffffffff000 := rfl
  have maxSize : taskSizeMaxX86 = 0x7ffffffff000 := by decide
  unfold entryPageTop entryBlockTop pageRoundUp pageSize at top
  rw [taskSize] at top
  rw [maxSize]
  omega

/-- A native launch depends on the probe only through its snapshot. -/
theorem NativeLaunch.transfer {P Q : Probe} {en : ExecEntry} {inp : ProcInput}
    (same : P.snapshot = Q.snapshot) (launch : NativeLaunch P en inp) : NativeLaunch Q en inp := by
  obtain ⟨entry, input, abort⟩ := launch
  rw [same] at entry
  exact ⟨entry, input, abort⟩

/-- The probe's own launch is a native launch when the probe is checked and its input does not
model `abort()`. -/
theorem nativeLaunch_self (P : Probe) [checked : P.Checked] (abort : P.input.abortTerminal = false) :
    NativeLaunch P P.entry P.input :=
  ⟨checked.launched.2, checked.launched.1, abort⟩

end Silmaril.Process.LPS.Probes

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines

namespace Probe

variable (P : Probe) (en : ExecEntry) (inp : ProcInput)

@[simp] theorem launchedAt_fileBytes : (P.launchedAt en inp).fileBytes = P.fileBytes := rfl
@[simp] theorem launchedAt_header : (P.launchedAt en inp).header = P.header := rfl
@[simp] theorem launchedAt_programHeader : (P.launchedAt en inp).programHeader = P.programHeader := rfl
@[simp] theorem launchedAt_base : (P.launchedAt en inp).base = P.base := rfl
@[simp] theorem launchedAt_size : (P.launchedAt en inp).size = P.size := rfl
@[simp] theorem launchedAt_image : (P.launchedAt en inp).image = P.image := rfl
@[simp] theorem launchedAt_segment : (P.launchedAt en inp).segment = P.segment := rfl

end Probe

/-! ## Side conditions at a symbolic launch

The kit's tactics discharge side conditions by `decide +kernel`, which refuses a goal with
free variables. At `P.launchedAt en inp` a byte-level side condition (a decoding, a window
of the segment) mentions the launch only through `launchedAt`; this rule erases it first. It
is tried before the kit's own `probe_side` rules, which remain the fallback. -/
macro_rules
  | `(tactic| probe_side) =>
    `(tactic| (simp only [Probe.launchedAt_bytes, Probe.launchedAt_size, Probe.launchedAt_base,
      Probe.launchedAt_fileBytes, Probe.launchedAt_header, Probe.launchedAt_programHeader,
      Probe.launchedAt_image, Probe.launchedAt_segment, Probe.launchedAt_segs]; decide +kernel))

/-- The entry core at a launch: every register zero but `rsp`, the entry point in `rip`. -/
theorem Probe.core0_launchedAt (P : Probe) (en : ExecEntry) (inp : ProcInput) :
    (P.launchedAt en inp).core0 =
      ({ regs := fun _ => 0, rip := BitVec.ofNat 64 P.image.initPc
         flags := ⟨some false, some false, some false, some false, some false, some false⟩ } :
        Silmaril.X86.State).write .rsp en.sp := rfl

namespace Probe

variable (P : Probe) (core : Silmaril.X86.State) (n : Word)

theorem sysIn_sysno : (P.sysIn core n).sysno = n := rfl
theorem sysInM_sysno (memory : Memory) : (P.sysInM core memory n).sysno = n := rfl
theorem sysInM_arg0 (memory : Memory) : (P.sysInM core memory n).arg 0 = core.read .rdi := rfl
theorem sysInM_arg1 (memory : Memory) : (P.sysInM core memory n).arg 1 = core.read .rsi := rfl
theorem sysInM_arg2 (memory : Memory) : (P.sysInM core memory n).arg 2 = core.read .rdx := rfl
theorem sysInM_arg3 (memory : Memory) : (P.sysInM core memory n).arg 3 = core.read .r10 := rfl
theorem sysIn_arg0 : (P.sysIn core n).arg 0 = core.read .rdi := rfl
theorem sysIn_arg1 : (P.sysIn core n).arg 1 = core.read .rsi := rfl
theorem sysIn_arg2 : (P.sysIn core n).arg 2 = core.read .rdx := rfl
theorem sysIn_arg3 : (P.sysIn core n).arg 3 = core.read .r10 := rfl
theorem sysIn_arg4 : (P.sysIn core n).arg 4 = core.read .r8 := rfl
theorem sysIn_arg5 : (P.sysIn core n).arg 5 = core.read .r9 := rfl

end Probe

/-! ## Addresses below the image and the stack

At a valid launch the stack reservation starts at least `x86LaunchBounds.spWindowLo - 8 MiB`,
so an address below the image and below that bound is mapped by neither region. A channel
write from it reads no byte (`writeSource_launched_low`), whatever the launch. -/

theorem readableBytesAux_none {mp : Word → Option Byte} {a : Word} (none' : mp a = none) (k : Nat) :
    readableBytesAux mp a k = [] := by
  cases k <;> simp [readableBytesAux, none']

theorem Probe.permits_launched_low {P : Probe} {en : ExecEntry} {inp : ProcInput}
    (valid : X86Launch.ValidEntry x86ExtNative P.snapshot en inp) {a : Word}
    (belowImage : a.toNat < P.base)
    (belowStack : (a.toNat : Int) + stackMaxSize < x86LaunchBounds.spWindowLo) :
    (P.launchedAt en inp).mem0.permits .read a.toNat = false := by
  have lo : x86LaunchBounds.spWindowLo ≤ uns en.sp := valid.2.1
  have size : stackMaxSize = 8388608 := by decide
  have sizeNat : stackMaxSize.toNat = 8388608 := by decide
  have window : x86LaunchBounds.spWindowLo = 0x7ffb7fffe000 := by decide
  rw [size, window] at belowStack
  rw [window] at lo
  simp only [uns] at lo
  simp only [Probe.mem0, Probe.launchedAt_segment, Probe.launchedAt_entry,
    Silmaril.Process.Memory.permits, initialMemory, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.any_cons, List.any_nil, Bool.or_false,
    Bool.or_eq_false_iff, Bool.and_eq_false_iff,
    Silmaril.Process.Region.Contains, segmentRegion, sizeNat]
  refine ⟨Or.inl (decide_eq_false ?_), Or.inl (decide_eq_false ?_)⟩
  · intro inside
    exact absurd inside.1 (by change ¬ P.base ≤ a.toNat; omega)
  · intro inside
    have := inside.1
    omega

theorem Probe.viewByte_launched_low {P : Probe} {en : ExecEntry} {inp : ProcInput}
    (valid : X86Launch.ValidEntry x86ExtNative P.snapshot en inp) {a : Word}
    (belowImage : a.toNat < P.base)
    (belowStack : (a.toNat : Int) + stackMaxSize < x86LaunchBounds.spWindowLo) :
    viewByte (P.launchedAt en inp).mem0 .read a = none := by
  have lo : x86LaunchBounds.spWindowLo ≤ uns en.sp := valid.2.1
  have size : stackMaxSize = 8388608 := by decide
  have sizeNat : stackMaxSize.toNat = 8388608 := by decide
  have window : x86LaunchBounds.spWindowLo = 0x7ffb7fffe000 := by decide
  rw [size, window] at belowStack
  rw [window] at lo
  simp only [uns] at lo
  have notPerm : (P.launchedAt en inp).mem0.permits .read a.toNat = false := by
    simp only [Probe.mem0, Probe.launchedAt_segment, Probe.launchedAt_entry,
      Silmaril.Process.Memory.permits, initialMemory, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_false_iff, Bool.and_eq_false_iff,
      Silmaril.Process.Region.Contains, segmentRegion, sizeNat]
    refine ⟨Or.inl (decide_eq_false ?_), Or.inl (decide_eq_false ?_)⟩
    · intro inside
      exact absurd inside.1 (by change ¬ P.base ≤ a.toNat; omega)
    · intro inside
      have := inside.1
      omega
  unfold viewByte
  rw [notPerm]
  rfl

theorem Probe.writeSource_launched_low {P : Probe} {en : ExecEntry} {inp : ProcInput}
    (valid : X86Launch.ValidEntry x86ExtNative P.snapshot en inp)
    (core : Silmaril.X86.State) (n : Word) {buf count : Word}
    (belowImage : buf.toNat < P.base)
    (belowStack : (buf.toNat : Int) + stackMaxSize < x86LaunchBounds.spWindowLo) :
    writeSource ((P.launchedAt en inp).sysIn core n).mem buf count = [] := by
  unfold writeSource readableBytes
  exact readableBytesAux_none (Probe.viewByte_launched_low valid belowImage belowStack) _

/-- Register reads of a core the program built from the entry core, by rewriting. -/
macro "probe_regs" : tactic =>
  `(tactic| simp only [Probe.sysIn_arg0, Probe.sysIn_arg1, Probe.sysIn_arg2, Probe.sysIn_arg3,
      Probe.sysIn_arg4, Probe.sysIn_arg5, Probe.core0_launchedAt, Probe.resume, BitVec.setWidth_eq,
      Probe.sysIn_sysno, Probe.sysInM_sysno, Probe.sysInM_arg0, Probe.sysInM_arg1, Probe.sysInM_arg2,
      Probe.sysInM_arg3, Silmaril.X86.Ext.Sz.read, Silmaril.X86.State.read,
      Silmaril.X86.State.write, Silmaril.X86.Ext.Sz.write, Silmaril.Machine.RegisterFile.write_same,
      Silmaril.Machine.RegisterFile.write_other, ne_eq, reduceCtorEq, not_false_eq_true])

/-- A nonzero register. -/
macro "probe_reg_ne" : tactic => `(tactic| (probe_regs <;> decide +kernel))

/-- The boundary guard is off: every argument register outside the guard window. -/
macro "probe_any_off" : tactic => `(tactic| simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_false_iff])

/-- One argument register outside the guard window: the entry stack pointer by the launch
bound in the context (`NativeLaunch.sp_below`), any other value by evaluation. -/
macro "probe_reg_window" : tactic => `(tactic| first | ((with_reducible show NativeX86.All.inGuardWindow (ExecEntry.sp _) = false); exact Probe.inGuardWindow_of_lt ‹_›) | decide +kernel)

macro "probe_reg_clear" : tactic => `(tactic| (rw [Probe.boundarySuspect_regs] <;> (try probe_any_off) <;> (try probe_regs) <;> (repeat' apply And.intro) <;> probe_reg_window))

/-- A side condition about registers at a symbolic launch: a register is nonzero, or the
hub's boundary guard is off for a pending call. The shape is checked first, at reducible
transparency, so other goals are left to the kit's rules (the rewriting would otherwise
traverse memory terms). -/
macro_rules
  | `(tactic| probe_side) => `(tactic| ((with_reducible show _ ≠ _); probe_reg_ne))

macro_rules
  | `(tactic| probe_side) =>
    `(tactic| ((with_reducible show NativeX86.All.boundarySuspect _ _ = false); probe_reg_clear))

macro_rules
  | `(tactic| probe_side) => `(tactic| ((with_reducible show accessOkbX86 _ _ = true); probe_reg_ne))

/-- A channel write from an address below the image and the stack reads nothing, given the
launch's `ValidEntry` in the context. -/
macro_rules
  | `(tactic| probe_side) => `(tactic| ((with_reducible show writeSource _ _ _ = []); refine Probe.writeSource_launched_low ?_ _ _ ?_ ?_ <;> first | assumption | probe_reg_ne))

macro_rules
  | `(tactic| probe_side) => `(tactic| ((with_reducible show (_ : Word) = _); probe_reg_ne))

macro_rules
  | `(tactic| probe_side) => `(tactic| ((with_reducible show uns _ < _); probe_reg_ne))

macro_rules
  | `(tactic| probe_side) => `(tactic| ((with_reducible show BitVec.toNat _ < _); probe_reg_ne))

macro_rules
  | `(tactic| probe_side) => `(tactic| ((with_reducible show (_ : Bool) = _); probe_reg_ne))

macro_rules
  | `(tactic| probe_side) => `(tactic| ((with_reducible show ((BitVec.toNat _ : Nat) : Int) + _ < _); probe_reg_ne))

end Silmaril.Process.LPS.Probes
