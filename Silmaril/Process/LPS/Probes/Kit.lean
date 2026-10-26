module

public import Silmaril.Process.LPS.Machines.X86LaunchControls
public import Silmaril.Process.LPS.RunHelpers
public import Silmaril.Process.LPS.Sys.FsIo
public import Silmaril.Process.LPS.NativeX86AllControls

/-! # A kit for proofs about tiny static x86-64 ELF probes

A `Probe` is the byte image of a static ELF64 executable with one R+X PT_LOAD of
file offset 0 (the shape `examples/verification-projects/theorem-dev/lps-probes`
builds). `Probe.snapshot` loads exactly those bytes, so the LPS launch of
`Machines.X86Launch` runs the program Linux ran. `Probe.Checked` collects the
decidable layout and launch-validity facts; a probe module proves it with
`probe_checked`.

What Linux did is an `Observed` value generated from the probe's JSON fixture.
The kit states the two positive readings against it:

* `Probe.Admits refused o`: the model has a finite run from the initial
  configuration whose raw syscalls (number, arguments, return) match the
  recorded strace lines, whose events are exactly the recorded output followed
  by the recorded exit, and which ends in the recorded exit status;
* `Probe.Determined refused o`: the universal reading, an `Omni.Exec` proof that
  every maximal execution halts with exactly those events and that status (no
  execution errors, is unmodeled or gets stuck). Probes with nondeterministic
  syscalls instead state an `Omni.Exec` with an explicit list of alternatives.

The symbolic loader rules of `X86LaunchExecution` are generalized: any window of
the loaded segment is fetched or read from the initialized memory without
evaluating the eager 8 MiB stack map (`Probe.mem0_window`,
`Probe.readableBytesAux_mem0`). On top of these, each kind of transition has a
characterization of all its successors (`Probe.sstep_instr_iff`,
`Probe.sstep_trap_iff`, `Probe.sstep_exit_iff`, `Probe.sstep_write_iff`), and
from it an `Omni.Exec` rule and a `Run` rule. The tactics `probe_instr off len`,
`probe_trap off`, `probe_exit status` and `probe_write off count` apply them with the side
conditions discharged by evaluation, so a proof reads as a disassembly listing
of the segment offsets.

The instruction rules over `Probe.cfg` require the memory to stay the initial
memory; the `…M` rules over `Probe.cfgM` take any memory that still holds the
loaded segment (`Probe.Intact`), such as the memory after a `read` into the
stack. All require the model to have no lazy mappings.

The syscall table (`Probes.table`) is the hub's complete native x86-64 table
`NativeX86.All.nativeTable`, with no probe-local arms. Each arm the probes reach
is characterized through `Probes.Dispatches`: off the hub's boundary guard
(`NativeX86.All.boundarySuspect`, a side condition the tactics decide) the
number has exactly the outcomes of the family's x86-64 arm.

An observation may also pin the files the probe leaves behind (`Observed.files`,
compared with the final model's file system by `Observed.Ends`) and the
arguments at which the probe passed its entry stack pointer
(`Observed.stackArgs`), which Linux randomizes.
-/

@[expose] public section
set_option autoImplicit false

/-! ## Generic run facts -/

namespace Silmaril.Process.LPS.Omni

variable {isa : UserIsa} {segs : List Segment} {spec : Sys SyscallEffect}
  {refused : RefusalFilter}

/-- A refusal filter only removes syscall transitions. -/
theorem sstep_noFilter {c : Config isa} {evs : List Event} {target : StepTo isa}
    (step : SStep segs spec refused c evs target) : SStep segs spec noFilter c evs target := by
  cases step with
  | instr a b c => exact .instr a b c
  | instrFault a b c => exact .instrFault a b c
  | instrUnmodeled a b c => exact .instrUnmodeled a b c
  | syscall a b c _ e f => exact .syscall a b c (fun h => h) e f
  | syscallMaterializationFault a b c _ e f => exact .syscallMaterializationFault a b c (fun h => h) e f
  | exit a b c d e => exact .exit a b c d e
  | killed a b c d => exact .killed a b c d
  | syscallUnmodeled a b c => exact .syscallUnmodeled a b c

theorem finiteExec_noFilter {c : Config isa} {trace : List Event} {outcome : Omni.Outcome isa}
    (run : Omni.FiniteExec segs spec refused c trace outcome) :
    Omni.FiniteExec segs spec noFilter c trace outcome := by
  induction run with
  | halt h => exact .halt h
  | error step => exact .error (sstep_noFilter step)
  | next step _ ih => exact .next (sstep_noFilter step) ih

theorem star_noFilter {c c' : Config isa} {trace : List Event}
    (path : Star segs spec refused c trace c') : Star segs spec noFilter c trace c' := by
  induction path with
  | refl => exact .refl _
  | step step _ ih => exact .step (sstep_noFilter step) ih

/-- An execution proof without refusals covers every finite execution under any
refusal filter. -/
theorem Exec.sound_any {c : Config isa} {post : Omni.Post isa} {trace : List Event}
    {outcome : Omni.Outcome isa} (run : Omni.Exec segs spec noFilter c post)
    (finite : Omni.FiniteExec segs spec refused c trace outcome) : post trace outcome :=
  run.sound (finiteExec_noFilter finite)

/-- An execution proof is preserved along any path. -/
theorem Exec.star {c c' : Config isa} {post : Omni.Post isa} {trace : List Event}
    (run : Omni.Exec segs spec refused c post) (path : Star segs spec refused c trace c') :
    Omni.Exec segs spec refused c' (fun rest outcome => post (trace ++ rest) outcome) := by
  induction path generalizing post with
  | refl => exact run.consequence (fun _ _ h => h)
  | step step _ ih =>
    cases run with
    | halt halted _ => exact False.elim (halted (Omni.step_from_running step))
    | step _ _ _ next =>
      exact (ih (next _ _ step)).consequence (fun _ _ h => by simpa only [List.append_assoc] using h)

/-- Every observable trace prefix extends to a trace satisfying the postcondition. -/
theorem Exec.obsTrace {c : Config isa} {post : Omni.Post isa} {trace : List Event}
    (run : Omni.Exec segs spec noFilter c post) (observed : ObsTrace segs spec refused c trace) :
    ∃ rest outcome, trace <+: rest ∧ post rest outcome := by
  obtain ⟨full, final, path, pre⟩ := observed
  obtain ⟨tail, outcome, _, satisfied⟩ := (run.star (star_noFilter path)).realizes
  exact ⟨full ++ tail, outcome, pre.trans (List.prefix_append _ _), satisfied⟩

/-- A postcondition that excludes errors excludes every reachable error transition. -/
theorem Exec.no_error {c : Config isa} {post : Omni.Post isa}
    (run : Omni.Exec segs spec noFilter c post) (noError : ∀ trace final, ¬ post trace (.error final)) :
    ¬ ReachesError segs spec refused c := by
  intro reaches
  obtain ⟨trace, final, finite⟩ := (reachesError_iff_finiteExec c).mp reaches
  exact noError _ _ (run.sound_any finite)

/-- The general step rule: from a characterization of every successor. -/
theorem exec_of_successors {c : Config isa} {post : Omni.Post isa} {α : Type}
    {allowed : α → Prop} {events : α → List Event} {next : α → Config isa}
    (running : c.model.halted = none)
    (successors : ∀ evs target, SStep segs spec refused c evs target ↔
      ∃ x, allowed x ∧ evs = events x ∧ target = .next (next x))
    (inhabited : ∃ x, allowed x)
    (rest : ∀ x, allowed x →
      Omni.Exec segs spec refused (next x) (fun trace outcome => post (events x ++ trace) outcome)) :
    Omni.Exec segs spec refused c post := by
  refine .step running ?_ ?_ ?_
  · obtain ⟨x, hx⟩ := inhabited
    exact ⟨events x, .next (next x), (successors _ _).mpr ⟨x, hx, rfl, rfl⟩⟩
  · intro evs step
    obtain ⟨_, _, _, impossible⟩ := (successors _ _).mp step
    cases impossible
  · intro evs c' step
    obtain ⟨x, hx, rfl, target⟩ := (successors _ _).mp step
    cases target
    exact rest x hx

theorem exec_of_unique {c c' : Config isa} {post : Omni.Post isa} {events : List Event}
    (running : c.model.halted = none)
    (successors : ∀ evs target, SStep segs spec refused c evs target ↔
      evs = events ∧ target = .next c')
    (rest : Omni.Exec segs spec refused c' (fun trace outcome => post (events ++ trace) outcome)) :
    Omni.Exec segs spec refused c post :=
  exec_of_successors (allowed := fun _ : Unit => True) (events := fun _ => events)
    (next := fun _ => c') running
    (fun evs target => by simp only [successors, true_and, exists_const]) ⟨(), trivial⟩
    (fun _ _ => rest)

end Silmaril.Process.LPS.Omni

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines
open Silmaril.Process.LPS.Machines.X86Launch
open Silmaril.Process (Memory Access Region Permissions)

/-! ## What Linux did -/

/-- One strace line: native number, the raw arguments strace printed (as many as
the call takes) and the raw return (`none` for a call that does not return). -/
structure RawSyscall where
  nr : Nat
  args : List Int
  ret : Option Int
  deriving DecidableEq, Repr

inductive ObservedOutcome where
  | exited (status : Nat)
  | killed (signal : Nat)
  deriving DecidableEq, Repr

/-- What a probe did on Linux, as recorded by `lps_probes.py`: the raw syscalls
after its execve, the bytes it read from stdin (the prefix of the declared stdin
that its `read(0, …)` calls returned), the bytes written to stdout and stderr, the
outcome, and the regular files the work directory holds afterwards (except the
probe binary, which the model loads as the image rather than holding it in the file
system). `stackArgs` lists the `(call index, argument index)` pairs at which the
probe passed its entry stack pointer: Linux randomizes that address, so the fixture
records the position, and the model's call must pass the model's entry SP. -/
structure Observed where
  syscalls : List RawSyscall
  stdin : List Byte := []
  stdout : List Byte
  stderr : List Byte
  outcome : ObservedOutcome
  files : Fs.FileSystem := []
  stackArgs : List (Nat × Nat) := []

/-- One syscall of a model run: the pending number, the six argument registers and
the value RAX holds when the call returns (`none` when the run halted in it). -/
structure Call where
  nr : Word
  args : List Word
  ret : Option Word

/-- An observed strace line names the same call: equal number, the printed
arguments are the leading argument registers, and equal raw return. -/
def RawSyscall.Matches (raw : RawSyscall) (call : Call) : Prop :=
  call.nr = BitVec.ofNat 64 raw.nr ∧ raw.args.map (BitVec.ofInt 64) <+: call.args ∧
    call.ret = raw.ret.map (BitVec.ofInt 64)

instance (raw : RawSyscall) (call : Call) : Decidable (raw.Matches call) := by
  unfold RawSyscall.Matches
  infer_instance

/-- The recorded strace lines and the model's calls agree one for one. -/
def RawSyscall.matchesAll : List RawSyscall → List Call → Bool
  | [], [] => true
  | raw :: raws, call :: calls => decide (raw.Matches call) && matchesAll raws calls
  | _, _ => false

/-- The arguments a strace line pins, with the entry stack pointer `sp` at the
positions `stack`. -/
def RawSyscall.expectedArgs (raw : RawSyscall) (sp : Word) (stack : List Nat) : List Word :=
  raw.args.zipIdx.map fun (arg, index) => if index ∈ stack then sp else BitVec.ofInt 64 arg

/-- `Matches`, where the arguments at `stack` are the entry stack pointer `sp`. -/
def RawSyscall.MatchesAt (sp : Word) (stack : List Nat) (raw : RawSyscall) (call : Call) : Prop :=
  call.nr = BitVec.ofNat 64 raw.nr ∧ raw.expectedArgs sp stack <+: call.args ∧
    call.ret = raw.ret.map (BitVec.ofInt 64)

instance (sp : Word) (stack : List Nat) (raw : RawSyscall) (call : Call) :
    Decidable (raw.MatchesAt sp stack call) := by
  unfold RawSyscall.MatchesAt
  infer_instance

/-- The recorded strace lines and the model's calls agree one for one; `stack`
names the entry-stack-pointer arguments by call index (from `index`). -/
def RawSyscall.matchesAllAt (sp : Word) (stack : List (Nat × Nat)) :
    Nat → List RawSyscall → List Call → Bool
  | _, [], [] => true
  | index, raw :: raws, call :: calls =>
    decide (raw.MatchesAt sp ((stack.filter (·.1 == index)).map (·.2)) call) &&
      matchesAllAt sp stack (index + 1) raws calls
  | _, _, _ => false

namespace Observed

variable (o : Observed)

def terminal (fs : Fs.FileSystem) : Event :=
  match o.outcome with
  | .exited status => .exitEv (BitVec.ofNat 64 status) fs
  | .killed signal => .killEv (BitVec.ofNat 64 signal) fs

/-- The LPS events of the observation. All stdin reads are listed before the
writes, and all stdout bytes before stderr bytes; `lps_probes.py` rejects fixtures
whose calls interleave them otherwise. -/
def events (fs : Fs.FileSystem) : List Event :=
  o.stdin.map (.readEv 0) ++ o.stdout.map (.writeEv 1) ++ o.stderr.map (.writeEv 2) ++ [o.terminal fs]

/-- The final configuration's file system is the observed final file system, and
it has the observed outcome. -/
def Ends {isa : UserIsa} (final : Config isa) : Prop :=
  final.model.fs = o.files ∧
    match o.outcome with
    | .exited status => final.model.halted = some (BitVec.ofNat 64 status) ∧ final.model.killedBy = none
    | .killed signal => final.model.killedBy = some (BitVec.ofNat 64 signal)

/-- The model's calls match the recorded raw syscalls, with the entry stack
pointer `sp` at the recorded stack positions. -/
def MatchesCalls (sp : Word) (calls : List Call) : Bool :=
  RawSyscall.matchesAllAt sp o.stackArgs 0 o.syscalls calls

end Observed


/-! ## Runs with their raw syscalls -/

section Runs

variable (segs : List Segment) (spec : Sys SyscallEffect) (refused : RefusalFilter)

/-- The return value RAX holds after a syscall transition, unless it halted. -/
def returned (c : Config x86ExtNative) : Option Word :=
  if c.model.halted.isSome then none else some (c.ms.m.core.read .rax)

/-- A finite execution, together with the syscalls it issued. -/
inductive Run : Config x86ExtNative → List Call → List Event → Omni.Outcome x86ExtNative → Prop where
  | halt {c} : c.model.halted ≠ none → Run c [] [] (.halt c)
  | error {c evs} : SStep segs spec refused c evs .error → Run c [] evs (.error c)
  | instr {c evs c' calls trace outcome} : c.ms.pending = none →
      SStep segs spec refused c evs (.next c') → Run c' calls trace outcome →
      Run c calls (evs ++ trace) outcome
  | sys {c n evs c' calls trace outcome} : c.ms.pending = some n →
      SStep segs spec refused c evs (.next c') → Run c' calls trace outcome →
      Run c (⟨n, x86ExtNative.syscallArgs c.ms, returned c'⟩ :: calls) (evs ++ trace) outcome

variable {segs spec refused}

theorem Run.finite {c : Config x86ExtNative} {calls : List Call} {trace : List Event}
    {outcome : Omni.Outcome x86ExtNative} (run : Run segs spec refused c calls trace outcome) :
    Omni.FiniteExec segs spec refused c trace outcome := by
  induction run with
  | halt h => exact .halt h
  | error step => exact .error step
  | instr _ step _ ih => exact .next step ih
  | sys _ step _ ih => exact .next step ih

theorem Run.star {c : Config x86ExtNative} {calls : List Call} {trace : List Event}
    {final : Config x86ExtNative} (run : Run segs spec refused c calls trace (.halt final)) :
    Star segs spec refused c trace final := by
  generalize result : Omni.Outcome.halt final = outcome at run
  induction run with
  | halt _ => cases result; exact .refl _
  | error _ => cases result
  | instr _ step _ ih => exact .step step (ih result)
  | sys _ step _ ih => exact .step step (ih result)

end Runs

/-! ## Probes -/

/-- `argv[0]` of the harness's execve: `./probe`. -/
def harnessArgv0 : List Byte := [46, 47, 112, 114, 111, 98, 101]

/-- The launch input of the harness: `argv = ["./probe"]`, an empty environment
and empty stdin. Credentials, limits and the remaining environment are those of
the inhabited control input; the probes do not observe them. -/
def harnessInput : ProcInput := { X86Launch.Controls.input with argv := [harnessArgv0] }

/-- The harness launch input with the declared stdin bytes (`inputs.stdinHex`). -/
def harnessInputWith (stdin : List Byte) : ProcInput :=
  { harnessInput with stdin := InputStream.ofList stdin }

theorem harnessInput_valid : X86Launch.ValidInput harnessInput := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold ValidArgv totalArgBytes
      decide +kernel
    · simp [ValidEnvp, harnessInput, X86Launch.Controls.input, totalArgBytes]
    · simp [harnessInput, X86Launch.Controls.input, ProcInput.fs, fsSeedTmp, Fs.ValidFs, Fs.sorted]
    · simp [harnessInput, X86Launch.Controls.input, Fs.KeysRelative]
    · unfold ValidCreds ValidId
      decide +kernel
    · unfold ValidNofile
      decide +kernel
    · unfold ValidSigmask
      decide +kernel
    · intro n
      rfl
  · rfl

/-- The stdin bytes are not constrained by the launch. -/
theorem harnessInputWith_valid (stdin : List Byte) : X86Launch.ValidInput (harnessInputWith stdin) := by
  obtain ⟨⟨argv, envp, fs, keys, creds, nofile, sigmask, urandom⟩, rest⟩ := harnessInput_valid
  exact ⟨⟨argv, envp, fs, keys, creds, nofile, sigmask, urandom⟩, rest⟩

/-- The harness input with the probe's declared input files as the launch file
system (`ProcInput.imageFs`): the files the harness puts in the work directory. -/
def harnessInputFiles (files : Fs.FileSystem) : ProcInput := { harnessInput with imageFs := files }

theorem keysRelative_of_all {files : Fs.FileSystem}
    (relative : files.all (fun pf => pf.1.head? != some Fs.slashByte) = true) :
    Fs.KeysRelative files := by
  intro pf member
  have head := List.all_eq_true.mp relative pf member
  rcases pf with ⟨path, data⟩
  cases path with
  | nil => trivial
  | cons byte rest =>
    simp only [List.head?_cons, bne_iff_ne, ne_eq, Option.some.injEq] at head
    exact head

theorem harnessInputFiles_valid (files : Fs.FileSystem) (valid : Fs.ValidFs files)
    (relative : files.all (fun pf => pf.1.head? != some Fs.slashByte) = true) :
    X86Launch.ValidInput (harnessInputFiles files) := by
  obtain ⟨⟨argv, envp, _, _, creds, nofile, sigmask, urandom⟩, hwcap⟩ := harnessInput_valid
  exact ⟨⟨argv, envp, valid, keysRelative_of_all relative, creds, nofile, sigmask, urandom⟩, hwcap⟩

/-- The syscall table of every probe: the hub's complete native x86-64 table
(`NativeX86.All.nativeTable`). Its ninety reference slots dispatch the families'
x86-64 arms and its extensions the x86-64-only entry points (legacy `open`,
`arch_prctl(ARCH_SET_FS)`, …), every arm under the hub's boundary and
configuration chaos (`NativeX86.All.chaos`). -/
abbrev table : List SpecArm := NativeX86.All.nativeTable

/-- The native x86 syscall table used for every probe. -/
abbrev spec : Sys SyscallEffect := dispatch table

/-! ### Dispatch through the hub table -/

/-- `table` dispatches `number` to the arm specification `f` under the hub's boundary
guard: on a boundary-suspect input (`NativeX86.All.boundarySuspect`) the only
outcome is `unmodeled`, otherwise the outcomes are those of `f`. -/
def Dispatches (number : Nat) (f : SyscallInput → Sys SyscallEffect) : Prop :=
  ∀ input : SyscallInput, input.sysno.toNat = number → ∀ model outcome,
    spec input model outcome ↔
      if NativeX86.All.boundarySuspect number input = true then outcome = .unmodeled
      else f input input model outcome

/-- The chaos form of an arm other than `sigaltstack` (131) and the `do_epoll_wait` arms
(232, 281, 441, whose version chaos is `NativeX86.All.epollOrderChaos`) is its boundary
guard. -/
theorem chaos_arm_spec {number : Nat} {name : String} {f : SyscallInput → Sys SyscallEffect}
    (not131 : number ∉ [131, 232, 281, 441]) (input : SyscallInput) (model : Model) (outcome : Outcome SyscallEffect) :
    (NativeX86.All.chaos (arm number name f)).spec input model outcome ↔
      if NativeX86.All.boundarySuspect number input = true then outcome = .unmodeled
      else f input input model outcome := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at not131
  obtain ⟨n131, n232, n281, n441⟩ := not131
  unfold NativeX86.All.chaos
  rw [NativeX86.All.sigaltstackChaos_other _ n131,
    NativeX86.All.epollOrderChaos_other _ n232 n281 n441]
  exact Iff.rfl

/-- A reference slot dispatches the family's x86-64 arm (`NativeX86.All.dispatch_slot`). -/
theorem dispatches_slot (row : NativeX86.NativeNumber) (mem : row ∈ NativeX86.numbers)
    {f : SyscallInput → Sys SyscallEffect}
    (family : lookupArm familyX86Arms row.nativeNo = some (arm row.nativeNo row.name f))
    (not131 : row.nativeNo ∉ [131, 232, 281, 441]) : Dispatches row.nativeNo f := by
  intro input sysno model outcome
  exact (NativeX86.All.Controls.dispatch_slot row mem _ family input sysno model outcome).trans
    (chaos_arm_spec not131 input model outcome)

/-- An x86-64-only entry point (`NativeX86.All.extensionArms`) dispatches its arm. -/
theorem dispatches_extension {number : Nat} {name : String} {f : SyscallInput → Sys SyscallEffect}
    (lookup : lookupArm NativeX86.All.extensionArms number = some (arm number name f))
    (not131 : number ∉ [131, 232, 281, 441]) : Dispatches number f := by
  intro input sysno model outcome
  have found : lookupArm table number = some (NativeX86.All.chaos (arm number name f)) := by
    rw [table, NativeX86.All.nativeTable_eq, NativeX86.All.lookupArm_append,
      NativeX86.All.lookupArm_map _ NativeX86.All.chaos_no, lookup]
    rfl
  simp only [spec, dispatch, sysno, found]
  exact chaos_arm_spec not131 input model outcome

/-- Off the boundary, a dispatched number has exactly the outcomes of its arm. -/
theorem Dispatches.spec_iff {number : Nat} {f : SyscallInput → Sys SyscallEffect}
    (dispatches : Dispatches number f) {input : SyscallInput} (sysno : input.sysno.toNat = number)
    (clear : NativeX86.All.boundarySuspect number input = false) (model : Model)
    (outcome : Outcome SyscallEffect) :
    spec input model outcome ↔ f input input model outcome := by
  rw [dispatches input sysno model outcome]
  simp only [clear, Bool.false_eq_true, ↓reduceIte]

/-- On the boundary, a dispatched number is only `unmodeled`. -/
theorem Dispatches.suspect_iff {number : Nat} {f : SyscallInput → Sys SyscallEffect}
    (dispatches : Dispatches number f) {input : SyscallInput} (sysno : input.sysno.toNat = number)
    (suspect : NativeX86.All.boundarySuspect number input = true) (model : Model)
    (outcome : Outcome SyscallEffect) :
    spec input model outcome ↔ outcome = .unmodeled := by
  rw [dispatches input sysno model outcome]
  simp only [suspect, ↓reduceIte]

theorem dispatches_read :
    Dispatches 0 (fun i => readSpecX86 (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)) :=
  dispatches_slot ⟨63, 0, "read"⟩ (by decide) rfl (by decide)

theorem dispatches_write :
    Dispatches 1 (fun i => writeSpecX86 (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)) :=
  dispatches_slot ⟨64, 1, "write"⟩ (by decide) rfl (by decide)

theorem dispatches_close : Dispatches 3 (fun i => closeSpec (fd32 (i.arg 0))) :=
  dispatches_slot ⟨57, 3, "close"⟩ (by decide) rfl (by decide)

theorem dispatches_exit : Dispatches 60 (fun i => exitSpec (i.arg 0)) :=
  dispatches_slot ⟨93, 60, "exit"⟩ (by decide) rfl (by decide)

theorem dispatches_exit_group : Dispatches 231 (fun i => exitSpec (i.arg 0)) :=
  dispatches_slot ⟨94, 231, "exit_group"⟩ (by decide) rfl (by decide)

theorem dispatches_openat :
    Dispatches 257 (fun i => openatSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2)) :=
  dispatches_slot ⟨56, 257, "openat"⟩ (by decide) rfl (by decide)

/-- Legacy x86-64 `open` (2) is an extension arm of the hub table. -/
theorem dispatches_open : Dispatches 2 (fun i => openSpecX86 (i.arg 0) (i.arg 1)) :=
  dispatches_extension (name := "open") rfl (by decide)

/-- The bytes of a probe ELF with its parsed header and single program header. -/
structure Probe where
  fileBytes : List Byte
  header : Silmaril.Formats.ELF.Header
  programHeader : Silmaril.Formats.ELF.ProgramHeader
  input : ProcInput := harnessInput
  entry : ExecEntry := X86Launch.Controls.entry

namespace Probe

variable (P : Probe)

def base : Nat := P.programHeader.virtualAddress
def size : Nat := P.programHeader.memorySize
/-- The loaded bytes: the file prefix the PT_LOAD maps (its file offset is 0). -/
def bytes : List Byte := P.fileBytes.take P.programHeader.fileSize

/-- The segment permissions: `rwx` for a writable image (`PF_R|PF_W|PF_X`, the
`"image": "rwx"` probes that read into a buffer of their own image), else `rx`. -/
def perms : String := if P.programHeader.flags = 7 then "rwx" else "rx"

def segment : Segment := ⟨P.base, P.size, P.perms, P.bytes⟩

def image : Image :=
  ⟨[P.segment], P.header.entry,
    ⟨P.base + P.header.programOffset, P.header.programEntrySize, P.header.programCount⟩⟩

def snapshot : Snapshot := ⟨P.header, [P.programHeader], P.image⟩

abbrev segs : List Segment := P.image.segments

def stack : List Byte := entryStack P.image P.entry P.input

/-- The initialized memory, kept symbolic. -/
def mem0 : Memory := initialMemory [P.segment] P.entry.sp P.stack

def initial : Config x86ExtNative := init x86ExtNative P.snapshot P.entry sourceAllocLimit P.input

/-- The actual LPS behaviour of the launched probe. -/
def behavior (refused : RefusalFilter) : Behavior :=
  X86Launch.runWith x86ExtNative spec refused P.snapshot sourceAllocLimit P.entry P.input

/-- A configuration over the initial memory. -/
abbrev cfg (core : Silmaril.X86.State) (pending : Option Word) (model : Model) : Config x86ExtNative :=
  ⟨⟨⟨core, P.mem0⟩, pending⟩, model⟩

/-- A configuration over any memory. -/
abbrev cfgM (core : Silmaril.X86.State) (memory : Memory) (pending : Option Word) (model : Model) :
    Config x86ExtNative :=
  ⟨⟨⟨core, memory⟩, pending⟩, model⟩

/-- A memory that still holds the loaded segment: its region and its bytes. -/
structure Intact (memory : Memory) : Prop where
  region : segmentRegion P.segment ∈ memory.regions
  installed : ∀ index (bound : index < P.bytes.length),
    memory.bytes.get? (P.base + index) = some P.bytes[index]

def core0 : Silmaril.X86.State := P.initial.ms.m.core
def model0 : Model := P.initial.model

theorem initial_at : P.initial = P.cfg P.core0 none P.model0 := rfl

theorem behavior_initial (refused : RefusalFilter) :
    P.behavior refused = runWithStack x86ExtNative entryStack spec refused P.image sourceAllocLimit
      P.entry P.input := rfl

theorem installWrapping_nil (memory : Silmaril.Process.ByteMemory) (base : Nat) :
    installWrapping memory base [] = memory := rfl

theorem initialMemory_zero_bytes (segment : Segment) :
    (initialMemory [segment] 0 []).bytes = installWrapping ∅ segment.base segment.bytes := by
  have zero : (0 : Word).toNat = 0 := rfl
  simp only [initialMemory, List.foldl_cons, List.foldl_nil, zero, Nat.zero_sub, Nat.sub_zero,
    List.replicate_zero, installWrapping_nil]

theorem segment_readable : P.segment.readable = true := by
  show P.perms.contains 'r' = true
  unfold perms; split <;> simp
theorem segment_writable : P.segment.writable = decide (P.programHeader.flags = 7) := by
  show P.perms.contains 'w' = _
  unfold perms; split <;> simp [*]
theorem segment_executable : P.segment.executable = true := by
  show P.perms.contains 'x' = true
  unfold perms; split <;> simp

/-- The loaded segment is readable and executable (and writable for an `rwx` image). -/
theorem segmentPermissions_allows (access : Access) (notWrite : access ≠ .write) :
    (segmentPermissions P.segment).allows access = true := by
  cases access with
  | read => simp [segmentPermissions, Permissions.allows, P.segment_readable]
  | write => exact absurd rfl notWrite
  | execute => simp [segmentPermissions, Permissions.allows, P.segment_executable]

/-- The segment offset of the entry point. -/
def entryOffset : Nat := P.header.entry - P.base

/-- Some instruction of at most 15 bytes decodes at `offset` inside the segment. -/
def decodesAt (offset : Nat) : Bool :=
  (List.range 16).any fun length =>
    decide (offset + length ≤ P.size) &&
      match Silmaril.X86.Ext.decode ((P.bytes.drop offset).take length) with
      | some (_, decoded) => decoded == length
      | none => false

/-- `memoryRead` of the image, with the segment's permission string evaluated. -/
def imageRead (address : Word) (length : Nat) : Option (List Byte) :=
  if (P.base : Int) ≤ uns address ∧ uns address + length ≤ P.base + P.size then
    (List.range length).mapM fun k => P.segment.byteAt ((uns address - P.base).toNat + k)
  else none

theorem memoryRead_image (address : Word) (length : Nat) :
    memoryRead P.segs address length = P.imageRead address length := by
  unfold memoryRead imageRead
  simp only [segs, image, findSegment]
  by_cases inside : (P.base : Int) ≤ uns address ∧ uns address + length ≤ P.base + P.size
  · have inside' : (P.segment.base : Int) ≤ uns address ∧
        uns address + length ≤ P.segment.base + P.segment.size := inside
    rw [ite_eq_left inside', ite_eq_left inside]
    simp only [P.segment_readable, ite_true]
    rfl
  · have outside : ¬ ((P.segment.base : Int) ≤ uns address ∧
        uns address + length ≤ P.segment.base + P.segment.size) := inside
    rw [ite_eq_right outside, ite_eq_right inside]

/-- The decidable facts the kit relies on; `probe_layout` proves them. The ELF
header and program header are those the Lean ELF reader parses from the bytes. -/
structure Layout : Prop where
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
  belowStack : P.base + P.size ≤ P.entry.sp.toNat - stackMaxSize.toNat
  stackFits : P.entry.sp.toNat + P.stack.length ≤ 2 ^ 64
  entryInside : P.base ≤ P.header.entry
  entryBelow : P.entryOffset < P.size
  entryDecodes : P.decodesAt P.entryOffset = true
  programHeadersRead :
    (P.imageRead (zw P.image.phdrs.addr) (P.image.phdrs.num * P.image.phdrs.ent)).isSome = true

/-! ### Reading the loaded segment -/

section Window

variable {P} (memory : Memory) (region : segmentRegion P.segment ∈ memory.regions)
  (installed : ∀ index (bound : index < P.bytes.length),
    memory.bytes.get? (P.base + index) = some P.bytes[index])

include region in
theorem permits_of_allows (access : Access)
    (allowed : (segmentPermissions P.segment).allows access = true) (address : Nat)
    (lower : P.base ≤ address) (upper : address < P.base + P.size) :
    memory.permits access address = true := by
  unfold Memory.permits
  rw [List.any_eq_true]
  refine ⟨_, region, ?_⟩
  rw [segmentRegion, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨lower, upper⟩, allowed⟩

include region in
theorem permits_of (access : Access) (notWrite : access ≠ .write) (address : Nat)
    (lower : P.base ≤ address) (upper : address < P.base + P.size) :
    memory.permits access address = true :=
  permits_of_allows memory region access (P.segmentPermissions_allows access notWrite) address lower upper

include region installed in
theorem readWith_of (layout : P.Layout) (access : Access) (notWrite : access ≠ .write) :
    memory.readWith access P.base P.size = some P.bytes := by
  have sizes := layout.sizes
  have fits := layout.belowStack
  have bounded := P.entry.sp.isLt
  have read := Memory.readWith_eq memory access P.base P.bytes ?_ installed
  · rwa [sizes] at read
  · change memory.checkSpan access P.base P.bytes.length = true
    rw [Memory.checkSpan_iff]
    refine ⟨by unfold Silmaril.Process.addressLimit; omega,
      by unfold Silmaril.Process.addressLimit; omega, ?_⟩
    intro offset bound
    exact permits_of memory region access notWrite _ (by omega) (by omega)

include region installed in
theorem window_of (layout : P.Layout) (access : Access) (notWrite : access ≠ .write)
    (offset length : Nat) (start : offset < P.size) (fits : offset + length ≤ P.size) :
    memory.readWith access (P.base + offset) length = some ((P.bytes.drop offset).take length) :=
  Memory.readWith_sub_range (readWith_of memory region installed layout access notWrite) start fits

end Window

theorem size_lt (layout : P.Layout) : P.base + P.size < 2 ^ 64 := by
  have := layout.belowStack
  have := P.entry.sp.isLt
  omega

/-- The image as the launch's entry check sees it: no stack. -/
abbrev memZero : Memory := initialMemory [P.segment] 0 []

theorem memZero_get (layout : P.Layout) (index : Nat) (bound : index < P.bytes.length) :
    P.memZero.bytes.get? (P.base + index) = some P.bytes[index] := by
  have sizes := layout.sizes
  have fits := P.size_lt layout
  rw [initialMemory_zero_bytes]
  exact installWrapping_get ∅ P.base P.bytes index bound (show P.base + P.bytes.length ≤ 2 ^ 64 by omega)

theorem memZero_region : segmentRegion P.segment ∈ P.memZero.regions := by
  simp [initialMemory]

theorem entryFetchable (layout : P.Layout) :
    x86ExtNative.entryFetchable P.segs P.image.initPc = true := by
  obtain ⟨length, _, ok⟩ := List.any_eq_true.mp layout.entryDecodes
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨fits, decodes⟩ := ok
  have entry := layout.entryInside
  have start := layout.entryBelow
  have pc : P.image.initPc = P.base + P.entryOffset := by
    simp only [image, entryOffset]
    omega
  split at decodes
  · next instruction decoded window =>
    have same : decoded = length := by simpa using decodes
    subst same
    have read := window_of P.memZero P.memZero_region (P.memZero_get layout) layout .execute
      (by decide) P.entryOffset decoded start fits
    have fetched := Silmaril.X86.Ext.fetch_eq_decoded_iff.mpr
      ⟨_, (show P.memZero.fetchBytes P.image.initPc decoded = _ by rw [pc]; exact read), window⟩
    change (match Silmaril.X86.Ext.fetch (initialMemory P.segs 0 []) P.image.initPc with
      | .decoded _ _ => true
      | _ => decide ((initialMemory P.segs 0 []).fetchBytes P.image.initPc 2 =
        some [0x0f, 0x05])) = true
    rw [show initialMemory P.segs 0 [] = P.memZero from rfl, fetched]
  · cases decodes

theorem snapshot_valid (layout : P.Layout) : ValidSnapshot x86ExtNative P.snapshot := by
  refine ⟨layout.headerMatches, ?_, ?_, List.pairwise_singleton _ _, P.entryFetchable layout, ?_⟩
  · have program : ProgramHeaderMatches P.programHeader P.segment := by
      refine ⟨layout.load, rfl, rfl, by rw [layout.fileBacked], ?_, ?_, ?_⟩ <;>
        rcases layout.readExecute with flags | flags <;>
          simp [flags, P.segment_readable, P.segment_writable, P.segment_executable]
    constructor
    · intro segment member
      simp only [snapshot, image, List.mem_singleton] at member
      exact ⟨P.programHeader, List.mem_singleton_self _, member ▸ program⟩
    · intro ph member _
      simp only [snapshot, List.mem_singleton] at member
      exact ⟨P.segment, List.mem_singleton_self _, member ▸ program⟩
  · intro segment member
    simp only [snapshot, image, List.mem_singleton] at member
    subst member
    exact ⟨layout.sizes, layout.positive, layout.taskBound⟩
  · change (memoryRead P.segs _ _).isSome = true
    rw [memoryRead_image]
    exact layout.programHeadersRead

class Checked : Prop where
  layout : Layout P
  /-- The probe is a valid static launch: the kit cannot prove facts about an
  ELF the launch would reject. -/
  launched : X86Launch.ValidInput P.input ∧ X86Launch.ValidEntry x86ExtNative P.snapshot P.entry P.input

theorem launch [checked : Checked P] :
    Launched x86ExtNative P.snapshot P.entry sourceAllocLimit P.input P.initial :=
  ⟨checked.launched.1, checked.launched.2, rfl⟩

section Memory

variable [checked : Checked P]

omit checked in
theorem mem0_region : segmentRegion P.segment ∈ P.mem0.regions := by
  simp [mem0, initialMemory]

theorem mem0_get (index : Nat) (bound : index < P.bytes.length) :
    P.mem0.bytes.get? (P.base + index) = some P.bytes[index] := by
  have sizes := checked.layout.sizes
  have below := checked.layout.belowStack
  rw [mem0, initialMemory_below_stack_get _ _ _ _ (by omega) checked.layout.stackFits]
  exact P.memZero_get checked.layout index bound

omit checked in
theorem mem0_permits (access : Access) (notWrite : access ≠ .write) (address : Nat)
    (lower : P.base ≤ address) (upper : address < P.base + P.size) :
    P.mem0.permits access address = true :=
  permits_of P.mem0 P.mem0_region access notWrite address lower upper

/-- Any window of the loaded segment, from the actual initialized memory. -/
theorem mem0_window (access : Access) (notWrite : access ≠ .write) (offset length : Nat)
    (start : offset < P.size) (fits : offset + length ≤ P.size) :
    P.mem0.readWith access (P.base + offset) length =
      some ((P.bytes.drop offset).take length) :=
  window_of P.mem0 P.mem0_region P.mem0_get checked.layout access notWrite offset length start fits

theorem mem0_view (offset : Nat) (bound : offset < P.size) :
    viewByte P.mem0 .read (BitVec.ofNat 64 (P.base + offset)) = P.bytes[offset]? := by
  have sizes := checked.layout.sizes
  have fits := P.size_lt checked.layout
  have toNat : (BitVec.ofNat 64 (P.base + offset)).toNat = P.base + offset := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  unfold viewByte
  rw [toNat, P.mem0_permits .read (by decide) _ (by omega) (by omega)]
  simp only [ite_true]
  rw [← Std.ExtHashMap.get?_eq_getElem?, P.mem0_get offset (by omega),
    List.getElem?_eq_getElem (by omega)]

/-- The bytes a syscall reads from the probe image through the read view. -/
theorem readableBytesAux_mem0 (offset count : Nat) (fits : offset + count ≤ P.size) :
    readableBytesAux (viewByte P.mem0 .read) (BitVec.ofNat 64 (P.base + offset)) count =
      (P.bytes.drop offset).take count := by
  have sizes := checked.layout.sizes
  induction count generalizing offset with
  | zero => simp [readableBytesAux]
  | succ count ih =>
    have bound : offset < P.bytes.length := by omega
    simp only [readableBytesAux]
    rw [P.mem0_view offset (by omega), List.getElem?_eq_getElem bound]
    simp only
    have next : BitVec.ofNat 64 (P.base + offset) + 1 = BitVec.ofNat 64 (P.base + (offset + 1)) := by
      rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    rw [next, ih (offset + 1) (by omega), List.drop_eq_getElem_cons bound]
    rfl

end Memory

/-! ## Transition rules -/

section Rules

variable {refused : RefusalFilter}

/-- The core after returning from a syscall with `ret` (RAX), as `x86AdvancePastSvc`
leaves it: RCX holds the return address and R11 the RFLAGS image. -/
def resume (core : Silmaril.X86.State) (ret : Word) : Silmaril.X86.State :=
  let written := core.write .rax ret
  { ((written.write .rcx (core.rip + 2)).write .r11 ((rflagsImage core.flags).getD 0)) with
    rip := core.rip + 2 }

theorem resume_effect (core : Silmaril.X86.State) (n : Word) (other : n ≠ 158) (ret : Word)
    (copyins : List (Word × Nat)) :
    x86ExtNative.advancePastSvc (x86ExtNative.applyEffect ⟨⟨core, P.mem0⟩, some n⟩
      ((mkEffect ret [] []).withCopyins copyins)) = ⟨⟨resume core ret, P.mem0⟩, none⟩ := by
  have notArch : ¬ (some n = some (158 : Word) ∧ core.read .rdi = 0x1002 ∧ ret = 0) :=
    fun h => other (Option.some.inj h.1)
  change x86AdvancePastSvc (x86ApplyEffectNative ⟨⟨core, P.mem0⟩, some n⟩ _) = _
  unfold x86ApplyEffectNative
  split
  · next h => exact absurd h notArch
  · rfl

theorem accountStep_instr [Checked P] {off len : Nat} {instruction : Silmaril.X86.Ext.Instr}
    {core core' : Silmaril.X86.State} {model : Model} (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (fits : off + len ≤ P.size) (two : off + 2 ≤ P.size)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core P.mem0 len = .ok core' P.mem0) :
    accountStep x86ExtNative P.segs ⟨⟨core, P.mem0⟩, none⟩ model =
      .ok (⟨⟨core', P.mem0⟩, none⟩, model) := by
  have fetched := P.mem0_window .execute (by decide) off len (by omega) fits
  have prefix2 := P.mem0_window .execute (by decide) off 2 (by omega) two
  apply Progress.accountStep_of_noLazy _ _ model _ lazy
  change x86NativeStep ⟨⟨core, P.mem0⟩, none⟩ = _
  rw [x86NativeStep_of_fetch (s := ⟨⟨core, P.mem0⟩, none⟩)
    (show P.mem0.fetchBytes core.rip.toNat 2 ≠ some [0x0f, 0x05] by
      rw [rip, Memory.fetchBytes, prefix2]
      exact fun h => notSyscall (Option.some.inj h))
    (show P.mem0.fetchBytes core.rip.toNat len = some _ by rw [rip, Memory.fetchBytes, fetched])
    decoded]
  change x86ExecResult _ (Silmaril.X86.Ext.exec instruction core P.mem0 len) = _
  rw [exec]
  rfl

/-- An ordinary instruction at segment offset `off` has exactly one successor. -/
theorem sstep_instr_iff [Checked P] {off len : Nat} {instruction : Silmaril.X86.Ext.Instr}
    {core core' : Silmaril.X86.State} {model : Model}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (fits : off + len ≤ P.size) (two : off + 2 ≤ P.size)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core P.mem0 len = .ok core' P.mem0)
    (evs : List Event) (target : StepTo x86ExtNative) :
    SStep P.segs spec refused (P.cfg core none model) evs target ↔
      evs = [] ∧ target = .next (P.cfg core' none model) := by
  have account := P.accountStep_instr lazy rip fits two notSyscall decoded exec
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

/-- `syscall` at offset `off` traps with the pending number from RAX. -/
theorem sstep_trap_iff [Checked P] {off : Nat} {core : Silmaril.X86.State} {model : Model}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (two : off + 2 ≤ P.size)
    (isSyscall : (P.bytes.drop off).take 2 = [0x0f, 0x05])
    (defined : (rflagsImage core.flags).isSome = true)
    (evs : List Event) (target : StepTo x86ExtNative) :
    SStep P.segs spec refused (P.cfg core none model) evs target ↔
      evs = [] ∧ target = .next (P.cfg core (some (core.read .rax)) model) := by
  have prefix2 := P.mem0_window .execute (by decide) off 2 (by omega) two
  have account : accountStep x86ExtNative P.segs ⟨⟨core, P.mem0⟩, none⟩ model =
      .ok (⟨⟨core, P.mem0⟩, some (core.read .rax)⟩, model) := by
    apply Progress.accountStep_of_noLazy _ _ model _ lazy
    exact x86NativeStep_syscall ⟨⟨core, P.mem0⟩, none⟩
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

/-- The syscall input of a pending configuration. -/
abbrev sysIn (core : Silmaril.X86.State) (n : Word) : SyscallInput :=
  sysInput x86ExtNative P.segs (⟨⟨core, P.mem0⟩, some n⟩ : X86State) n

/-- At a number without constant-size pointer arguments the hub's boundary guard
reads only the six argument registers. -/
theorem boundarySuspect_regs {num : Nat} (noConst : NativeX86.All.constPtrArgs num = [])
    (core : Silmaril.X86.State) (memory : Memory) (n : Word) :
    NativeX86.All.boundarySuspect num
        (sysInput x86ExtNative P.segs (⟨⟨core, memory⟩, some n⟩ : X86State) n) =
      [Silmaril.X86.Reg.rdi, .rsi, .rdx, .r10, .r8, .r9].any
        (fun r => NativeX86.All.inGuardWindow (core.read r)) := by
  unfold NativeX86.All.boundarySuspect
  rw [noConst, List.any_nil, Bool.or_false]
  rfl

/-- A register value below `TASK_SIZE_MAX` is outside the guard window. -/
theorem inGuardWindow_of_lt {w : Word} (below : uns w < taskSizeMaxX86) :
    NativeX86.All.inGuardWindow w = false := by
  unfold NativeX86.All.inGuardWindow
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Int.not_le]
  exact Or.inl below

/-- A pending call whose only outcome halts normally. -/
theorem sstep_halt_iff {core : Silmaril.X86.State} {n : Word} {model model' : Model}
    {effect : SyscallEffect} {code : Word} (running : model.halted = none)
    (outcomes : ∀ outcome, spec (P.sysIn core n) model outcome ↔ outcome = .ok effect model' [])
    (halted : model'.halted = some code) (unkilled : model'.killedBy = none)
    (evs : List Event) (target : StepTo x86ExtNative) :
    SStep P.segs spec refused (P.cfg core (some n) model) evs target ↔
      evs = [.exitEv code model'.fs] ∧ target = .next (P.cfg core (some n) model') := by
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

/-- A pending call whose outcomes return to the program with an unchanged model. -/
theorem sstep_return_iff {core : Silmaril.X86.State} {n : Word} {model : Model}
    {α : Type} {allowed : α → Prop} {ret : α → Word} {copyins : α → List (Word × Nat)}
    {events : α → List Event} (other : n ≠ 158)
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (outcomes : ∀ outcome, spec (P.sysIn core n) model outcome ↔
      ∃ x, allowed x ∧ outcome = .ok ((mkEffect (ret x) [] []).withCopyins (copyins x)) model (events x))
    (evs : List Event) (target : StepTo x86ExtNative) :
    SStep P.segs spec refused (P.cfg core (some n) model) evs target ↔
      ∃ x, (allowed x ∧ ¬ refused (P.sysIn core n) model
          ((mkEffect (ret x) [] []).withCopyins (copyins x))) ∧
        evs = events x ∧ target = .next (P.cfg (resume core (ret x)) none model) := by
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
      rw [P.resume_effect core n other]
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
      have : model.killedBy = none := by simp [Model.killedBy, Model.halted] at running ⊢; simp [running]
      rw [this] at k
      cases k
    | syscallUnmodeled _ p s =>
      cases p
      obtain ⟨x, _, same⟩ := (outcomes _).mp s
      cases same
  · rintro ⟨x, ⟨hx, notRefused⟩, rfl, rfl⟩
    have step := SStep.syscall (segs := P.segs) (spec := spec) (refused := refused)
      (isa := x86ExtNative) (x8 := n)
      (ms := (⟨⟨core, P.mem0⟩, some n⟩ : X86State)) running rfl ((outcomes _).mpr ⟨x, hx, rfl⟩)
      notRefused running (materialized _)
    rwa [P.resume_effect core n other] at step

/-! ### Native syscall outcomes -/

theorem native_exit_iff (input : SyscallInput) (model : Model) (outcome : Outcome SyscallEffect)
    (number : input.sysno = 60) (clear : NativeX86.All.boundarySuspect 60 input = false) :
    spec input model outcome ↔
      outcome = .ok (mkEffect 0 [] []) (model.withHalted (input.arg 0 &&& 255)) [] := by
  rw [dispatches_exit.spec_iff (by rw [number]; rfl) clear model outcome]
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

/-- `exit` (60) halts with the low byte of RDI, from any running model, off the
hub's boundary guard. -/
theorem sstep_exit_iff {core : Silmaril.X86.State} {model : Model} (running : model.halted = none)
    (clear : NativeX86.All.boundarySuspect 60 (P.sysIn core 60) = false)
    (evs : List Event) (target : StepTo x86ExtNative) :
    SStep P.segs spec refused (P.cfg core (some 60) model) evs target ↔
      evs = [.exitEv (core.read .rdi &&& 255) model.fs] ∧
        target = .next (P.cfg core (some 60) (model.withHalted (core.read .rdi &&& 255))) :=
  P.sstep_halt_iff running (fun outcome => native_exit_iff _ model outcome rfl clear) rfl
    (by simp [Model.killedBy, Model.withHalted]) evs target

/-- LPS `write` on a channel descriptor (`Sys/Fs/ReadWrite.v` `write_spec`, the
channel branch), over any `access_ok` predicate `ok`: the environment delivers any
nonempty prefix of the readable source bytes, up to the clamped count; the events
are the delivered bytes. -/
theorem write_channel_iff (ok : Word → Int → Bool) (input : SyscallInput) (model : Model)
    (outcome : Outcome SyscallEffect)
    {ch : Word} (lookup : fdLookup model.fds (fd32 (input.arg 0)) = some (.channel ch))
    (nonzero : ch ≠ 0) (modeled : modeledRwRangeWith ok (input.arg 1) (input.arg 2) = true)
    (count : input.arg 2 ≠ 0) {bs : List Byte}
    (source : writeSource input.mem (input.arg 1) (input.arg 2) = bs) (nonempty : bs ≠ []) :
    writeSpecWith ok (fd32 (input.arg 0)) (input.arg 1) (input.arg 2) input model outcome ↔
      ∃ ds : List Byte, (1 ≤ ds.length ∧ (ds.length : Int) ≤ rwCountClamp (input.arg 2) ∧
          ds = bs.take ds.length) ∧
        outcome = .ok ((mkEffect (lenWord ds) [] []).withCopyins [(input.arg 1, ds.length)]) model
          (ds.map (.writeEv ch)) := by
  have zeroCh : wIs0 ch = false := by simpa [wIs0] using nonzero
  have zeroCount : wIs0 (input.arg 2) = false := by simpa [wIs0] using count
  cases outcome with
  | ok effect model' evs =>
    simp [writeSpecWith, bind, Sys.bind, Sys.input, Sys.getModel, lookup, zeroCh, modeled, zeroCount,
      source, Sys.choose, Sys.emit, recordCopyins, Sys.pure, retOnly, nonempty, mkEffect,
      SyscallEffect.withCopyins]
    exact exists_congr fun _ => and_congr_right fun _ =>
      ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨b, a, c⟩, fun ⟨b, a, c⟩ => ⟨⟨a, b⟩, c⟩⟩
  | unmodeled =>
    simp [writeSpecWith, bind, Sys.bind, Sys.input, Sys.getModel, lookup, zeroCh, modeled, zeroCount,
      source, Sys.choose, Sys.emit, recordCopyins, Sys.pure, retOnly, nonempty, mkEffect,
      SyscallEffect.withCopyins]

/-- Native `write` (1) to a channel: the family's x86-64 `write`, LPS `write_spec`
with x86-64 `access_ok`. -/
theorem native_write_iff (input : SyscallInput) (model : Model) (outcome : Outcome SyscallEffect)
    (number : input.sysno = 1) (clear : NativeX86.All.boundarySuspect 1 input = false) {ch : Word}
    (lookup : fdLookup model.fds (fd32 (input.arg 0)) = some (.channel ch))
    (nonzero : ch ≠ 0) (modeled : modeledRwRangeWith accessOkbX86 (input.arg 1) (input.arg 2) = true)
    (count : input.arg 2 ≠ 0) {bs : List Byte}
    (source : writeSource input.mem (input.arg 1) (input.arg 2) = bs) (nonempty : bs ≠ []) :
    spec input model outcome ↔
      ∃ ds : List Byte, (1 ≤ ds.length ∧ (ds.length : Int) ≤ rwCountClamp (input.arg 2) ∧
          ds = bs.take ds.length) ∧
        outcome = .ok ((mkEffect (lenWord ds) [] []).withCopyins [(input.arg 1, ds.length)]) model
          (ds.map (.writeEv ch)) := by
  rw [dispatches_write.spec_iff (by rw [number]; rfl) clear model outcome]
  exact write_channel_iff accessOkbX86 input model outcome lookup nonzero modeled count source nonempty

/-- The reference-sanctioned results of a channel write of `bs`: any nonempty
prefix may be delivered (a short write returns fewer bytes than requested). -/
def WritePrefix (bs ds : List Byte) : Prop := ds ≠ [] ∧ ds <+: bs

instance (bs ds : List Byte) : Decidable (WritePrefix bs ds) := by
  unfold WritePrefix
  infer_instance

theorem writePrefix_iff {bs ds : List Byte} {count : Int} (bounded : (bs.length : Int) ≤ count) :
    (1 ≤ ds.length ∧ (ds.length : Int) ≤ count ∧ ds = bs.take ds.length) ↔ WritePrefix bs ds := by
  constructor
  · rintro ⟨positive, _, taken⟩
    refine ⟨fun empty => by simp [empty] at positive, ?_⟩
    rw [taken]
    exact List.take_prefix _ _
  · rintro ⟨nonempty, pre⟩
    have length := pre.length_le
    refine ⟨List.length_pos_iff.mpr nonempty, by omega, (List.prefix_iff_eq_take.mp pre)⟩

/-- `write` (1) of `count` image bytes at segment offset `off` to a channel. -/
theorem sstep_write_iff [checked : Checked P] {core : Silmaril.X86.State} {n : Word} {model : Model}
    {off count : Nat} {ch : Word} (number : n = 1)
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (lookup : fdLookup model.fds (fd32 (core.read .rdi)) = some (.channel ch)) (nonzero : ch ≠ 0)
    (buffer : core.read .rsi = BitVec.ofNat 64 (P.base + off))
    (modeled : modeledRwRangeWith accessOkbX86 (core.read .rsi) (core.read .rdx) = true)
    (nonzeroCount : core.read .rdx ≠ 0)
    (clear : NativeX86.All.boundarySuspect 1 (P.sysIn core n) = false)
    (clamp : rwCountClamp (core.read .rdx) = count) (clampWord : (zw (rwCountClamp (core.read .rdx))).toNat = count)
    (fits : off + count ≤ P.size) (nonempty : (P.bytes.drop off).take count ≠ [])
    (evs : List Event) (target : StepTo x86ExtNative) :
    SStep P.segs spec refused (P.cfg core (some n) model) evs target ↔
      ∃ ds, (WritePrefix ((P.bytes.drop off).take count) ds ∧ ¬ refused (P.sysIn core n) model
          ((mkEffect (lenWord ds) [] []).withCopyins [(core.read .rsi, ds.length)])) ∧
        evs = ds.map (.writeEv ch) ∧ target = .next (P.cfg (resume core (lenWord ds)) none model) := by
  subst number
  have bounded : (((P.bytes.drop off).take count).length : Int) ≤ rwCountClamp (core.read .rdx) := by
    rw [clamp]
    simp only [List.length_take]
    omega
  refine P.sstep_return_iff (allowed := WritePrefix ((P.bytes.drop off).take count))
    (by decide) running lazy (fun outcome => ?_) evs target
  refine (native_write_iff (P.sysIn core 1) model outcome rfl clear lookup nonzero modeled nonzeroCount
    (bs := (P.bytes.drop off).take count) ?_ nonempty).trans ?_
  · change readableBytesAux (viewByte P.mem0 .read) (core.read .rsi)
      (zw (rwCountClamp (core.read .rdx))).toNat = _
    rw [clampWord, buffer]
    exact P.readableBytesAux_mem0 off count fits
  · exact exists_congr fun ds => and_congr_left fun _ => writePrefix_iff bounded

theorem returned_resume {core : Silmaril.X86.State} {model : Model} (ret : Word)
    (running : model.halted = none) :
    returned (P.cfg (resume core ret) none model) = some ret := by
  simp [returned, running, resume]

/-! ### Execution rules -/

theorem exec_instr {checked : Checked P} {post : Omni.Post x86ExtNative} {off len : Nat}
    {instruction : Silmaril.X86.Ext.Instr} {core core' : Silmaril.X86.State} {model : Model}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (fits : off + len ≤ P.size) (two : off + 2 ≤ P.size)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core P.mem0 len = .ok core' P.mem0)
    (rest : Omni.Exec P.segs spec refused (P.cfg core' none model) post) :
    Omni.Exec P.segs spec refused (P.cfg core none model) post :=
  Omni.exec_of_unique running (P.sstep_instr_iff running lazy rip fits two notSyscall decoded exec) rest

theorem exec_trap {checked : Checked P} {post : Omni.Post x86ExtNative} {off : Nat}
    {core : Silmaril.X86.State} {model : Model}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (two : off + 2 ≤ P.size)
    (isSyscall : (P.bytes.drop off).take 2 = [0x0f, 0x05])
    (defined : (rflagsImage core.flags).isSome = true)
    (rest : Omni.Exec P.segs spec refused (P.cfg core (some (core.read .rax)) model) post) :
    Omni.Exec P.segs spec refused (P.cfg core none model) post :=
  Omni.exec_of_unique running (P.sstep_trap_iff running lazy rip two isSyscall defined) rest

theorem exec_exit {post : Omni.Post x86ExtNative} {core : Silmaril.X86.State} {n status : Word}
    {model : Model} (number : n = 60) (rdi : core.read .rdi = status) (running : model.halted = none)
    (clear : NativeX86.All.boundarySuspect 60 (P.sysIn core n) = false)
    (done : post [.exitEv (status &&& 255) model.fs]
      (.halt (P.cfg core (some n) (model.withHalted (status &&& 255))))) :
    Omni.Exec P.segs spec refused (P.cfg core (some n) model) post := by
  subst number rdi
  refine Omni.exec_of_unique running (P.sstep_exit_iff running clear) (.halt (by simp [Model.withHalted, Model.halted]) ?_)
  simpa only [List.append_nil] using done

theorem exec_write {checked : Checked P} {post : Omni.Post x86ExtNative} {core : Silmaril.X86.State}
    {n : Word} {model : Model} {off count : Nat} {ch : Word} (number : n = 1)
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (lookup : fdLookup model.fds (fd32 (core.read .rdi)) = some (.channel ch)) (nonzero : ch ≠ 0)
    (buffer : core.read .rsi = BitVec.ofNat 64 (P.base + off))
    (modeled : modeledRwRangeWith accessOkbX86 (core.read .rsi) (core.read .rdx) = true)
    (nonzeroCount : core.read .rdx ≠ 0)
    (clear : NativeX86.All.boundarySuspect 1 (P.sysIn core n) = false)
    (clamp : rwCountClamp (core.read .rdx) = count) (clampWord : (zw (rwCountClamp (core.read .rdx))).toNat = count)
    (fits : off + count ≤ P.size) (nonempty : (P.bytes.drop off).take count ≠ [])
    (rest : ∀ ds, WritePrefix ((P.bytes.drop off).take count) ds →
      Omni.Exec P.segs spec noFilter (P.cfg (resume core (lenWord ds)) none model)
        (fun trace outcome => post (ds.map (.writeEv ch) ++ trace) outcome)) :
    Omni.Exec P.segs spec noFilter (P.cfg core (some n) model) post :=
  Omni.exec_of_successors running
    (P.sstep_write_iff number running lazy lookup nonzero buffer modeled nonzeroCount clear clamp clampWord
      fits nonempty)
    ⟨_, ⟨nonempty, List.prefix_refl _⟩, fun h => h⟩ (fun ds allowed => rest ds allowed.1)

/-! ### Run rules -/

theorem run_instr {checked : Checked P} {off len : Nat} {instruction : Silmaril.X86.Ext.Instr}
    {core core' : Silmaril.X86.State} {model : Model} {calls : List Call} {trace : List Event}
    {outcome : Omni.Outcome x86ExtNative}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (fits : off + len ≤ P.size) (two : off + 2 ≤ P.size)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core P.mem0 len = .ok core' P.mem0)
    (rest : Run P.segs spec refused (P.cfg core' none model) calls trace outcome) :
    Run P.segs spec refused (P.cfg core none model) calls trace outcome :=
  .instr rfl ((P.sstep_instr_iff running lazy rip fits two notSyscall decoded exec _ _).mpr
    ⟨rfl, rfl⟩) rest

theorem run_trap {checked : Checked P} {off : Nat} {core : Silmaril.X86.State} {model : Model}
    {calls : List Call} {trace : List Event} {outcome : Omni.Outcome x86ExtNative}
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (two : off + 2 ≤ P.size)
    (isSyscall : (P.bytes.drop off).take 2 = [0x0f, 0x05])
    (defined : (rflagsImage core.flags).isSome = true)
    (rest : Run P.segs spec refused (P.cfg core (some (core.read .rax)) model) calls trace outcome) :
    Run P.segs spec refused (P.cfg core none model) calls trace outcome :=
  .instr rfl ((P.sstep_trap_iff running lazy rip two isSyscall defined _ _).mpr ⟨rfl, rfl⟩) rest

theorem run_exit {core : Silmaril.X86.State} {n status : Word} {model : Model} (number : n = 60)
    (rdi : core.read .rdi = status) (running : model.halted = none)
    (clear : NativeX86.All.boundarySuspect 60 (P.sysIn core n) = false) :
    Run P.segs spec refused (P.cfg core (some n) model)
      [⟨n, x86ExtNative.syscallArgs (⟨⟨core, P.mem0⟩, some n⟩ : X86State), none⟩]
      [.exitEv (status &&& 255) model.fs]
      (.halt (P.cfg core (some n) (model.withHalted (status &&& 255)))) := by
  subst number rdi
  exact .sys rfl ((P.sstep_exit_iff running clear _ _).mpr ⟨rfl, rfl⟩)
    (.halt (by simp [Model.withHalted, Model.halted]))

theorem run_write {checked : Checked P} {core : Silmaril.X86.State} {n : Word} {model : Model}
    {off count : Nat} {ch : Word} {calls : List Call} {trace : List Event}
    {outcome : Omni.Outcome x86ExtNative} (number : n = 1)
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (lookup : fdLookup model.fds (fd32 (core.read .rdi)) = some (.channel ch)) (nonzero : ch ≠ 0)
    (buffer : core.read .rsi = BitVec.ofNat 64 (P.base + off))
    (modeled : modeledRwRangeWith accessOkbX86 (core.read .rsi) (core.read .rdx) = true)
    (nonzeroCount : core.read .rdx ≠ 0)
    (clear : NativeX86.All.boundarySuspect 1 (P.sysIn core n) = false)
    (clamp : rwCountClamp (core.read .rdx) = count) (clampWord : (zw (rwCountClamp (core.read .rdx))).toNat = count)
    (fits : off + count ≤ P.size) (nonempty : (P.bytes.drop off).take count ≠ [])
    (ds : List Byte) (delivered : WritePrefix ((P.bytes.drop off).take count) ds)
    (accepted : ¬ refused (P.sysIn core n) model
      ((mkEffect (lenWord ds) [] []).withCopyins [(core.read .rsi, ds.length)]))
    (rest : Run P.segs spec refused (P.cfg (resume core (lenWord ds)) none model) calls trace outcome) :
    Run P.segs spec refused (P.cfg core (some n) model)
      (⟨n, x86ExtNative.syscallArgs (⟨⟨core, P.mem0⟩, some n⟩ : X86State), some (lenWord ds)⟩ :: calls)
      (ds.map (.writeEv ch) ++ trace) outcome :=
  P.returned_resume (lenWord ds) running ▸
    .sys rfl ((P.sstep_write_iff number running lazy lookup nonzero buffer modeled nonzeroCount clear clamp
      clampWord fits nonempty _ _).mpr ⟨ds, ⟨delivered, accepted⟩, rfl, rfl⟩) rest

end Rules

/-! ### Configurations over any memory that holds the image

After a `read` into the stack the memory is no longer `P.mem0`. The `…M` rules
below take any memory that still holds the loaded segment (`Intact`); the
instruction fetches and image reads are the same windows. -/

theorem intact_mem0 [Checked P] : P.Intact P.mem0 := ⟨P.mem0_region, P.mem0_get⟩

section IntactMemory

variable {P} [checked : Checked P] {memory : Memory}

theorem Intact.window (intact : P.Intact memory) (access : Access) (notWrite : access ≠ .write)
    (offset length : Nat) (start : offset < P.size) (fits : offset + length ≤ P.size) :
    memory.readWith access (P.base + offset) length = some ((P.bytes.drop offset).take length) :=
  window_of memory intact.region intact.installed checked.layout access notWrite offset length start fits

theorem Intact.view (intact : P.Intact memory) (offset : Nat) (bound : offset < P.size) :
    viewByte memory .read (BitVec.ofNat 64 (P.base + offset)) = P.bytes[offset]? := by
  have sizes := checked.layout.sizes
  have fits := P.size_lt checked.layout
  have toNat : (BitVec.ofNat 64 (P.base + offset)).toNat = P.base + offset := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  unfold viewByte
  rw [toNat, permits_of memory intact.region .read (by decide) _ (by omega) (by omega)]
  simp only [ite_true]
  rw [← Std.ExtHashMap.get?_eq_getElem?, intact.installed offset (by omega),
    List.getElem?_eq_getElem (by omega)]

/-- The bytes a syscall reads from the probe image through the read view. -/
theorem Intact.readable (intact : P.Intact memory) (offset count : Nat)
    (fits : offset + count ≤ P.size) :
    readableBytesAux (viewByte memory .read) (BitVec.ofNat 64 (P.base + offset)) count =
      (P.bytes.drop offset).take count := by
  have sizes := checked.layout.sizes
  induction count generalizing offset with
  | zero => simp [readableBytesAux]
  | succ count ih =>
    have bound : offset < P.bytes.length := by omega
    simp only [readableBytesAux]
    rw [intact.view offset (by omega), List.getElem?_eq_getElem bound]
    simp only
    have next : BitVec.ofNat 64 (P.base + offset) + 1 = BitVec.ofNat 64 (P.base + (offset + 1)) := by
      rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    rw [next, ih (offset + 1) (by omega), List.drop_eq_getElem_cons bound]
    rfl

end IntactMemory

section RulesM

variable {refused : RefusalFilter} {memory : Memory}

theorem accountStep_instrM [Checked P] {off len : Nat} {instruction : Silmaril.X86.Ext.Instr}
    {core core' : Silmaril.X86.State} {model : Model} (intact : P.Intact memory)
    (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (fits : off + len ≤ P.size) (two : off + 2 ≤ P.size)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core memory len = .ok core' memory) :
    accountStep x86ExtNative P.segs ⟨⟨core, memory⟩, none⟩ model =
      .ok (⟨⟨core', memory⟩, none⟩, model) := by
  have fetched := intact.window .execute (by decide) off len (by omega) fits
  have prefix2 := intact.window .execute (by decide) off 2 (by omega) two
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

/-- An ordinary instruction at segment offset `off` has exactly one successor. -/
theorem sstep_instr_iffM [Checked P] {off len : Nat} {instruction : Silmaril.X86.Ext.Instr}
    {core core' : Silmaril.X86.State} {model : Model} (intact : P.Intact memory)
    (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (fits : off + len ≤ P.size) (two : off + 2 ≤ P.size)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core memory len = .ok core' memory)
    (evs : List Event) (target : StepTo x86ExtNative) :
    SStep P.segs spec refused (cfgM core memory none model) evs target ↔
      evs = [] ∧ target = .next (cfgM core' memory none model) := by
  have account := P.accountStep_instrM intact lazy rip fits two notSyscall decoded exec
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

/-- `syscall` at offset `off` traps with the pending number from RAX. -/
theorem sstep_trap_iffM [Checked P] {off : Nat} {core : Silmaril.X86.State} {model : Model}
    (intact : P.Intact memory) (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (two : off + 2 ≤ P.size)
    (isSyscall : (P.bytes.drop off).take 2 = [0x0f, 0x05])
    (defined : (rflagsImage core.flags).isSome = true)
    (evs : List Event) (target : StepTo x86ExtNative) :
    SStep P.segs spec refused (cfgM core memory none model) evs target ↔
      evs = [] ∧ target = .next (cfgM core memory (some (core.read .rax)) model) := by
  have prefix2 := intact.window .execute (by decide) off 2 (by omega) two
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

/-- The syscall input of a pending configuration over `memory`. -/
abbrev sysInM (core : Silmaril.X86.State) (memory : Memory) (n : Word) : SyscallInput :=
  sysInput x86ExtNative P.segs (⟨⟨core, memory⟩, some n⟩ : X86State) n

theorem resume_effectM (core : Silmaril.X86.State) (memory : Memory) (n : Word) (other : n ≠ 158)
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

theorem killedBy_of_halted {model : Model} (running : model.halted = none) :
    model.killedBy = none := by
  unfold Model.killedBy
  unfold Model.halted at running
  split <;> simp [running]

/-- A pending call whose outcomes (indexed by `α`) all return to the program:
each changes the model to `model' x`, applies `effect x` to the memory (giving
`memory' x`) and emits `events x`. -/
theorem sstep_sys_iff {core : Silmaril.X86.State} {n : Word} {model : Model}
    {α : Type} {allowed : α → Prop} {effect : α → SyscallEffect} {model' : α → Model}
    {events : α → List Event} {memory' : α → Memory} (other : n ≠ 158)
    (running : model.halted = none)
    (outcomes : ∀ outcome, spec (P.sysInM core memory n) model outcome ↔
      ∃ x, allowed x ∧ outcome = .ok (effect x) (model' x) (events x))
    (live : ∀ x, allowed x → (model' x).halted = none)
    (lazy : ∀ x, allowed x → (model' x).vmLazy = [])
    (applied : ∀ x, allowed x → applyMemoryEffect memory (effect x) = memory' x)
    (evs : List Event) (target : StepTo x86ExtNative) :
    SStep P.segs spec refused (cfgM core memory (some n) model) evs target ↔
      ∃ x, (allowed x ∧ ¬ refused (P.sysInM core memory n) model (effect x)) ∧
        evs = events x ∧
        target = .next (cfgM (resume core (effect x).ret) (memory' x) none (model' x)) := by
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
      rw [Progress.materializeModelAccesses_noLazy _ _ (lazy x hx)] at m
      cases m
      refine ⟨x, ⟨hx, notRefused⟩, rfl, ?_⟩
      rw [resume_effectM core memory n other, applied x hx]
    | syscallMaterializationFault _ p s _ _ m =>
      cases p
      obtain ⟨x, hx, same⟩ := (outcomes _).mp s
      cases same
      rw [Progress.materializeModelAccesses_noLazy _ _ (lazy x hx)] at m
      cases m
    | exit _ p s h _ =>
      cases p
      obtain ⟨x, hx, same⟩ := (outcomes _).mp s
      cases same
      rw [live x hx] at h
      cases h
    | killed _ p s k =>
      cases p
      obtain ⟨x, hx, same⟩ := (outcomes _).mp s
      cases same
      rw [killedBy_of_halted (live x hx)] at k
      cases k
    | syscallUnmodeled _ p s =>
      cases p
      obtain ⟨x, _, same⟩ := (outcomes _).mp s
      cases same
  · rintro ⟨x, ⟨hx, notRefused⟩, rfl, rfl⟩
    have step := SStep.syscall (segs := P.segs) (spec := spec) (refused := refused)
      (isa := x86ExtNative) (x8 := n)
      (ms := (⟨⟨core, memory⟩, some n⟩ : X86State)) running rfl ((outcomes _).mpr ⟨x, hx, rfl⟩)
      notRefused (live x hx) (Progress.materializeModelAccesses_noLazy _ _ (lazy x hx))
    rwa [resume_effectM core memory n other, applied x hx] at step

/-- A pending call whose only outcome halts normally. -/
theorem sstep_halt_iffM {core : Silmaril.X86.State} {n : Word} {model model' : Model}
    {effect : SyscallEffect} {code : Word} (running : model.halted = none)
    (outcomes : ∀ outcome, spec (P.sysInM core memory n) model outcome ↔
      outcome = .ok effect model' [])
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

theorem sstep_exit_iffM {core : Silmaril.X86.State} {model : Model} (running : model.halted = none)
    (clear : NativeX86.All.boundarySuspect 60 (P.sysInM core memory 60) = false)
    (evs : List Event) (target : StepTo x86ExtNative) :
    SStep P.segs spec refused (cfgM core memory (some 60) model) evs target ↔
      evs = [.exitEv (core.read .rdi &&& 255) model.fs] ∧
        target = .next (cfgM core memory (some 60) (model.withHalted (core.read .rdi &&& 255))) :=
  P.sstep_halt_iffM running (fun outcome => native_exit_iff _ model outcome rfl clear) rfl
    (by simp [Model.killedBy, Model.withHalted]) evs target

theorem returned_resumeM {core : Silmaril.X86.State} {model : Model} (ret : Word)
    (running : model.halted = none) :
    returned (cfgM (resume core ret) memory none model) = some ret := by
  simp [returned, running, resume]

/-! ### Execution and run rules over any intact memory -/

theorem exec_instrM [Checked P] {post : Omni.Post x86ExtNative} {off len : Nat}
    {instruction : Silmaril.X86.Ext.Instr} {core core' : Silmaril.X86.State} {model : Model}
    (intact : P.Intact memory) (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (fits : off + len ≤ P.size) (two : off + 2 ≤ P.size)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core memory len = .ok core' memory)
    (rest : Omni.Exec P.segs spec refused (cfgM core' memory none model) post) :
    Omni.Exec P.segs spec refused (cfgM core memory none model) post :=
  Omni.exec_of_unique running
    (P.sstep_instr_iffM intact running lazy rip fits two notSyscall decoded exec) rest

theorem exec_trapM [Checked P] {post : Omni.Post x86ExtNative} {off : Nat}
    {core : Silmaril.X86.State} {model : Model}
    (intact : P.Intact memory) (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (two : off + 2 ≤ P.size)
    (isSyscall : (P.bytes.drop off).take 2 = [0x0f, 0x05])
    (defined : (rflagsImage core.flags).isSome = true)
    (rest : Omni.Exec P.segs spec refused (cfgM core memory (some (core.read .rax)) model) post) :
    Omni.Exec P.segs spec refused (cfgM core memory none model) post :=
  Omni.exec_of_unique running (P.sstep_trap_iffM intact running lazy rip two isSyscall defined) rest

theorem exec_exitM {post : Omni.Post x86ExtNative} {core : Silmaril.X86.State} {n status : Word}
    {model : Model} (number : n = 60) (rdi : core.read .rdi = status) (running : model.halted = none)
    (clear : NativeX86.All.boundarySuspect 60 (P.sysInM core memory n) = false)
    (done : post [.exitEv (status &&& 255) model.fs]
      (.halt (cfgM core memory (some n) (model.withHalted (status &&& 255))))) :
    Omni.Exec P.segs spec refused (cfgM core memory (some n) model) post := by
  subst number rdi
  refine Omni.exec_of_unique running (P.sstep_exit_iffM running clear)
    (.halt (by simp [Model.withHalted, Model.halted]) ?_)
  simpa only [List.append_nil] using done

/-- A pending call with the outcomes of `sstep_sys_iff`, for every reference
alternative (no refusals). -/
theorem exec_sys {post : Omni.Post x86ExtNative} {core : Silmaril.X86.State} {n : Word}
    {model : Model} {α : Type} {allowed : α → Prop} {effect : α → SyscallEffect}
    {model' : α → Model} {events : α → List Event} {memory' : α → Memory} (other : n ≠ 158)
    (running : model.halted = none)
    (outcomes : ∀ outcome, spec (P.sysInM core memory n) model outcome ↔
      ∃ x, allowed x ∧ outcome = .ok (effect x) (model' x) (events x))
    (live : ∀ x, allowed x → (model' x).halted = none)
    (lazy : ∀ x, allowed x → (model' x).vmLazy = [])
    (applied : ∀ x, allowed x → applyMemoryEffect memory (effect x) = memory' x)
    (inhabited : ∃ x, allowed x)
    (rest : ∀ x, allowed x →
      Omni.Exec P.segs spec noFilter (cfgM (resume core (effect x).ret) (memory' x) none (model' x))
        (fun trace outcome => post (events x ++ trace) outcome)) :
    Omni.Exec P.segs spec noFilter (cfgM core memory (some n) model) post :=
  Omni.exec_of_successors running (P.sstep_sys_iff other running outcomes live lazy applied)
    (by obtain ⟨x, hx⟩ := inhabited; exact ⟨x, hx, fun h => h⟩) (fun x allowedX => rest x allowedX.1)

theorem run_instrM [Checked P] {off len : Nat} {instruction : Silmaril.X86.Ext.Instr}
    {core core' : Silmaril.X86.State} {model : Model} {calls : List Call} {trace : List Event}
    {outcome : Omni.Outcome x86ExtNative}
    (intact : P.Intact memory) (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (fits : off + len ≤ P.size) (two : off + 2 ≤ P.size)
    (notSyscall : (P.bytes.drop off).take 2 ≠ [0x0f, 0x05])
    (decoded : Silmaril.X86.Ext.decode ((P.bytes.drop off).take len) = some (instruction, len))
    (exec : Silmaril.X86.Ext.exec instruction core memory len = .ok core' memory)
    (rest : Run P.segs spec refused (cfgM core' memory none model) calls trace outcome) :
    Run P.segs spec refused (cfgM core memory none model) calls trace outcome :=
  .instr rfl ((P.sstep_instr_iffM intact running lazy rip fits two notSyscall decoded exec _ _).mpr
    ⟨rfl, rfl⟩) rest

theorem run_trapM [Checked P] {off : Nat} {core : Silmaril.X86.State} {model : Model}
    {calls : List Call} {trace : List Event} {outcome : Omni.Outcome x86ExtNative}
    (intact : P.Intact memory) (running : model.halted = none) (lazy : model.vmLazy = [])
    (rip : core.rip.toNat = P.base + off) (two : off + 2 ≤ P.size)
    (isSyscall : (P.bytes.drop off).take 2 = [0x0f, 0x05])
    (defined : (rflagsImage core.flags).isSome = true)
    (rest : Run P.segs spec refused (cfgM core memory (some (core.read .rax)) model) calls trace
      outcome) :
    Run P.segs spec refused (cfgM core memory none model) calls trace outcome :=
  .instr rfl ((P.sstep_trap_iffM intact running lazy rip two isSyscall defined _ _).mpr ⟨rfl, rfl⟩) rest

theorem run_exitM {core : Silmaril.X86.State} {n status : Word} {model : Model} (number : n = 60)
    (rdi : core.read .rdi = status) (running : model.halted = none)
    (clear : NativeX86.All.boundarySuspect 60 (P.sysInM core memory n) = false) :
    Run P.segs spec refused (cfgM core memory (some n) model)
      [⟨n, x86ExtNative.syscallArgs (⟨⟨core, memory⟩, some n⟩ : X86State), none⟩]
      [.exitEv (status &&& 255) model.fs]
      (.halt (cfgM core memory (some n) (model.withHalted (status &&& 255)))) := by
  subst number rdi
  exact .sys rfl ((P.sstep_exit_iffM running clear _ _).mpr ⟨rfl, rfl⟩)
    (.halt (by simp [Model.withHalted, Model.halted]))

/-- The run through one chosen alternative `x` of a pending call. -/
theorem run_sys {core : Silmaril.X86.State} {n : Word} {model : Model} {α : Type}
    {allowed : α → Prop} {effect : α → SyscallEffect} {model' : α → Model}
    {events : α → List Event} {memory' : α → Memory} {calls : List Call} {trace : List Event}
    {outcome : Omni.Outcome x86ExtNative} (other : n ≠ 158)
    (running : model.halted = none)
    (outcomes : ∀ outcome, spec (P.sysInM core memory n) model outcome ↔
      ∃ x, allowed x ∧ outcome = .ok (effect x) (model' x) (events x))
    (live : ∀ x, allowed x → (model' x).halted = none)
    (lazy : ∀ x, allowed x → (model' x).vmLazy = [])
    (applied : ∀ x, allowed x → applyMemoryEffect memory (effect x) = memory' x)
    (x : α) (chosen : allowed x)
    (accepted : ¬ refused (P.sysInM core memory n) model (effect x))
    (rest : Run P.segs spec refused (cfgM (resume core (effect x).ret) (memory' x) none (model' x))
      calls trace outcome) :
    Run P.segs spec refused (cfgM core memory (some n) model)
      (⟨n, x86ExtNative.syscallArgs (⟨⟨core, memory⟩, some n⟩ : X86State), some (effect x).ret⟩ ::
        calls) (events x ++ trace) outcome := by
  have ret := returned_resumeM (core := core) (memory := memory' x) (effect x).ret (live x chosen)
  rw [← ret]
  exact .sys rfl ((P.sstep_sys_iff other running outcomes live lazy applied _ _).mpr
    ⟨x, ⟨chosen, accepted⟩, rfl, rfl⟩) rest

end RulesM


/-! ## Linux observations as statements about the launched probe -/

section Observations

variable {refused : RefusalFilter} {o o' : Observed}

/-- Reality is admitted: some finite run from the initial configuration issues the
recorded raw syscalls, emits exactly the recorded output followed by the recorded
exit, and ends with the recorded outcome. -/
def Admits (refused : RefusalFilter) (o : Observed) : Prop :=
  ∃ calls trace final, Run P.segs spec refused P.initial calls trace (.halt final) ∧
    o.MatchesCalls P.entry.sp calls = true ∧ trace = o.events final.model.fs ∧ o.Ends final

/-- Build an admission from a run; `apply` it and prove the run (goal `run`)
first, the remaining goals are then closed by evaluation (`probe_sides`). -/
theorem admits_of {calls : List Call} {trace : List Event} {final : Config x86ExtNative}
    (run : Run P.segs spec refused P.initial calls trace (.halt final))
    (raw : o.MatchesCalls P.entry.sp calls = true)
    (events : trace = o.events final.model.fs) (ends : o.Ends final) : P.Admits refused o :=
  ⟨calls, trace, final, run, raw, events, ends⟩

/-- The postcondition of a probe whose run is determined by the observation. -/
def Exactly (o : Observed) : Omni.Post x86ExtNative := fun trace outcome =>
  ∃ final, outcome = .halt final ∧ trace = o.events final.model.fs ∧ o.Ends final

/-- The universal reading: every maximal execution (none errors, is unmodeled or
gets stuck) halts with exactly the recorded events and outcome. -/
def Determined (refused : RefusalFilter) (o : Observed) : Prop :=
  Omni.Exec P.segs spec refused P.initial (Exactly o)

theorem Admits.traces (admits : P.Admits refused o) :
    ∃ fs, (P.behavior refused).traces (o.events fs) := by
  obtain ⟨_, _, final, run, _, rfl, _⟩ := admits
  exact ⟨final.model.fs, _, final, run.star, List.prefix_refl _⟩

theorem Determined.sound (determined : P.Determined refused o) {trace : List Event}
    {outcome : Omni.Outcome x86ExtNative}
    (finite : Omni.FiniteExec P.segs spec refused P.initial trace outcome) : Exactly o trace outcome :=
  Omni.Exec.sound determined finite

theorem Determined.admits_events (determined : P.Determined refused o) :
    ∃ trace outcome, Omni.FiniteExec P.segs spec refused P.initial trace outcome ∧
      Exactly o trace outcome :=
  Omni.Exec.realizes determined

/-- An unmodeled step is an error transition. -/
theorem unmodeled_reachesError {isa : UserIsa} {segs : List Segment} {sp : Sys SyscallEffect}
    {c : Config isa} (reaches : ReachesUnmodeled segs sp refused c) : ReachesError segs sp refused c := by
  obtain ⟨trace, final, path, running, cases⟩ := reaches
  rcases cases with ⟨pending, account⟩ | ⟨n, pending, unmodeled⟩
  · exact ⟨trace, final, [], path, .instrUnmodeled running pending account⟩
  · exact ⟨trace, final, [], path, .syscallUnmodeled running pending unmodeled⟩

theorem Determined.no_error (determined : P.Determined noFilter o) :
    ¬ (P.behavior refused).errors :=
  Omni.Exec.no_error determined (fun _ _ ⟨_, impossible, _⟩ => by cases impossible)

theorem Determined.no_unmodeled (determined : P.Determined noFilter o) :
    ¬ (P.behavior refused).unmodeled :=
  fun reaches => Determined.no_error P determined (unmodeled_reachesError reaches)

/-- A mutant refutes the original's universal claim as soon as it admits a
run whose events differ. -/
theorem not_determined_of_admits (admits : P.Admits refused o')
    (differ : ∀ fs fs', o'.events fs ≠ o.events fs') : ¬ P.Determined refused o := by
  intro determined
  obtain ⟨_, _, final, run, _, rfl, _⟩ := admits
  obtain ⟨final', _, same, _⟩ := Omni.Exec.sound determined run.finite
  exact differ _ _ same

end Observations

end Probe

/-! ## Tactics

Each rule tactic takes the segment offset of the instruction (and its length and
decoded form), applies the rule, and discharges the side conditions by
evaluation. It leaves the goal for the rest of the program. -/

/-- The hub's boundary guard is off for the pending call: by evaluation, or
register by register (`Probe.boundarySuspect_regs`), with a hypothesis bounding a
symbolic register below `TASK_SIZE_MAX`. -/
macro "probe_clear_eval" : tactic =>
  `(tactic| first
    | decide +kernel
    | rfl
    | (rw [Probe.boundarySuspect_regs _ (by decide +kernel)]
       simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_false_iff]
       (repeat' apply And.intro) <;>
         first | rfl | decide +kernel | (apply Probe.inGuardWindow_of_lt; assumption)))

/-- `probe_clear_eval` on a goal `boundarySuspect _ _ = false` only. -/
macro "probe_clear" : tactic =>
  `(tactic| (show NativeX86.All.boundarySuspect _ _ = false; probe_clear_eval))

/-- Evaluation of a side condition: closed decidable facts by `decide +kernel`,
the remaining definitional ones (with symbolic syscall results) by `rfl`. -/
macro "probe_side" : tactic =>
  `(tactic| first
    | decide +kernel
    | rfl
    | decide
    | exact inferInstance
    | exact ⟨rfl, rfl⟩
    | exact ⟨rfl, rfl, rfl⟩
    | exact fun h => h
    | assumption
    | exact Probe.intact_mem0 _
    | probe_clear)

/-- Close every side goal that evaluation decides, leaving the continuation. -/
macro "probe_sides" : tactic => `(tactic| all_goals try probe_side)

/-- `probe_instr off len instr`: the instruction `instr` of `len` bytes at
segment offset `off`. -/
macro "probe_instr " off:term:max len:term:max instr:term:max : tactic =>
  `(tactic| (first
    | apply Probe.exec_instr _ (off := $off) (len := $len) (instruction := $instr)
    | apply Probe.run_instr _ (off := $off) (len := $len) (instruction := $instr)
    | apply Probe.exec_instrM _ (off := $off) (len := $len) (instruction := $instr)
    | apply Probe.run_instrM _ (off := $off) (len := $len) (instruction := $instr)) <;> probe_sides)

/-- `probe_trap off`: the `syscall` instruction at segment offset `off`. -/
macro "probe_trap " off:term:max : tactic =>
  `(tactic| (first
    | apply Probe.exec_trap _ (off := $off)
    | apply Probe.run_trap _ (off := $off)
    | apply Probe.exec_trapM _ (off := $off)
    | apply Probe.run_trapM _ (off := $off)) <;> probe_sides)

/-- `probe_exit status`: the pending native `exit` halts the run; `status` is the
value of RDI (the low byte is the exit status). -/
macro "probe_exit " status:term:max : tactic =>
  `(tactic| (first
    | apply Probe.exec_exit _ (status := $status)
    | apply Probe.run_exit _ (status := $status)
    | apply Probe.exec_exitM _ (status := $status)
    | apply Probe.run_exitM _ (status := $status)) <;> probe_sides)

/-- `probe_write off count`: the pending native `write` of `count` image bytes at
segment offset `off` to a channel descriptor. For an `Omni.Exec` goal it leaves
the continuation for every delivered prefix `ds`; for a `Run` goal, pass the
delivered bytes with `probe_write off count with ds`. -/
macro "probe_write " off:term:max count:term:max : tactic =>
  `(tactic| (apply Probe.exec_write _ (off := $off) (count := $count) <;> probe_sides))

macro "probe_write " off:term:max count:term:max " with " ds:term : tactic =>
  `(tactic| (apply Probe.run_write _ (off := $off) (count := $count) (ds := $ds) <;> probe_sides))

/-- The layout facts of a generated probe, by evaluation. -/
macro "probe_layout" : tactic =>
  `(tactic| (constructor <;> (try unfold HeaderMatches) <;> decide +kernel))

end Silmaril.Process.LPS.Probes
