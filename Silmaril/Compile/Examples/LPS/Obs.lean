module

public import Silmaril.Process.LPS.ELFImageX86
public import Silmaril.Process.LPS.Machines.X86NativeLaunch
public import Silmaril.Process.LPS.Equivalence

/-! # Observational specifications of example programs over LPS process observations

The example ladder (`examples/compilers-on-lps/*.c`) is specified by what an LPS process
shows, not by any compiler's source semantics:

* a **trace** is a list of LPS `Event`s (byte-granular stdin reads `readEv 0 b`, writes
  `writeEv ch b`, and the final `exitEv`/`killEv` with the file system). `Behavior.traces` is
  prefix-closed, so a `ProcSpec` is a safety property: it must hold of **every prefix**, and
  says what the end (`ending`) may be once it is reached;
* a `ProcSpec` reads a `refusable` flag and the whole `ProcInput` (stdin stream, argv, initial
  file system), so it is universal over the inputs LPS quantifies. Refusals and the allocation
  budget are quantified by `SnapshotSafe` (every `SpuriousCfg`, every budget `lim`). The
  refusal outcomes a spec names (`StartupRefused`, `oom` for `Malloc`) are allowed only with
  `refusable = true`; when nothing can be refused (`Unrefused`: `forcedOnlyCfg` and no
  reachable budget refusal) the spec is read with `refusable = false`;
* a `ProcReq` adds **liveness**: on its `exits` inputs, a run in which nothing can be refused
  must exit (`MustExit`, LPS's `must_exit_in_at`: no error, no divergence). Without it every
  safety spec is met by an executable that loops (`jmp $`) or faults at once;
* `LpsSafe dom file spec` / `LpsMeets dom file req`: the static ELF `file` loads
  (`ELFImage.loadX86`) and its canonical native x86 process (`X86NativeLaunch.canonical`),
  launched validly on inputs in `dom`, never reaches an unmodelled step and satisfies the
  safety spec (and, for `LpsMeets`, the liveness requirement). Errors (`SError`) are excluded
  only by liveness, as in `Core.Spec.Allowed`, where exhaustion is always allowed;
* `CompilerSafe`/`CompilerMeets compile src dom _`: every executable a compiler produces from
  `src` is safe / meets the requirement. These are the shapes of the per-program targets.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Compile.Examples.LPS

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Formats

/-! ## Projections of a trace -/

/-- The bytes written on channel `ch`, in order. -/
def outOn (ch : Word) : List Event → List Byte
  | [] => []
  | .writeEv c b :: tr => if c = ch then b :: outOn ch tr else outOn ch tr
  | _ :: tr => outOn ch tr

/-- The bytes read from channel `ch`, in order. -/
def inOn (ch : Word) : List Event → List Byte
  | [] => []
  | .readEv c b :: tr => if c = ch then b :: inOn ch tr else inOn ch tr
  | _ :: tr => inOn ch tr

/-- What the process wrote to stdout. -/
abbrev stdoutOf (tr : List Event) : List Byte := outOn 1 tr
/-- What the process read from stdin. -/
abbrev stdinOf (tr : List Event) : List Byte := inOn 0 tr

/-- Is this event a write to a channel other than stdout? -/
def Event.otherWrite : Event → Bool
  | .writeEv c _ => c != 1
  | _ => false

/-- Every write is to stdout: nothing goes to stderr (or any other channel). -/
def OnlyStdout (tr : List Event) : Prop := tr.any Event.otherWrite = false

instance (tr : List Event) : Decidable (OnlyStdout tr) := inferInstanceAs (Decidable (_ = _))

/-- How a process ended. -/
inductive Outcome where
  | exit (code : Word)
  | killed (sig : Word)
  deriving DecidableEq, Repr

/-- The end an event records, with the final file system. -/
def Event.ending : Event → Option (Outcome × Fs.FileSystem)
  | .exitEv code fs => some (.exit code, fs)
  | .killEv sig fs => some (.killed sig, fs)
  | _ => none

/-- The end of a trace, if it has been reached. -/
def ending (tr : List Event) : Option (Outcome × Fs.FileSystem) := tr.findSome? Event.ending

/-- `P` holds of the end, once it is reached. -/
def OnEnd (tr : List Event) (P : Outcome → Fs.FileSystem → Prop) : Prop :=
  ∀ o fs, ending tr = some (o, fs) → P o fs

instance (tr : List Event) (P : Outcome → Fs.FileSystem → Prop)
    [∀ o fs, Decidable (P o fs)] : Decidable (OnEnd tr P) :=
  match h : ending tr with
  | none => isTrue fun o fs e => by simp [h] at e
  | some (o, fs) =>
    if hp : P o fs then isTrue fun o' fs' e => by
      rw [h] at e
      cases e
      exact hp
    else isFalse fun hall => hp (hall o fs h)

/-- `l` is a prefix of the stream `s`. -/
def StreamPrefix (s : InputStream) (l : List Byte) : Prop := s.takeFrom 0 l.length = l

/-- `l` is all of the stream `s`: a prefix followed by end of file. -/
def StreamIs (s : InputStream) (l : List Byte) : Prop := StreamPrefix s l ∧ s.byteAt l.length = none

instance (s : InputStream) (l : List Byte) : Decidable (StreamPrefix s l) :=
  inferInstanceAs (Decidable (_ = _))
instance (s : InputStream) (l : List Byte) : Decidable (StreamIs s l) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The outcomes of an allocation refused before `main` runs: ccomp/core-comp's `crt0` exits
with 127 when its `mmap` of the linear memory or stack is refused; a C library that cannot
allocate its thread block aborts (SIGABRT). Either way nothing has been read or written to
stdout. A spec allows these outcomes only when its `refusable` flag is set (see `ProcSpec`). -/
def StartupRefused (o : Outcome) : Prop := o = .exit 127 ∨ o = .killed 6

instance (o : Outcome) : Decidable (StartupRefused o) := inferInstanceAs (Decidable (_ ∨ _))

/-- A safety specification of a program: a property of the `refusable` flag, the input and
each observable trace prefix. `refusable = false` is the reading for a run in which nothing can
be refused (`Unrefused`): a spec must then forbid the refusal outcomes (`StartupRefused`,
`malloc`'s `oom`), so that an executable that exits 127 at once does not meet it. -/
abbrev ProcSpec := Bool → ProcInput → List Event → Prop

/-- A program's requirement: its safety spec, and the inputs on which a run in which nothing
can be refused must **exit** (`MustExit`: every execution exits normally, never errors and
never diverges). `cat` on an infinite stdin cannot exit, so its `exits` is `FiniteStdin`. -/
structure ProcReq where
  spec : ProcSpec
  exits : ProcInput → Prop

/-! ## Meeting a specification -/

/-- The behaviour on input `inp` never gives up (no unmodelled step is reachable) and all its
traces satisfy `spec r`. -/
def BehaviorMeets (spec : ProcSpec) (r : Bool) (inp : ProcInput) (b : Behavior) : Prop :=
  ¬ b.unmodeled ∧ ∀ tr, b.traces tr → spec r inp tr

/-- Nothing can be refused in this run: no spurious refusal is enabled (`forcedOnlyCfg`) and
no allocation-budget refusal is reachable (`X86NativeLaunch.BudgetSafe`, the premise of LPS's
own agreement shapes, `Shapes.agrees`). -/
def Unrefused (cfg : SpuriousCfg) (snapshot : X86Launch.Snapshot) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) : Prop :=
  cfg = forcedOnlyCfg ∧ X86NativeLaunch.BudgetSafe x86ExtNative cfg snapshot lim en inp

/-- **Safety**: every valid native x86 launch of `snapshot` with an input in `dom`, under every
refusal configuration and allocation budget, meets `spec true`, and meets `spec false` when
nothing can be refused. -/
def SnapshotSafe (dom : ProcInput → Prop) (snapshot : X86Launch.Snapshot) (spec : ProcSpec) :
    Prop :=
  ∀ (cfg : SpuriousCfg) (lim : Int) (en : ExecEntry) (inp : ProcInput), dom inp →
    X86Launch.ValidInput inp → X86Launch.ValidEntry x86ExtNative snapshot en inp →
      BehaviorMeets spec true inp (X86NativeLaunch.canonical cfg snapshot lim en inp) ∧
      (Unrefused cfg snapshot lim en inp →
        BehaviorMeets spec false inp (X86NativeLaunch.canonical cfg snapshot lim en inp))

/-- The native launch must exit (LPS `MustExit.v` `must_exit_in_at`, with any status byte:
the safety spec pins the status), from the configuration `canonical` starts from. -/
def MustExit (cfg : SpuriousCfg) (snapshot : X86Launch.Snapshot) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) : Prop :=
  MustExitInAt snapshot.image.segments NativeX86.extendedSyscallSpec
    (NativeX86.defaultRefusalFilter cfg) byteCodes (X86Launch.init x86ExtNative snapshot en lim inp)

/-- **Liveness**: every valid launch with an input in `dom ∩ exits`, in which nothing can be
refused, exits: no fault, no divergence, no stall. This excludes the executables that meet
every safety spec by doing nothing (`jmp $`, a fault at entry: `not_mustExitInAt_of_loop`,
`not_mustExitInAt_of_error`). -/
def SnapshotLive (dom : ProcInput → Prop) (snapshot : X86Launch.Snapshot)
    (exits : ProcInput → Prop) : Prop :=
  ∀ (cfg : SpuriousCfg) (lim : Int) (en : ExecEntry) (inp : ProcInput), dom inp → exits inp →
    X86Launch.ValidInput inp → X86Launch.ValidEntry x86ExtNative snapshot en inp →
      Unrefused cfg snapshot lim en inp → MustExit cfg snapshot lim en inp

/-- Safety and liveness. -/
def SnapshotMeets (dom : ProcInput → Prop) (snapshot : X86Launch.Snapshot) (req : ProcReq) :
    Prop :=
  SnapshotSafe dom snapshot req.spec ∧ SnapshotLive dom snapshot req.exits

/-- The static ELF executable `file` loads, and its process satisfies the safety spec on
`dom`. This is all a soundness theorem whose source semantics always allows exhaustion
(`Core.Spec.Allowed`) can give. -/
def LpsSafe (dom : ProcInput → Prop) (file : ELF.Bytes) (spec : ProcSpec) : Prop :=
  ∃ snapshot, ELFImage.loadX86 x86ExtNative file = some snapshot ∧ SnapshotSafe dom snapshot spec

/-- The static ELF executable `file` loads, and its process meets `req` on `dom`. -/
def LpsMeets (dom : ProcInput → Prop) (file : ELF.Bytes) (req : ProcReq) : Prop :=
  ∃ snapshot, ELFImage.loadX86 x86ExtNative file = some snapshot ∧ SnapshotMeets dom snapshot req

/-- Every executable that `compile` produces from `src` is safe for `spec` on `dom`. -/
def CompilerSafe {Src : Type} (compile : Src → Option ELF.Bytes) (src : Src)
    (dom : ProcInput → Prop) (spec : ProcSpec) : Prop :=
  ∀ file, compile src = some file → LpsSafe dom file spec

/-- Every executable that `compile` produces from `src` meets `req` on `dom`. -/
def CompilerMeets {Src : Type} (compile : Src → Option ELF.Bytes) (src : Src)
    (dom : ProcInput → Prop) (req : ProcReq) : Prop :=
  ∀ file, compile src = some file → LpsMeets dom file req

/-- The whole input domain. -/
def anyInput : ProcInput → Prop := fun _ => True

/-- Stdin is finite. -/
def FiniteStdin (inp : ProcInput) : Prop := ∃ l, StreamIs inp.stdin l

/-! ## Elementary facts -/

theorem SnapshotSafe.mono {dom : ProcInput → Prop} {snapshot : X86Launch.Snapshot}
    {spec spec' : ProcSpec} (h : SnapshotSafe dom snapshot spec)
    (imp : ∀ r inp tr, spec r inp tr → spec' r inp tr) : SnapshotSafe dom snapshot spec' :=
  fun cfg lim en inp hd hi he =>
    ⟨⟨(h cfg lim en inp hd hi he).1.1,
        fun tr t => imp _ _ _ ((h cfg lim en inp hd hi he).1.2 tr t)⟩,
      fun hu => ⟨((h cfg lim en inp hd hi he).2 hu).1,
        fun tr t => imp _ _ _ (((h cfg lim en inp hd hi he).2 hu).2 tr t)⟩⟩

theorem LpsSafe.mono {dom : ProcInput → Prop} {file : ELF.Bytes} {spec spec' : ProcSpec}
    (h : LpsSafe dom file spec) (imp : ∀ r inp tr, spec r inp tr → spec' r inp tr) :
    LpsSafe dom file spec' :=
  let ⟨s, hl, hs⟩ := h
  ⟨s, hl, hs.mono imp⟩

/-- Meeting a requirement includes its safety. -/
theorem LpsMeets.safe {dom : ProcInput → Prop} {file : ELF.Bytes} {req : ProcReq}
    (h : LpsMeets dom file req) : LpsSafe dom file req.spec :=
  let ⟨s, hl, hs, _⟩ := h
  ⟨s, hl, hs⟩

/-- Every behaviour has the empty trace, so a met spec holds of `[]`: a spec that rejects
the empty trace is met by no executable (checked for each spec in `Checks`). -/
theorem SnapshotSafe.nil {dom : ProcInput → Prop} {snapshot : X86Launch.Snapshot}
    {spec : ProcSpec} (h : SnapshotSafe dom snapshot spec) {cfg : SpuriousCfg} {lim : Int}
    {en : ExecEntry} {inp : ProcInput} (hd : dom inp) (hi : X86Launch.ValidInput inp)
    (he : X86Launch.ValidEntry x86ExtNative snapshot en inp) : spec true inp [] :=
  (h cfg lim en inp hd hi he).1.2 [] (X86Launch.runWith_empty_trace _ _ _ _ _ _ _)

/-- A running configuration that steps silently to itself (`jmp $`) does not exit. -/
theorem not_mustExitInAt_of_loop {isa : UserIsa} {segs : List Segment}
    {sys : Sys SyscallEffect} {refused : RefusalFilter} {S : List Word} {c : Config isa}
    (hh : c.model.halted = none) (loop : SStep segs sys refused c [] (.next c)) :
    ¬ MustExitInAt segs sys refused S c := by
  intro h
  induction h with
  | halted h' => simp [hh] at h'
  | running _ _ _ _ ih => exact ih [] _ loop hh loop

/-- A running configuration that can fault does not exit. -/
theorem not_mustExitInAt_of_error {isa : UserIsa} {segs : List Segment}
    {sys : Sys SyscallEffect} {refused : RefusalFilter} {S : List Word} {c : Config isa}
    {evs : List Event} (err : SStep segs sys refused c evs .error) :
    ¬ MustExitInAt segs sys refused S c := by
  intro h
  cases h with
  | halted h' _ _ =>
    cases err <;> simp_all
  | running _ _ noErr _ => exact noErr evs err

@[simp] theorem outOn_nil (ch : Word) : outOn ch [] = [] := rfl
@[simp] theorem inOn_nil (ch : Word) : inOn ch [] = [] := rfl
@[simp] theorem ending_nil : ending [] = none := rfl

theorem outOn_append (ch : Word) (a b : List Event) :
    outOn ch (a ++ b) = outOn ch a ++ outOn ch b := by
  induction a with
  | nil => rfl
  | cons e a ih =>
    cases e with
    | writeEv c b => by_cases h : c = ch <;> simp [outOn, h, ih]
    | _ => simp [outOn, ih]

theorem inOn_append (ch : Word) (a b : List Event) :
    inOn ch (a ++ b) = inOn ch a ++ inOn ch b := by
  induction a with
  | nil => rfl
  | cons e a ih =>
    cases e with
    | readEv c b => by_cases h : c = ch <;> simp [inOn, h, ih]
    | _ => simp [inOn, ih]

@[simp] theorem outOn_writes (ch : Word) (l : List Byte) :
    outOn ch (l.map (.writeEv ch)) = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [outOn, ih]

@[simp] theorem inOn_writes (ch c : Word) (l : List Byte) : inOn ch (l.map (.writeEv c)) = [] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [inOn, ih]

@[simp] theorem ending_writes (c : Word) (l : List Byte) : ending (l.map (.writeEv c)) = none := by
  induction l with
  | nil => rfl
  | cons b l ih => exact ih

theorem ending_writes_append (c : Word) (l : List Byte) (rest : List Event) :
    ending (l.map (.writeEv c) ++ rest) = ending rest := by
  induction l with
  | nil => rfl
  | cons b l ih => exact ih

@[simp] theorem ending_exitEv (code : Word) (fs : Fs.FileSystem) :
    ending [.exitEv code fs] = some (.exit code, fs) := rfl

@[simp] theorem outOn_exitEv (ch code : Word) (fs : Fs.FileSystem) :
    outOn ch [.exitEv code fs] = [] := rfl

@[simp] theorem inOn_exitEv (ch code : Word) (fs : Fs.FileSystem) :
    inOn ch [.exitEv code fs] = [] := rfl

theorem onlyStdout_writes (l : List Byte) : OnlyStdout (l.map (.writeEv 1)) := by
  simp [OnlyStdout, Event.otherWrite]

theorem onlyStdout_writes_exit (l : List Byte) (code : Word) (fs : Fs.FileSystem) :
    OnlyStdout (l.map (.writeEv 1) ++ [.exitEv code fs]) := by
  have := onlyStdout_writes l
  simp_all [OnlyStdout, Event.otherWrite]

/-- `OnEnd` of a trace that has not ended. -/
theorem onEnd_of_ending_none {tr : List Event} {P : Outcome → Fs.FileSystem → Prop}
    (h : ending tr = none) : OnEnd tr P := fun o fs e => by simp [h] at e

/-- `OnEnd` of a trace that has ended. -/
theorem onEnd_of_ending_some {tr : List Event} {P : Outcome → Fs.FileSystem → Prop}
    {o : Outcome} {fs : Fs.FileSystem} (h : ending tr = some (o, fs)) (hp : P o fs) :
    OnEnd tr P := fun o' fs' e => by
  rw [h] at e
  cases e
  exact hp

/-- The prefixes of "write `out` to channel `ch`, then exit": a part of the output, or all
of it with the end. -/
theorem prefix_writes_then (ch : Word) (out : List Byte) (e : Event) (tr : List Event)
    (h : tr <+: out.map (.writeEv ch) ++ [e]) :
    (∃ n, tr = (out.take n).map (.writeEv ch)) ∨ tr = out.map (.writeEv ch) ++ [e] := by
  rcases List.prefix_concat_iff.mp h with h | h
  · exact .inr h
  · refine .inl ⟨tr.length, ?_⟩
    rw [List.map_take]
    exact List.prefix_iff_eq_take.mp h

end Silmaril.Compile.Examples.LPS
