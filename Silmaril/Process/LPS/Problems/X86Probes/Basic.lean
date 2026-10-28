module

public import Silmaril.Process.LPS.Probes.Launches

/-! # The x86 probe corpus as problems: common pieces

Each ELF probe of `examples/verification-projects/theorem-dev/lps-probes` is a harness with
one build (`plain`, the probe's snapshot) on the hub's native x86-64 profile
(`Problems.nativeX86`). Its statements are published shapes (`haltsMayFail`,
`haltsWithinBudget`, the agreement forms for pairs) or extended ones (#3610). The
statements themselves are generated (`Problems.X86Probes.Corpus`); this file has the harness
record and the postconditions the universal theorems use.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.X86Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Probes

/-- The harness record of a probe. A probe has no driver input file: it is launched as
`./probe` with the launch's argv, environment, files and stdin (`DriverInput` is
documentation, not a premise). -/
def probeHarness (name : String) (statements : List (String × Statement)) (proved : List String) :
    Harness where
  project := "lps-probes"
  harness := name
  entry := "_start"
  driver := { argv0 := "./probe", inputFile := "" }
  distribution := none
  statements := statements
  proved := proved

/-- The native x86-64 problem of a probe: its snapshot as the plain build. -/
def probeProblem (harness : Harness) (P : Probe) : ProfileProblem X86Launch.Snapshot :=
  nativeProblem harness (plainOnly P.snapshot)

/-- Two probes compared by the plain `agrees` shape at the standard budgets. -/
def probePair (name : String) (first second : Probe) : PairProblem X86Launch.Snapshot where
  name := name
  profile := nativeX86
  first := first.snapshot
  second := second.snapshot
  budgets := .standard
  shape := .agrees

/-! ## The catalogue -/

/-- What is known of a statement of the corpus. -/
inductive Status where
  | proved
  | refuted
  /-- Stated, neither proved nor refuted here. -/
  | stated
  deriving DecidableEq, Repr

/-- A proved statement holds, a refuted one fails; a stated one carries no claim. -/
def Status.Holds : Status → Prop → Prop
  | .proved, p => p
  | .refuted, p => ¬ p
  | .stated, _ => True

def Status.settled : Status → Bool
  | .stated => false
  | _ => true

/-- One statement of the corpus: the problem (a probe, or a pair of probes), the statement's
name, the statement itself and its status. -/
structure Entry where
  problem : String
  statement : String
  prop : Prop
  status : Status

def Entry.key (e : Entry) : String := e.problem ++ "/" ++ e.statement

/-- A settled entry: the proof of the statement, or of its negation, as its status says. -/
structure Settled where
  entry : Entry
  holds : entry.status.Holds entry.prop

/-! ## Postconditions -/

/-- Every execution exits with `code` after emitting nothing but the exit. -/
def ExitOnly (code : Word) : Omni.Post x86ExtNative := fun trace outcome =>
  ∃ final, outcome = .halt final ∧ trace = [.exitEv code final.model.fs] ∧
    final.model.halted = some code ∧ final.model.killedBy = none

theorem ExitOnly.exitsIn {code : Word} {allowed : List Word} (member : code ∈ allowed)
    (trace : List Event) (outcome : Omni.Outcome x86ExtNative) (post : ExitOnly code trace outcome) :
    Omni.ExitsIn allowed trace outcome := by
  obtain ⟨final, rfl, _, halted, unkilled⟩ := post
  exact ⟨code, halted, member, unkilled⟩

theorem ExitOnly.silent {code : Word} (trace : List Event) (outcome : Omni.Outcome x86ExtNative)
    (post : ExitOnly code trace outcome) : TraceSpec.silent.denote trace := by
  obtain ⟨final, _, rfl, _, _⟩ := post
  exact ⟨rfl, rfl⟩

/-! ## What a trace writes -/

theorem written_writes (fd : Word) (bs : List Byte) (rest : List Event) :
    written fd (bs.map (.writeEv fd) ++ rest) = bs ++ written fd rest := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [written, ih]

theorem writesOtherThan_writes (fd : Word) (bs : List Byte) (rest : List Event) :
    writesOtherThan fd (bs.map (.writeEv fd) ++ rest) = writesOtherThan fd rest := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [writesOtherThan, ih]

/-- A trace that writes `ds` to stdout and then exits shows a prefix of `bs` when `ds` is
one. -/
theorem stdoutPrefix_of {bs ds : List Byte} (pre : ds <+: bs) (code : Word) (fs : Fs.FileSystem) :
    (TraceSpec.stdoutPrefix bs).denote (ds.map (.writeEv 1) ++ [.exitEv code fs]) := by
  refine ⟨?_, ?_⟩
  · rw [written_writes]
    simpa [written] using pre
  · rw [writesOtherThan_writes]
    rfl

/-- A trace that writes a nonempty prefix `ds` of `bs` to stdout and then exits shows a
nonempty prefix of `bs`. -/
theorem stdoutNonemptyPrefix_of {bs ds : List Byte} (delivered : Probe.WritePrefix bs ds) (code : Word)
    (fs : Fs.FileSystem) :
    (TraceSpec.stdoutNonemptyPrefix bs).denote (ds.map (.writeEv 1) ++ [.exitEv code fs]) := by
  obtain ⟨pre, others⟩ := stdoutPrefix_of delivered.2 code fs
  refine ⟨?_, pre, others⟩
  rw [written_writes]
  simpa [written] using delivered.1

/-! ## The observation without the file system

`Probe.Exactly o` pins the final file system to the observed one (`Observed.Ends`), which
is the harness's. At another launch the file system is the input's, so the launch-independent
postcondition `Emits o` keeps the events (each with the final file system) and the status,
and drops the file-system clause. -/

/-- Every execution halts with the observed events and outcome, at whatever file system
the launch has. -/
def Emits (o : Probes.Observed) : Omni.Post x86ExtNative := fun trace outcome =>
  ∃ final, outcome = .halt final ∧ trace = o.events final.model.fs ∧
    match o.outcome with
    | .exited status => final.model.halted = some (BitVec.ofNat 64 status) ∧ final.model.killedBy = none
    | .killed signal => final.model.killedBy = some (BitVec.ofNat 64 signal)

theorem Emits.exitsIn {o : Probes.Observed} {status : Nat} (exited : o.outcome = .exited status)
    {allowed : List Word} (member : BitVec.ofNat 64 status ∈ allowed)
    (trace : List Event) (outcome : Omni.Outcome x86ExtNative) (post : Emits o trace outcome) :
    Omni.ExitsIn allowed trace outcome := by
  obtain ⟨final, rfl, _, ends⟩ := post
  rw [exited] at ends
  exact ⟨_, ends.1, member, ends.2⟩

theorem written_single (fd : Word) (e : Event) (notWrite : ∀ ch b, e ≠ .writeEv ch b) :
    written fd [e] = [] := by
  cases e with
  | writeEv ch b => exact absurd rfl (notWrite ch b)
  | _ => rfl

theorem writesOtherThan_single (fd : Word) (e : Event) (notWrite : ∀ ch b, e ≠ .writeEv ch b) :
    writesOtherThan fd [e] = false := by
  cases e with
  | writeEv ch b => exact absurd rfl (notWrite ch b)
  | _ => rfl

theorem terminal_notWrite (o : Probes.Observed) (fs : Fs.FileSystem) (ch : Word) (b : Byte) :
    o.terminal fs ≠ .writeEv ch b := by
  unfold Probes.Observed.terminal
  split <;> exact fun h => by cases h

/-- An observation that reads nothing and writes only `o.stdout` to stdout shows exactly
`o.stdout`. -/
theorem Emits.stdout {o : Probes.Observed} (noStdin : o.stdin = []) (noStderr : o.stderr = [])
    (trace : List Event) (outcome : Omni.Outcome x86ExtNative) (post : Emits o trace outcome) :
    (TraceSpec.stdoutPrefix o.stdout).denote trace := by
  obtain ⟨final, rfl, rfl, _⟩ := post
  unfold Probes.Observed.events
  rw [noStdin, noStderr]
  simp only [List.map_nil, List.nil_append, List.append_nil]
  refine ⟨?_, ?_⟩
  · rw [written_writes, written_single _ _ (terminal_notWrite o _), List.append_nil]
  · rw [writesOtherThan_writes]
    exact writesOtherThan_single _ _ (terminal_notWrite o _)

/-- An observation that reads and writes nothing is silent. -/
theorem Emits.silent {o : Probes.Observed} (noStdin : o.stdin = []) (noStdout : o.stdout = [])
    (noStderr : o.stderr = []) (trace : List Event) (outcome : Omni.Outcome x86ExtNative)
    (post : Emits o trace outcome) : TraceSpec.silent.denote trace := by
  obtain ⟨pre, others⟩ := Emits.stdout noStdin noStderr trace outcome post
  rw [noStdout] at pre
  exact ⟨List.prefix_nil.mp pre, others⟩

/-! ## A channel write of a prefix, then an exit computed from its length -/

/-- Every execution writes a nonempty prefix `ds` of `bs` to stdout (a short write delivers
fewer bytes) and exits with `code ds.length`. -/
def WroteThenExit (bs : List Byte) (code : Nat → Word) : Omni.Post x86ExtNative :=
  fun trace outcome =>
    ∃ ds final, outcome = .halt final ∧ Probe.WritePrefix bs ds ∧
      trace = ds.map (.writeEv 1) ++ [.exitEv (code ds.length) final.model.fs] ∧
      final.model.halted = some (code ds.length) ∧ final.model.killedBy = none

theorem WroteThenExit.exitsIn {bs : List Byte} {code : Nat → Word} {allowed : List Word}
    (member : ∀ k, 0 < k → k ≤ bs.length → code k ∈ allowed)
    (trace : List Event) (outcome : Omni.Outcome x86ExtNative)
    (post : WroteThenExit bs code trace outcome) : Omni.ExitsIn allowed trace outcome := by
  obtain ⟨ds, final, rfl, ⟨nonempty, pre⟩, _, halted, unkilled⟩ := post
  refine ⟨_, halted, member _ ?_ pre.length_le, unkilled⟩
  exact List.length_pos_iff.mpr nonempty

theorem WroteThenExit.stdoutPrefix {bs : List Byte} {code : Nat → Word}
    (trace : List Event) (outcome : Omni.Outcome x86ExtNative)
    (post : WroteThenExit bs code trace outcome) : (TraceSpec.stdoutPrefix bs).denote trace := by
  obtain ⟨ds, final, _, ⟨_, pre⟩, rfl, _⟩ := post
  exact stdoutPrefix_of pre _ _

theorem WroteThenExit.stdoutNonemptyPrefix {bs : List Byte} {code : Nat → Word}
    (trace : List Event) (outcome : Omni.Outcome x86ExtNative)
    (post : WroteThenExit bs code trace outcome) : (TraceSpec.stdoutNonemptyPrefix bs).denote trace := by
  obtain ⟨ds, final, _, delivered, rfl, _⟩ := post
  exact stdoutNonemptyPrefix_of delivered _ _

/-- A write's delivered bytes are one of the nonempty prefixes of the message. -/
theorem writePrefix_mem_tail {bs ds : List Byte} (h : Probe.WritePrefix bs ds) : ds ∈ bs.inits.tail := by
  have m := (List.mem_inits ds bs).mpr h.2
  cases bs with
  | nil => exact absurd (List.prefix_nil.mp h.2) h.1
  | cons a t =>
    rcases List.mem_cons.mp m with same | rest
    · exact absurd same h.1
    · exact rest

/-- The exit status `exit(0 - n)` of a probe that returns a write's count negated. -/
def negStatus (k : Nat) : Word := (0 - zw (k : Int)) &&& 255

/-- The exit status `exit(n)` of a probe that exits with a write's count. -/
def countStatus (k : Nat) : Word := zw (k : Int) &&& 255

end Silmaril.Process.LPS.Problems.X86Probes
