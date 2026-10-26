module

public import Silmaril.Process.LPS.Problems.Profile
public import Silmaril.Process.LPS.Problems.GnuSha256sum.Registry

/-! # GNU `sha256sum` (stdin tier) in the parity problem format

The parity problems (`Problems.Profile`) state a program's correctness as a
`ProfileProblem`: a harness, a `StatementProfile` (ISA, launch, syscall table, refusal
reading, allocation classifier, entry and input domains) and the artifact of each build. Its
statements are the published halting shapes (`Statement.haltsMayFail`,
`Statement.haltsWithinBudget`, `ProfileProblem.denote`) and the extended one
(`ExtStatement.haltsMayFailWith`, `ProfileProblem.denoteExt`).

This file states `sha256sum-min` on the stdin tier in that format and relates it to
`lps-total` (`Registry.lpsTotal`, `TotalGoal`).

**Profile** (`profile oracle message`). The same semantics as `lps-total`:

* ISA `machine oracle` (`Machines.x86WithFlagOracle8`, the `X86.Ext8` variant with the flag
  oracle at `syscall`);
* the x86 launch `X86Launch.init` and entry envelope `X86Launch.ValidEntry`;
* the native syscall table of `X86NativeLaunch.runWith` (`NativeX86.extendedSyscallSpec`) and
  its refusal filter `NativeX86.defaultRefusalFilter` at the reading's configuration (no
  filter in the plain reading, as in `StatementProfile.reference`);
* the native allocation classifier;
* the stdin-tier input domain: `X86Launch.ValidInput`, `argv` of one element, standard
  input the finite stream of `message`.

It differs from the hub's `Problems.nativeX86` in the ISA (`x86ExtNative` there: no 8-bit ALU
forms, which this binary needs), the table (`NativeX86.All.nativeTable` there) and the input
domain (every valid input there: other argv would make `sha256sum` open files). The profile is
indexed by the flag oracle (a profile has one ISA) and by the message (a `TraceSpec` is a
fixed byte string, so the expected stdout fixes the message).

**Statements** (`statements message`):

* `halts_may_fail`: `haltsMayFail` with exit set `[0]`;
* `halts_within_budget`: `haltsWithinBudget` at the standard budget with exit set `[0]`;
* `halts_may_fail_stdout` (extended): `haltsMayFailWith [0] (stdoutPrefix (expected message))`:
  every execution exits 0, and what it writes to fd 1 is a prefix of `hex(SHA-256(message))
  ++ "  -\n"`, nothing written to any other descriptor.

**Relation to `lps-total`.** `lpsTotal` implies each of them at every oracle and message
(`profileTotal_of_lpsTotal`, VERIFIED). The converse does not hold as stated: `lps-total` also
says the complete ideal trace occurs and the run never reaches an error or an unmodelled
state at every refusal configuration and budget, which the halting shapes do not express.
`profile-total` (`Registry` style, `@[problem]`) is the conjunction over every oracle and message;
it is linked from `lps-total` by `profileTotal_link` (VERIFIED), so it is solved when
`lps-total` is.

Status: everything in this file is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.GnuSha256sum.Parity

open Silmaril.Problems
open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines

/-! ## The profile and the problem -/

/-- The stdin-tier input domain at `message`: a valid x86 launch input with one argument and
standard input the finite stream of `message`. -/
def ValidStdinInput (message : List Byte) (abortModelled : Bool) (input : ProcInput) : Prop :=
  X86Launch.ValidInput input ∧ input.abortTerminal = abortModelled ∧ input.argv.length = 1 ∧
    input.stdin = InputStream.ofList message

/-- The refusal filter of a reading: none in the plain reading, the native filter at the
reading's configuration otherwise. -/
def refusalsOf : Reading → RefusalFilter
  | none => noFilter
  | some environment => NativeX86.defaultRefusalFilter environment

/-- The statement profile of `lps-total` at one flag oracle, on the stdin tier at `message`. -/
def profile (oracle : Nat → X86FlagChoices.Choice) (message : List Byte) :
    StatementProfile X86Launch.Snapshot where
  isa := machine oracle
  image := X86Launch.Snapshot.image
  initialConfig := X86Launch.init (machine oracle)
  syscalls := fun _ => NativeX86.extendedSyscallSpec
  refusals := refusalsOf
  allocClassifier := NativeX86.allocBudgetRefusedB
  validEntry := X86Launch.ValidEntry (machine oracle)
  validInput := ValidStdinInput message

/-- The harness record: the pinned ELF `sha256sum-min` launched as `sha256sum` with no
operand. -/
def harness (statements : List (String × Statement)) (proved : List String) : Harness where
  project := "gnu-sha256sum"
  harness := "sha256sum-min"
  entry := "_start"
  driver := { argv0 := "sha256sum", inputFile := "" }
  distribution := none
  statements := statements
  proved := proved

/-- The exit set: status 0 only. -/
def exits : ExitChoice := .listed [0]

/-- The published statements. -/
def statements : List (String × Statement) :=
  [("halts_may_fail", .haltsMayFail .plain exits),
   ("halts_within_budget", .haltsWithinBudget .plain .standard exits)]

/-- The extended statement at `message`. -/
def stdoutStatement (message : List Byte) : ExtStatement :=
  .haltsMayFailWith .plain exits (.stdoutPrefix (expected message))

/-- The problem: one build, `plain`, the pinned snapshot. -/
def problem (oracle : Nat → X86FlagChoices.Choice) (message : List Byte) :
    ProfileProblem X86Launch.Snapshot :=
  ⟨harness statements (statements.map Prod.fst), profile oracle message, plainOnly snapshot⟩

/-! ## What the statements say (`rfl`) -/

theorem haltsMayFail_eq (oracle : Nat → X86FlagChoices.Choice) (message : List Byte) :
    (problem oracle message).denote (.haltsMayFail .plain exits) =
      (profile oracle message).haltsMayFail [0] snapshot := rfl

theorem haltsWithinBudget_eq (oracle : Nat → X86FlagChoices.Choice) (message : List Byte) :
    (problem oracle message).denote (.haltsWithinBudget .plain .standard exits) =
      (profile oracle message).haltsWithinBudget BudgetChoice.standard.budgets.limSource [0]
        snapshot := rfl

theorem stdout_eq (oracle : Nat → X86FlagChoices.Choice) (message : List Byte) :
    (problem oracle message).denoteExt (stdoutStatement message) =
      (profile oracle message).haltsMayFailWith [0]
        (TraceSpec.stdoutPrefix (expected message)).denote snapshot := rfl

/-- The extended statement strengthens `halts_may_fail`. -/
theorem stdout_base (message : List Byte) :
    (stdoutStatement message).base = .haltsMayFail .plain exits := rfl

/-- The domain is inhabited at every oracle and message (`NonVacuity`, `entryFetchable`): the
halting statements do not hold vacuously. -/
theorem domain_nonempty (oracle : Nat → X86FlagChoices.Choice) (message : List Byte) :
    ∃ en inp, (profile oracle message).validEntry snapshot en inp ∧
      (profile oracle message).validInput false inp :=
  ⟨launchEntry, launchInput message, launchEntry_valid oracle message (entryFetchable oracle),
    launchInput_valid message, rfl, rfl, rfl⟩

/-! ## From `lps-total` -/

section Omni

variable {isa : UserIsa} {segs : List Segment} {spec : Sys SyscallEffect}
  {refused : RefusalFilter}

/-- An omni judgment can record the maximal execution each outcome comes from. -/
theorem exec_mexec {c : Config isa} {Q : Omni.Post isa} (h : Omni.Exec segs spec refused c Q) :
    Omni.Exec segs spec refused c (fun tr o => Q tr o ∧ Omni.MExec segs spec refused c tr o) := by
  induction h with
  | halt hh hq => exact .halt hh ⟨hq, .halt hh⟩
  | step hh hprog herr _ ih =>
    exact .step hh hprog (fun evs he => ⟨herr evs he, .error he⟩)
      fun evs c' hs => Omni.exec_conseq (ih evs c' hs) fun _ _ h => ⟨h.1, .next hs h.2⟩

end Omni

theorem written_prefix (fd : Word) {tr full : List Event} (pre : tr <+: full) :
    written fd tr <+: written fd full := by
  induction tr generalizing full with
  | nil => exact List.nil_prefix
  | cons e tr ih =>
    obtain ⟨rest, rfl⟩ := pre
    have := ih (full := tr ++ rest) (List.prefix_append _ _)
    cases e with
    | writeEv ch b =>
      simp only [written, List.cons_append]
      split
      · exact List.cons_prefix_cons.mpr ⟨rfl, this⟩
      · exact this
    | _ => simpa [written] using this

theorem writesOtherThan_prefix (fd : Word) {tr full : List Event} (pre : tr <+: full)
    (none : writesOtherThan fd full = false) : writesOtherThan fd tr = false := by
  induction tr generalizing full with
  | nil => rfl
  | cons e tr ih =>
    obtain ⟨rest, rfl⟩ := pre
    cases e with
    | writeEv ch b =>
      simp only [writesOtherThan, List.cons_append, Bool.or_eq_false_iff] at none ⊢
      exact ⟨none.1, ih (List.prefix_append _ _) none.2⟩
    | _ => exact ih (List.prefix_append _ _) none

theorem written_reads (fd : Word) (bs : List Byte) (rest : List Event) :
    written fd (bs.map (Event.readEv 0) ++ rest) = written fd rest := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa [written] using ih

theorem writesOtherThan_reads (fd : Word) (bs : List Byte) (rest : List Event) :
    writesOtherThan fd (bs.map (Event.readEv 0) ++ rest) = writesOtherThan fd rest := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa [writesOtherThan] using ih

theorem written_writes (fd : Word) (bs : List Byte) (rest : List Event) :
    written fd (bs.map (Event.writeEv fd) ++ rest) = bs ++ written fd rest := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [written, ih]

theorem writesOtherThan_writes (fd : Word) (bs : List Byte) (rest : List Event) :
    writesOtherThan fd (bs.map (Event.writeEv fd) ++ rest) = writesOtherThan fd rest := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [writesOtherThan, ih]

/-- Every prefix of the ideal trace shows a prefix of the expected output on stdout and
nothing on any other descriptor. -/
theorem stdoutPrefix_of_ideal {message : List Byte} {fs : Fs.FileSystem} {tr : List Event}
    (pre : tr <+: idealTrace message fs) :
    (TraceSpec.stdoutPrefix (expected message)).denote tr := by
  have ideal : written 1 (idealTrace message fs) = expected message ∧
      writesOtherThan 1 (idealTrace message fs) = false := by
    simp only [idealTrace, List.append_assoc, written_reads, writesOtherThan_reads,
      written_writes, writesOtherThan_writes]
    exact ⟨by simp [written], rfl⟩
  exact ⟨ideal.1 ▸ written_prefix 1 pre, writesOtherThan_prefix 1 pre ideal.2⟩

/-- `Total` at one launch gives the extended halting shape's postcondition at that launch. -/
theorem exec_of_total {oracle : Nat → X86FlagChoices.Choice} {cfg : SpuriousCfg} {limit : Int}
    {en : ExecEntry} {inp : ProcInput} {message : List Byte}
    (total : Total oracle cfg limit en inp message) :
    Omni.Exec snapshot.image.segments NativeX86.extendedSyscallSpec
      (NativeX86.defaultRefusalFilter cfg) (initial oracle limit en inp)
      (fun trace outcome => Omni.ExitsIn [0] trace outcome ∧
        (TraceSpec.stdoutPrefix (expected message)).denote trace) := by
  have exec := exec_mexec ((Omni.mustExitInAt_iff_exec [0] _).mp total.mustExit)
  refine Omni.exec_conseq exec fun tr o ⟨exitsIn, mexec⟩ => ⟨exitsIn, ?_⟩
  cases o with
  | error => exact exitsIn.elim
  | halt c' =>
    have star := (Omni.mexec_halt_star mexec).1
    exact stdoutPrefix_of_ideal (total.safety.safe tr ⟨tr, c', star, List.prefix_refl _⟩)

theorem admissible_of {oracle : Nat → X86FlagChoices.Choice} {message : List Byte}
    {en : ExecEntry} {inp : ProcInput} {abortModelled : Bool}
    (validEntry : (profile oracle message).validEntry snapshot en inp)
    (validInput : (profile oracle message).validInput abortModelled inp) :
    Admissible oracle en inp message :=
  ⟨validInput.2.2.2, validInput.2.2.1, validInput.1, validEntry⟩

/-- **The parity statements of `sha256sum-min`**: at every flag oracle and every message, the
published halting shapes and the extended stdout shape of `problem oracle message`. -/
def ProfileTotal : Prop :=
  ∀ (oracle : Nat → X86FlagChoices.Choice) (message : List Byte),
    (problem oracle message).denote (.haltsMayFail .plain exits) ∧
      (problem oracle message).denote (.haltsWithinBudget .plain .standard exits) ∧
      (problem oracle message).denoteExt (stdoutStatement message)

/-- `lps-total` implies the parity statements (VERIFIED). -/
theorem profileTotal_of_totalGoal (total : TotalGoal) : ProfileTotal := by
  intro oracle message
  refine ⟨?_, ?_, ?_⟩
  · rw [haltsMayFail_eq]
    intro en inp validEntry validInput
    exact (total oracle mayFailCfg sourceAllocLimit en inp message trivial
      (admissible_of validEntry validInput)).mustExit
  · rw [haltsWithinBudget_eq]
    intro en inp validEntry validInput _
    exact (total oracle forcedOnlyCfg _ en inp message trivial
      (admissible_of validEntry validInput)).mustExit
  · rw [stdout_eq]
    intro en inp validEntry validInput
    exact exec_of_total (total oracle mayFailCfg sourceAllocLimit en inp message trivial
      (admissible_of validEntry validInput))

/-! ## As a problem -/

/-- The parity statements of `sha256sum-min` on the stdin tier, as a problem. -/
@[problem "sha256/gnu-sha256sum-x86-64/profile-total"]
def profileTotal : Prop := ProfileTotal

/-- `profile-total` follows from `lps-total` (VERIFIED). -/
theorem profileTotal_link : All [Registry.lpsTotal] → profileTotal := fun ⟨total, _⟩ =>
  profileTotal_of_totalGoal total

end Silmaril.Process.LPS.Problems.GnuSha256sum.Parity
