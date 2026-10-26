module

public import Silmaril.Process.LPS.Problems.Sha256Cli.Elf
public import Silmaril.Process.LPS.Equivalence
public import Silmaril.Process.LPS.Machines.X86FlagChoices
public import Silmaril.Process.CLI.Sha256

/-! # The `sha256` filter, end to end in LPS: the target statements

**Binary.** The pinned ELF `apps/sha256-cli/build/sha256` (`Sha256Cli.elfNat`, 2368 bytes,
SHA-256 `6eaae149…89e1f7`), the freestanding x86-64 filter that the #3029/#3025 chain
transcribes (`Process.CLI.Sha256Cli.Binary`). It is *not* GNU coreutils `sha256sum`: it
prints the 64 hex digits and `"\n"` (`CLI.Sha256.expected`), where GNU prints the digits and
`"  -\n"` (`Apps.Sha256sum`, see `Sha256Cli.Segments.gnu_stdout`).

**Digest domain.** The executable digest specification is total on finite byte lists.
Its padding encodes bit length modulo `2^64`; FIPS 180-4's SHA-256 domain is
bit length below `2^64`. Outside that bound this theorem concerns the specification's
length-wrapping extension, not an extension prescribed by FIPS. The bounded1024-byte
tier is inside the standard domain. Prose-standard correspondence remains a separate
specification-review obligation from binary-to-executable-spec correctness.

**Semantics.** LPS (`Process.LPS`, the Lean port of rocq-linux-process-semantics) with the
native x86-64 launch of #3492/#3534: `X86NativeLaunch.runWith` = `X86Launch.runWith` with
the native x86-64 syscall table and refusal filter, over the machine
`Machines.x86WithFlagOracle oracle`, **for every flag oracle**. The deterministic adapter
`x86ExtNative` is unusable here: it declines a `syscall` whose RFLAGS image has an undefined
flag, and the binary executes `xor %eax,%eax; …; syscall` (XOR leaves AF undefined;
`X86LaunchExecution.xor_zeroing_flags_refused`), so under `x86ExtNative` every run of this
binary is `unmodeled` at its first system call. `SYSCALL` copies RFLAGS to R11, which the
program never reads, so quantifying over the oracle loses nothing.

**Nondeterminism.** LPS `read` on stdin returns any non-empty prefix of the remaining stream
up to the count, and `write` to stdout accepts any non-empty prefix; events are per byte. So
`Behavior.traces` already ranges over every read partition and write split, and the trace
statement below is partition-independent by construction. Neither call has an injected
failure (they are not in LPS's `injectedTable`), so the refusal configuration is quantified
too.

**Tiers** (each a `Prop`; none is asserted in this file):

* `TotalGoal`: on every finite stdin, every launch is error free, nothing is unmodelled,
  every observable trace is a prefix of `idealTrace` (read the input, write exactly
  `hex(SHA-256(input)) ++ "\n"` to fd 1, exit 0 with the file system unchanged), every
  execution exits with status 0 (`MustExitInAt … [0]`), and the complete ideal trace occurs.
* `PartialGoal`: the first three only (safety: no fault, nothing unmodelled, trace prefix).
* `BoundedGoal n`: `TotalGoal` for inputs of at most `n` bytes.

"Touches nothing else" is the trace prefix property: LPS observes reads, writes to every
descriptor, and the whole file system at exit, so a prefix of `idealTrace` reads only stdin,
writes only stdout and exits with `inp.fs`.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.Sha256Cli

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Process.LPS.Fs (FileSystem)

/-- The user machine: native x86-64 with an explicit oracle for undefined flags at `syscall`. -/
abbrev machine (oracle : Nat → X86FlagChoices.Choice) : UserIsa := x86WithFlagOracle oracle

/-- The LPS behaviour of the pinned binary. -/
def behaviour (oracle : Nat → X86FlagChoices.Choice) (refusals : SpuriousCfg) (limit : Int)
    (en : ExecEntry) (inp : ProcInput) : Behavior :=
  X86NativeLaunch.runWith (machine oracle) refusals snapshot limit en inp

/-- Its initial configuration. -/
def initial (oracle : Nat → X86FlagChoices.Choice) (limit : Int) (en : ExecEntry)
    (inp : ProcInput) : Config (machine oracle) :=
  X86Launch.init (machine oracle) snapshot en limit inp

/-- The only complete observation allowed: read the message, write the digest line to fd 1,
exit 0 with the file system `fs`. -/
def idealTrace (message : List Byte) (fs : FileSystem) : List Event :=
  message.map (Event.readEv 0) ++ (CLI.Sha256.expected message).map (Event.writeEv 1) ++
    [Event.exitEv 0 fs]

/-- A guarded launch on a finite standard input. -/
def Admissible (oracle : Nat → X86FlagChoices.Choice) (en : ExecEntry) (inp : ProcInput)
    (message : List Byte) : Prop :=
  inp.stdin = InputStream.ofList message ∧ X86Launch.ValidInput inp ∧
    X86Launch.ValidEntry (machine oracle) snapshot en inp

/-- Partial correctness of one behaviour. -/
structure Partial (b : Behavior) (message : List Byte) (fs : FileSystem) : Prop where
  errorFree : ErrorFree b
  modeled : ¬ b.unmodeled
  safe : ∀ tr, b.traces tr → tr <+: idealTrace message fs

/-- Total correctness of one launch. -/
structure Total (oracle : Nat → X86FlagChoices.Choice) (refusals : SpuriousCfg) (limit : Int)
    (en : ExecEntry) (inp : ProcInput) (message : List Byte) : Prop where
  safety : Partial (behaviour oracle refusals limit en inp) message inp.fs
  mustExit : MustExitInAt snapshot.image.segments NativeX86.extendedSyscallSpec
    (NativeX86.defaultRefusalFilter refusals) [0] (initial oracle limit en inp)
  complete : (behaviour oracle refusals limit en inp).traces (idealTrace message inp.fs)

/-- Total correctness on the messages of `domain`. -/
def TotalOn (domain : List Byte → Prop) : Prop :=
  ∀ (oracle : Nat → X86FlagChoices.Choice) (refusals : SpuriousCfg) (limit : Int)
    (en : ExecEntry) (inp : ProcInput) (message : List Byte),
    domain message → Admissible oracle en inp message → Total oracle refusals limit en inp message

/-- **The target**: total correctness on every finite standard input. -/
def TotalGoal : Prop := TotalOn fun _ => True

/-- Partial correctness on every finite standard input. -/
def PartialGoal : Prop :=
  ∀ (oracle : Nat → X86FlagChoices.Choice) (refusals : SpuriousCfg) (limit : Int)
    (en : ExecEntry) (inp : ProcInput) (message : List Byte),
    Admissible oracle en inp message →
      Partial (behaviour oracle refusals limit en inp) message inp.fs

/-- Total correctness for inputs of at most `n` bytes. -/
def BoundedGoal (n : Nat) : Prop := TotalOn fun message => message.length ≤ n

/-! ## The tiers are ordered (VERIFIED) -/

theorem partialGoal_of_totalGoal (h : TotalGoal) : PartialGoal :=
  fun oracle refusals limit en inp message admissible =>
    (h oracle refusals limit en inp message trivial admissible).safety

theorem boundedGoal_of_totalGoal (h : TotalGoal) (n : Nat) : BoundedGoal n :=
  fun oracle refusals limit en inp message _ admissible =>
    h oracle refusals limit en inp message trivial admissible

theorem TotalOn.mono {domain domain' : List Byte → Prop} (h : TotalOn domain')
    (sub : ∀ message, domain message → domain' message) : TotalOn domain :=
  fun oracle refusals limit en inp message member admissible =>
    h oracle refusals limit en inp message (sub message member) admissible

/-! ## The conclusion is not trivial (VERIFIED)

`idealTrace` fixes the output: no write to stderr, no second exit, no exit with another status,
and nothing read beyond the message is a prefix of it. -/

theorem idealTrace_length (message : List Byte) (fs : FileSystem) :
    (idealTrace message fs).length = message.length + 66 := by
  simp [idealTrace, CLI.Sha256.expected_length]

theorem stderr_not_prefix (message : List Byte) (fs : FileSystem) (b : Byte) :
    ¬ (message.map (Event.readEv 0) ++ [Event.writeEv 2 b]) <+: idealTrace message fs := by
  rintro ⟨rest, h⟩
  simp only [idealTrace, List.append_assoc] at h
  have h' := List.append_cancel_left h
  cases hexp : CLI.Sha256.expected message with
  | nil =>
    have length := CLI.Sha256.expected_length message
    rw [hexp] at length
    simp at length
  | cons d ds =>
    rw [hexp] at h'
    simp only [List.map_cons, List.cons_append, List.cons.injEq] at h'
    exact absurd h'.1 (by simp)

theorem wrong_status_not_prefix (message : List Byte) (fs fs' : FileSystem) (code : Word)
    (nonzero : code ≠ 0) :
    ¬ (message.map (Event.readEv 0) ++ (CLI.Sha256.expected message).map (Event.writeEv 1) ++
      [Event.exitEv code fs']) <+: idealTrace message fs := by
  rintro ⟨rest, h⟩
  simp only [idealTrace, List.append_assoc] at h
  have h' := List.append_cancel_left (List.append_cancel_left h)
  simp only [List.singleton_append, List.cons.injEq] at h'
  exact nonzero (by injection h'.1)

end Silmaril.Process.LPS.Problems.Sha256Cli
