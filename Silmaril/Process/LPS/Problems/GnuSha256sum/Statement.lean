module

public import Silmaril.Process.LPS.Problems.GnuSha256sum.Elf
public import Silmaril.Process.LPS.Problems.Sha256Cli.Segments
public import Silmaril.Process.LPS.Machines.X86FlagChoices8

/-! # GNU `sha256sum`, end to end in LPS: the target statements (stdin tier)

**Binary.** The pinned ELF `sha256sum-min` (`GnuSha256sum.elfNat`, 35512 bytes, SHA-256
`22fa6345…d42817`): the static, libc-free x86-64 reimplementation of every option of GNU
coreutils 9.4 `sha256sum` (`apps/sha256sum-min`), whose loadable segments
`Apps.Sha256sum.Binary.Image` transcribes.

**Specification.** `Apps.Sha256sum.sha256sum : World → Outcome`, the executable model of
GNU `sha256sum`. On the stdin tier (argv is just the program name, no operand) the program
reads standard input to its end and prints `hex(SHA-256(stdin)) ++ "  -\n"`, exit status 0
(`Apps.Sha256sum.Sys.sha256sum_stdin`). `expected message` is *defined* as the spec's
`stdout` on such a world, and `spec_stdin` shows it is that same record (and status 0, empty
stderr) for every world of the tier: every program name, `POSIXLY_CORRECT` set or not, any
file system.

**Semantics.** As for the `sha256` filter (`Sha256Cli.Statement`): LPS with the native x86-64
launch, over `Machines.x86WithFlagOracle8 oracle` (the filter's machine with the `X86.Ext8`
8-bit ALU forms, which gcc uses about 300 times in this driver) for every flag oracle, every refusal
configuration and every budget. On this path the binary issues `read(0)` until EOF,
`write(1)` (the stdout buffer, flushed by `close_stdout`), `close(0)`, `close(1)`, `close(2)`
and `exit_group(0)`. `close` is not an LPS event, and none of these calls has an injected
failure (they are not in LPS's `injectedTable`).

**Tiers** (each a `Prop`; none is asserted in this file):

* `TotalGoal`: on every finite stdin and every argv of one element, every launch is error
  free, nothing is unmodelled, every observable trace is a prefix of `idealTrace` (read the
  input, write exactly `(sha256sum w).stdout` to fd 1, exit 0 with the file system
  unchanged), every execution exits with status 0, and the complete ideal trace occurs.
* `PartialGoal`: the first three only (safety).
* `BoundedGoal n`: `TotalGoal` for inputs of at most `n` bytes.

Status: everything proved in this file is VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.GnuSha256sum

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.Process.LPS.Fs (FileSystem)

/-- The user machine: native x86-64 with an explicit oracle for undefined flags at `syscall`,
over the `X86.Ext8` variant (the `sha256` filter's machine plus the 8-bit ALU forms; the
plain `X86.Ext` machine is `unmodeled` at the driver's first byte compare, for example
`cmp %cl,0x20(%rsp)` at `0x403c53` on the stdin path). -/
abbrev machine (oracle : Nat → X86FlagChoices.Choice) : UserIsa := x86WithFlagOracle8 oracle

/-- The LPS behaviour of the pinned binary. -/
def behaviour (oracle : Nat → X86FlagChoices.Choice) (refusals : SpuriousCfg) (limit : Int)
    (en : ExecEntry) (inp : ProcInput) : Behavior :=
  X86NativeLaunch.runWith (machine oracle) refusals snapshot limit en inp

/-- Its initial configuration. -/
def initial (oracle : Nat → X86FlagChoices.Choice) (limit : Int) (en : ExecEntry)
    (inp : ProcInput) : Config (machine oracle) :=
  X86Launch.init (machine oracle) snapshot en limit inp

/-! ## The specification side -/

/-- Bytes of the LPS model as bytes of the specification. -/
def toSpec (bytes : List Byte) : Apps.Sha256sum.Bytes := bytes.map UInt8.ofBitVec

/-- The specification world of a stdin-tier launch: argv as given, standard input the
message, `POSIXLY_CORRECT` and the file oracle arbitrary (they are not consulted). -/
def world (argv : List (List Byte)) (posix : Bool) (fs : Apps.Sha256sum.Bytes → Apps.Sha256sum.ReadResult)
    (message : List Byte) : Apps.Sha256sum.World :=
  { argv := argv.map toSpec, posix, fs, stdin := .bytes (toSpec message) }

/-- A reference world of the stdin tier: program name `sha256sum`, no file. -/
def stdinWorld (message : List Byte) : Apps.Sha256sum.World :=
  world [(Apps.Sha256sum.lit "sha256sum").map UInt8.toBitVec] false
    (fun _ => .openErr .ENOENT) message

/-- **The required output**: GNU `sha256sum`'s standard output on the message, by the
specification. -/
def expected (message : List Byte) : List Byte :=
  (Apps.Sha256sum.sha256sum (stdinWorld message)).stdout.map UInt8.toBitVec

/-- On every stdin-tier world the specification prints the stdin record, nothing on stderr,
and exits 0. -/
theorem spec_stdin (prog : List Byte) (posix : Bool)
    (fs : Apps.Sha256sum.Bytes → Apps.Sha256sum.ReadResult) (message : List Byte) :
    Apps.Sha256sum.sha256sum (world [prog] posix fs message) =
      { stdout := Apps.Sha256sum.Sys.stdinRecord (toSpec message), stderr := [], status := 0 } :=
  Apps.Sha256sum.Sys.sha256sum_stdin _ _ _ _

/-- `expected` is the specification's stdout on **every** stdin-tier world. -/
theorem expected_eq_spec (prog : List Byte) (posix : Bool)
    (fs : Apps.Sha256sum.Bytes → Apps.Sha256sum.ReadResult) (message : List Byte) :
    expected message =
      (Apps.Sha256sum.sha256sum (world [prog] posix fs message)).stdout.map UInt8.toBitVec := by
  simp only [expected, stdinWorld, spec_stdin]

/-- The specification's status on every stdin-tier world is 0 and its stderr is empty. -/
theorem spec_status (prog : List Byte) (posix : Bool)
    (fs : Apps.Sha256sum.Bytes → Apps.Sha256sum.ReadResult) (message : List Byte) :
    (Apps.Sha256sum.sha256sum (world [prog] posix fs message)).status = 0 ∧
      (Apps.Sha256sum.sha256sum (world [prog] posix fs message)).stderr = [] := by
  simp [spec_stdin]

/-- `expected` is the stdin record. -/
theorem expected_eq_record (message : List Byte) :
    expected message = (Apps.Sha256sum.Sys.stdinRecord (toSpec message)).map UInt8.toBitVec := by
  simp only [expected, stdinWorld, spec_stdin]

/-- `expected` is the `sha256` filter's output with `"\n"` replaced by `"  -\n"`. -/
theorem expected_eq_filter (message : List Byte) :
    expected message = (CLI.Sha256.expected message).dropLast ++ [0x20, 0x20, 0x2d, 0x0a] := by
  rw [expected_eq_record]; exact Sha256Cli.gnu_stdout message

@[simp] theorem expected_length (message : List Byte) : (expected message).length = 68 := by
  rw [expected_eq_record, List.length_map]; exact Apps.Sha256sum.Sys.stdinRecord_length _

/-! ## The LPS statements -/

/-- The only complete observation allowed: read the message, write `expected message` to
fd 1, exit 0 with the file system `fs`. -/
def idealTrace (message : List Byte) (fs : FileSystem) : List Event :=
  message.map (Event.readEv 0) ++ (expected message).map (Event.writeEv 1) ++
    [Event.exitEv 0 fs]

/-- A guarded stdin-tier launch: finite standard input, argv of exactly the program name. -/
def Admissible (oracle : Nat → X86FlagChoices.Choice) (en : ExecEntry) (inp : ProcInput)
    (message : List Byte) : Prop :=
  inp.stdin = InputStream.ofList message ∧ inp.argv.length = 1 ∧ X86Launch.ValidInput inp ∧
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

/-- **The target** (stdin tier): total correctness on every finite standard input. -/
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

`idealTrace` fixes the output: 68 bytes, the `sha256` filter's digits followed by `"  -\n"`
(so the filter's own trace is *not* allowed), no write to stderr and no exit with another
status. -/

theorem idealTrace_length (message : List Byte) (fs : FileSystem) :
    (idealTrace message fs).length = message.length + 69 := by
  simp [idealTrace]

theorem stderr_not_prefix (message : List Byte) (fs : FileSystem) (b : Byte) :
    ¬ (message.map (Event.readEv 0) ++ [Event.writeEv 2 b]) <+: idealTrace message fs := by
  rintro ⟨rest, h⟩
  simp only [idealTrace, List.append_assoc] at h
  have h' := List.append_cancel_left h
  cases hexp : expected message with
  | nil =>
    have length := expected_length message
    rw [hexp] at length
    simp at length
  | cons d ds =>
    rw [hexp] at h'
    simp only [List.map_cons, List.cons_append, List.cons.injEq] at h'
    exact absurd h'.1 (by simp)

theorem wrong_status_not_prefix (message : List Byte) (fs fs' : FileSystem) (code : Word)
    (nonzero : code ≠ 0) :
    ¬ (message.map (Event.readEv 0) ++ (expected message).map (Event.writeEv 1) ++
      [Event.exitEv code fs']) <+: idealTrace message fs := by
  rintro ⟨rest, h⟩
  simp only [idealTrace, List.append_assoc] at h
  have h' := List.append_cancel_left (List.append_cancel_left h)
  simp only [List.singleton_append, List.cons.injEq] at h'
  exact nonzero (by injection h'.1)

/-- The `sha256` filter's complete trace (digits and `"\n"`) is not allowed here. -/
theorem filter_trace_not_prefix (message : List Byte) (fs : FileSystem) :
    ¬ Sha256Cli.idealTrace message fs <+: idealTrace message fs := by
  rintro ⟨rest, h⟩
  -- the filter's 65th output byte is `"\n"`, ours is `' '`
  simp only [Sha256Cli.idealTrace, idealTrace, List.append_assoc] at h
  have h' := List.append_cancel_left h
  rw [expected_eq_filter] at h'
  obtain ⟨digits, last, hsplit⟩ : ∃ digits last, CLI.Sha256.expected message = digits ++ [last] ∧
      last = 0x0a := by
    refine ⟨(CLI.Sha256.expected message).dropLast, 0x0a, ?_, rfl⟩
    simp [CLI.Sha256.expected]
  obtain ⟨hsplit, rfl⟩ := hsplit
  rw [hsplit] at h'
  simp only [List.dropLast_concat, List.map_append, List.map_cons, List.map_nil,
    List.append_assoc, List.cons_append, List.nil_append] at h'
  have h'' := List.append_cancel_left h'
  simp only [List.cons.injEq] at h''
  exact absurd h''.1 (by decide)

end Silmaril.Process.LPS.Problems.GnuSha256sum
