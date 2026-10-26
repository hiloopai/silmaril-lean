module

public import Silmaril.Process.CLI.Spec
public import Silmaril.Crypto.SHA256

/-! # The specification of a `sha256` filter

The program reads standard input to end of file and writes the lowercase hex
SHA-256 digest of the bytes read, followed by a newline, to standard output,
then exits 0. The digest is `Silmaril.Crypto.SHA256.digest`, the spec the
#882 pilot proved the compression function against.

The specification is stated on trace projections only (`CLI.stdout`,
`CLI.stdinRead`), so it does not depend on how the program splits its reads
and writes, and it makes no claim about an infinite input stream other than
that nothing may be printed before the input ends.

Failure is allowed, but only when explained: a nonzero exit status requires a
refusal by the environment in the trace (an error return or a write that
accepted nothing). This one rule gives the strong statement in a reliable
environment as a theorem (`exits_of_noRefusal`) instead of a second spec.

`lenient` additionally lets a program exit 0 after a refusal (one that does
not check write errors); `strict.Le lenient`.

`checkExit` is an executable decision procedure for the exit clause on a finite
input, proved sound: the oracle for a pipe fuzzer that records the event trace
of the binary under test and injects short transfers and errors.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256

open Silmaril.Process.Syscall

/-- A lowercase hex digit, as an ASCII byte. -/
def hexDigit (n : Nat) : Byte := BitVec.ofNat 8 (if n < 10 then 0x30 + n else 0x61 + (n - 10))

def hexByte (byte : UInt8) : List Byte := [hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)]

/-- The exact output for a message: 64 hex digits and a newline. -/
def expected (message : List Byte) : List Byte :=
  (Silmaril.Crypto.SHA256.digest (message.map UInt8.ofBitVec)).flatMap hexByte ++ [0x0a]

theorem flatMap_hexByte_length (bytes : List UInt8) :
    (bytes.flatMap hexByte).length = 2 * bytes.length := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
    simp only [List.flatMap_cons, List.length_append, ih, hexByte, List.length_cons,
      List.length_nil]
    omega

@[simp] theorem expected_length (message : List Byte) : (expected message).length = 65 := by
  rw [expected, List.length_append, flatMap_hexByte_length, Silmaril.Crypto.SHA256.digest_length]
  rfl

/-- Before the input is known to end, nothing is printed; after, only a prefix
of the answer. Nothing is written to any descriptor but stdout. -/
def PrefixOk (input : ProcInput) (events : List Event) : Prop :=
  WritesOnlyTo [1] events ∧
    (stdout events = [] ∨ ∃ message, input.stdin = .ofList message ∧ stdout events <+: expected message)

/-- Success means the whole input was read and the exact answer written. -/
def Success (input : ProcInput) (events : List Event) : Prop :=
  ∃ message, input.stdin = .ofList message ∧ stdinRead events = message ∧ SawEof 0 events ∧
    stdout events = expected message

def strict : CliSpec where
  prefixOk := PrefixOk
  exitOk input events status := (status = 0 ∧ Success input events) ∨ (status ≠ 0 ∧ Refused events)

def lenient : CliSpec where
  prefixOk := PrefixOk
  exitOk input events status := (status = 0 ∧ Success input events) ∨ Refused events

/-- Correctness of returned answers only. Nonzero exits, crashes, blocking and
divergence need no justification. This alone gives no guarantee about bytes
emitted by a run that subsequently fails. -/
def completed : CliSpec where
  prefixOk _ _ := True
  exitOk input events status := status = 0 → Success input events

/-- Prefix safety alone, including prefixes of failing or diverging runs. -/
def prefixes : CliSpec where
  prefixOk := PrefixOk
  exitOk _ _ _ := True

/-- The default partial contract: permitted output prefixes, and exact answers
on successful completion. Progress and explanations for failure are optional. -/
def partialCorrect : CliSpec where
  prefixOk := PrefixOk
  exitOk input events status := status = 0 → Success input events

theorem strict_le_partial : strict.Le partialCorrect := by
  refine ⟨fun _ _ h => h, ?_⟩
  rintro input events status (⟨_, success⟩ | ⟨nonzero, _⟩) zero
  · exact success
  · exact (nonzero zero).elim

/-- The two safety levels can be established and consumed independently. -/
theorem agrees_partial_iff {M : Model} {image : Image} :
    Agrees M image partialCorrect ↔ Agrees M image prefixes ∧ Agrees M image completed := by
  constructor
  · intro h
    constructor
    · intro input x valid init events y run
      exact ⟨(h input x valid init events y run).1, fun _ _ => trivial⟩
    · intro input x valid init events y run
      exact ⟨trivial, (h input x valid init events y run).2⟩
  · rintro ⟨hp, hc⟩ input x valid init events y run
    exact ⟨(hp input x valid init events y run).1, (hc input x valid init events y run).2⟩

theorem strict_le_lenient : strict.Le lenient := by
  refine ⟨fun _ _ h => h, ?_⟩
  rintro input events status (ok | ⟨_, refused⟩)
  · exact .inl ok
  · exact .inr refused

/-- In an environment that never refuses, every exit of a program meeting
`strict` is a success. -/
theorem exits_of_noRefusal {M : Model} {image : Image} (h : Agrees M image strict)
    (noRefusal : M.env.EventsSatisfy fun e => ¬ e.IsRefusal)
    {input : ProcInput} {x : PState M.isa M.env} (valid : input.Valid) (init : M.Init image input x)
    {events : List Event} {y : PState M.isa M.env} (run : Proc.Runs M.isa M.env x events y)
    {status : Nat} (stop : Proc.Stop M.isa M.env y (.exited status)) :
    status = 0 ∧ Success input events := by
  rcases (h input x valid init events y run).2 status stop with ok | ⟨_, refused⟩
  · exact ok
  · exfalso
    obtain ⟨e, member, refusal⟩ := refused
    obtain ⟨s, q, r, s', step⟩ := Proc.runs_events_admitted run e member
    exact noRefusal s q e r s' step refusal

/-! ## An executable exit oracle -/

def checkExit (message : List Byte) (events : List Event) (status : Nat) : Bool :=
  (status == 0 && stdinRead events == message && events.contains (.read 0 []) &&
      stdout events == expected message) ||
    (status != 0 && events.any fun e => decide e.IsRefusal)

theorem checkExit_sound {input : ProcInput} {message : List Byte}
    (stdin : input.stdin = .ofList message) {events : List Event} {status : Nat}
    (check : checkExit message events status = true) : strict.exitOk input events status := by
  simp only [checkExit, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    List.contains_iff_mem, List.any_eq_true, decide_eq_true_eq] at check
  rcases check with ⟨⟨⟨zero, read⟩, eof⟩, out⟩ | ⟨nonzero, e, member, refusal⟩
  · exact .inl ⟨zero, message, stdin, read, eof, out⟩
  · exact .inr ⟨nonzero, e, member, refusal⟩

end Silmaril.Process.CLI.Sha256
