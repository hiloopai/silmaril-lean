module

public import Silmaril.Cli.Institution.Std.Defs
public import Silmaril.Apps.Sha256sum.Run

/-!
# The standard `sha256sum` specification, at every level of the CLI institution

One specification of GNU coreutils' `sha256sum`, for every implementation (glibc and musl
builds, WASI components, binaries in a simulator) to be stated against. The behaviour is
silmaril's `Silmaril.Apps.Sha256sum.sha256sum : World → Outcome` (all options, checking mode,
error messages); this module reads it on the invocations of `Silmaril.Cli` and restricts it to
**input domains**, the restrictions under which an implementation is proved.

**Invocations as worlds.** `world conv i`: `argv` is the program name and the arguments in
UTF-8, `POSIXLY_CORRECT` is read from the environment, standard input is `i.stdin` (a byte
stream), stdout is not a full device, and an operand `p` reads the file `conv p` of `i.fs`
(a path that names no file, or that `conv` cannot place, fails to open with `ENOENT`).

**Levels.**

| name | level | statement |
|---|---|---|
| `stdin` | `L1` | `Std.sha256Stdin`: stdout `hex(SHA-256(stdin)) ++ "  -\n"`, exit `0` |
| `cmd`, `cmdOn D` | `L2` | program name, arguments, stdin; no files (every operand is missing): stdout, stderr and exit code of the specification |
| `spec conv D` | `L3` | on invocations in the domain `D`: stdout, stderr, exit code of the specification, and no file changed |

**Domains** (`Dom`): `Dom.all`; `Dom.stdin` (no arguments); `Dom.files conv` (at least one
operand, every operand plain and naming a file); `Dom.mixed conv` (every operand plain and
naming a file or missing, the tier of the file-error proof). An operand is **plain**
(`PlainOp`) when it is non-empty, does not start with `-`, holds no NUL, and holds no `\`,
newline or carriage return (so the output line shows it verbatim); a missing operand's quoted
form must fit gnulib's 256-byte quoting slot (`QuoteFits`).

`Thms`: the levels are related by the level morphisms (`spec_le_lift_stdin`,
`spec_le_lift_cmd`), so an implementation proved at `L3` meets `stdin` and `cmd` through its
reducts; domains are monotone (`spec_anti`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli.Spec.Sha256sum

open Silmaril.Cli.Institution (Level Sen Out1 In2)
open Silmaril.Apps.Sha256sum (World Outcome ReadResult)

/-! ## Invocations as worlds -/

/-- **A path convention**: the file of the invocation that a byte path names, if any. -/
abbrev PathConv : Type := List UInt8 → Option FPath

/-- The read oracle of an invocation's files: a file is read whole; anything else fails to
open with `ENOENT`. -/
def readOf (conv : PathConv) (i : Input) (p : List UInt8) : ReadResult :=
  match conv p >>= i.fs with
  | some d => .ok d
  | none => .openErr .ENOENT

/-- **The world of an invocation.** -/
def world (conv : PathConv) (i : Input) : World where
  argv := (i.prog :: i.args).map utf8
  posix := (i.getEnv "POSIXLY_CORRECT").isSome
  fs := readOf conv i
  stdin := .bytes i.stdin
  stdoutFull := false

/-- The outcome of the specification on an invocation. -/
abbrev outcome (conv : PathConv) (i : Input) : Outcome :=
  Silmaril.Apps.Sha256sum.sha256sum (world conv i)

/-! ## Domains -/

/-- A domain of invocations. -/
abbrev Dom : Type := Input → Prop

/-- **A plain operand**: non-empty, not an option, no NUL, and shown verbatim on the output
line (no `\`, newline or carriage return). -/
def PlainOp (a : String) : Prop :=
  utf8 a ≠ [] ∧ (utf8 a).head? ≠ some 45 ∧ ∀ c ∈ utf8 a, c ≠ 0 ∧ c ≠ 92 ∧ c ≠ 10 ∧ c ≠ 13

/-- gnulib's quoted form of a missing operand fits its 256-byte quoting slot. -/
def QuoteFits (a : String) : Prop := (Silmaril.Apps.Sha256sum.quotef (utf8 a)).length < 256

/-- The operand names a file of the invocation. -/
def Present (conv : PathConv) (i : Input) (a : String) : Prop := ∃ d, (conv (utf8 a)).bind i.fs = some d

namespace Dom

/-- Every invocation. -/
def all : Dom := fun _ => True

/-- No arguments: the digest of standard input. -/
def stdin : Dom := fun i => i.args = []

/-- **The success tier**: at least one operand, each plain and naming a file. -/
def files (conv : PathConv) : Dom := fun i =>
  i.args ≠ [] ∧ ∀ a ∈ i.args, PlainOp a ∧ Present conv i a

/-- **The file-error tier**: at least one operand, each plain and naming a file, or missing
with a quoted form that fits gnulib's slot. -/
def mixed (conv : PathConv) : Dom := fun i =>
  i.args ≠ [] ∧ ∀ a ∈ i.args, PlainOp a ∧ (Present conv i a ∨ (¬ Present conv i a ∧ QuoteFits a))

end Dom

/-! ## The specification at each level -/

/-- **`L3`: the standard `sha256sum` specification on a domain**: stdout, stderr and the exit
code (the status modulo 256) are the specification's, and no file changed. -/
def spec (conv : PathConv) (D : Dom := Dom.all) : Spec := fun i o =>
  D i → o.stdout = (outcome conv i).stdout ∧ o.stderr = (outcome conv i).stderr ∧
    o.exit = UInt8.ofNat (outcome conv i).status ∧ o.fs = i.fs

/-- The world of an `L2` invocation: no environment, no files (every operand fails to open
with `ENOENT`). -/
def worldCmd (a : In2) : World where
  argv := (a.prog :: a.args).map utf8
  posix := false
  fs := fun _ => .openErr .ENOENT
  stdin := .bytes a.stdin
  stdoutFull := false

/-- The `L2` observation of an outcome. -/
def outOf (r : Outcome) : Spec.Out :=
  { stdout := r.stdout, stderr := r.stderr, exit := UInt8.ofNat r.status }

/-- **`L2`: the specification without files** (every operand is missing). -/
def cmd : Sen Level.command.sig :=
  Sen.command fun a => outOf (Silmaril.Apps.Sha256sum.sha256sum (worldCmd a))

/-- `L2` on a domain of `L2` invocations. -/
def cmdOn (D : In2 → Prop) : Sen Level.command.sig := fun a o => D a → cmd a o

/-- The `L2` file-error tier: at least one operand, each plain, with a quoted form that fits
gnulib's slot (at `L2` every operand is missing). -/
def Dom2.missing : In2 → Prop := fun a =>
  a.args ≠ [] ∧ ∀ x ∈ a.args, PlainOp x ∧ QuoteFits x

/-- **`L1`: the digest line of standard input** (the standard sentence `Std.sha256Stdin`). -/
abbrev stdin : Sen Level.stream.sig := Silmaril.Cli.Institution.Std.sha256Stdin

end Silmaril.Cli.Spec.Sha256sum
