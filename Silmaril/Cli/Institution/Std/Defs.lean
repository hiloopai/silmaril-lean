module

public import Silmaril.Cli.Institution.Defs
public import Silmaril.Apps.Sha256sum.StdinRef

/-!
# Standard sentences of the CLI institution

Named sentences that implementations of standard problems share, so that every program
meeting a standard problem states it the same way.

| sentence | level | meaning |
|---|---|---|
| `Std.hello` | `L1` | prints `hello, world\n`, exit `0` |
| `Std.cat` | `L1` | stdin to stdout unchanged, exit `0` |
| `Std.sha256Stdin` | `L1` | `hex(SHA-256(stdin)) ++ "  -\n"`, exit `0` (GNU `sha256sum`, no operands) |
| `Problem.sen P` | `L1` | a judged stdin → stdout problem (leetcode style) |

**Judged problems** (`Problem`): a parser of the input bytes, a predicate on the parsed input and
the answer bytes, and the sentence `Problem.sen P`: on every stdin that parses, stdout is an
accepted answer and the exit code `0`; stdin that does not parse is unconstrained (a
precondition). A leetcode-style problem is one `Problem` value; each of its solutions (for
instance a C program compiled by various compilers at various optimization levels) is stated
against `Level.lift (Problem.sen P)` or, at `L1`, against `Problem.sen P`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli.Institution.Std

open Level

/-- `hello, world` and a newline. -/
def helloBytes : Bytes := utf8 "hello, world\n"

/-- **Hello world** (`L1`). -/
def hello : Sen Level.stream.sig := Sen.prints helloBytes

/-- **cat** (`L1`): stdin to stdout. -/
def cat : Sen Level.stream.sig := Sen.filter id

/-- **sha256sum on stdin** (`L1`): GNU coreutils' output line for standard input. -/
def sha256Stdin : Sen Level.stream.sig := Sen.filter Silmaril.Apps.Sha256sum.Sys.stdinRecord

end Silmaril.Cli.Institution.Std

namespace Silmaril.Cli.Institution

/-- **A judged stdin → stdout problem** (leetcode style). -/
structure Problem : Type 1 where
  /-- The problem's name (e.g. `"leetcode.1.two-sum"`). -/
  name : String
  /-- The parsed input. -/
  Inp : Type
  /-- The input format: the parse of stdin, `none` when stdin is not a valid input. -/
  parse : Bytes → Option Inp
  /-- The answers accepted for an input (as bytes on stdout). -/
  accepts : Inp → Bytes → Prop

/-- **The sentence of a judged problem** (`L1`): on stdin that parses, an accepted answer and
exit `0`; on stdin that does not parse, nothing (neither stdout nor the exit code). -/
def Problem.sen (P : Problem) : Sen Level.stream.sig :=
  fun (s : Bytes) (o : Out1) => ∀ x, P.parse s = some x → P.accepts x o.stdout ∧ o.exit = 0

/-- A problem with a unique answer, given by a reference function. -/
def Problem.ofFn (name : String) {α : Type} (parse : Bytes → Option α) (answer : α → Bytes) :
    Problem :=
  ⟨name, α, parse, fun x out => out = answer x⟩

end Silmaril.Cli.Institution
