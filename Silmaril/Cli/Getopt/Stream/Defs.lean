module

public import Silmaril.Cli.Getopt.Defs

/-!
# getopt as a stream of results

`Silmaril.Cli.Getopt.parse` reads an argument vector the way a program that stops at the first
usage error sees it. A C program calls `getopt` in a loop instead, and each call returns one
result. This file models two readings of that loop.

**Going on after errors** (`parseAll`). On a usage error getopt prints a diagnostic, returns `?`
and goes on with the next character of a cluster (`-xq` with an unknown `x` still reads `-q`)
or with the next token. `parseAll t ord argv` is the whole loop: the results in order
(`Event`: an option with its argument, or a diagnostic), then the operands. A program that
ignores `?` sees the options of `Report.opts`; `Report.errors` are the diagnostics.
`Silmaril.Cli.Getopt.Stream.Thms` proves that without a usage error the loop reads what `parse`
reads (`parseAll_ok`), and that its first diagnostic is the error `parse` stops at
(`parseAll_error`).

**Operands in order** (`parseInOrder`). With an optstring starting with `-` (GNU's
`RETURN_IN_ORDER`), getopt returns every operand in place, as the argument of the option
character code 1, so a program sees options and operands interleaved; only the tokens after
`--` remain operands. `parseInOrder t argv` gives the results in order (`Event.operand` for an
operand; `-` alone is an operand) and the operands after `--`. Forgetting the interleaving
gives the GNU permuting reading (`parseInOrder_permute`).

A Silmaril addition; the guide is `docs/projects/cli.md`.
-/

@[expose] public section

namespace Silmaril.Cli.Getopt

open Silmaril.Cli

/-- What one call of `getopt` returns. -/
inductive Event where
  /-- an option, by key, with its argument -/
  | opt (key : String) (g : Given)
  /-- an operand returned in place (character code 1, with an optstring starting with `-`) -/
  | operand (w : String)
  /-- `?`: a usage error, with the diagnostic -/
  | error (e : Error)
  deriving DecidableEq, Repr, Inhabited

/-- The option of an event. -/
def Event.opt? : Event → Option (String × Given)
  | .opt k g => some (k, g)
  | _ => none

/-- The operand of an event. -/
def Event.operand? : Event → Option String
  | .operand w => some w
  | _ => none

/-- The diagnostic of an event. -/
def Event.error? : Event → Option Error
  | .error e => some e
  | _ => none

/-- Option occurrences as events. -/
def Event.ofOpts (ps : List (String × Given)) : List Event := ps.map fun p => .opt p.1 p.2

/-- The events of a reading of one token: its occurrences, or one diagnostic (`b`: whether
the next token counts as consumed on an error). -/
def Event.ofRead (b : Bool) : Except Error Read → List Event × Bool
  | .ok (ps, c) => (Event.ofOpts ps, c)
  | .error e => ([.error e], b)

/-! ## Going on after errors -/

/-- A cluster, going on after an unknown character (glibc reads the next character). -/
def readClusterAll (t : Table) (tok : String) (next : Option String) :
    List Char → List Event × Bool
  | [] => ([], false)
  | ch :: r =>
    if t.wLong && ch == 'W' then
      Event.ofRead (r.isEmpty && next.isSome) (readCluster t tok next (ch :: r))
    else
    match findChar t ch with
    | none =>
      let q := readClusterAll t tok next r
      (.error (.unknown tok) :: q.1, q.2)
    | some s =>
      match s.arg with
      | .none =>
        let q := readClusterAll t tok next r
        (.opt s.key .on :: q.1, q.2)
      | _ => Event.ofRead false (readCluster t tok next (ch :: r))

/-- One option token, going on after errors: the events, and whether the next token was
consumed. -/
def readTokAll (t : Table) (tok : String) (next : Option String) : List Event × Bool :=
  match classify tok with
  | .short n =>
    if t.longOnly then Event.ofRead false (readLongOnly t tok next n.toList)
    else readClusterAll t tok next n.toList
  | _ => Event.ofRead false (readTok t tok next)

/-- The whole `getopt` loop: the results in order, the operands, and whether `--` ended the
options. -/
structure Report where
  events : List Event := []
  operands : List String := []
  dashdash : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- The options a program that skips `?` sees. -/
def Report.opts (r : Report) : List (String × Given) := r.events.filterMap Event.opt?

/-- The diagnostics, in order. -/
def Report.errors (r : Report) : List Error := r.events.filterMap Event.error?

/-- Events in front of a report. -/
def Report.cons (es : List Event) (r : Report) : Report := { r with events := es ++ r.events }

/-- A reading without errors as a report. -/
def Report.ofParsed (p : Parsed) : Report :=
  { events := Event.ofOpts p.opts, operands := p.operands, dashdash := p.dashdash }

/-- **The `getopt` loop, going on after usage errors.** -/
def parseAll (t : Table) (ord : Order) : List String → Report
  | [] => {}
  | tok :: rest =>
    match classify tok with
    | .dashdash => { operands := rest, dashdash := true }
    | .word _ =>
      match ord with
      | .requireOrder => { operands := tok :: rest }
      | .permute =>
        let r := parseAll t ord rest
        { r with operands := tok :: r.operands }
    | _ =>
      match readTokAll t tok rest.head? with
      | (es, false) => (parseAll t ord rest).cons es
      | (es, true) =>
        match rest with
        -- not reached: a token consumes the next one only when there is one
        | [] => { events := es ++ [.error (.missing tok)] }
        | _ :: rest' => (parseAll t ord rest').cons es

/-! ## Operands in order -/

/-- **The `getopt` loop with an optstring starting with `-`**: options and operands in order,
then the operands after `--`; the first usage error ends the reading. -/
def parseInOrder (t : Table) : List String → Except Error (List Event × List String)
  | [] => .ok ([], [])
  | tok :: rest =>
    match classify tok with
    | .dashdash => .ok ([], rest)
    | .word _ => (parseInOrder t rest).map fun r => (.operand tok :: r.1, r.2)
    | _ =>
      match readTok t tok rest.head? with
      | .error e => .error e
      | .ok (ps, false) => (parseInOrder t rest).map fun r => (Event.ofOpts ps ++ r.1, r.2)
      | .ok (ps, true) =>
        match rest with
        | [] => .error (.missing tok)
        | _ :: rest' => (parseInOrder t rest').map fun r => (Event.ofOpts ps ++ r.1, r.2)

/-- The options, and the operands (those returned in order, then those after `--`), of an
in-order reading. -/
def splitInOrder (r : List Event × List String) : List (String × Given) × List String :=
  (r.1.filterMap Event.opt?, r.1.filterMap Event.operand? ++ r.2)

/-- The in-order reading of a tool (its table). -/
def Tool.parseInOrder (t : Tool) (argv : List String) : Except Error (List Event × List String) :=
  Getopt.parseInOrder t.table argv

/-- The `getopt` loop of a tool in an environment, going on after errors. -/
def Tool.parseAll (t : Tool) (env : String → Option String) (argv : List String) : Report :=
  Getopt.parseAll t.table (t.order env) argv

end Silmaril.Cli.Getopt
