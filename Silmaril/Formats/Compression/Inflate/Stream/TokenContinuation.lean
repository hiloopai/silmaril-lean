module

public import Silmaril.Formats.Compression.Inflate.Stream.TokenMachine

/-!
# Total denotations of suspended token machines

A suspended parser denotes its remaining parsing
program followed by token application. A suspended output phase denotes checked
completion of its remaining output, including overlapping copies. This is a
logical continuation semantics: it does not run the physical machine to find a
large enough scheduler budget or require a successful input.

The invariant explicitly restricts successful parsing continuations to RFC token
ranges, while allowing unavailable history to produce the specification's error.
Each physical step preserves the denotation under every later input extension.
No C/Core/assembly execution correspondence is asserted.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.TokenContinuation

open Silmaril.Formats.Compression

/-- RFC bounds are properties of successful tokens, not of arbitrary parser
programs. In particular, a continuation returning distance zero is excluded. -/
def TokenAdmissible : Manual.Token → Prop
  | .matchBytes length distance =>
    3 ≤ length ∧ length ≤ 258 ∧ 0 < distance ∧ distance ≤ windowLimit
  | _ => True

/-- This semantic predicate also covers continuation programs retained after
partial bit reads. Future input may turn an incomplete read into a valid token. -/
def ParserAdmissible (parser : Parser Manual.Token) (reader : LSBReader) : Prop :=
  ∀ future token rest,
    parser.eval (Reservoir.readerFeed reader future) = .ok (token, rest) → TokenAdmissible token

/-- Finish exactly the remaining output and observe it. A malformed output
phase has an explicit error rather than a partial or optional denotation. -/
def outputDenote (pending : TokenOutput) (reader : LSBReader) :
    Except Deflate.DecompressError Deflate.SymbolStep :=
  match pending.step pending.remaining with
  | .error _ => .error .decodeOverrun
  | .ok completed =>
    match completed.observe reader with
    | some result => .ok result
    | none => .error .decodeOverrun

/-- A total logical continuation of the physical token machine. -/
def denote (machine : TokenMachine) (reader : LSBReader) :
    Except Deflate.DecompressError Deflate.SymbolStep :=
  match machine with
  | .parsing parser _ _ bytes =>
    match parser.eval reader with
    | .error err => .error err
    | .ok (token, rest) => Manual.applyToken bytes token rest
  | .emitting _ pending | .done _ pending => outputDenote pending reader
  | .error err _ _ _ => .error err

/-- Output phases carry valid bounded history. A done machine must really have
a completed phase. Parser errors retain the well-represented prior output. -/
def WellFormed (machine : TokenMachine) (reader : LSBReader) : Prop :=
  match machine with
  | .parsing parser _ history bytes => history.Represents bytes ∧ ParserAdmissible parser reader
  | .emitting _ pending => pending.Valid
  | .done _ completed => completed.Valid ∧ ∃ flag, completed.phase = .complete flag
  | .error _ _ history bytes => history.Represents bytes

end Silmaril.Formats.Compression.Inflate.Stream.TokenContinuation
