module

public import Silmaril.Formats.SExp.EncodingWatFullLexer

/-!
# A linear-time copy of silmaril's full WAT lexer

silmaril's certified lexer `Silmaril.Formats.SExpEncoding.Wat.lexGoFull` gives every block
comment `(; … ;)` the fuel `r.length + 1`, where `r` is the rest of the input: it walks the
whole remaining input at each comment, so text with many comments (wasmprinter writes an
`(;i;)` index comment on every type, function, global, …) lexes in quadratic time (8.4 s for
the 1.9 MB text of a 300 KB module, `wasm-tools-gen-diag --wat-phases`).

`lexF p n N cs` is `lexGoFull p n cs` with the block-comment fuel `N`, a bound fixed once for
the whole input; `lexFull? p s` runs it with `N = n = s.length + 1` and brackets the tokens,
as the last stage of `Silmaril.Formats.SExpEncoding.Wat.sexpWatFullExec?` does.

`Thms`: `lexF_eq` (equal to `lexGoFull` whenever `cs.length < N`), so `lexFull?_eq`, and
`lexFull?_sound` (the tree is one the WAT S-expression grammar `sexpWat` gives the text).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.WatLex

open Silmaril Silmaril.Formats.SExpEncoding Silmaril.Formats.SExpEncoding.Wat

/-- `lexGoFull` with the fuel `N` for every block comment. -/
def lexF (p : Profile) : Nat → Nat → Chars → Option (List Tok)
  | 0, _, _ => none
  | _ + 1, _, [] => some []
  | n + 1, N, c :: r =>
      if IsSpaceChar c then lexF p n N r
      else if c = ';' ∧ r.head? = some ';' then
        match (splitLine p r.tail).2 with
        | none => some []
        | some (_, rest) => lexF p n N rest
      else if c = '(' ∧ r.head? = some ';' then
        match blockTail? N r.tail with
        | none => none
        | some rest => lexF p n N rest
      else if c = '(' then
        if p = .core3 ∧ r.head? = some '@' then
          match annotationTail? r with
          | none => none
          | some annotation => lexF p n N annotation.rest
        else (Tok.lp :: ·) <$> lexF p n N r
      else if c = ')' then (Tok.rp :: ·) <$> lexF p n N r
      else if c = '"' then
        match fullStrBody? r with
        | none => none
        | some (_b, bytes, rest) =>
          if bytes.length < 2 ^ 32 ∧
              followAtomB p true rest = true then
            (Tok.atom (.str bytes) :: ·) <$> lexF p n N rest
          else none
      else if p = .core3 ∧ c = '$' ∧ r.head? = some '"' then
        match quotedIdTail? r with
        | none => none
        | some quoted =>
            if followAtomB p false quoted.rest = true then
              (Tok.atom (.id quoted.name) :: ·) <$> lexF p n N quoted.rest
            else none
      else if IsIdChar c then
        if followAtomB p false (idRun r).2 = true then
          (Tok.atom (classify (c :: (idRun r).1)) :: ·) <$> lexF p n N (idRun r).2
        else none
      else none

/-- **The full lexer and bracket matcher in linear time** (on a text): the last stage of
`sexpWatFullExec?`. -/
def lexFull? (p : Profile) (s : String) : Option SExp :=
  let cs := s.toList
  let n := cs.length + 1
  (lexF p n n cs).bind bracketExec?

end Silmaril.Wasm.Tools.Gen.Cmd.WatLex
