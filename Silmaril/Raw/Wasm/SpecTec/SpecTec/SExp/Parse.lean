module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.SExp.Basic

/-!
# Reading an `--ast` stream

A direct, *unverified* reader for the lexical convention that
`Silmaril/SpecTec/SExp/Lexical.lean` specifies.  `spectec_import`
(`Silmaril/SpecTec/Import.lean`) uses it at elaboration time, where speed
matters — the wasm-3.0 stream is 1.5 MB — so it walks an `Array Char`
with an index cursor, in the style of `Silmaril/Wasm/Wat/Lexer.lean`, and is
written with `partial def`.

Nothing downstream *trusts* this reader: what an import certifies is a
property of the `IL.Script` it produces, namely that the script's printed form
decodes back to it.  Proving `parse?` sound and complete against
`Silmaril.SpecTec.lexicalRel` is the natural next step and is deliberately not
attempted here (`docs/projects/spectec/README.md`).

The one lexical constraint that this reader *does* enforce, because it is
cheap, is that a node's tag follows its `(` with no intervening space, exactly
as `spectec/src/util/sexpr.ml:23` emits it.
-/

@[expose] public section

namespace Silmaril.SpecTec.SExp

/-- The two whitespace characters `Util.Sexpr.pp` can emit
(`spectec/src/util/sexpr.ml:22`). -/
def isLayout (c : Char) : Bool := c == ' ' || c == '\n'

/-- A character that may appear in a bare token. -/
def isBareChar (c : Char) : Bool :=
  !isLayout c && c != '(' && c != ')' && c != '"'

/-- A position in the stream. -/
structure Cursor where
  /-- The whole stream. -/
  chars : Array Char
  /-- The index of the next character. -/
  pos : Nat := 0

/-- The character at the cursor, if any. -/
def Cursor.peek (c : Cursor) : Option Char := c.chars[c.pos]?

/-- Advance by one character. -/
def Cursor.next (c : Cursor) : Cursor := { c with pos := c.pos + 1 }

/-- The text between two positions. -/
def Cursor.slice (c : Cursor) (start : Nat) : String :=
  String.ofList (List.ofFn fun i : Fin (c.pos - start) => c.chars.getD (start + i.1) ' ')

/-- Skip a run of layout. -/
partial def skipLayout (c : Cursor) : Cursor :=
  match c.peek with
  | some ch => if isLayout ch then skipLayout c.next else c
  | none => c

/-- Advance past a maximal run of bare-token characters. -/
partial def skipBare (c : Cursor) : Cursor :=
  match c.peek with
  | some ch => if isBareChar ch then skipBare c.next else c
  | none => c

/-- Advance past a quoted token, honouring backslash escapes.  The cursor must
be positioned just after the opening quote; the result is positioned just after
the closing one. -/
partial def skipQuoted (c : Cursor) : Except String Cursor :=
  match c.peek with
  | none => .error "unterminated string"
  | some '"' => .ok c.next
  | some '\\' => if c.next.peek.isSome then skipQuoted c.next.next else .error "unterminated escape"
  | some _ => skipQuoted c.next

mutual

/-- Read one S-expression. -/
partial def parseOne (c : Cursor) : Except String (SExp × Cursor) := do
  let c := skipLayout c
  match c.peek with
  | none => .error "unexpected end of input"
  | some ')' => .error "unexpected `)`"
  | some '(' =>
      let start := c.pos + 1
      let c := skipBare c.next
      if c.pos = start then .error "a node must have a bare tag immediately after `(`"
      else
        let tag := c.slice start
        let (children, c) ← parseChildren c #[]
        .ok (.node tag children.toList, c)
  | some '"' =>
      let start := c.pos
      let c ← skipQuoted c.next
      .ok (.atom (c.slice start), c)
  | some ch =>
      if isBareChar ch then
        let start := c.pos
        let c := skipBare c
        .ok (.atom (c.slice start), c)
      else .error s!"unexpected character {ch}"

/-- Read children up to the closing `)`. -/
partial def parseChildren (c : Cursor) (acc : Array SExp) :
    Except String (Array SExp × Cursor) := do
  let c := skipLayout c
  match c.peek with
  | none => .error "unterminated node"
  | some ')' => .ok (acc, c.next)
  | some _ =>
      let (child, c) ← parseOne c
      parseChildren c (acc.push child)

end

/-- Read a sequence of top-level S-expressions. -/
partial def parseStreamAux (c : Cursor) (acc : Array SExp) : Except String (Array SExp) := do
  let c := skipLayout c
  if c.peek.isNone then .ok acc
  else
    let (form, c) ← parseOne c
    parseStreamAux c (acc.push form)

/-- Read a whole `--ast` stream. -/
def parseStream (s : String) : Except String (List SExp) :=
  (parseStreamAux { chars := s.toList.toArray } #[]).map Array.toList

/-- Read a single S-expression, rejecting trailing input. -/
def parse (s : String) : Except String SExp := do
  match ← parseStream s with
  | [e] => .ok e
  | es => .error s!"expected one S-expression, found {es.length}"

end Silmaril.SpecTec.SExp
