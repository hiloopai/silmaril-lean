module

public import Silmaril.Cerberus.Frontend.Lexer.Defs
/-! # GNU `asm` before the frontend

Cerberus parses GNU `asm` statements and drops them: its Cabs keeps only the template
strings (`Cabs.StatementNode.asm`) and its Cabs → Ail translation drops the statement,
so the typed Ail the compiler receives no longer has it. `lower` runs on the
preprocessed text first and makes dropping correct, or rejects the program:

* An `asm` with an **empty template** executes nothing, so its meaning is that of its
  operands: an input operand is evaluated; a read-write output `"+r"(x)` evaluates the
  lvalue `x` and leaves it unchanged; a write-only output `"=r"(x)` tied to an input
  `"0"(v)` (the same register) receives `v`'s bits: `v` when both have the same size,
  `v` zero-extended when `x` has 8 bytes and `v` 4 (gcc materializes a 4-byte input in
  a 32-bit register, and x86-64 zero-extends 32-bit writes). Such an `asm` with operands
  is replaced by the comma expression `((void)0, (void)(i₁), …, (void)sizeof(char[ok ?
  1 : -1]), (x) = __builtin_choose_expr(same, (v), (unsigned int)(v)))` in the text (the
  array of negative size makes the frontend reject any other pair of sizes), keeping
  its newlines so that locations do not move. Supported: at most one output, inputs tied to
  it by its number; any other operand list is rejected (an untied write-only output
  would be indeterminate). Without operands it is dropped (`asm("")`,
  `asm volatile ("" ::: "memory")`, the usual optimization barriers).
* An `asm` with a **non-empty template** runs instructions the compiler cannot see: an
  extended one (with `:`), or a basic one in statement position (after `;`, `{`, `}`,
  `:`, `else`, `do` or at the start of the text), is rejected. A basic one after
  anything else is an asm label (`int f(void) asm("g")`) and is dropped; so is
  `if (c) asm("nop");`, which the token scan reads as a label.
* `asm goto` and named operands (`[x] "r"(e)`) are rejected.

The scan is on the lexer's tokens (`Silmaril.Cerberus.Frontend.Lexer`), so comments and
string literals are not mistaken for `asm`; a text that does not lex is left alone (the
frontend reports it).

## Intended theorem

For an empty template, `lower` preserves the GNU meaning of the program: the
replaced expression has the operands' effects in an order GNU C allows (it leaves the
order of operand evaluation unspecified).
-/

@[expose] public section

namespace Silmaril.Compile.C.Asm

open Silmaril.Cerberus Frontend

/-- A token and its byte range in the text. -/
abbrev Tok := Token × Nat × Nat

/-- The tokens of a preprocessed text with their byte ranges, ending with `eof`
(`Lexer.tokensFrom`, keeping the offsets). -/
def lexFrom (fuel : Nat) (s : Lexer.State) (acc : Array Tok) : Option (Array Tok) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match Lexer.step s with
    | .error _ => none
    | .ok (.skip s') => lexFrom fuel s' acc
    | .ok (.token kind j e) =>
      let t : Tok := (⟨kind, s.posAt j, s.posAt e⟩, j, e)
      match kind with
      | .eof => some (acc.push t)
      | _ => lexFrom fuel { s with offset := e } (acc.push t)

def lex (text : ByteArray) : Option (Array Tok) :=
  lexFrom (text.size + 2) ⟨text, 0, 1, 0, none, ""⟩ #[]

def isPunct (p : Punct) (t : Tok) : Bool :=
  match t.1.kind with
  | .punct q => q == p
  | _ => false

def isKeyword (k : Keyword) (t : Tok) : Bool :=
  match t.1.kind with
  | .keyword q => q == k
  | _ => false

/-- The text of a string-literal token's lexemes (escapes undecoded). -/
def stringText? (t : Tok) : Option String :=
  match t.1.kind with
  | .string _ lexemes => some (lexemes.foldl (fun a l => match l with
      | .utf8 s => a ++ s
      | .bytes _ => a ++ "?") "")
  | _ => none

/-- A token after which `asm` starts a statement or a file-scope `asm`. -/
def startsStatement (t : Tok) : Bool :=
  isPunct .semicolon t || isPunct .lbrace t || isPunct .rbrace t || isPunct .colon t ||
    isKeyword .else_ t || isKeyword .do_ t

/-- An operand: its constraint, whether it is named, and the byte range of its
expression. -/
structure Operand where
  constraint : String
  named : Bool
  expr : Nat × Nat

/-- What an `asm` at a token index is: where it ends (the index of its `)`), and how
to treat it. -/
inductive Shape where
  /-- Drop it (the frontend does). -/
  | drop
  /-- Replace the tokens up to its `)` with this text. -/
  | replace (text : String)
  /-- Reject the program. -/
  | reject (why : String)

/-- The index after the `)` that closes the `(` before index `k`. -/
def closeParen (ts : Array Tok) (k : Nat) : Option Nat := Id.run do
  let mut depth := 1
  let mut j := k
  while j < ts.size do
    let t := ts[j]!
    if isPunct .lparen t then depth := depth + 1
    else if isPunct .rparen t then
      depth := depth - 1
      if depth == 0 then return some (j + 1)
    else if t.1.kind matches .eof then return none
    j := j + 1
  return none

/-- The operands of a list starting at index `k`, and the index after them (at `:`, `::`
or `)`). -/
def operands (ts : Array Tok) (k : Nat) : Option (Array Operand × Nat) := Id.run do
  let mut j := k
  let mut acc : Array Operand := #[]
  let stop (t : Tok) := isPunct .colon t || isPunct .colonColon t || isPunct .rparen t
  if ts[j]?.any stop then return some (acc, j)
  while j < ts.size do
    let mut named := false
    if ts[j]?.any (isPunct .lbrack) then
      named := true
      j := j + 3
    let mut c := ""
    while (ts[j]?.bind stringText?).isSome do
      c := c ++ (ts[j]?.bind stringText?).getD ""
      j := j + 1
    if !(ts[j]?.any (isPunct .lparen)) then return none
    let some e := closeParen ts (j + 1) | return none
    acc := acc.push ⟨c, named, (ts[j + 1]!.2.1, ts[e - 1]!.2.1)⟩
    j := e
    if ts[j]?.any (isPunct .comma) then j := j + 1
    else if ts[j]?.any stop then return some (acc, j)
    else return none
  return none

/-- The expression of an empty-template `asm` with these operands (see the module doc). -/
def emptyTemplate (text : ByteArray) (outs ins : Array Operand) : Except String String := do
  let src (o : Operand) : String :=
    (String.fromUTF8? (text.extract o.expr.1 o.expr.2)).getD ""
  if (outs ++ ins).any (·.named) then throw "inline assembly with named operands"
  if outs.size > 1 then throw "inline assembly with several output operands"
  let tied (i : Operand) := outs.size == 1 && i.constraint == "0"
  let mut parts : Array String := #["(void)0"]
  for i in ins do
    if !tied i then
      if i.constraint.any Char.isDigit then throw "inline assembly with an unmatched tied operand"
      parts := parts.push s!"(void)({src i})"
  for o in outs do
    if o.constraint.contains '+' then
      if ins.any tied then throw "inline assembly with a tied read-write operand"
      parts := parts.push s!"(void)({src o})"
    else match ins.find? tied with
      | some i =>
        let (x, v) := (src o, src i)
        let same := s!"sizeof({x}) == sizeof({v})"
        let wide := s!"sizeof({x}) == 8 && sizeof({v}) == 4"
        parts := parts.push (s!"(void)sizeof(char[{same} || {wide} ? 1 : -1]), " ++
          s!"({x}) = __builtin_choose_expr({same}, ({v}), (unsigned int)({v}))")
      | none => throw "inline assembly with an output operand of indeterminate value"
  return "(" ++ ", ".intercalate parts.toList ++ ")"

/-- The shape of the `asm` keyword at index `i` and the index of its `)`. -/
def shape (text : ByteArray) (ts : Array Tok) (i : Nat) : Shape × Nat := Id.run do
  let mut j := i + 1
  let mut goto := false
  while ts[j]?.any (fun t => isKeyword .volatile t || isKeyword .asmVolatile t ||
      isKeyword .inline t || isKeyword .goto t) do
    goto := goto || ts[j]?.any (isKeyword .goto)
    j := j + 1
  if !(ts[j]?.any (isPunct .lparen)) then return (.drop, i)
  j := j + 1
  let mut template := ""
  while (ts[j]?.bind stringText?).isSome do
    template := template ++ (ts[j]?.bind stringText?).getD ""
    j := j + 1
  -- sections: outputs, inputs, clobbers, labels
  let mut sec := 0
  let mut outs : Array Operand := #[]
  let mut ins : Array Operand := #[]
  while j < ts.size && !isPunct .rparen ts[j]! do
    if isPunct .colon ts[j]! then sec := sec + 1; j := j + 1
    else if isPunct .colonColon ts[j]! then sec := sec + 2; j := j + 1
    else if sec == 1 || sec == 2 then
      match operands ts j with
      | some (ops, e) =>
        if sec == 1 then outs := ops else ins := ops
        j := e
      | none => return (.reject "inline assembly the compiler cannot read", i)
    else if sec ≥ 3 then j := j + 1
    else return (.reject "inline assembly the compiler cannot read", i)
  if goto || sec ≥ 4 then return (.reject "asm goto", j)
  if !template.isEmpty then
    if sec > 0 || i == 0 || ts[i - 1]?.any startsStatement then
      return (.reject "inline assembly with a non-empty template", j)
    return (.drop, j)
  if outs.isEmpty && ins.isEmpty then return (.drop, j)
  match emptyTemplate text outs ins with
  | .ok e => return (.replace e, j)
  | .error why => return (.reject why, j)

/-- Whether the bytes `asm` occur in the text (a quick test before lexing). -/
def mentionsAsm (text : ByteArray) : Bool := Id.run do
  for j in [0:text.size - 2] do
    if text[j]! == 97 && text[j + 1]! == 115 && text[j + 2]! == 109 then return true
  return false

/-- The preprocessed text with every `asm` made safe to drop, or the first one that is
not, with its position and why. A text that does not lex is returned unchanged. -/
def lower (text : ByteArray) : Except (Pos × String) ByteArray := do
  if !mentionsAsm text then return text
  let some ts := lex text | return text
  let mut out := ByteArray.empty
  let mut copied := 0
  for i in [0:ts.size] do
    if isKeyword .asm ts[i]! then
      match shape text ts i with
      | (.drop, _) => pure ()
      | (.reject why, _) => throw (ts[i]!.1.start, why)
      | (.replace e, k) =>
        let (a, b) := (ts[i]!.2.1, ts[k]!.2.2)
        let lines := (text.extract a b).toList.filter (· == 10)
        out := out ++ text.extract copied a ++ e.toUTF8 ++ ⟨lines.toArray⟩
        copied := b
  return out ++ text.extract copied text.size

end Silmaril.Compile.C.Asm
