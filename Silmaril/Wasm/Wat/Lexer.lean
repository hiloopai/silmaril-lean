module

public meta import Lean

/-! # Lexical layer for the WAT quotations

This elaboration-time lexer retains byte strings and source character offsets.
It recognizes WAT line comments, nested block comments, and exact string escapes.
It deliberately does not reuse the Lisp parser: Lisp comments and escapes differ.
-/

public meta section

namespace Silmaril.Wasm.Wat

inductive Node where
  | atom (pos : Nat) (text : String)
  | string (pos : Nat) (bytes : ByteArray)
  | quotedIdentifier (pos : Nat) (bytes : ByteArray)
  | list (pos : Nat) (children : List Node)
  deriving Inhabited

def Node.pos : Node → Nat
  | .atom p _ | .string p _ | .quotedIdentifier p _ | .list p _ => p

def Node.atom? : Node → Option String
  | .atom _ s => some s
  | .quotedIdentifier _ bytes => (String.fromUTF8? bytes).map ("$" ++ ·)
  | _ => none

def Node.isIdentifier : Node → Bool
  | .quotedIdentifier .. => true
  | .atom _ s => s.startsWith "$"
  | _ => false

def Node.head? : Node → Option String
  | .list _ (.atom _ s :: _) => some s
  | _ => none

def failAt {α : Type} (p : Nat) (message : String) : Except String α :=
  .error s!"WAT at character {p}: {message}"

structure Cursor where
  chars : Array Char
  pos : Nat := 0

def Cursor.peek (c : Cursor) (n : Nat := 0) : Option Char := c.chars[c.pos + n]?
def Cursor.next (c : Cursor) (n : Nat := 1) : Cursor := { c with pos := c.pos + n }

def whitespace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

def idChar (c : Char) : Bool := c.isAlphanum && c.toNat < 128 ||
  "!#$%&'*+-./:<=>?@\\^_`|~".contains c

/-- Strings and atoms cannot be adjacent parts of a reserved longest-match token. -/
def tokenBoundary (c : Cursor) : Bool := match c.peek with
  | none => true
  | some ch => whitespace ch || ch == '(' || ch == ')' ||
    (ch == ';' && c.peek 1 == some ';')

def requireBoundary (start : Nat) (c : Cursor) : Except String Unit :=
  unless tokenBoundary c do
    failAt start "reserved token: adjacent tokens require whitespace, parentheses, or a comment"

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Underscores occur only between digits; signs and radix markers are handled separately. -/
def digits (radix : Nat) (text : String) : Except String Nat := do
  let mut value := 0
  let mut previousDigit := false
  for c in text.toList do
    if c == '_' then
      unless previousDigit do throw "misplaced underscore in numeric literal"
      previousDigit := false
    else
      let some d := hexDigit c | throw "invalid digit in numeric literal"
      unless d < radix do throw "invalid digit for numeric radix"
      value := value * radix + d
      previousDigit := true
  unless previousDigit do throw "numeric literal must end in a digit"
  return value

def unsigned (text : String) : Except String Nat :=
  if text.startsWith "0x" then digits 16 (text.drop 2).toString else digits 10 text

/-- Exact WAT `iN`: unsigned, or explicitly signed within the signed range. -/
def integerBits (width : Nat) (text : String) : Except String Nat := do
  let neg := text.startsWith "-"
  let signed := neg || text.startsWith "+"
  let magnitude ← unsigned (if signed then (text.drop 1).toString else text)
  if neg then
    unless magnitude ≤ 2 ^ (width - 1) do throw "negative integer literal out of range"
    return (2 ^ width - magnitude) % 2 ^ width
  else
    unless magnitude < 2 ^ (if signed then width - 1 else width) do
      throw "integer literal out of range"
    return magnitude

partial def blockComment (start depth : Nat) (c : Cursor) : Except String Cursor := do
  match c.peek, c.peek 1 with
  | none, _ => failAt start "unterminated block comment"
  | some '(', some ';' => blockComment start (depth + 1) (c.next 2)
  | some ';', some ')' =>
      if depth == 1 then return c.next 2 else blockComment start (depth - 1) (c.next 2)
  | _, _ => blockComment start depth c.next

partial def quoted (start : Nat) (c : Cursor) (acc : ByteArray := .empty) :
    Except String (ByteArray × Cursor) := do
  match c.peek with
  | none => failAt start "unterminated string"
  | some '"' =>
      unless acc.size < 2 ^ 32 do failAt start "string exceeds unsigned 32-bit length"
      return (acc, c.next)
  | some '\\' =>
      let c := c.next
      match c.peek with
      | none => failAt start "unterminated string escape"
      | some 'u' =>
          unless c.peek 1 == some '{' do failAt c.pos "expected '{' in Unicode escape"
          let mut rest := c.next 2
          let mut chars := []
          while rest.peek.isSome && rest.peek != some '}' do
            chars := rest.peek.get! :: chars
            rest := rest.next
          unless rest.peek == some '}' do failAt c.pos "unterminated Unicode escape"
          let n ← digits 16 (String.ofList chars.reverse)
          unless n < 0x110000 && !(0xD800 ≤ n && n < 0xE000) do
            failAt c.pos "invalid Unicode scalar"
          quoted start rest.next (acc ++ (String.singleton (Char.ofNat n)).toUTF8)
      | some ch =>
          if let some hi := hexDigit ch then
            let some lo := (c.peek 1).bind hexDigit |
              failAt c.pos "byte escape requires two hexadecimal digits"
            quoted start (c.next 2) (acc.push (UInt8.ofNat (16 * hi + lo)))
          else
            let byte ← match ch with
              | 't' => pure 9 | 'n' => pure 10 | 'r' => pure 13
              | '"' => pure 34 | '\'' => pure 39 | '\\' => pure 92
              | _ => failAt c.pos "unsupported string escape"
            quoted start c.next (acc.push byte)
  | some ch =>
      unless ch.toNat ≥ 0x20 && ch.toNat != 0x7F do
        failAt c.pos "unescaped control character in string"
      quoted start c.next (acc ++ (String.singleton ch).toUTF8)

def lineComment (c : Cursor) : Cursor := Id.run do
  let mut c := c
  while c.peek.isSome && c.peek != some '\n' && c.peek != some '\r' do c := c.next
  return c

mutual
  /-- Unknown Core3 annotations are whitespace, with balanced strings and comments. -/
  partial def annotation (start : Nat) (c : Cursor) : Except String Cursor := do
    let rest ← if c.peek == some '"' then do
      let (bytes, rest) ← quoted c.pos c.next
      let some name := String.fromUTF8? bytes | failAt c.pos "annotation name is not valid UTF-8"
      unless !name.isEmpty do failAt start "annotation requires a nonempty identifier"
      requireBoundary c.pos rest
      pure rest
    else do
      let mut rest := c
      while rest.peek.any idChar do rest := rest.next
      unless rest.pos > c.pos do failAt start "annotation requires an identifier after '(@'"
      requireBoundary c.pos rest
      pure rest
    annotationBody start 1 rest

  partial def annotationBody (start depth : Nat) (c : Cursor) : Except String Cursor := do
    match c.peek, c.peek 1 with
    | none, _ => failAt start "unterminated annotation"
    | some ';', some ';' => annotationBody start depth (lineComment (c.next 2))
    | some '(', some ';' => annotationBody start depth (← blockComment c.pos 1 (c.next 2))
    | some '(', _ => annotationBody start (depth + 1) c.next
    | some ')', _ =>
        if depth == 1 then return c.next else annotationBody start (depth - 1) c.next
    | some '"', _ => annotationBody start depth (← quoted c.pos c.next).2
    | some ch, _ =>
        unless whitespace ch || idChar ch || ",;[]{}".contains ch do
          failAt c.pos "invalid character outside an annotation string or comment"
        annotationBody start depth c.next
end

partial def skip (c : Cursor) : Except String Cursor := do
  match c.peek, c.peek 1 with
  | some ';', some ';' => skip (lineComment (c.next 2))
  | some '(', some ';' => skip (← blockComment c.pos 1 (c.next 2))
  | some '(', some '@' => skip (← annotation c.pos (c.next 2))
  | some ch, _ => if whitespace ch then skip c.next else return c
  | _, _ => return c

mutual
  partial def node (c : Cursor) : Except String (Node × Cursor) := do
    let c ← skip c
    match c.peek with
    | none => failAt c.pos "expected an expression"
    | some ')' => failAt c.pos "unexpected ')'"
    | some '(' =>
        let (children, rest) ← nodes true c.pos c.next
        return (.list c.pos children, rest)
    | some '"' =>
        let (bytes, rest) ← quoted c.pos c.next
        requireBoundary c.pos rest
        return (.string c.pos bytes, rest)
    | some '$' =>
        if c.peek 1 == some '"' then
          let (bytes, rest) ← quoted c.pos (c.next 2)
          let some name := String.fromUTF8? bytes | failAt c.pos "identifier is not valid UTF-8"
          unless !name.isEmpty do failAt c.pos "identifier must not be empty"
          requireBoundary c.pos rest
          return (.quotedIdentifier c.pos bytes, rest)
        else atomNode c
    | some _ =>
        atomNode c

  partial def atomNode (c : Cursor) : Except String (Node × Cursor) := do
    let mut rest := c
    let mut token := []
    while rest.peek.any idChar do
      token := rest.peek.get! :: token
      rest := rest.next
    if token.isEmpty then failAt c.pos "unexpected character (comments start with ';;' or '(;')"
    else
      requireBoundary c.pos rest
      return (.atom c.pos (String.ofList token.reverse), rest)

  partial def nodes (nested : Bool) (start : Nat) (c : Cursor) :
      Except String (List Node × Cursor) := do
    let c ← skip c
    match c.peek with
    | none => if nested then failAt start "unterminated '('" else return ([], c)
    | some ')' => if nested then return ([], c.next) else failAt c.pos "unexpected ')'"
    | _ =>
        let (first, rest) ← node c
        let (others, rest) ← nodes nested start rest
        return (first :: others, rest)
end

def parse (text : String) : Except String (List Node) := do
  return (← nodes false 0 ⟨text.toList.toArray, 0⟩).1

end Silmaril.Wasm.Wat
