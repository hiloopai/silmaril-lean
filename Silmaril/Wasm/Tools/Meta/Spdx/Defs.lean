module

public import Silmaril.Wasm.Tools.Meta.Spdx.Data.Defs

/-!
# SPDX license expressions (spdx 0.13.5, strict mode)

`checkLicense s` is `none` exactly when `spdx::Expression::parse(s)` (`ParseMode::STRICT`)
accepts `s`, and otherwise the reason. wasm-metadata's `Licenses` stores the original string
(`Expression`'s `Display` prints `original`), so acceptance is all `metadata add --licenses` and
`metadata show` need.

The lexer: whitespace separates tokens; `(`, `)`, `+` (not after whitespace); otherwise the
longest run of `[A-Za-z0-9.:-]`, read as `AND`/`and`, `OR`/`or`, `WITH`/`with`, a license
identifier (`+` suffixes ignored), an exception identifier, `[DocumentRef-X:]LicenseRef-Y`,
`[DocumentRef-X:]AdditionRef-Y`, or an unknown term (an error). The parser accepts the token
sequences of the grammar `expr ::= simple [WITH addition] | expr (AND|OR) expr | ( expr )` with
`simple ::= license-id [+] | license-ref`, balanced parentheses, no deprecated license
identifier, and no `+` after a GNU license. Identifiers: SPDX license list 3.28.0
(`Spdx.Data`). Error messages: spdx's reason only (not its caret diagram).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Meta.Spdx

/-- Parsed identifier lists: names and flags, sorted. -/
def parseData (d : String) : Array (String × Nat) :=
  (d.splitOn "\n").toArray.map fun l => match l.splitOn " " with
    | [n, f] => (n, f.toNat!)
    | _ => (l, 0)

def licenses : Array (String × Nat) := parseData licenseData
def exceptions : Array (String × Nat) := parseData exceptionData

/-- Byte-wise string order (Rust's `str::cmp`). -/
def strLt (a b : String) : Bool := a.toUTF8.toList < b.toUTF8.toList

/-- Binary search for a name. -/
def lookup (arr : Array (String × Nat)) (name : String) : Option Nat :=
  let rec go : Nat → Nat → Nat → Option Nat
    | 0, _, _ => none
    | f + 1, lo, hi =>
      if lo ≥ hi then none else
      let mid := (lo + hi) / 2
      let (n, fl) := arr[mid]!
      if n == name then some fl else if strLt n name then go f (mid + 1) hi else go f lo mid
  go 64 0 arr.size

/-- `license_id`: trailing `+` removed, then looked up. -/
def licenseFlags (m : String) : Option Nat :=
  lookup licenses (String.ofList (m.toList.reverse.dropWhile (· == '+')).reverse)

/-- Tokens. -/
inductive Tok where
  | lic (gnu deprecated : Bool) | licRef | exc | addRef | plus | lparen | rparen | with_ | and_ | or_
  deriving DecidableEq, Inhabited

def isRefChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == '.'

/-- `find_ref`: the `[A-Za-z0-9.-]*` after a prefix, if the text starts with it. -/
def findRef (prefix_ text : String) : Option String :=
  if text.startsWith prefix_ then
    some (String.ofList ((text.toList.drop prefix_.length).takeWhile isRefChar))
  else none

/-- The classification of a text token. -/
def classify (m : String) : Option Tok :=
  if m == "AND" || m == "and" then some .and_
  else if m == "OR" || m == "or" then some .or_
  else if m == "WITH" || m == "with" then some .with_
  else match licenseFlags m with
  | some fl => some (.lic (fl / 16 % 2 == 1) (fl / 4 % 2 == 1))
  | none =>
    if (lookup exceptions m).isSome then some .exc else
    let docAnd (p : String) : Bool := match m.splitOn ":" with
      | d :: rest@(_ :: _) => (findRef "DocumentRef-" d).isSome && (findRef p (":".intercalate rest)).isSome
      | _ => false
    if docAnd "LicenseRef-" || (findRef "LicenseRef-" m).isSome then some .licRef
    else if docAnd "AdditionRef-" || (findRef "AdditionRef-" m).isSome then some .addRef
    else none

/-- The lexer. -/
def lex : Nat → List Char → Bool → Except String (List Tok)
  | 0, _, _ => .ok []
  | f + 1, cs, _ =>
    let ws := cs.takeWhile Char.isWhitespace
    let cs := cs.drop ws.length
    match cs with
    | [] => .ok []
    | '+' :: r => if !ws.isEmpty then .error "a `+` was found after whitespace" else
        (lex f r false).map (.plus :: ·)
    | '(' :: r => (lex f r false).map (.lparen :: ·)
    | ')' :: r => (lex f r false).map (.rparen :: ·)
    | _ =>
      let m := cs.takeWhile fun c => isRefChar c || c == ':'
      if m.isEmpty then .error "invalid character(s)" else
      match classify (String.ofList m) with
      | none => .error "unknown term"
      | some t =>
        -- the token's length is the identifier's (a `+` suffix is lexed separately)
        let len := match t with
          | .lic .. => (m.reverse.dropWhile (· == '+')).length
          | _ => m.length
        (lex f (cs.drop len) false).map (t :: ·)

/-- Whether a token may follow `last` (the parser's `match last_token`). -/
def follows (last : Option Tok) (t : Tok) : Bool :=
  let startish := match last with
    | none | some .and_ | some .or_ | some .lparen => true
    | _ => false
  match t with
  | .lic .. | .licRef | .lparen => startish
  | .plus => match last with | some (.lic ..) => true | _ => false
  | .with_ => match last with | some (.lic ..) | some .licRef | some .plus => true | _ => false
  | .and_ | .or_ | .rparen => match last with
    | some (.lic ..) | some .licRef | some .rparen | some .exc | some .addRef | some .plus => true
    | _ => false
  | .exc | .addRef => last == some .with_

/-- The parser's checks over the tokens: transitions, parentheses, deprecated identifiers,
`+` after GNU licenses, a complete final token. -/
def check : List Tok → Option Tok → Nat → Option String
  | [], last, depth =>
    match last with
    | none => some "empty expression"
    | some (.lic ..) | some .licRef | some .exc | some .addRef | some .rparen | some .plus =>
      if depth > 0 then some "unclosed parens" else none
    | some _ => some "unexpected end of expression"
  | t :: ts, last, depth =>
    if !follows last t then some "unexpected term" else
    match t with
    | .lic _ true => some "a deprecated license identifier was used"
    | .plus => match last with
      | some (.lic true _) => some "GNU licenses may not have a `+`"
      | _ => check ts (some t) depth
    | .lparen => check ts (some t) (depth + 1)
    | .rparen => if depth == 0 then some "unopened parens" else check ts (some t) (depth - 1)
    | _ => check ts (some t) depth

/-- **`spdx::Expression::parse` in strict mode**: `none` when accepted. -/
def checkLicense (s : String) : Option String :=
  match lex (s.length + 1) s.toList true with
  | .error e => some e
  | .ok ts => check ts none 0

end Silmaril.Wasm.Tools.Meta.Spdx

end
