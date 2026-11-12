module

public import Mathlib.Data.List.Basic

/-!
# SpecTec surface syntax: the lexer

A transcription of the SpecTec frontend's lexer
`specs/spectec/src/spectec/src/frontend/lexer.mll` (vendored from
`WebAssembly/spec@608711107b7f1edb13efd57b7d79b49477462d36`); every rule below
cites its line there.

## The specification and the lexer

* `Step cs t r` is one application of a lexer rule: from input `cs` it emits
  `t` (a token, or `none` for layout that emits nothing) and leaves `r`.
  `AfterNl` and `AfterNlNl` are the two auxiliary entry points `after_nl` and
  `after_nl_nl` that decide what a run of newlines means (`lexer.mll:121-131`).
* `Lexes cs ts` chains steps to the end of the input.
* `lex?` is a total lexer (fuel, so the kernel reduces it), and
  `Silmaril.Wasm.SpecTec.Surface.Lexer.lex?_sound` says that whatever it returns
  is a `Lexes` derivation.

The regular expressions of `lexer.mll` are written with a few primitive
scanners: `List.takeWhile`/`List.dropWhile` for runs of one character class,
`scanSep` for `digit ('_'? digit)*`, and `scanText` for the body of a text
literal. Longest match is spelled out per rule: each constructor of `Step`
carries the condition under which no other rule of `lexer.mll` matches a
longer lexeme at the same position (or an earlier rule a lexeme of the same
length).

## Deviations from `lexer.mll`

* `UPID`/`LOID` (and their `_SUB`/`_LPAREN` forms) are one token `Token.id`
  (`Token.idParen`): `lexer.mll:267-272` reclassifies an upper-case identifier
  by asking the parser whether it was declared a variable (`is_var`,
  `lexer.mll:54-58`), which is parser state. Here the parser decides by
  position.
* Backquoted identifiers (`lexer.mll:273-276`) are `Token.tickId` and
  `Token.tickIdParen`; the case swap of `lexer.mll:273-276` is left to the
  parser, like `is_var`.
* Literals keep their spelling: `Token.nat`, `Token.hex`, `Token.char` carry
  their digits (with `_` separators), `Token.text` the raw body between the
  quotes, escapes undecoded.
* Error rules (`lexer.mll:261-265,289-292`) are absent: where they would fire,
  `lex?` fails.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Surface.Lexer

/-! ## Tokens -/

/-- The tokens of `parser.mly:137-210` that the fragment needs, with the
deviations listed in the module docstring. -/
inductive Token where
  /-- A fixed token: a keyword (`lexer.mll:235-256`) or a symbol
  (`lexer.mll:134-233`), by its spelling. -/
  | sym (s : String)
  /-- `UPID`, `LOID`, `UPID_SUB`, `LOID_SUB` (`lexer.mll:267-270`). -/
  | id (s : List Char)
  /-- `UPID_LPAREN`, `LOID_LPAREN` (`lexer.mll:271-272`): an identifier
  immediately followed by `(`. -/
  | idParen (s : List Char)
  /-- `DOTID`, `DOTID_SUB` (`lexer.mll:277-278`), without the dot. -/
  | dotId (s : List Char)
  /-- A backquoted identifier (`lexer.mll:273-274`), without the backquote;
  the case of its first letter is swapped by the parser, not here. -/
  | tickId (s : List Char)
  /-- A backquoted identifier immediately followed by `(`
  (`lexer.mll:275-276`). -/
  | tickIdParen (s : List Char)
  /-- `NATLIT` (`lexer.mll:257`): the decimal digits as written. -/
  | nat (s : List Char)
  /-- `HEXLIT` (`lexer.mll:258`): the digits after `0x`. -/
  | hex (s : List Char)
  /-- `CHARLIT` (`lexer.mll:259`): the digits after `U+`. -/
  | char (s : List Char)
  /-- `TEXTLIT` (`lexer.mll:260`): the raw body between the quotes. -/
  | text (s : List Char)
  /-- `HOLEN` (`lexer.mll:226`): the digits after `%`. -/
  | holeN (s : List Char)
  /-- `COMMA_NL` (`lexer.mll:151`). -/
  | commaNl
  /-- `NL_BAR` (`lexer.mll:122,127`). -/
  | nlBar
  /-- `NL_NL` (`lexer.mll:131`): one blank line. -/
  | nlNl
  /-- `NL_NL_NL` (`lexer.mll:128`): two blank lines. -/
  | nlNlNl
  deriving DecidableEq, Repr, Inhabited

/-! ## Character classes (`lexer.mll:62-116`) -/

/-- `digit` (`lexer.mll:63`). -/
def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- `hexdigit` (`lexer.mll:64`): upper-case only. -/
def isHex (c : Char) : Bool := isDigit c || ('A' ≤ c && c ≤ 'F')

/-- `letter` (`lexer.mll:69-71`). -/
def isLetter (c : Char) : Bool := ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z')

/-- `idcharsub` (`lexer.mll:72-73`): `letter | digit | '\'' | '_'`. -/
def isIdCharSub (c : Char) : Bool := isLetter c || isDigit c || c == '\'' || c == '_'

/-- The first character of `upid | loid | upidsub | loidsub`
(`lexer.mll:75-79`). The union of those four expressions is exactly
`(letter | '_') idcharsub*`, which is how identifiers are scanned here. -/
def isIdStart (c : Char) : Bool := isLetter c || c == '_'

/-- `indent` (`lexer.mll:116`). -/
def isIndent (c : Char) : Bool := c == ' ' || c == '\t'

/-- `space # '\n'` (`lexer.mll:90,284`). -/
def isSpace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r'

/-- A non-newline character, `utf8_no_nl` (`lexer.mll:105`): a Lean `Char` is
a Unicode scalar value, so it is always a valid UTF-8 encoding. -/
def notNl (c : Char) : Bool := c != '\n'

/-- A plain text-literal character, the first alternative of `character`
(`lexer.mll:109-110`): not `"`, not `\`, not a control character. -/
def isTextPlain (c : Char) : Bool :=
  c != '"' && c != '\\' && decide (0x20 ≤ c.toNat) && c.toNat != 0x7f

/-- `escape` (`lexer.mll:107`). -/
def isEscape (c : Char) : Bool :=
  c == 'n' || c == 'r' || c == 't' || c == '\\' || c == '\'' || c == '"'

/-! ## Primitive scanners -/

/-- The tail `('_'? p)*` of `p ('_'? p)*`, longest match. -/
def scanSepTail (p : Char → Bool) : List Char → List Char × List Char
  | '_' :: c :: r =>
    if p c then
      let (a, b) := scanSepTail p r
      ('_' :: c :: a, b)
    else ([], '_' :: c :: r)
  | c :: r =>
    if p c then
      let (a, b) := scanSepTail p r
      (c :: a, b)
    else ([], c :: r)
  | [] => ([], [])

/-- `p ('_'? p)*` (`lexer.mll:65,67`), longest match: the lexeme and the
rest. The lexeme is empty when the input does not start with `p`. -/
def scanSep (p : Char → Bool) : List Char → List Char × List Char
  | c :: r =>
    if p c then
      let (a, b) := scanSepTail p r
      (c :: a, b)
    else ([], c :: r)
  | [] => ([], [])

/-- The body of a text literal, `character*` up to the closing quote
(`lexer.mll:108-114`), and the input after the closing quote. Fuel bounds the
`\u{…}` escape, after which the rest is not a subterm. -/
def scanText : Nat → List Char → Option (List Char × List Char)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, '"' :: r => some ([], r)
  | n + 1, '\\' :: 'u' :: '{' :: r =>
    let h := r.takeWhile isHex
    match r.dropWhile isHex with
    | '}' :: r' =>
      if h = [] then none else
      (scanText n r').map fun (b, rest) => ('\\' :: 'u' :: '{' :: h ++ '}' :: b, rest)
    | _ => none
  | n + 1, '\\' :: c :: d :: r =>
    if isEscape c then
      (scanText n (d :: r)).map fun (b, rest) => ('\\' :: c :: b, rest)
    else if isHex c && isHex d then
      (scanText n r).map fun (b, rest) => ('\\' :: c :: d :: b, rest)
    else none
  | n + 1, c :: r =>
    if isTextPlain c then (scanText n r).map fun (b, rest) => (c :: b, rest) else none

/-- A block comment after its opening `(;` (`lexer.mll:294-300`), nested to
depth `d + 1`: the input after the matching `;)`. Fuel bounds the scan. -/
def skipComment : Nat → Nat → List Char → Option (List Char)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | _ + 1, 0, ';' :: ')' :: r => some r
  | n + 1, d + 1, ';' :: ')' :: r => skipComment n d r
  | n + 1, d, '(' :: ';' :: r => skipComment n (d + 1) r
  | n + 1, d, _ :: r => skipComment n d r

/-! ## Fixed tokens -/

/-- The symbols of `lexer.mll:134-233` (layout rules aside), by spelling. -/
def symbols : List String :=
  ["(", ")", "[", "]", "{", "}", ":", ":_", ";", ",", ".", "..", "...", "|", "||", "--",
   "=", "=/=", "<", ">", "<=", ">=", "~~", "<:", ":>", ":=", "==", "=++", "=_", "==_", "~~_",
   "~", "/\\", "\\/", "(/\\)", "(\\/)", "(!)", "(?)", "(+)", "(*)", "(++)",
   "?", "+", "-", "*", "/", "\\", "^", "++", "+-", "-+",
   "<-", "</-", "->", "=>", "->_", "=>_", "~>", "~>_", "~>*", "~>*_", "<<", ">>", "<<_", ">>_",
   "|-", "-|", "|-_", "-|_", "==>", "<=>", "$", "_|_", "^|^", "%", "%%", "!%", "#", "##",
   "%latex", "`"]

/-- The keywords of `lexer.mll:235-256`, except `hint(`. -/
def keywords : List String :=
  ["bool", "nat", "int", "rat", "real", "text", "syntax", "grammar", "relation", "rule", "var",
   "def", "if", "otherwise", "eps", "true", "false", "infinity"]

/-- The input starts, after optional indentation and an optional line comment,
with a newline: the shape `indent* line_comment? '\n'` of `lexer.mll:151`. -/
def commaNlTail (r : List Char) : Option (List Char) :=
  match r.dropWhile isIndent with
  | '\n' :: r' => some r'
  | ';' :: ';' :: b =>
    match b.dropWhile notNl with
    | '\n' :: r' => some r'
    | _ => none
  | _ => none

/-- Positions where a rule other than the symbol rules matches a longer lexeme
than any symbol (or where an unsupported rule would): an identifier or keyword
(`lexer.mll:235-276`, except `_|_`, which is a symbol), a number, a text
literal, layout, a line continuation `\` newline (`lexer.mll:286`), a line
comment, `.id` (`lexer.mll:277-278`), `%n` (`lexer.mll:226`), `,` newline
(`lexer.mll:151`), a block comment (`lexer.mll:283`) and a backquoted
identifier (`lexer.mll:273-276`). -/
def special : List Char → Bool
  | '_' :: '|' :: '_' :: _ => false
  | '\\' :: '\n' :: _ => true
  | ';' :: ';' :: _ => true
  | '.' :: c :: _ => isIdStart c
  | '%' :: c :: _ => isDigit c
  | '(' :: ';' :: _ => true
  | '`' :: c :: _ => isIdStart c
  | ',' :: r => (commaNlTail r).isSome
  | c :: _ => isIdStart c || isDigit c || c == '"' || isSpace c || c == '\n'
  | [] => false

/-! ## Layout (`lexer.mll:121-131`) -/

/-- The rest of a line after indentation leaves `after_nl` with `""`
(`lexer.mll:124`): neither of the two longer rules `lexer.mll:122-123`
applies. -/
def nlOther : List Char → Bool
  | '\n' :: _ => false
  | '|' :: c :: _ => !isIndent c
  | _ => true

/-- The rest of a line after indentation leaves `after_nl_nl` with `""` and
`NL_NL` (`lexer.mll:131`): none of the rules `lexer.mll:127-130` applies. -/
def nlNlOther : List Char → Bool
  | [] => false
  | '\n' :: _ => false
  | '|' :: c :: _ => !isIndent c
  | ';' :: ';' :: _ => false
  | _ => true

/-- `after_nl_nl` (`lexer.mll:126-131`), entered after a blank line. -/
inductive AfterNlNl : List Char → Option Token → List Char → Prop where
  /-- `indent* "|" [' ' '\t']` gives `NL_BAR` (`lexer.mll:127`). -/
  | bar {cs r : List Char} {c : Char} :
      cs.dropWhile isIndent = '|' :: c :: r → isIndent c → AfterNlNl cs (some .nlBar) r
  /-- `indent* '\n'` gives `NL_NL_NL` (`lexer.mll:128`). -/
  | nl {cs r : List Char} : cs.dropWhile isIndent = '\n' :: r → AfterNlNl cs (some .nlNlNl) r
  /-- `indent* line_comment '\n'` loops (`lexer.mll:129`). -/
  | comment {cs b r r' : List Char} {t : Option Token} :
      cs.dropWhile isIndent = ';' :: ';' :: b → b.dropWhile notNl = '\n' :: r →
      AfterNlNl r t r' → AfterNlNl cs t r'
  /-- `indent* eof` ends the input (`lexer.mll:130`). -/
  | eof {cs : List Char} : cs.dropWhile isIndent = [] → AfterNlNl cs none []
  /-- `indent* line_comment eof` ends the input (`lexer.mll:130`). -/
  | eofComment {cs b : List Char} :
      cs.dropWhile isIndent = ';' :: ';' :: b → b.dropWhile notNl = [] → AfterNlNl cs none []
  /-- Otherwise `""` gives `NL_NL` and consumes nothing (`lexer.mll:131`). -/
  | other {cs : List Char} : nlNlOther (cs.dropWhile isIndent) → AfterNlNl cs (some .nlNl) cs

/-- `after_nl` (`lexer.mll:121-124`), entered after a newline. -/
inductive AfterNl : List Char → Option Token → List Char → Prop where
  /-- `indent* "|" [' ' '\t']` gives `NL_BAR` (`lexer.mll:122`). -/
  | bar {cs r : List Char} {c : Char} :
      cs.dropWhile isIndent = '|' :: c :: r → isIndent c → AfterNl cs (some .nlBar) r
  /-- `indent* '\n'` continues in `after_nl_nl` (`lexer.mll:123`). -/
  | nl {cs r r' : List Char} {t : Option Token} :
      cs.dropWhile isIndent = '\n' :: r → AfterNlNl r t r' → AfterNl cs t r'
  /-- Otherwise `""` returns to `token`, emitting nothing (`lexer.mll:124`). -/
  | other {cs : List Char} : nlOther (cs.dropWhile isIndent) → AfterNl cs none cs

/-! ## One step of `token` (`lexer.mll:133-292`) -/

/-- The identifier lexeme at the head of the input: the longest run of
`idcharsub`. -/
abbrev wordOf (cs : List Char) : List Char := cs.takeWhile isIdCharSub

/-- What follows the identifier lexeme at the head of the input. -/
abbrev afterWord (cs : List Char) : List Char := cs.dropWhile isIdCharSub

/-- The input continues with `+` and a hexadecimal digit, so that a preceding
`U` is a `CHARLIT` prefix (`lexer.mll:259`). -/
def plusHex : List Char → Bool
  | '+' :: c :: _ => isHex c
  | _ => false

/-- The input continues with `x` and a hexadecimal digit, so that a preceding
`0` is a `HEXLIT` prefix (`lexer.mll:258`). -/
def hexAfter : List Char → Bool
  | 'x' :: c :: _ => isHex c
  | _ => false

/-- One step of the `token` rule: from `cs`, emit `t` and continue with `r`. -/
inductive Step : List Char → Option Token → List Char → Prop where
  /-- `space # '\n'` is skipped (`lexer.mll:284`). -/
  | space {c : Char} {r : List Char} : isSpace c → Step (c :: r) none r
  /-- A line continuation `\` newline is skipped (`lexer.mll:286`). -/
  | cont {r : List Char} : Step ('\\' :: '\n' :: r) none r
  /-- A newline enters `after_nl` (`lexer.mll:152`, which takes precedence
  over `lexer.mll:285` for the same lexeme). -/
  | newline {r r' : List Char} {t : Option Token} : AfterNl r t r' → Step ('\n' :: r) t r'
  /-- A line comment and its newline enter `after_nl` (`lexer.mll:152`). -/
  | commentNl {b r r' : List Char} {t : Option Token} :
      b.dropWhile notNl = '\n' :: r → AfterNl r t r' → Step (';' :: ';' :: b) t r'
  /-- A line comment at the end of the input ends it (`lexer.mll:280`). -/
  | commentEof {b : List Char} : b.dropWhile notNl = [] → Step (';' :: ';' :: b) none []
  /-- `"," indent* line_comment? '\n'` gives `COMMA_NL` (`lexer.mll:151`). -/
  | commaNl {r r' : List Char} : commaNlTail r = some r' → Step (',' :: r) (some .commaNl) r'
  /-- A symbol, longest among the symbols, where no other rule matches longer
  (`lexer.mll:134-233`). -/
  | sym {s : String} {r : List Char} :
      s ∈ symbols →
      (∀ s' ∈ symbols, s'.toList <+: s.toList ++ r → s'.toList.length ≤ s.toList.length) →
      special (s.toList ++ r) = false → Step (s.toList ++ r) (some (.sym s)) r
  /-- `hint(` (`lexer.mll:251`), which ties with and precedes the identifier
  rule `lexer.mll:272`. -/
  | hint {r : List Char} : Step ('h' :: 'i' :: 'n' :: 't' :: '(' :: r) (some (.sym "hint(")) r
  /-- A keyword (`lexer.mll:235-256`): the whole identifier lexeme, not
  followed by `(` (which would make `lexer.mll:272` longer). -/
  | keyword {c : Char} {cs : List Char} :
      isIdStart c → String.ofList (wordOf (c :: cs)) ∈ keywords →
      (afterWord (c :: cs)).head? ≠ some '(' →
      Step (c :: cs) (some (.sym (String.ofList (wordOf (c :: cs))))) (afterWord (c :: cs))
  /-- An identifier (`lexer.mll:267-270`): the longest `idcharsub` run after a
  letter or `_`, not a keyword, not followed by `(`, and not the prefix of a
  longer `U+…` or `_|_`. -/
  | ident {c : Char} {cs : List Char} :
      isIdStart c → String.ofList (wordOf (c :: cs)) ∉ keywords →
      (afterWord (c :: cs)).head? ≠ some '(' →
      ¬ (wordOf (c :: cs) = ['U'] ∧ plusHex (afterWord (c :: cs))) →
      ¬ (wordOf (c :: cs) = ['_'] ∧ ['|', '_'] <+: afterWord (c :: cs)) →
      Step (c :: cs) (some (.id (wordOf (c :: cs)))) (afterWord (c :: cs))
  /-- An identifier immediately followed by `(` (`lexer.mll:271-272`), except
  `hint(`. -/
  | idParen {c : Char} {cs r : List Char} :
      isIdStart c → afterWord (c :: cs) = '(' :: r → wordOf (c :: cs) ≠ ['h', 'i', 'n', 't'] →
      Step (c :: cs) (some (.idParen (wordOf (c :: cs)))) r
  /-- `NATLIT` (`lexer.mll:257`), unless `0x` and a hex digit follow
  (`lexer.mll:258` is then longer). -/
  | nat {cs s r : List Char} :
      scanSep isDigit cs = (s, r) → s ≠ [] → ¬ (s = ['0'] ∧ hexAfter r) →
      Step cs (some (.nat s)) r
  /-- `HEXLIT` (`lexer.mll:258`). -/
  | hex {cs s r : List Char} :
      scanSep isHex cs = (s, r) → s ≠ [] → Step ('0' :: 'x' :: cs) (some (.hex s)) r
  /-- `CHARLIT` (`lexer.mll:259`). -/
  | char {cs s r : List Char} :
      scanSep isHex cs = (s, r) → s ≠ [] → Step ('U' :: '+' :: cs) (some (.char s)) r
  /-- `TEXTLIT` (`lexer.mll:260`). -/
  | text {n : Nat} {cs b r : List Char} :
      scanText n cs = some (b, r) → Step ('"' :: cs) (some (.text b)) r
  /-- `HOLEN` (`lexer.mll:226`). -/
  | holeN {cs s r : List Char} :
      scanSep isDigit cs = (s, r) → s ≠ [] → Step ('%' :: cs) (some (.holeN s)) r
  /-- `DOTID`, `DOTID_SUB` (`lexer.mll:277-278`). -/
  | dotId {c : Char} {cs : List Char} :
      isIdStart c → Step ('.' :: c :: cs) (some (.dotId (wordOf (c :: cs)))) (afterWord (c :: cs))
  /-- A backquoted identifier (`lexer.mll:273-274`), not followed by `(`. -/
  | tickId {c : Char} {cs : List Char} :
      isIdStart c → (afterWord (c :: cs)).head? ≠ some '(' →
      Step ('`' :: c :: cs) (some (.tickId (wordOf (c :: cs)))) (afterWord (c :: cs))
  /-- A backquoted identifier followed by `(` (`lexer.mll:275-276`). -/
  | tickIdParen {c : Char} {cs r : List Char} :
      isIdStart c → afterWord (c :: cs) = '(' :: r →
      Step ('`' :: c :: cs) (some (.tickIdParen (wordOf (c :: cs)))) r
  /-- A block comment is skipped (`lexer.mll:283`). -/
  | blockComment {n : Nat} {cs r : List Char} :
      skipComment n 0 cs = some r → Step ('(' :: ';' :: cs) none r

/-- A lexing of a whole input: steps until the input is exhausted. -/
inductive Lexes : List Char → List Token → Prop where
  /-- The end of the input (`lexer.mll:287`). -/
  | nil : Lexes [] []
  /-- A step that emits nothing. -/
  | skip {cs r : List Char} {ts : List Token} : Step cs none r → Lexes r ts → Lexes cs ts
  /-- A step that emits a token. -/
  | tok {cs r : List Char} {t : Token} {ts : List Token} :
      Step cs (some t) r → Lexes r ts → Lexes cs (t :: ts)

/-! ## The lexer -/

/-- `after_nl_nl`, with fuel for the comment-line loop. -/
def afterNlNl? : Nat → List Char → Option (Option Token × List Char)
  | 0, _ => none
  | n + 1, cs =>
    match cs.dropWhile isIndent with
    | [] => some (none, [])
    | '\n' :: r => some (some .nlNlNl, r)
    | '|' :: c :: r =>
      if isIndent c then some (some .nlBar, r)
      else if nlNlOther (cs.dropWhile isIndent) then some (some .nlNl, cs) else none
    | ';' :: ';' :: b =>
      match b.dropWhile notNl with
      | [] => some (none, [])
      | '\n' :: r => afterNlNl? n r
      | _ => none
    | _ => if nlNlOther (cs.dropWhile isIndent) then some (some .nlNl, cs) else none

/-- `after_nl`. -/
def afterNl? (cs : List Char) : Option (Option Token × List Char) :=
  match cs.dropWhile isIndent with
  | '\n' :: r => afterNlNl? (r.length + 1) r
  | '|' :: c :: r =>
    if isIndent c then some (some .nlBar, r)
    else if nlOther (cs.dropWhile isIndent) then some (none, cs) else none
  | _ => if nlOther (cs.dropWhile isIndent) then some (none, cs) else none

/-- Fixed-token candidates: the longest symbol that is a prefix of the input,
checked to be one. -/
def symStep? (cs : List Char) : Option (Option Token × List Char) :=
  let best := symbols.foldl (fun (b : Option String) s =>
    if s.toList.isPrefixOf cs && (b.map (·.toList.length)).getD 0 < s.toList.length then some s
    else b) none
  match best with
  | none => none
  | some s =>
    if symbols.contains s && s.toList.isPrefixOf cs && special cs == false &&
        symbols.all (fun s' => !s'.toList.isPrefixOf cs || decide (s'.toList.length ≤ s.toList.length))
    then some (some (.sym s), cs.drop s.toList.length) else none

/-- An identifier lexeme `w` not followed by `(`, with what follows it `r`:
a keyword, or an identifier unless it starts a longer `U+…` or `_|_`. -/
def identAt? (w r : List Char) : Option (Option Token × List Char) :=
  if keywords.contains (String.ofList w) then some (some (.sym (String.ofList w)), r)
  else if w = ['U'] && plusHex r then none
  else if w = ['_'] && ['|', '_'].isPrefixOf r then none
  else some (some (.id w), r)

/-- An identifier lexeme `w` followed by `r`. -/
def wordAt? (w r : List Char) : Option (Option Token × List Char) :=
  if r.head? == some '(' then
    if w = ['h', 'i', 'n', 't'] then none else some (some (.idParen w), r.tail)
  else identAt? w r

/-- Identifier-shaped candidates: `hint(`, keywords, identifiers and `id(`. -/
def wordStep? : List Char → Option (Option Token × List Char)
  | 'h' :: 'i' :: 'n' :: 't' :: '(' :: r => some (some (.sym "hint("), r)
  | c :: cs => if isIdStart c then wordAt? (wordOf (c :: cs)) (afterWord (c :: cs)) else none
  | [] => none

/-- A token made of a nonempty `p ('_'? p)*` run. -/
def sepTok? (p : Char → Bool) (mk : List Char → Token) (cs : List Char) :
    Option (Option Token × List Char) :=
  match scanSep p cs with
  | ([], _) => none
  | (s, r) => some (some (mk s), r)

/-- After `0x`: a `HEXLIT`, or else the `NATLIT` `0`. -/
def zeroX? (cs : List Char) : Option (Option Token × List Char) :=
  match scanSep isHex cs with
  | ([], _) => some (some (.nat ['0']), 'x' :: cs)
  | (s, r) => some (some (.hex s), r)

/-- A `NATLIT`, unless it is the `0` of a `HEXLIT`. -/
def natStep? (cs : List Char) : Option (Option Token × List Char) :=
  match scanSep isDigit cs with
  | ([], _) => none
  | (s, r) => if s = ['0'] && hexAfter r then none else some (some (.nat s), r)

/-- A backquoted identifier lexeme `w` followed by `r`. -/
def tickAt? (w r : List Char) : Option (Option Token × List Char) :=
  if r.head? == some '(' then some (some (.tickIdParen w), r.tail) else some (some (.tickId w), r)

/-- Literal candidates: numbers, text, `%n`, `.id`, backquoted identifiers and
block comments. -/
def litStep? : List Char → Option (Option Token × List Char)
  | '0' :: 'x' :: cs => zeroX? cs
  | 'U' :: '+' :: cs => sepTok? isHex .char cs
  | '"' :: cs => (scanText (cs.length + 1) cs).map fun (b, r) => (some (.text b), r)
  | '%' :: cs => sepTok? isDigit .holeN cs
  | '.' :: c :: cs =>
    if isIdStart c then some (some (.dotId (wordOf (c :: cs))), afterWord (c :: cs)) else none
  | '`' :: c :: cs => if isIdStart c then tickAt? (wordOf (c :: cs)) (afterWord (c :: cs)) else none
  | '(' :: ';' :: cs => (skipComment (cs.length + 1) 0 cs).map fun r => (none, r)
  | cs => natStep? cs

/-- Layout candidates: spaces, newlines, comments, `,` newline. -/
def layoutStep? : List Char → Option (Option Token × List Char)
  | '\\' :: '\n' :: r => some (none, r)
  | '\n' :: r => afterNl? r
  | ';' :: ';' :: b =>
    match b.dropWhile notNl with
    | [] => some (none, [])
    | '\n' :: r => afterNl? r
    | _ => none
  | ',' :: r => (commaNlTail r).map fun r' => (some .commaNl, r')
  | c :: r => if isSpace c then some (none, r) else none
  | [] => none

/-- One lexer step: the first candidate that applies. -/
def step? (cs : List Char) : Option (Option Token × List Char) :=
  layoutStep? cs <|> wordStep? cs <|> litStep? cs <|> symStep? cs

/-- Steps to the end of the input; `n` bounds the number of steps. -/
def lexList? : Nat → List Char → Option (List Token)
  | _, [] => some []
  | 0, _ :: _ => none
  | n + 1, c :: cs =>
    match step? (c :: cs) with
    | some (none, r) => lexList? n r
    | some (some t, r) => (lexList? n r).map (t :: ·)
    | none => none

/-- The lexer. Every step consumes at least one character, so `length + 1`
steps suffice. -/
def lex? (s : String) : Option (List Token) :=
  let cs := s.toList
  lexList? (cs.length + 1) cs

end Silmaril.Wasm.SpecTec.Surface.Lexer
