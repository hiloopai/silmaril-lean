module

public import Init

/-!
# WIT text: tokens, lexer and layout

The lexical layer of the WIT text format (`design/mvp/WIT.md` of
WebAssembly/component-model at `8505ba73dda2775b9438c0b8d169b96a556f864a`, "Lexical
structure"; the tokenizer of `wit-parser` 0.263.0, `src/ast/lex.rs`, for the keyword
list and the treatment of `%`).

* `Tok`: identifiers (`id`, the name without its `%` escape), keywords (`kw`),
  one-character symbols (`sym`), `->` (`arrow`), number literals (`num`: integers and
  semantic versions, one token) and doc-comment lines (`doc`: the characters after
  `///` up to the end of the line).
* `lex : List Char → Option (List Tok)`: whitespace (space, tab, newline, carriage
  return), line comments `// …` and nested block comments `/* … */` are skipped; a line
  comment that starts with exactly three slashes is a doc line. A word that is a
  keyword is a keyword unless it is written with `%`.
* `Tok.str`: the characters of a token (a keyword-named identifier gets its `%`).
* `render`: a layout of tokens annotated with a break (`Brk`: nothing, a space or a
  new line), indenting by brace depth. A requested `none` that would glue two tokens
  into something else (`stopB` fails) becomes a space, so every layout lexes back
  (`Silmaril.Wasm.Wit.Text.lex_render`).

## Deviations from `wit-parser`

`wit-parser` 0.263.0 treats *every* comment right before an item as documentation
(and dedents and trims the lines); here only `///` lines are documentation, as WIT.md
says, and their text is kept verbatim (the parser strips one leading space). Block doc
comments `/** … */` are read as ordinary comments. Identifiers are ASCII (`wit-parser`
lexes Unicode `XID` characters and rejects them later). Integers and versions are one
`num` token (a run of letters, digits and `-`, with `.` and `+` when followed by one of
those); `wit-parser` assembles versions from several tokens.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Text

/-- The keywords of `wit-parser` 0.263.0. -/
inductive Kw where
  | «use»
  | «type»
  | «func»
  | «u8»
  | «u16»
  | «u32»
  | «u64»
  | «s8»
  | «s16»
  | «s32»
  | «s64»
  | «f32»
  | «f64»
  | «char»
  | «resource»
  | «own»
  | «borrow»
  | «record»
  | «flags»
  | «variant»
  | «enum»
  | «bool»
  | «string»
  | «option»
  | «result»
  | «future»
  | «stream»
  | errorContext
  | «list»
  | «map»
  | underscore
  | «as»
  | «from»
  | «static»
  | «interface»
  | «tuple»
  | «world»
  | «import»
  | «export»
  | «package»
  | ctor
  | «include»
  | «with»
  | «async»
  deriving Repr, DecidableEq, Inhabited

/-- The spelling of a keyword. -/
def Kw.name : Kw → String
  | .«use» => "use"
  | .«type» => "type"
  | .«func» => "func"
  | .«u8» => "u8"
  | .«u16» => "u16"
  | .«u32» => "u32"
  | .«u64» => "u64"
  | .«s8» => "s8"
  | .«s16» => "s16"
  | .«s32» => "s32"
  | .«s64» => "s64"
  | .«f32» => "f32"
  | .«f64» => "f64"
  | .«char» => "char"
  | .«resource» => "resource"
  | .«own» => "own"
  | .«borrow» => "borrow"
  | .«record» => "record"
  | .«flags» => "flags"
  | .«variant» => "variant"
  | .«enum» => "enum"
  | .«bool» => "bool"
  | .«string» => "string"
  | .«option» => "option"
  | .«result» => "result"
  | .«future» => "future"
  | .«stream» => "stream"
  | .errorContext => "error-context"
  | .«list» => "list"
  | .«map» => "map"
  | .underscore => "_"
  | .«as» => "as"
  | .«from» => "from"
  | .«static» => "static"
  | .«interface» => "interface"
  | .«tuple» => "tuple"
  | .«world» => "world"
  | .«import» => "import"
  | .«export» => "export"
  | .«package» => "package"
  | .ctor => "constructor"
  | .«include» => "include"
  | .«with» => "with"
  | .«async» => "async"

/-- Every keyword. -/
def Kw.all : List Kw :=
  [.«use», .«type», .«func», .«u8», .«u16», .«u32», .«u64», .«s8», .«s16», .«s32», .«s64», .«f32», .«f64», .«char», .«resource», .«own», .«borrow», .«record», .«flags», .«variant», .«enum», .«bool», .«string», .«option», .«result», .«future», .«stream», .errorContext, .«list», .«map», .underscore, .«as», .«from», .«static», .«interface», .«tuple», .«world», .«import», .«export», .«package», .ctor, .«include», .«with», .«async»]

/-- The keyword a word spells, if any. -/
def kwOf? (s : String) : Option Kw := Kw.all.find? (·.name == s)

/-- Tokens. -/
inductive Tok where
  /-- An identifier, without its `%` escape. -/
  | id (s : String)
  /-- A keyword. -/
  | kw (k : Kw)
  /-- One of `= , : . ; ( ) { } < > @ * /`. -/
  | sym (c : Char)
  /-- `->`. -/
  | arrow
  /-- An integer or a semantic version. -/
  | num (s : String)
  /-- A doc-comment line: the characters after `///`. -/
  | doc (s : String)
  deriving Repr, DecidableEq, Inhabited

/-! ## Characters -/

/-- An ASCII letter. -/
def isLetter (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

/-- An ASCII digit. -/
def isDigitC (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- The first character of a word: a letter or `_`. -/
def wordStart (c : Char) : Bool := isLetter c || c == '_'

/-- The other characters of a word (and of a number literal): letters, digits, `-`. -/
def wordCont (c : Char) : Bool := isLetter c || isDigitC c || c == '-'

/-- Whitespace. -/
def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- The one-character symbols. -/
def symChars : List Char := ['=', ',', ':', '.', ';', '(', ')', '{', '}', '<', '>', '@', '*', '/']

/-! ## Lexer -/

/-- The rest of a line and what follows its newline. -/
def takeLine : List Char → List Char × List Char
  | [] => ([], [])
  | '\n' :: r => ([], r)
  | c :: r => (c :: (takeLine r).1, (takeLine r).2)

/-- Skip the rest of a block comment, `d` nested comments deep. -/
def skipBlock : Nat → List Char → Option (List Char)
  | _, [] => none
  | 0, '*' :: '/' :: r => some r
  | d + 1, '*' :: '/' :: r => skipBlock d r
  | d, '/' :: '*' :: r => skipBlock (d + 1) r
  | d, _ :: r => skipBlock d r

/-- The rest of a number literal: letters, digits and `-`, and `.` or `+` followed by
one of those. -/
def takeNum : List Char → List Char × List Char
  | [] => ([], [])
  | c :: r =>
    if wordCont c || ((c == '.' || c == '+') && (r.head?.map wordCont).getD false) then
      (c :: (takeNum r).1, (takeNum r).2)
    else ([], c :: r)

theorem takeLine_length_le (cs : List Char) : (takeLine cs).2.length ≤ cs.length := by
  fun_induction takeLine cs <;> simp_all <;> omega

theorem skipBlock_length_le (d : Nat) (cs : List Char) : ∀ r, skipBlock d cs = some r →
    r.length ≤ cs.length := by
  fun_induction skipBlock d cs <;> intro r h <;> simp_all <;> omega

theorem takeNum_length_le (cs : List Char) : (takeNum cs).2.length ≤ cs.length := by
  fun_induction takeNum cs <;> simp_all <;> omega

theorem dropWhile_length_le' (p : Char → Bool) : ∀ l : List Char,
    (l.dropWhile p).length ≤ l.length
  | [] => by simp
  | c :: l => by
    rw [List.dropWhile_cons]; split
    · have := dropWhile_length_le' p l; simp; omega
    · simp

/-- The token of a word: a keyword or an identifier. -/
def wordTok (w : String) : Tok :=
  match kwOf? w with
  | some k => .kw k
  | none => .id w

/-- The lexer. -/
def lex (cs : List Char) : Option (List Tok) :=
  match cs with
  | [] => some []
  | '/' :: '/' :: '/' :: r =>
    have := takeLine_length_le r
    if r.head? = some '/' then lex (takeLine r).2
    else (Tok.doc (String.ofList (takeLine r).1) :: ·) <$> lex (takeLine r).2
  | '/' :: '/' :: r =>
    have := takeLine_length_le r
    lex (takeLine r).2
  | '/' :: '*' :: r =>
    match h : skipBlock 0 r with
    | none => none
    | some r' =>
      have := skipBlock_length_le 0 r r' h
      lex r'
  | '-' :: '>' :: r => (Tok.arrow :: ·) <$> lex r
  | '%' :: c :: r =>
    have := dropWhile_length_le' wordCont r
    if isLetter c then
      (Tok.id (String.ofList (c :: r.takeWhile wordCont)) :: ·) <$> lex (r.dropWhile wordCont)
    else none
  | c :: r =>
    have := dropWhile_length_le' wordCont r
    have := takeNum_length_le r
    if isWs c then lex r
    else if isDigitC c then
      (Tok.num (String.ofList (c :: (takeNum r).1)) :: ·) <$> lex (takeNum r).2
    else if wordStart c then
      (wordTok (String.ofList (c :: r.takeWhile wordCont)) :: ·) <$> lex (r.dropWhile wordCont)
    else if symChars.contains c then (Tok.sym c :: ·) <$> lex r
    else none
termination_by cs.length
decreasing_by all_goals (simp_all; try omega)

/-! ## Printing tokens -/

/-- The characters of a token. -/
def Tok.str : Tok → List Char
  | .id s => if (kwOf? s).isSome then '%' :: s.toList else s.toList
  | .kw k => k.name.toList
  | .sym c => [c]
  | .arrow => ['-', '>']
  | .num s => s.toList
  | .doc s => '/' :: '/' :: '/' :: (s.toList ++ ['\n'])

/-- An identifier the lexer reads back: a letter, then letters, digits and `-`. -/
def idOk (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => isLetter c && cs.all wordCont

/-- A number literal the lexer reads back: a digit, then what `takeNum` takes, all of
it. -/
def numOk (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => isDigitC c && (takeNum cs).2.isEmpty

/-- Tokens the lexer reads back. -/
def Tok.ok : Tok → Bool
  | .id s => idOk s
  | .kw _ => true
  | .sym c => symChars.contains c
  | .arrow => true
  | .num s => numOk s
  | .doc s => !s.toList.contains '\n' && s.toList.head? != some '/'

/-- The characters `cs` may follow token `t` without a separator: they do not extend a
word or a number, and do not turn `/` into a comment. -/
def stopB : Tok → List Char → Bool
  | .id _, cs | .kw _, cs => match cs with
    | [] => true
    | c :: _ => !wordCont c
  | .num _, cs => (takeNum cs).1.isEmpty
  | .sym '/', cs => match cs with
    | '/' :: _ | '*' :: _ => false
    | _ => true
  | _, _ => true

/-! ## Layout -/

/-- What follows a token in a layout. -/
inductive Brk where
  | none
  | sp
  | nl
  deriving Repr, DecidableEq, Inhabited

/-- A token with the break after it. -/
abbrev PTok := Tok × Brk

/-- The tokens of a layout. -/
def toks (ps : List PTok) : List Tok := ps.map Prod.fst

/-- Brace depth after a token. -/
def depthAfter (d : Nat) : Tok → Nat
  | .sym '{' => d + 1
  | .sym '}' => d - 1
  | _ => d

/-- The indentation of a new line at depth `d` before `next` (one less before `}`). -/
def indent (d : Nat) (next : Option PTok) : List Char :=
  List.replicate (2 * (if (next.map Prod.fst) = some (.sym '}') then d - 1 else d)) ' '

/-- The separator after token `a` with break `b`, at depth `d` (after `a`), before the
token `next` and the characters `r`. -/
def gap (d : Nat) (a : Tok) (b : Brk) (next : Option PTok) (r : List Char) : List Char :=
  match a with
  | .doc _ => indent d next
  | _ => match b with
    | .nl => '\n' :: indent d next
    | .sp => [' ']
    | .none =>
      if (next.map Prod.fst) = some (.sym '{') ∧ a ≠ .sym '.' then [' ']
      else if stopB a r then [] else [' ']

/-- Lay a token list out as characters, starting at depth `d`. -/
def render (d : Nat) : List PTok → List Char
  | [] => []
  | (a, b) :: rest =>
    let d' := depthAfter d a
    let r := render d' rest
    a.str ++ gap d' a b rest.head? r ++ r

end Silmaril.Wasm.Wit.Text
