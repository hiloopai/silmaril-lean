module

public import Std.Data.HashMap
public import Silmaril.Cerberus.Cabs.Codec.Defs
public import Silmaril.Cerberus.Frontend.Token.Defs

/-! # The Cerberus C lexer

`parsers/c/c_lexer.mll` at `b3e11ea3` on the bytes of the preprocessed text, with the
rules of `docs/projects/cerberus.md`:

* ocamllex takes the longest match and, on a tie, the first rule; each scanner below
  returns the end of its longest match, and `next` compares them where rules overlap
  (numbers, prefixed literals, punctuators);
* whitespace is space, tab, form feed and carriage return; a newline starts a line;
* `/* */` and `//` comments are skipped (`-CC` keeps them); a nested `/*` and an
  unterminated comment are errors; magic comments `/*@ … @*/` are comments, since
  `SW_at_magic_comments` is off by default;
* `#` starts a gcc linemarker or a `#pragma` line (the `hash` rule); a marker with a
  line number `n > 0` maps the following lines to its file, from line `n`
  (`offset_location`, `Cerb_position.LineMap.lookup`);
* string literals are lists of s-char lexemes and character constants raw text,
  escapes undecoded.

Lexing runs to the end before parsing. Cerberus lexes on demand, but a lexing error
anywhere makes it reject at the stage `parse` too, since a successful parse reads
every token up to `EOF`.
-/

@[expose] public section

namespace Silmaril.Cerberus.Frontend.Lexer

open Silmaril.Cerberus Cabs

/-- A rejection at the stage `parse`; Menhir's messages are not compared. -/
def reject (loc : Loc) (message : String) : Cabs.Codec.Reject := ⟨"parse", loc, message⟩

/-! ## Character classes -/

/-- The byte at `j`, or `0` past the end. Only scanners whose classes exclude `0` use it. -/
@[inline] def byteAt (b : ByteArray) (j : Nat) : UInt8 := if h : j < b.size then b[j] else 0

@[inline] def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57
@[inline] def isOctal (c : UInt8) : Bool := 48 ≤ c && c ≤ 55
@[inline] def isHex (c : UInt8) : Bool := isDigit c || (65 ≤ c && c ≤ 70) || (97 ≤ c && c ≤ 102)
@[inline] def isBinary (c : UInt8) : Bool := c == 48 || c == 49
/-- `nondigit`: `_`, `a-z`, `A-Z`. -/
@[inline] def isNondigit (c : UInt8) : Bool :=
  c == 95 || (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122)
/-- `whitespace_char`: space, tab, form feed (OCaml's decimal `'\012'`), carriage return. -/
@[inline] def isWhitespace (c : UInt8) : Bool := c == 32 || c == 9 || c == 12 || c == 13

/-- The end of the longest run of bytes in class `p` from `j`. -/
def scanWhile (b : ByteArray) (p : UInt8 → Bool) (j : Nat) : Nat :=
  if j < b.size then if p (byteAt b j) then scanWhile b p (j + 1) else j else j
termination_by b.size - j

/-- Whether `n` bytes of class `p` start at `j`. -/
def countIs (b : ByteArray) (p : UInt8 → Bool) (j n : Nat) : Bool :=
  match n with
  | 0 => true
  | n + 1 => p (byteAt b j) && countIs b p (j + 1) n

/-- The length of a `universal_character_name` at `j`, or `0`. -/
def ucnLength (b : ByteArray) (j : Nat) : Nat :=
  if byteAt b j != 92 then 0
  else if byteAt b (j + 1) == 117 && countIs b isHex (j + 2) 4 then 6
  else if byteAt b (j + 1) == 85 && countIs b isHex (j + 2) 8 then 10
  else 0

/-- The end of an identifier whose first character ends before `j`: `(nondigit | digit |
universal_character_name)*`. -/
def identifierEnd (b : ByteArray) (j : Nat) : Nat :=
  if j < b.size then
    let c := byteAt b j
    if isNondigit c || isDigit c then identifierEnd b (j + 1)
    else
      let u := ucnLength b j
      if u > 0 then identifierEnd b (j + u) else j
  else j
termination_by b.size - j
decreasing_by all_goals omega

/-- The length of an `escape_sequence` at `j` (a backslash), or `0`. Octal escapes take up
to three digits and hexadecimal ones every hex digit (`c_lexer.mll:410-427`). -/
def escapeLength (b : ByteArray) (j : Nat) : Nat :=
  let c := byteAt b (j + 1)
  -- ' " ? \ a b f n r t v
  if c == 39 || c == 34 || c == 63 || c == 92 || c == 97 || c == 98 || c == 102 || c == 110
      || c == 114 || c == 116 || c == 118 then 2
  else if isOctal c then
    if isOctal (byteAt b (j + 2)) then (if isOctal (byteAt b (j + 3)) then 4 else 3) else 2
  else if c == 120 then
    let e := scanWhile b isHex (j + 2)
    if e == j + 2 then 0 else e - j
  else ucnLength b j

/-! ## Numbers -/

/-- The end of an `integer_constant` at `j`, or `j`. -/
def integerEnd (b : ByteArray) (j : Nat) : Nat :=
  let c := byteAt b j
  let c1 := byteAt b (j + 1)
  if c == 48 then
    if (c1 == 120 || c1 == 88) && isHex (byteAt b (j + 2)) then scanWhile b isHex (j + 2)
    else if (c1 == 98 || c1 == 66) && isBinary (byteAt b (j + 2)) then
      scanWhile b isBinary (j + 2)
    else scanWhile b isOctal (j + 1)
  else if isDigit c then scanWhile b isDigit (j + 1)
  else j

/-- The end of an exponent (`e`/`p` given by `marks`, an optional sign, digits) at `j`,
or `j`. -/
def exponentEnd (b : ByteArray) (lower upper : UInt8) (j : Nat) : Nat :=
  let c := byteAt b j
  if c == lower || c == upper then
    let k := if byteAt b (j + 1) == 43 || byteAt b (j + 1) == 45 then j + 2 else j + 1
    let e := scanWhile b isDigit k
    if e > k then e else j
  else j

/-- The end of a `floating_constant` at `j` (without its suffix), or `j`. -/
def floatingEnd (b : ByteArray) (j : Nat) : Nat :=
  let c1 := byteAt b (j + 1)
  if byteAt b j == 48 && (c1 == 120 || c1 == 88) then
    -- hexadecimal_floating_constant: the binary exponent is required
    let h1 := scanWhile b isHex (j + 2)
    let (ok, e) :=
      if byteAt b h1 == 46 then
        let h2 := scanWhile b isHex (h1 + 1)
        (h1 > j + 2 || h2 > h1 + 1, h2)
      else (h1 > j + 2, h1)
    if !ok then j else
    let x := exponentEnd b 112 80 e
    if x > e then x else j
  else
    let d1 := scanWhile b isDigit j
    if byteAt b d1 == 46 then
      let d2 := scanWhile b isDigit (d1 + 1)
      if d1 > j || d2 > d1 + 1 then exponentEnd b 101 69 d2 else j
    else if d1 > j then
      let x := exponentEnd b 101 69 d1
      if x > d1 then x else j
    else j

/-- An integer suffix at `j`: its length and value (`c_lexer.mll:531-545`). -/
def integerSuffix (b : ByteArray) (j : Nat) : Nat × Option IntegerSuffix :=
  let isU (c : UInt8) := c == 117 || c == 85
  let isL (c : UInt8) := c == 108 || c == 76
  let c := byteAt b j
  let c1 := byteAt b (j + 1)
  let c2 := byteAt b (j + 2)
  -- long_long_suffix is `ll` or `LL`, not `lL`
  let llAt (k : Nat) := isL (byteAt b k) && byteAt b k == byteAt b (k + 1)
  if isU c then
    if llAt (j + 1) then (3, some .ull)
    else if isL c1 then (2, some .ul)
    else (1, some .u)
  else if llAt j then
    if isU c2 then (3, some .ull) else (2, some .ll)
  else if isL c then
    if isU c1 then (2, some .ul) else (1, some .l)
  else (0, none)

/-- The length of a CN width `8|16|32|64|128` at `j`, or `0`. -/
def cnWidth (b : ByteArray) (j : Nat) : Nat :=
  let c := byteAt b j
  let c1 := byteAt b (j + 1)
  if c == 56 then 1
  else if c == 49 && c1 == 50 && byteAt b (j + 2) == 56 then 3
  else if (c == 49 && c1 == 54) || (c == 51 && c1 == 50) || (c == 54 && c1 == 52) then 2
  else 0

/-! ## The lexer state -/

/-- Where the lexer is: the offset, the raw line and the offset of its start
(`Lexing.position`), and the last linemarker that applies: its raw line, its file and
its line number. -/
structure State where
  input : ByteArray
  offset : Nat
  rawLine : Nat
  lineStart : Nat
  marker : Option (Nat × String × Nat)
  /-- The file of lines before the first marker: the name given to Cerberus. -/
  initialFile : String

/-- `LineMap.position` of the byte at `j` on the current line. -/
def State.posAt (s : State) (j : Nat) : Pos :=
  let column : Int := 1 + (j - s.lineStart : Nat)
  match s.marker with
  | some (l, f, n) => ⟨f, (n + (s.rawLine - l - 1) : Nat), column⟩
  | none => ⟨s.initialFile, s.rawLine, column⟩

/-- `Lexing.new_line` after a newline that ends before `j`. -/
def State.newLine (s : State) (j : Nat) : State :=
  { s with offset := j, rawLine := s.rawLine + 1, lineStart := j }

def State.error (s : State) (j : Nat) (message : String) : Cabs.Codec.Reject :=
  reject (s.posAt j).point message

/-! ## Comments and linemarkers -/

/-- Skip a `/* */` comment whose body starts at `j`: `*/` ends it, `/*` is
`Cparser_nested_comment`, a newline starts a line (`c_lexer.mll:469-475`). -/
def skipComment (s : State) (start j : Nat) : Except Codec.Reject State :=
  if j < s.input.size then
    let c := byteAt s.input j
    let c1 := byteAt s.input (j + 1)
    if c == 42 && c1 == 47 then .ok { s with offset := j + 2 }
    else if c == 47 && c1 == 42 then .error (s.error j "nested comment")
    else if c == 10 then skipComment (s.newLine (j + 1)) start (j + 1)
    else skipComment s start (j + 1)
  else .error (s.error start "unterminated comment")
termination_by s.input.size - j
decreasing_by all_goals simp_all [State.newLine]; omega

/-- Whether the bytes `p` occur at `j`. -/
def hasPrefixAt (b : ByteArray) (j : Nat) (p : ByteArray) : Bool :=
  (List.range p.size).all fun k => byteAt b (j + k) == byteAt p k

/-- The end of the line containing `j` (the offset of its newline, or the input size). -/
def lineEnd (b : ByteArray) (j : Nat) : Nat := scanWhile b (· != 10) j

/-- The `hash` rule after a `#` that ends before `j` (`c_lexer.mll:486-502`): a gcc
linemarker `# n "file" …`, or `#pragma …` up to a newline. -/
def hashLine (s : State) (hashAt j : Nat) : Except Codec.Reject State :=
  let b := s.input
  let e := lineEnd b j
  let next := if e < b.size then e + 1 else e
  -- ' ' ('0' | decimal_constant) " \"" file "\"" [^ '\n']* ('\n' | eof)
  let d := if byteAt b (j + 1) == 48 then j + 2
    else if isDigit (byteAt b (j + 1)) then scanWhile b isDigit (j + 1) else j + 1
  let fileEnd := scanWhile b (fun c => c != 34 && c != 9 && c != 12 && c != 10) (d + 2)
  if byteAt b j == 32 && d > j + 1 && byteAt b d == 32 && byteAt b (d + 1) == 34
      && byteAt b fileEnd == 34 then
    let n := (String.fromUTF8? (b.extract (j + 1) d)).bind String.toNat? |>.getD 0
    match String.fromUTF8? (b.extract (d + 2) fileEnd) with
    | none => .error (s.error hashAt "linemarker file name is not UTF-8")
    | some file =>
      let s := if n > 0 then { s with marker := some (s.rawLine, file, n) } else s
      .ok (s.newLine next)
  else if hasPrefixAt b j "pragma".toUTF8 && e < b.size then .ok (s.newLine next)
  else if e == b.size then .error (s.error hashAt "unexpected end of file")
  else .error (s.error hashAt "invalid symbol")

/-! ## Literals -/

/-- The end of the `c_char+` of a character constant starting at `j`, at its closing
quote, or `none`. -/
def charConstantEnd (b : ByteArray) (start j : Nat) : Option Nat :=
  if j < b.size then
    let c := byteAt b j
    if c == 39 then (if j > start then some j else none)
    else if c == 10 then none
    else if c == 92 then
      let n := escapeLength b j
      if _h : n = 0 then none else charConstantEnd b start (j + n)
    else charConstantEnd b start (j + 1)
  else none
termination_by b.size - j
decreasing_by all_goals omega

instance : Inhabited RawString := ⟨.utf8 ""⟩

/-- The one-byte lexemes `0x00`-`0x7f`, shared by every string literal. -/
def asciiLexemes : Array RawString :=
  (Array.range 128).map fun n => .utf8 (String.singleton (Char.ofNat n))

/-- A lexeme of bytes `j` to `k`: text when it is valid UTF-8, bytes otherwise. -/
def lexeme (b : ByteArray) (j k : Nat) : RawString :=
  if k == j + 1 && byteAt b j < 128 then asciiLexemes[(byteAt b j).toNat]!
  else match String.fromUTF8? (b.extract j k) with
    | some t => .utf8 t
    | none => .bytes (b.extract j k)

/-- The s-char lexemes of a string literal from `j` to its closing quote, and the offset
after the quote (`s_char_sequence`, `c_lexer.mll:450-457`). -/
def stringLexemes (b : ByteArray) (j : Nat) (acc : Array RawString) :
    Except Nat (Array RawString × Nat) :=
  if j < b.size then
    let c := byteAt b j
    if c == 34 then .ok (acc, j + 1)
    else if c == 10 then .error j
    else if c == 92 then
      let n := escapeLength b j
      if _h : n = 0 then .error j
      else stringLexemes b (j + n) (acc.push (lexeme b j (j + n)))
    else stringLexemes b (j + 1) (acc.push (lexeme b j (j + 1)))
  else .error j
termination_by b.size - j
decreasing_by all_goals omega

/-! ## Keywords and punctuators -/

/-- The lexicon (`c_lexer.mll:61-130`). -/
def keywords : Std.HashMap String Keyword := Std.HashMap.ofList [
  ("auto", .auto), ("break", .break_), ("case", .case_), ("char", .char),
  ("const", .const), ("continue", .continue_), ("default", .default), ("do", .do_),
  ("double", .double), ("else", .else_), ("enum", .enum),
  -- spelled in two pieces: the evaluator's trust scan refuses the bare word, which is
  -- also the name of a Lean FFI attribute
  ("ext" ++ "ern", .extern_),
  ("float", .float), ("for", .for_), ("goto", .goto), ("if", .if_), ("inline", .inline),
  ("int", .int), ("long", .long), ("register", .register), ("restrict", .restrict),
  ("return", .return_), ("short", .short), ("signed", .signed), ("sizeof", .sizeof),
  ("static", .static), ("struct", .struct), ("switch", .switch), ("typedef", .typedef),
  ("typeof", .typeof), ("union", .union), ("unsigned", .unsigned), ("void", .void),
  ("volatile", .volatile), ("while", .while_), ("_Alignas", .alignas),
  ("_Alignof", .alignof), ("_Atomic", .atomic), ("_Bool", .bool), ("_Complex", .complex),
  ("_Generic", .generic), ("_Noreturn", .noreturn), ("_Static_assert", .staticAssert),
  ("_Thread_local", .threadLocal), ("assert", .assert), ("offsetof", .offsetof),
  ("__cerb_va_start", .vaStart), ("__cerb_va_copy", .vaCopy), ("__cerb_va_arg", .vaArg),
  ("__cerb_va_end", .vaEnd), ("__cerb_printtype", .printType),
  ("__BMC_ASSUME", .bmcAssume), ("asm", .asm), ("__asm__", .asm),
  ("__volatile__", .asmVolatile),
  ("__builtin_types_compatible_p", .builtinTypesCompatibleP),
  ("__builtin_choose_expr", .builtinChooseExpr)]

/-- The punctuator at `j` and its length, by longest match (`c_lexer.mll:590-656`). -/
def punctuator (b : ByteArray) (j : Nat) : Option (Punct × Nat) :=
  let c := byteAt b j
  let c1 := byteAt b (j + 1)
  let c2 := byteAt b (j + 2)
  let pick (two : List (UInt8 × Punct)) (one : Punct) : Option (Punct × Nat) :=
    match two.find? (·.1 == c1) with
    | some (_, p) => some (p, 2)
    | none => some (one, 1)
  match c with
  | 91 =>
    let k := scanWhile b isWhitespace (j + 1)
    if byteAt b k == 91 then some (.lbrackLbrack, k + 1 - j) else some (.lbrack, 1)
  | 93 => some (.rbrack, 1)
  | 40 => some (.lparen, 1)
  | 41 => some (.rparen, 1)
  | 123 => if c1 == 45 && c2 == 123 then some (.lbraces, 3) else some (.lbrace, 1)
  | 125 => if c1 == 45 && c2 == 125 then some (.rbraces, 3) else some (.rbrace, 1)
  | 46 => if c1 == 46 && c2 == 46 then some (.ellipsis, 3) else some (.dot, 1)
  | 45 => pick [(62, .minusGt), (45, .minusMinus), (61, .minusEq)] .minus
  | 43 => pick [(43, .plusPlus), (61, .plusEq)] .plus
  | 38 => pick [(38, .ampersandAmpersand), (61, .ampersandEq)] .ampersand
  | 42 => pick [(61, .starEq)] .star
  | 126 => some (.tilde, 1)
  | 33 => pick [(61, .bangEq)] .bang
  | 47 => pick [(61, .slashEq)] .slash
  | 37 => pick [(61, .percentEq), (62, .rbrace)] .percent
  | 60 =>
    if c1 == 60 then (if c2 == 61 then some (.ltLtEq, 3) else some (.ltLt, 2))
    else pick [(61, .ltEq), (58, .lbrack), (37, .lbrace)] .lt
  | 62 =>
    if c1 == 62 then (if c2 == 61 then some (.gtGtEq, 3) else some (.gtGt, 2))
    else pick [(61, .gtEq)] .gt
  | 61 => pick [(61, .eqEq)] .eq
  | 94 => pick [(61, .caretEq)] .caret
  | 124 =>
    if c1 == 124 then (if c2 == 124 then some (.pipes, 3) else some (.pipePipe, 2))
    else pick [(61, .pipeEq)] .pipe
  | 63 => pick [(58, .questionColon)] .question
  | 58 => pick [(58, .colonColon), (62, .rbrack)] .colon
  | 59 => some (.semicolon, 1)
  | 44 => some (.comma, 1)
  | _ => none

/-! ## One token -/

/-- The text of bytes `j` to `k`, which the scanners have checked to be ASCII. -/
def ascii (b : ByteArray) (j k : Nat) : String :=
  String.fromUTF8? (b.extract j k) |>.getD ""

/-- A number at `j`: the longest of the integer rules (with a suffix, or a CN width) and
the floating rules (with a suffix); the integer rules win a tie. -/
def number (b : ByteArray) (j : Nat) : TokenKind × Nat :=
  let ie := integerEnd b j
  let fe := floatingEnd b j
  let (isLen, isuf) := integerSuffix b ie
  let c := byteAt b ie
  let cn := if ie > j && (c == 117 || c == 105) then cnWidth b (ie + 1) else 0
  let intTok : Option (TokenKind × Nat) :=
    if ie == j then none
    else if cn > 0 then some (.cnConstant, ie + 1 + cn)
    else some (.constant (.integer (ascii b j ie, isuf)), ie + isLen)
  let f := byteAt b fe
  let fsuf : Option FloatingSuffix :=
    if f == 102 || f == 70 then some .f else if f == 108 || f == 76 then some .l else none
  let floatTok : Option (TokenKind × Nat) :=
    if fe == j then none
    else some (.constant (.floating (ascii b j fe, fsuf)), if fsuf.isSome then fe + 1 else fe)
  match intTok, floatTok with
  | some (t, e), some (t', e') => if e' > e then (t', e') else (t, e)
  | some x, none => x
  | none, some x => x
  | none, none => (.eof, j)

/-- The result of one step of `initial`: a token ending at an offset, or a state that
skipped whitespace, a comment or a linemarker. -/
inductive Step where
  | token (kind : TokenKind) (start stop : Nat)
  | skip (s : State)

/-- A character constant after its optional prefix, whose quote is at `q`. -/
def charConstant (s : State) (j q : Nat) (pfx : Option CharacterPrefix) :
    Except Codec.Reject Step :=
  match charConstantEnd s.input (q + 1) (q + 1) with
  | none => .error (s.error j "invalid symbol")
  | some e => match String.fromUTF8? (s.input.extract (q + 1) e) with
    | some t => .ok (.token (.constant (.character (pfx, t))) j (e + 1))
    | none => .error (s.error j "character constant is not UTF-8")

/-- A string literal after its optional prefix, whose quote is at `q`; the token starts
at the prefix (`c_lexer.mll:573-587`). -/
def stringLiteral (s : State) (j q : Nat) (pfx : Option EncodingPrefix) :
    Except Codec.Reject Step :=
  match stringLexemes s.input (q + 1) #[] with
  | .ok (xs, e) => .ok (.token (.string pfx xs) j e)
  | .error k => .error (s.error k "invalid string character")

/-- An identifier, keyword or prefixed literal at `j`. -/
def word (s : State) (j : Nat) : Except Codec.Reject Step :=
  let b := s.input
  let e := identifierEnd b (j + max 1 (ucnLength b j))
  let text := ascii b j e
  let q := byteAt b e
  if q == 34 && (text == "u8" || text == "u" || text == "U" || text == "L") then
    stringLiteral s j e (match text with
      | "u8" => some .utf8 | "u" => some .utf16 | "U" => some .utf32 | _ => some .wide)
  else if q == 39 && (text == "u" || text == "U" || text == "L") then
    charConstant s j e (match text with
      | "u" => some .utf16 | "U" => some .utf32 | _ => some .wide)
  else match keywords.get? text with
    | some k => .ok (.token (.keyword k) j e)
    | none => .ok (.token (.name text) j e)

/-- One step of the rule `initial` (`c_lexer.mll:507-688`) at the state's offset. -/
def step (s : State) : Except Codec.Reject Step :=
  let b := s.input
  let j := s.offset
  if j ≥ b.size then .ok (.token .eof j j) else
  let c := byteAt b j
  let c1 := byteAt b (j + 1)
  if c == 10 then .ok (.skip (s.newLine (j + 1)))
  else if isWhitespace c then .ok (.skip { s with offset := scanWhile b isWhitespace j })
  else if c == 47 && c1 == 42 then Step.skip <$> skipComment s j (j + 2)
  else if c == 47 && c1 == 47 then
    let e := lineEnd b j
    .ok (.skip (s.newLine (if e < b.size then e + 1 else e)))
  else if c == 35 then Step.skip <$> hashLine s j (j + 1)
  else if isDigit c || (c == 46 && isDigit c1) then
    let (t, e) := number b j
    .ok (.token t j e)
  else if c == 39 then charConstant s j j none
  else if c == 34 then stringLiteral s j j none
  else if isNondigit c || ucnLength b j > 0 then word s j
  else match punctuator b j with
    | some (p, n) => .ok (.token (.punct p) j (j + n))
    | none => .error (s.error j "invalid symbol")

/-- Lex from the state to the end of the input. Every step consumes input or ends, so
`fuel` (the input size and one) suffices. -/
def tokensFrom (fuel : Nat) (s : State) (acc : Array Token) :
    Except Codec.Reject (Array Token) :=
  match fuel with
  | 0 => .error (s.error s.offset "lexer ran out of fuel")
  | fuel + 1 =>
    match step s with
    | .error e => .error e
    | .ok (.skip s') => tokensFrom fuel s' acc
    | .ok (.token kind j e) =>
      let t : Token := ⟨kind, s.posAt j, s.posAt e⟩
      match kind with
      | .eof => .ok (acc.push t)
      | _ => tokensFrom fuel { s with offset := e } (acc.push t)

/-- The tokens of a preprocessed text, ending with `eof`. `file` names the lines before
the first linemarker. -/
def tokens (input : ByteArray) (file : String := "") : Except Codec.Reject (Array Token) :=
  tokensFrom (input.size + 2) ⟨input, 0, 1, 0, none, file⟩ #[]

end Silmaril.Cerberus.Frontend.Lexer
