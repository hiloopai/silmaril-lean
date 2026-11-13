module

public import Silmaril.Wasm.Wac.Text.Ast.Defs

/-!
# WAC text: tokens, lexer and layout

The lexical layer of WAC, following the `logos` lexer of `wac-parser` 0.12.0
(bytecodealliance/wac `5a7480c69ae7a4dc9eb161f485cbcb8c95e372c9`,
`crates/wac-parser/src/lexer.rs`):

* `Tok`: identifiers (`id`, without the `%` escape), keywords (`kw`), string literals
  (`str`, the characters between the quotes; no escapes), package names
  `ns:name@version` (`pname`) and package paths `ns:name/a/b@version` (`ppath`), both
  with the source text of the name, the segments and the version, the symbols
  `; { } : = ( ) < > _ [ ] . , / @` (`sym`), `->` (`arrow`) and `...` (`ellipsis`).
* Longest match, as `logos`: a word that continues with `:id` is a package name, with
  `/id` after that a package path, and `@` followed by a digit adds a version
  (`[0-9]+(\.[0-9a-zA-Z+-]+)*`). A word that is a keyword is a keyword unless it is
  written with `%`.
* Identifiers are `%?word(-word)*` with `word = [a-z][a-z0-9]* | [A-Z][A-Z0-9]*`.
* Whitespace (space, tab, `\n`, `\r`, form feed), line comments `// …` and nested block
  comments `/* … */` are skipped. Doc comments (`wac-parser`'s `Lexer::comments`) are
  the line comments starting with `///` and the block comments starting with `/**`
  (except `/**/`), with the marker (and `*/`) removed and the text trimmed; the lexer
  attaches the doc comments before a token to it (`ATok`), and the parser reads them
  where an item may have docs and ignores them elsewhere.
* `inputOk`: like `detect_invalid_input`, control characters other than tab, line feed
  and carriage return, the bidirectional overrides and eight discouraged code points
  are rejected anywhere in the input.

Deviations: `Lexer::comments` stops at a carriage return between doc comments (its
whitespace class lacks `\r`); here `\r` is whitespace everywhere. Errors are reported
as `none`, without positions.

The printer side: `Tok.chars` spells a token, `render` lays out tokens with docs, with
any whitespace between tokens (`lex_render` in `Silmaril.Wasm.Wac.Text.Thms`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.Text

/-- The keywords of `wac-parser` 0.12.0. -/
inductive Kw where
  | «import» | «with» | «type» | «tuple» | «list» | «option» | «result» | «borrow»
  | «resource» | «variant» | «record» | «flags» | «enum» | «func» | «static» | ctor
  | «u8» | «s8» | «u16» | «s16» | «u32» | «s32» | «u64» | «s64» | «f32» | «f64»
  | «char» | «bool» | «string» | «interface» | «world» | «export» | «new» | «let»
  | «use» | «include» | «as» | «package» | «targets» | «async» | «stream» | «future»
  | errorContext
  deriving Repr, DecidableEq, Inhabited

/-- The spelling of a keyword. -/
def Kw.name : Kw → String
  | .«import» => "import" | .«with» => "with" | .«type» => "type" | .«tuple» => "tuple"
  | .«list» => "list" | .«option» => "option" | .«result» => "result"
  | .«borrow» => "borrow" | .«resource» => "resource" | .«variant» => "variant"
  | .«record» => "record" | .«flags» => "flags" | .«enum» => "enum" | .«func» => "func"
  | .«static» => "static" | .ctor => "constructor" | .«u8» => "u8" | .«s8» => "s8"
  | .«u16» => "u16" | .«s16» => "s16" | .«u32» => "u32" | .«s32» => "s32"
  | .«u64» => "u64" | .«s64» => "s64" | .«f32» => "f32" | .«f64» => "f64"
  | .«char» => "char" | .«bool» => "bool" | .«string» => "string"
  | .«interface» => "interface" | .«world» => "world" | .«export» => "export"
  | .«new» => "new" | .«let» => "let" | .«use» => "use" | .«include» => "include"
  | .«as» => "as" | .«package» => "package" | .«targets» => "targets"
  | .«async» => "async" | .«stream» => "stream" | .«future» => "future"
  | .errorContext => "error-context"

/-- Every keyword. -/
def Kw.all : List Kw :=
  [.«import», .«with», .«type», .«tuple», .«list», .«option», .«result», .«borrow»,
   .«resource», .«variant», .«record», .«flags», .«enum», .«func», .«static», .ctor,
   .«u8», .«s8», .«u16», .«s16», .«u32», .«s32», .«u64», .«s64», .«f32», .«f64»,
   .«char», .«bool», .«string», .«interface», .«world», .«export», .«new», .«let»,
   .«use», .«include», .«as», .«package», .«targets», .«async», .«stream», .«future»,
   .errorContext]

/-- The keyword a word spells, if any. -/
def kwOf? (s : String) : Option Kw := Kw.all.find? (·.name == s)

/-- Tokens. -/
inductive Tok where
  /-- An identifier, without its `%` escape. -/
  | id (s : String)
  /-- A keyword. -/
  | kw (k : Kw)
  /-- A string literal: the characters between the quotes. -/
  | str (s : String)
  /-- A package name `name@ver` (`name` is the source text `ns:name`). -/
  | pname (name : String) (ver : Option String)
  /-- A package path `name/segs@ver`. -/
  | ppath (name : String) (segs : String) (ver : Option String)
  /-- One of `; { } : = ( ) < > _ [ ] . , / @`. -/
  | sym (c : Char)
  /-- `->`. -/
  | arrow
  /-- `...`. -/
  | ellipsis
  deriving Repr, DecidableEq, Inhabited

/-- A token with the doc comments before it. -/
structure ATok where
  docs : Docs
  tok : Tok
  deriving Repr, DecidableEq, Inhabited

/-! ## Characters -/

/-- `[a-z]`. -/
def isLower (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'
/-- `[A-Z]`. -/
def isUpper (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'
/-- `[0-9]`. -/
def isDigitC (c : Char) : Bool := '0' ≤ c && c ≤ '9'
/-- The first character of a word. -/
def isLetter (c : Char) : Bool := isLower c || isUpper c

/-- The characters after the first of a word: `[a-z0-9]` after a lower-case letter,
`[A-Z0-9]` after an upper-case one. -/
def wordCont (up : Bool) (c : Char) : Bool := (if up then isUpper c else isLower c) || isDigitC c

/-- The characters of a version after a `.`: `[0-9a-zA-Z+-]`. -/
def verCont (c : Char) : Bool := isLetter c || isDigitC c || c == '-' || c == '+'

/-- Whitespace between tokens (`[ \t\r\n\f]`). -/
def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'

/-- Unicode `White_Space` (what Rust's `str::trim` removes). -/
def isWsU (c : Char) : Bool :=
  let n := c.toNat
  (9 ≤ n && n ≤ 13) || n == 32 || n == 0x85 || n == 0xa0 || n == 0x1680 ||
  (0x2000 ≤ n && n ≤ 0x200a) || n == 0x2028 || n == 0x2029 || n == 0x202f ||
  n == 0x205f || n == 0x3000

/-- Characters `wac-parser` rejects anywhere (`detect_invalid_input`): control codes
other than tab, line feed and carriage return; bidirectional overrides; eight deprecated
or discouraged code points. -/
def badChar (c : Char) : Bool :=
  let n := c.toNat
  (n < 0x20 && c != '\t' && c != '\n' && c != '\r') || (0x7f ≤ n && n ≤ 0x9f) ||
  (0x202a ≤ n && n ≤ 0x202e) || (0x2066 ≤ n && n ≤ 0x2069) ||
  n == 0x149 || n == 0x673 || n == 0xf77 || n == 0xf79 ||
  (0x17a3 ≤ n && n ≤ 0x17a4) || (0x17b4 ≤ n && n ≤ 0x17b5)

/-- The input has no rejected character. -/
def inputOk (cs : List Char) : Bool := !cs.any badChar

/-- Trim Unicode whitespace on both sides. -/
def trimU (cs : List Char) : List Char :=
  ((cs.dropWhile isWsU).reverse.dropWhile isWsU).reverse

/-- The one-character symbols. -/
def symChars : List Char := [';', '{', '}', ':', '=', '(', ')', '<', '>', '_', '[', ']', '.', ',', '/', '@']

/-! ## Scanning -/

/-- Split off the longest prefix satisfying `p`. -/
def spanL (p : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: r => if p c then (c :: (spanL p r).1, (spanL p r).2) else ([], c :: r)

theorem spanL_length_le (p : Char → Bool) (cs : List Char) :
    (spanL p cs).2.length ≤ cs.length := by
  fun_induction spanL p cs <;> simp_all <;> omega

/-- The words of an identifier body after its first word: `(-word)*`. -/
def idTail : List Char → List Char × List Char
  | '-' :: c :: r =>
    if isLetter c then
      ('-' :: c :: (spanL (wordCont (isUpper c)) r).1 ++ (idTail (spanL (wordCont (isUpper c)) r).2).1,
       (idTail (spanL (wordCont (isUpper c)) r).2).2)
    else ([], '-' :: c :: r)
  | cs => ([], cs)
termination_by cs => cs.length
decreasing_by all_goals (have := spanL_length_le (wordCont (isUpper c)) r; simp; omega)

theorem idTail_length_le (cs : List Char) : (idTail cs).2.length ≤ cs.length := by
  fun_induction idTail cs with
  | case1 c r h ih => have := spanL_length_le (wordCont (isUpper c)) r; simp; omega
  | case2 => simp
  | case3 => simp

/-- An identifier body `word(-word)*` (without `%`), if `cs` starts with a letter: its
characters and the rest. -/
def idBody : List Char → Option (List Char × List Char)
  | c :: r =>
    if isLetter c then
      some (c :: (spanL (wordCont (isUpper c)) r).1 ++ (idTail (spanL (wordCont (isUpper c)) r).2).1,
            (idTail (spanL (wordCont (isUpper c)) r).2).2)
    else none
  | [] => none

theorem idBody_lt {cs w r : List Char} (h : idBody cs = some (w, r)) :
    r.length < cs.length := by
  match cs with
  | [] => simp [idBody] at h
  | c :: t =>
    simp only [idBody] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      have h1 := idTail_length_le (spanL (wordCont (isUpper c)) t).2
      have h2 := spanL_length_le (wordCont (isUpper c)) t
      simp; omega
    · simp at h

/-- An identifier with its optional `%`, as source text. -/
def idRaw : List Char → Option (List Char × List Char)
  | '%' :: r => (idBody r).map fun p => ('%' :: p.1, p.2)
  | cs => idBody cs

theorem idRaw_lt {cs w r : List Char} (h : idRaw cs = some (w, r)) :
    r.length < cs.length := by
  unfold idRaw at h
  split at h
  · rename_i t
    cases hb : idBody t with
    | none => simp [hb] at h
    | some p =>
      simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      have := idBody_lt (cs := t) (w := p.1) (r := p.2) (by simp [hb])
      simp; omega
  · exact idBody_lt h

/-- `(sep id)*`, as source text: the `(:id)+` of a package name, the `(/id)+` of a
package path. -/
def sepIds (sep : Char) : List Char → List Char × List Char
  | c :: r =>
    if c = sep then
      match h : idRaw r with
      | some (w, r') =>
        have := idRaw_lt h
        (c :: w ++ (sepIds sep r').1, (sepIds sep r').2)
      | none => ([], c :: r)
    else ([], c :: r)
  | [] => ([], [])
termination_by cs => cs.length

theorem sepIds_length_le (sep : Char) (cs : List Char) :
    (sepIds sep cs).2.length ≤ cs.length := by
  fun_induction sepIds sep cs with
  | case1 => simp; omega
  | case2 => simp
  | case3 => simp
  | case4 => simp

/-- The rest of a version after its first digit: `[0-9]*(\.[0-9a-zA-Z+-]+)*`. -/
def verTail : List Char → List Char × List Char
  | '.' :: c :: r =>
    if verCont c then
      ('.' :: c :: (spanL verCont r).1 ++ (verTail (spanL verCont r).2).1,
       (verTail (spanL verCont r).2).2)
    else ([], '.' :: c :: r)
  | cs => ([], cs)
termination_by cs => cs.length
decreasing_by all_goals (have := spanL_length_le verCont r; simp; omega)

theorem verTail_length_le (cs : List Char) : (verTail cs).2.length ≤ cs.length := by
  fun_induction verTail cs with
  | case1 c r h ih => have := spanL_length_le verCont r; simp; omega
  | case2 => simp
  | case3 => simp

/-- An optional `@version` (`@` followed by a digit): the version text and the rest. -/
def atVer : List Char → Option (List Char) × List Char
  | '@' :: c :: r =>
    if isDigitC c then
      (some (c :: (spanL isDigitC r).1 ++ (verTail (spanL isDigitC r).2).1),
       (verTail (spanL isDigitC r).2).2)
    else (none, '@' :: c :: r)
  | cs => (none, cs)

theorem atVer_length_le (cs : List Char) : (atVer cs).2.length ≤ cs.length := by
  unfold atVer
  split
  · rename_i c r
    split
    · have := verTail_length_le (spanL isDigitC r).2
      have := spanL_length_le isDigitC r
      simp; omega
    · simp
  · simp

/-- The rest of a line and what follows its newline. -/
def takeLine : List Char → List Char × List Char
  | [] => ([], [])
  | '\n' :: r => ([], r)
  | c :: r => (c :: (takeLine r).1, (takeLine r).2)

theorem takeLine_length_le (cs : List Char) : (takeLine cs).2.length ≤ cs.length := by
  fun_induction takeLine cs <;> simp_all <;> omega

/-- The body of a block comment, `d` nested comments deep (after its `/*`): the
characters before the matching `*/`, and the rest. -/
def blockBody : Nat → List Char → Option (List Char × List Char)
  | _, [] => none
  | d, '*' :: '/' :: r =>
    match d with
    | 0 => some ([], r)
    | d + 1 => (blockBody d r).map fun p => ('*' :: '/' :: p.1, p.2)
  | d, '/' :: '*' :: r => (blockBody (d + 1) r).map fun p => ('/' :: '*' :: p.1, p.2)
  | d, c :: r => (blockBody d r).map fun p => (c :: p.1, p.2)

theorem blockBody_length_le (d : Nat) (cs : List Char) :
    ∀ b r, blockBody d cs = some (b, r) → r.length ≤ cs.length := by
  fun_induction blockBody d cs with
  | case1 => intro b r h; simp at h
  | case2 r => intro b r' h; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; simp; omega
  | case3 d r ih | case4 d r ih | case5 d c r _ _ ih =>
    intro b r' h
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨⟨p1, p2⟩, hp, -, rfl⟩ := h
    have := ih _ _ hp
    simp; omega

/-- The doc comment a line comment `//line` is: `///`-lines, trimmed. -/
def lineDoc : List Char → Option String
  | '/' :: l => some (String.ofList (trimU l))
  | _ => none

/-- The doc comment a block comment `/*body*/` is: `/**`-blocks other than `/**/`,
trimmed. -/
def blockDoc : List Char → Option String
  | '*' :: l => some (String.ofList (trimU l))
  | _ => none

/-- The token of a word: an identifier written with `%`, a keyword, or an identifier. -/
def wordTok (w : List Char) : Tok :=
  match w with
  | '%' :: s => .id (String.ofList s)
  | _ => match kwOf? (String.ofList w) with
    | some k => .kw k
    | none => .id (String.ofList w)

/-- The token at a word: an identifier or keyword, or (when `:id` follows) a package
name or path. -/
def nameTok (w cols segs : List Char) (ver : Option (List Char)) : Tok :=
  if cols = [] then wordTok w
  else if segs = [] then .pname (String.ofList (w ++ cols)) (ver.map String.ofList)
  else .ppath (String.ofList (w ++ cols)) (String.ofList segs.tail) (ver.map String.ofList)

/-- The lexer, after the doc comments `ds` that precede the next token. Doc comments at
the end of the input are dropped. -/
def lexAux (ds : Docs) (cs : List Char) : Option (List ATok) :=
  match cs with
  | [] => some []
  | '/' :: '/' :: r =>
    have := takeLine_length_le r
    lexAux (ds ++ (lineDoc (takeLine r).1).toList) (takeLine r).2
  | '/' :: '*' :: r =>
    match h : blockBody 0 r with
    | none => none
    | some (b, r') =>
      have := blockBody_length_le 0 r b r' h
      lexAux (ds ++ (blockDoc b).toList) r'
  | '.' :: '.' :: '.' :: r => (⟨ds, .ellipsis⟩ :: ·) <$> lexAux [] r
  | '-' :: '>' :: r => (⟨ds, .arrow⟩ :: ·) <$> lexAux [] r
  | '"' :: r =>
    have := spanL_length_le (· != '"') r
    match h : (spanL (· != '"') r).2 with
    | '"' :: r' =>
      have : r'.length < r.length + 1 := by rw [h] at this; simp at this; omega
      (⟨ds, .str (String.ofList (spanL (· != '"') r).1)⟩ :: ·) <$> lexAux [] r'
    | _ => none
  | c :: r =>
    if isWs c then lexAux ds r
    else if c = '%' ∨ isLetter c then
      match h : idRaw (c :: r) with
      | none => none
      | some (w, r1) =>
        have := idRaw_lt h
        have := sepIds_length_le ':' r1
        have := sepIds_length_le '/' (sepIds ':' r1).2
        have := atVer_length_le (sepIds '/' (sepIds ':' r1).2).2
        let cols := sepIds ':' r1
        if cols.1 = [] then
          (⟨ds, wordTok w⟩ :: ·) <$> lexAux [] r1
        else
          let segs := sepIds '/' cols.2
          let ver := atVer segs.2
          (⟨ds, nameTok w cols.1 segs.1 ver.1⟩ :: ·) <$> lexAux [] ver.2
    else if symChars.contains c then (⟨ds, .sym c⟩ :: ·) <$> lexAux [] r
    else none
termination_by cs.length
decreasing_by all_goals (simp_all; try omega)

/-- The lexer: tokens with their doc comments, or `none` on a lexical error. -/
def lex (cs : List Char) : Option (List ATok) :=
  if inputOk cs then lexAux [] cs else none

/-! ## Printing tokens -/

/-- The characters of a token (a keyword-named identifier gets its `%`). -/
def Tok.chars : Tok → List Char
  | .id s => if (kwOf? s).isSome then '%' :: s.toList else s.toList
  | .kw k => k.name.toList
  | .str s => '"' :: s.toList ++ ['"']
  | .pname n v => n.toList ++ (match v with | some v => '@' :: v.toList | none => [])
  | .ppath n s v =>
    n.toList ++ '/' :: s.toList ++ (match v with | some v => '@' :: v.toList | none => [])
  | .sym c => [c]
  | .arrow => ['-', '>']
  | .ellipsis => ['.', '.', '.']

/-- The characters of a doc comment line. -/
def docStr (d : String) : List Char := '/' :: '/' :: '/' :: ' ' :: d.toList ++ ['\n']

/-- Lay out tokens with their docs: each token's doc lines (each followed by the
indentation `ind i`), the token, and the separator `sep i` after the `i`-th token. -/
def renderWith (sep ind : Nat → List Char) : Nat → List ATok → List Char
  | _, [] => []
  | i, a :: rest =>
    a.docs.flatMap (fun d => docStr d ++ ind i) ++ a.tok.chars ++ sep i ++
      renderWith sep ind (i + 1) rest

/-- The plain layout: one space after every token. -/
def render (ts : List ATok) : List Char := renderWith (fun _ => [' ']) (fun _ => []) 0 ts

end Silmaril.Wasm.Wac.Text
