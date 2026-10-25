module

public import Silmaril.Logic.Metamath.Text.Ast

@[expose] public section

/-!
# Metamath lexer

The lexical layer of the Metamath specification (Megill and Wheeler,
*Metamath*, 2nd ed., §4.1.1–4.1.2). A source file may contain only the 94
printable non-whitespace ASCII characters and the white space characters
space, tab, line feed, form feed and carriage return. Tokens are the maximal
runs of non-whitespace characters. A token containing `$` must be one of the
keywords; every other token is a math symbol (labels are the math symbols
made of letters, digits, `-`, `_` and `.`).

The comment keyword `$(` starts a comment that runs to the next `$)`. As the
specification requires, the comment text may not contain the two-character
sequences `$(` or `$)` (comments do not nest), and the closing `$)` must be a
token of its own, surrounded by white space. This is the behaviour of
`metamath-exe`, which rejects `$( a$) $)` and `$( a $)b` as well as nested
comments. A comment token keeps its exact raw text between the delimiters,
including the surrounding white space.

The lexer is a character automaton `stepChar`. Lexing a character list is a
left fold of it, and lexing a `String` folds the string directly, without
building its character list; `lex_eq_lexChars` identifies the two.
-/

namespace Silmaril.Logic.Metamath.Text

/-- Metamath white space: space, tab, line feed, form feed and carriage return. -/
def isWs (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\x0c' || c == '\r'

/-- The 94 printable non-whitespace ASCII characters. -/
def isPrintable (c : Char) : Bool := 33 ≤ c.toNat && c.toNat ≤ 126

/-- The characters allowed in a Metamath source file. -/
def isAllowed (c : Char) : Bool := isPrintable c || isWs c

/-- The characters of a label: letters, digits, `-`, `_` and `.`. -/
def isLabelChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_' || c == '.'

/-- A math symbol: a nonempty string of printable characters other than `$`. -/
def isMathSymbol (s : String) : Bool :=
  !s.toList.isEmpty && s.toList.all fun c => isPrintable c && c != '$'

/-- A label: a nonempty string of label characters. -/
def isLabel (s : String) : Bool := !s.toList.isEmpty && s.toList.all isLabelChar

/-- A character list has no `$(` or `$)` substring. -/
def noCommentDelim : List Char → Bool
  | [] => true
  | a :: l =>
    (match l with
      | b :: _ => a != '$' || (b != '(' && b != ')')
      | [] => true) && noCommentDelim l

/-- The raw text of a comment between `$(` and `$)`: allowed characters,
beginning and ending with white space, with no `$(` or `$)` inside. -/
def isCommentText (s : String) : Bool :=
  s.toList.head?.any isWs && s.toList.reverse.head?.any isWs && s.toList.all isAllowed &&
    noCommentDelim s.toList

/-- The keywords other than the comment delimiters. -/
inductive Keyword where
  /-- `$c` -/
  | c
  /-- `$v` -/
  | v
  /-- `$f` -/
  | f
  /-- `$e` -/
  | e
  /-- `$d` -/
  | d
  /-- `$a` -/
  | a
  /-- `$p` -/
  | p
  /-- `$=` -/
  | eq
  /-- `$.` -/
  | stop
  /-- `${` -/
  | openScope
  /-- `$}` -/
  | closeScope
  /-- `$[` -/
  | openInclude
  /-- `$]` -/
  | closeInclude
  deriving DecidableEq, Repr, Inhabited

namespace Keyword

/-- The character following `$` in the keyword. -/
def char : Keyword → Char
  | c => 'c' | v => 'v' | f => 'f' | e => 'e' | d => 'd' | a => 'a' | p => 'p'
  | eq => '=' | stop => '.' | openScope => '{' | closeScope => '}'
  | openInclude => '[' | closeInclude => ']'

/-- The keyword `$x` for the character `x`. -/
def ofChar? : Char → Option Keyword
  | 'c' => some c | 'v' => some v | 'f' => some f | 'e' => some e | 'd' => some d
  | 'a' => some a | 'p' => some p | '=' => some eq | '.' => some stop
  | '{' => some openScope | '}' => some closeScope
  | '[' => some openInclude | ']' => some closeInclude
  | _ => none

/-- The keyword's text. -/
def toString (k : Keyword) : String := String.ofList ['$', k.char]

instance : ToString Keyword := ⟨toString⟩

@[simp] theorem ofChar?_char (k : Keyword) : ofChar? k.char = some k := by cases k <;> rfl

theorem char_ofChar? {x : Char} {k : Keyword} (h : ofChar? x = some k) : k.char = x := by
  unfold ofChar? at h
  split at h <;> first | (cases h; rfl) | cases h

@[simp] theorem char_ne_open (k : Keyword) : k.char ≠ '(' := by cases k <;> decide

@[simp] theorem char_ne_close (k : Keyword) : k.char ≠ ')' := by cases k <;> decide

@[simp] theorem isPrintable_char (k : Keyword) : isPrintable k.char := by cases k <;> decide

end Keyword

/-- A token: a keyword, a math symbol (which may be a label), or a comment with
its raw text. -/
inductive Token where
  | kw (k : Keyword)
  | sym (s : String)
  | comment (text : String)
  deriving DecidableEq, Repr, Inhabited

namespace Token

/-- The characters of a token as it appears in the source. -/
def chars : Token → List Char
  | kw k => ['$', k.char]
  | sym s => s.toList
  | comment t => '$' :: '(' :: t.toList ++ ['$', ')']

/-- The text of a token as it appears in the source. -/
def print : Token → String
  | kw k => k.toString
  | sym s => s
  | comment t => "$(" ++ t ++ "$)"

@[simp] theorem toList_print (t : Token) : t.print.toList = t.chars := by
  cases t <;> simp [print, chars, Keyword.toString]

/-- A token is well formed: math symbols are nonempty and `$`-free, comment
text is valid comment text. -/
def valid : Token → Bool
  | kw _ => true
  | sym s => isMathSymbol s
  | comment t => isCommentText t

end Token

/-- A lexical error, with the line number where it occurs. -/
inductive LexError where
  /-- A character outside printable ASCII and Metamath white space. -/
  | badChar (line : Nat) (c : Char)
  /-- A token containing `$` that is not a keyword. -/
  | badDollar (line : Nat) (tok : String)
  /-- A `$)` outside a comment. -/
  | strayCommentEnd (line : Nat)
  /-- A `$(` inside a comment. -/
  | nestedComment (line : Nat)
  /-- A `$)` inside a comment that is not surrounded by white space. -/
  | badCommentEnd (line : Nat)
  /-- A comment still open at the end of the file. -/
  | unterminatedComment
  deriving DecidableEq, Repr, Inhabited

/-- The state of the lexer automaton between two characters. The character
accumulators are reversed. -/
inductive LexMode where
  /-- Between tokens. -/
  | ws
  /-- Inside a token whose characters so far are `acc`. -/
  | word (acc : List Char)
  /-- Inside a comment whose text so far is `acc`, not ending in `$`; `prevWs`
  records whether the last character is white space. -/
  | cmt (acc : List Char) (prevWs : Bool)
  /-- Inside a comment whose text so far is `acc`, ending in `$`; `wsBefore`
  records whether the character before that `$` is white space. -/
  | cmtDollar (acc : List Char) (wsBefore : Bool)
  /-- Just after the `$)` closing a comment with text `acc`. -/
  | cmtEnd (acc : List Char)
  deriving DecidableEq, Repr, Inhabited

/-- The lexer state: tokens so far (reversed), the mode and the current line. -/
structure LexState where
  toks : List Token
  mode : LexMode
  line : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The initial lexer state. -/
def LexState.init : LexState := ⟨[], .ws, 1⟩

/-- Classify a complete token other than `$(`. -/
def wordToken (line : Nat) : List Char → Except LexError Token
  | ['$', x] =>
    match Keyword.ofChar? x with
    | some k => .ok (.kw k)
    | none =>
      if x = ')' then .error (.strayCommentEnd line)
      else .error (.badDollar line (String.ofList ['$', x]))
  | w =>
    if '$' ∈ w then .error (.badDollar line (String.ofList w)) else .ok (.sym (String.ofList w))

/-- One step of the lexer automaton. -/
def stepChar (st : LexState) (c : Char) : Except LexError LexState :=
  if !isAllowed c then .error (.badChar st.line c) else
  let line := if c = '\n' then st.line + 1 else st.line
  match st.mode with
  | .ws => .ok ⟨st.toks, if isWs c then .ws else .word [c], line⟩
  | .word acc =>
    if isWs c then
      if acc = ['(', '$'] then .ok ⟨st.toks, .cmt [c] true, line⟩
      else (wordToken st.line acc.reverse).map fun t => ⟨t :: st.toks, .ws, line⟩
    else .ok ⟨st.toks, .word (c :: acc), line⟩
  | .cmt acc prevWs =>
    .ok ⟨st.toks, if c = '$' then .cmtDollar (c :: acc) prevWs else .cmt (c :: acc) (isWs c), line⟩
  | .cmtDollar acc wsBefore =>
    if c = '(' then .error (.nestedComment st.line)
    else if c = ')' then
      if wsBefore then .ok ⟨st.toks, .cmtEnd acc.tail, line⟩
      else .error (.badCommentEnd st.line)
    else
      .ok ⟨st.toks, if c = '$' then .cmtDollar (c :: acc) false else .cmt (c :: acc) (isWs c),
        line⟩
  | .cmtEnd acc =>
    if isWs c then .ok ⟨.comment (String.ofList acc.reverse) :: st.toks, .ws, line⟩
    else .error (.badCommentEnd st.line)

/-- The lexer step on a possibly failed state. -/
def lexStep (st : Except LexError LexState) (c : Char) : Except LexError LexState :=
  st.bind (stepChar · c)

/-- End of input: flush the last token. -/
def LexState.finish (st : LexState) : Except LexError (List Token) :=
  match st.mode with
  | .ws => .ok st.toks.reverse
  | .word acc =>
    if acc = ['(', '$'] then .error .unterminatedComment
    else (wordToken st.line acc.reverse).map fun t => (t :: st.toks).reverse
  | .cmt .. | .cmtDollar .. => .error .unterminatedComment
  | .cmtEnd acc => .ok (.comment (String.ofList acc.reverse) :: st.toks).reverse

/-- Tokenize a character list. -/
def lexChars (l : List Char) : Except LexError (List Token) :=
  (l.foldl lexStep (.ok .init)).bind LexState.finish

/-- Tokenize a string. -/
def lex (s : String) : Except LexError (List Token) :=
  (s.foldl lexStep (.ok .init)).bind LexState.finish

theorem lex_eq_lexChars (s : String) : lex s = lexChars s.toList := by
  simp [lex, lexChars]

end Silmaril.Logic.Metamath.Text
