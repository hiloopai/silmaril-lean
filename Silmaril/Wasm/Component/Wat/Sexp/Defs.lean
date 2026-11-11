module

public import Init

/-!
# S-expressions of the WebAssembly text format: reader and printer

The concrete S-expression layer of component WAT (the component-model text
format, `design/mvp/Explainer.md` of WebAssembly/component-model, and the core
text format's lexical conventions, core spec §6.3).

* `Sexp`: atoms (keywords, numbers, identifiers: maximal runs of `idchar`s),
  string literals (their *bytes*) and lists. Annotations `(@id …)` are kept as
  ordinary lists whose head atom starts with `@` (as the Wasm 1.0 lexer
  reads them); this is how `(@custom "name" "data")` carries custom sections.
* `lex : List Char → Option (List Tok)`: whitespace, line comments `;; …` and
  nested block comments `(; … ;)` are skipped; string literals take the
  escapes `\t \n \r \" \' \\ \hh`; other characters stand for their UTF-8
  bytes.
* `parseSeq`: tokens to trees; `read : String → Option (List Sexp)`.
* `pp`: a printer with a simple layout (a list goes on one line when it fits in
  `width` columns, otherwise its children go on indented lines, consecutive
  atoms and strings staying on one line); strings are
  printed with printable ASCII verbatim and every other byte as `\hh`.
  `print s = pp false 0 s`.

The round trip `read (print s) = some [s]` for well-formed `s` (`Sexp.WF`:
atoms are non-empty runs of `idchar`s) is
`Silmaril.Wasm.Component.Wat.Sexp.read_print`.

## Deviations from the WAT lexer

The reader accepts a superset of WAT's lexical syntax: it does not insist on
the longest-match separation between atoms and strings (`a"b"` reads as two
tokens where WAT reserves it), it does not treat `\u{…}` escapes (rejected),
and annotations are not whitespace. Every text the printer produces is
lexically valid WAT.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Wat

/-- S-expressions: atoms, string literals (bytes) and lists. -/
inductive Sexp where
  | atom (s : String)
  | str (bs : List UInt8)
  | list (xs : List Sexp)
  deriving Repr, Inhabited

/-- Tokens. -/
inductive Tok where
  | lp
  | rp
  | atom (s : String)
  | str (bs : List UInt8)
  deriving Repr, DecidableEq, Inhabited

namespace Sexp

/-! ## Characters -/

/-- The punctuation `idchar`s of WAT (besides ASCII letters and digits). -/
def idPunct : List Char :=
  ['!', '#', '$', '%', '&', '\'', '*', '+', '-', '.', '/', ':', '<', '=', '>', '?', '@',
   '\\', '^', '_', '`', '|', '~']

/-- `idchar`: the characters of atoms. -/
def isIdChar (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || idPunct.contains c

/-- Whitespace characters. -/
def isSpace (c : Char) : Bool := c = ' ' || c = '\t' || c = '\n' || c = '\r'

/-- The value of a hexadecimal digit. -/
def hexVal? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- The lowercase hexadecimal digit of `n < 16`. -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

/-! ## Lexer -/

/-- Skip a line comment: everything up to and including a newline. -/
def skipLine : List Char → List Char
  | [] => []
  | '\n' :: cs => cs
  | _ :: cs => skipLine cs

/-- Skip the rest of a block comment, `d` nested comments deep. -/
def skipBlock : Nat → List Char → Option (List Char)
  | _, [] => none
  | 0, ';' :: ')' :: cs => some cs
  | d + 1, ';' :: ')' :: cs => skipBlock d cs
  | d, '(' :: ';' :: cs => skipBlock (d + 1) cs
  | d, _ :: cs => skipBlock d cs

/-- The UTF-8 bytes standing for a literal character in a string. -/
def charBytes (c : Char) : List UInt8 :=
  if c.toNat < 0x80 then [c.toNat.toUInt8] else (String.singleton c).toUTF8.toList

/-- The body of a string literal after the opening quote: its bytes and the
characters after the closing quote. -/
def lexStr : List Char → Option (List UInt8 × List Char)
  | [] => none
  | '"' :: cs => some ([], cs)
  | '\\' :: 't' :: cs => (lexStr cs).map fun p => (9 :: p.1, p.2)
  | '\\' :: 'n' :: cs => (lexStr cs).map fun p => (10 :: p.1, p.2)
  | '\\' :: 'r' :: cs => (lexStr cs).map fun p => (13 :: p.1, p.2)
  | '\\' :: '"' :: cs => (lexStr cs).map fun p => (34 :: p.1, p.2)
  | '\\' :: '\'' :: cs => (lexStr cs).map fun p => (39 :: p.1, p.2)
  | '\\' :: '\\' :: cs => (lexStr cs).map fun p => (92 :: p.1, p.2)
  | '\\' :: h :: l :: cs =>
    match hexVal? h, hexVal? l with
    | some a, some b => (lexStr cs).map fun p => ((16 * a + b).toUInt8 :: p.1, p.2)
    | _, _ => none
  | '\\' :: _ => none
  | c :: cs => if c.toNat < 0x20 ∨ c.toNat = 0x7f then none
      else (lexStr cs).map fun p => (charBytes c ++ p.1, p.2)

theorem skipLine_length_le (cs : List Char) : (skipLine cs).length ≤ cs.length := by
  fun_induction skipLine cs <;> simp <;> omega

theorem skipBlock_length_le (d : Nat) (cs : List Char) : ∀ r, skipBlock d cs = some r →
    r.length ≤ cs.length := by
  fun_induction skipBlock d cs <;> intro r h <;> simp_all <;> omega

theorem lexStr_length_le' (cs : List Char) : ∀ p, lexStr cs = some p → p.2.length ≤ cs.length := by
  fun_induction lexStr cs <;> intro p h
  all_goals first
    | (simp at h; done)
    | (simp at h; subst h; simp)
    | (rename_i ih
       rcases hc : lexStr _ with _ | q <;> rw [hc] at h <;> simp at h
       subst h; have := ih q hc; simp; omega)
    | (simp_all)

theorem lexStr_length_le (cs : List Char) (bs : List UInt8) (r : List Char)
    (h : lexStr cs = some (bs, r)) : r.length ≤ cs.length := lexStr_length_le' cs _ h

theorem dropWhile_length_le (p : Char → Bool) : ∀ l : List Char, (l.dropWhile p).length ≤ l.length
  | [] => by simp
  | c :: l => by
    rw [List.dropWhile_cons]; split
    · have := dropWhile_length_le p l; simp; omega
    · simp

/-- The lexer. -/
def lex (cs : List Char) : Option (List Tok) :=
  match cs with
  | [] => some []
  | ';' :: ';' :: r => lex (skipLine r)
  | '(' :: ';' :: r =>
    match h : skipBlock 0 r with
    | none => none
    | some r' =>
      have := skipBlock_length_le 0 r r' h
      lex r'
  | '(' :: r => (Tok.lp :: ·) <$> lex r
  | ')' :: r => (Tok.rp :: ·) <$> lex r
  | '"' :: r =>
    match h : lexStr r with
    | none => none
    | some (bs, r') =>
      have := lexStr_length_le r bs r' h
      (Tok.str bs :: ·) <$> lex r'
  | c :: r =>
    if isSpace c then lex r
    else if isIdChar c then
      have := dropWhile_length_le isIdChar r
      (Tok.atom (String.ofList (c :: r.takeWhile isIdChar)) :: ·) <$> lex (r.dropWhile isIdChar)
    else none
termination_by cs.length
decreasing_by all_goals (have := skipLine_length_le r; simp_all; try omega)

/-! ## Trees -/

/-- Parse a sequence of trees, stopping before a `)` or at the end. -/
def parseSeq : Nat → List Tok → Option (List Sexp × List Tok)
  | 0, _ => none
  | _ + 1, [] => some ([], [])
  | _ + 1, .rp :: ts => some ([], .rp :: ts)
  | n + 1, .atom a :: ts => (parseSeq n ts).map fun p => (.atom a :: p.1, p.2)
  | n + 1, .str b :: ts => (parseSeq n ts).map fun p => (.str b :: p.1, p.2)
  | n + 1, .lp :: ts =>
    match parseSeq n ts with
    | some (xs, .rp :: r) => (parseSeq n r).map fun p => (.list xs :: p.1, p.2)
    | _ => none

/-- Parse a whole token list. -/
def parseTop (ts : List Tok) : Option (List Sexp) :=
  match parseSeq (ts.length + 1) ts with
  | some (xs, []) => some xs
  | _ => none

/-- Read a text as a sequence of S-expressions. -/
def read (s : String) : Option (List Sexp) := lex s.toList >>= parseTop

/-! ## Printer -/

/-- The tokens of an S-expression. -/
def toks : Sexp → List Tok
  | .atom a => [.atom a]
  | .str b => [.str b]
  | .list xs => .lp :: (toksL xs ++ [.rp])
where
  toksL : List Sexp → List Tok
    | [] => []
    | x :: xs => toks x ++ toksL xs

/-- A byte inside a string literal. -/
def escByte (b : UInt8) : List Char :=
  if 0x20 ≤ b.toNat ∧ b.toNat < 0x7f ∧ b.toNat ≠ 0x22 ∧ b.toNat ≠ 0x5c then [Char.ofNat b.toNat]
  else ['\\', hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

/-- A string literal. -/
def quote (bs : List UInt8) : List Char := '"' :: (bs.flatMap escByte ++ ['"'])

/-- The line width of the layout. -/
def width : Nat := 100

/-- `n` spaces. -/
def spaces (n : Nat) : List Char := List.replicate n ' '

/-- Atoms and strings. -/
def isLeaf : Sexp → Bool
  | .list _ => false
  | _ => true

/-- The separator of two children of a list printed on several lines: a space
between leaves, a new indented line otherwise. -/
def breakSep (ind : Nat) (x y : Sexp) : List Char :=
  if isLeaf x && isLeaf y then [' '] else '\n' :: spaces ind

mutual
/-- Print `s` at indentation `ind`; `flat` forces a single line. -/
def pp (flat : Bool) (ind : Nat) : Sexp → List Char
  | .atom a => a.toList
  | .str b => quote b
  | .list xs =>
    let one := '(' :: (ppL true (fun _ _ => [' ']) 0 xs ++ [')'])
    if flat || ind + one.length ≤ width then one
    else '(' :: (ppL false (breakSep (ind + 2)) (ind + 2) xs ++ [')'])

/-- Print the children of a list, separated by `sep`. -/
def ppL (flat : Bool) (sep : Sexp → Sexp → List Char) (ind : Nat) : List Sexp → List Char
  | [] => []
  | [x] => pp flat ind x
  | x :: y :: xs => pp flat ind x ++ sep x y ++ ppL flat sep ind (y :: xs)
end

/-- Print an S-expression. -/
def print (s : Sexp) : String := String.ofList (pp false 0 s)

/-- Print a sequence of S-expressions, one per line. -/
def printAll (ss : List Sexp) : String :=
  String.ofList (ss.flatMap fun s => pp false 0 s ++ ['\n'])

/-! ## Well-formedness -/

/-- An atom the printer can print: a non-empty run of `idchar`s. -/
def AtomOk (a : String) : Prop := a.toList ≠ [] ∧ ∀ c ∈ a.toList, isIdChar c = true

instance (a : String) : Decidable (AtomOk a) := inferInstanceAs (Decidable (_ ∧ _))

mutual
/-- Every atom is printable. -/
def WF : Sexp → Prop
  | .atom a => AtomOk a
  | .str _ => True
  | .list xs => WFL xs

/-- `WF` of every element. -/
def WFL : List Sexp → Prop
  | [] => True
  | x :: xs => WF x ∧ WFL xs
end

end Sexp

end Silmaril.Wasm.Component.Wat
