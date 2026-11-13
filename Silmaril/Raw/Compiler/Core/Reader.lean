module

public import Silmaril.Cerberus.Codec.WellFormed.Defs

/-! # A fast reader for Cerberus Core documents

`read` decodes a `cerb-oracle --level core` document like the checked codec
`Codec.WellFormed.parseDocument`, and is proved equal to it (`read_eq`).

`parseDocument` parses the text with the general Lisp reader, converts it to a
tagged tree, re-prints the tree and compares the bytes, decodes it and checks
digests and map order. Re-printing nests string appends, and the digest walk
copies a child path at every node, so both cost the depth of the tree at every
byte or node. `read` replaces every step except the decoder:

1. `readTree?`, a byte-level recursive descent into a tagged tree whose
   children are stored in arrays. It is not trusted: its result is used only
   when the next step accepts it.
2. `spellable` and `printInto` check that the tree has only symbols the Lisp
   reader reads back unchanged, and that its canonical printing, built in one
   linear pass, is the input text. `parseDoc_printTagged` proves that the Lisp
   reader then returns the same tree, so `parseDocument` would have accepted
   the layout with that tree.
3. The decoder is `parseDocument`'s; `digestFine` checks digests without paths.

On any failure `read` returns what `parseDocument` returns, by calling it.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Reader

open Silmaril.TaggedCodec Silmaril.Formats Silmaril.Formats.SExpEncoding
open Silmaril.Formats.SExpParser Silmaril.Formats.SExpEncoding.ParserSound
open Silmaril.Cerberus.Codec Silmaril.Cerberus.Codec.WellFormed

/-! ## The byte-level reader (untrusted) -/

/-- A node whose children are read from an array in constant time. -/
def nodeOfArray (tag : String) (cs : Array Tree) : Tree := .tag tag cs.size fun i => cs[i]

/-- The end of a bare token starting at `i`: the next space, parenthesis, quote
or newline. -/
def symEnd (b : ByteArray) (i : Nat) : Nat :=
  if h : i < b.size then
    let c := b[i]
    if c == 32 || c == 40 || c == 41 || c == 34 || c == 10 then i else symEnd b (i + 1)
  else i
termination_by b.size - i

/-- The closing quote of a string literal whose body starts at `i`, and whether
the body has escapes. -/
def quoteEnd (b : ByteArray) (i : Nat) (esc : Bool) : Option (Nat × Bool) :=
  if h : i < b.size then
    let c := b[i]
    if c == 34 then some (i, esc)
    else if c == 92 then quoteEnd b (i + 2) true
    else quoteEnd b (i + 1) esc
  else none
termination_by b.size - i

/-- The bytes of a string-literal body with the printer's escapes undone. -/
def unescape (b : ByteArray) (i j : Nat) (acc : ByteArray) : Option ByteArray :=
  if h : i < j ∧ i < b.size then
    let c := b[i]
    if c == 92 then
      match b[i + 1]? with
      | some 92 => unescape b (i + 2) j (acc.push 92)
      | some 34 => unescape b (i + 2) j (acc.push 34)
      | some 110 => unescape b (i + 2) j (acc.push 10)
      | some 114 => unescape b (i + 2) j (acc.push 13)
      | some 116 => unescape b (i + 2) j (acc.push 9)
      | _ => none
    else unescape b (i + 1) j (acc.push c)
  else some acc
termination_by b.size - i

mutual
  /-- One datum starting at byte `i`, and the index after it. -/
  def readAt (b : ByteArray) : Nat → Nat → Option (Tree × Nat)
    | 0, _ => none
    | fuel + 1, i =>
      if h : i < b.size then
        let c := b[i]
        if c == 40 then
          let j := symEnd b (i + 1)
          if j == i + 1 then none else do
            let tag ← String.fromUTF8? (b.extract (i + 1) j)
            readChildren b fuel j tag #[]
        else if c == 34 then do
          let (j, esc) ← quoteEnd b (i + 1) false
          let body ← if esc then unescape b (i + 1) j .empty else some (b.extract (i + 1) j)
          let s ← String.fromUTF8? body
          some (.atom s, j + 1)
        else
          let j := symEnd b i
          if j == i then none else do
            let s ← String.fromUTF8? (b.extract i j)
            some (.atom s, j)
      else none

  /-- The children of a node, each after one space, up to its closing parenthesis. -/
  def readChildren (b : ByteArray) : Nat → Nat → String → Array Tree → Option (Tree × Nat)
    | 0, _, _, _ => none
    | fuel + 1, i, tag, acc =>
      if h : i < b.size then
        let c := b[i]
        if c == 41 then some (nodeOfArray tag acc, i + 1)
        else if c == 32 then do
          let (t, j) ← readAt b fuel (i + 1)
          readChildren b fuel j tag (acc.push t)
        else none
      else none
end

/-- A whole document: one datum and a final newline. -/
def readTree? (text : String) : Option Tree :=
  let b := text.toByteArray
  match readAt b (b.size + 1) 0 with
  | some (t, j) => if j + 1 == b.size && b[j]? == some 10 then some t else none
  | none => none

/-! ## Linear canonical printing -/

/-- Append a character as `SExpPrinter.escapeChar` spells it. -/
def pushEscaped (acc : String) (c : Char) : String :=
  if c = '\\' ∨ c = '"' ∨ c = '\n' ∨ c = '\r' ∨ c = '\t' then acc ++ SExpPrinter.escapeChar c
  else acc.push c

/-- Append `SExpPrinter.quote s`. -/
def quoteInto (acc s : String) : String :=
  (s.foldl pushEscaped (acc.push '"')).push '"'

/-- Append the canonical printing of a tagged tree (`printTagged`); `q` says the
parent is a `$str` node, whose atoms are quoted. -/
def printInto (q : Bool) (acc : String) : Tree → String
  | .atom s => if q then quoteInto acc s else acc ++ s
  | .tag tag n cs =>
    (Fin.foldl n (fun acc i => printInto (tag == "$str") (acc.push ' ') (cs i))
      (acc.push '(' ++ tag)).push ')'

/-! ## Symbols the Lisp reader reads back -/

/-- A bare token that `SExpParser.bare` reads back unchanged in every position:
nonempty, not the dotted-pair marker, and without delimiters or quotes. -/
def symOk (s : String) : Bool :=
  s.length != 0 && s != "." && s.foldl (fun ok c => ok && !delimiter c && c != '"') true

/-- Every bare atom and every tag is `symOk`; atoms of `$str` nodes are quoted. -/
def spellable (q : Bool) : Tree → Bool
  | .atom s => q || symOk s
  | .tag tag _ cs => symOk tag && (List.finRange _).all fun i => spellable (tag == "$str") (cs i)

/-! ## Digests without paths -/

/-- A digest child that `digestProblems` accepts. A digest is a `$str` of two
hexadecimal digits per byte, so 0 or 32 characters need no decoding
(`digestChildOk_eq`). -/
def digestChildOk (t : Tree) : Bool :=
  match Silmaril.TaggedCodec.Codec.str.dec t with
  | none => true
  | some s =>
    if s.length == 0 || s.length == 32 then true
    else match digest.dec t with
      | some d => digestOk d
      | none => true

/-- `digestProblems` finds nothing at this node. -/
def digestHere (tag : String) {n : Nat} (cs : Fin n → Tree) : Bool :=
  match digestIndex tag with
  | none => true
  | some index => if h : index < n then digestChildOk (cs ⟨index, h⟩) else true

/-- `digestProblems` finds nothing in the tree. -/
def digestFine : Tree → Bool
  | .atom _ => true
  | .tag tag _ cs => digestHere tag cs && (List.finRange _).all fun i => digestFine (cs i)


/-! ## Proofs: the printer -/

open SExpPrinter in
theorem pushEscaped_eq (acc : String) (c : Char) : pushEscaped acc c = acc ++ escapeChar c := by
  unfold pushEscaped
  split
  · rfl
  · rename_i h
    rw [String.push_eq_append]
    congr 1
    unfold escapeChar
    split <;> simp_all

theorem foldl_pushEscaped (l : List Char) (acc : String) :
    l.foldl pushEscaped acc = acc ++ String.join (l.map SExpPrinter.escapeChar) := by
  induction l generalizing acc with
  | nil => simp
  | cons c l ih => simp [ih, pushEscaped_eq, String.join_cons, String.append_assoc]

theorem quoteInto_eq (acc s : String) : quoteInto acc s = acc ++ SExpPrinter.quote s := by
  simp only [quoteInto, String.foldl_eq_foldl_toList, foldl_pushEscaped, String.push_eq_append,
    SExpPrinter.quote, String.append_assoc]
  rfl

abbrev pr (x : SExp) : String := SExpPrinter.printSExp2With printTaggedAtom x
abbrev prT (x : SExp) : String := SExpPrinter.printTailWith printTaggedAtom x

theorem pr_cons (a d : SExp) : pr (.cons a d) = "(" ++ pr a ++ prT d ++ ")" := by
  simp [SExpPrinter.printSExp2With]
theorem prT_nil : prT .nil = "" := by simp [SExpPrinter.printTailWith]
theorem prT_cons (a d : SExp) : prT (.cons a d) = " " ++ pr a ++ prT d := by
  simp [SExpPrinter.printTailWith]
theorem pr_nil : pr .nil = "()" := by simp [SExpPrinter.printSExp2With]
theorem pr_atom (a : Atom) : pr (.atom a) = printTaggedAtom a := by
  simp [SExpPrinter.printSExp2With]

theorem printInto_eq (q : Bool) (acc : String) (t : Tree) :
    printInto q acc t = acc ++ pr (ofTagged q t) := by
  induction t generalizing q acc with
  | atom s =>
    cases q
    · simp [printInto, ofTagged, pr_atom, printTaggedAtom]
    · simp [printInto, ofTagged, pr_atom, printTaggedAtom, quoteInto_eq]
  | tag tag n cs ih =>
    have tail : ∀ (is : List (Fin n)) (acc : String),
        is.foldl (fun acc i => printInto (tag == "$str") (acc.push ' ') (cs i)) acc =
          acc ++ prT (listOf (is.map fun i => ofTagged (tag == "$str") (cs i))) := by
      intro is
      induction is with
      | nil => intro acc; simp [prT_nil]
      | cons i is ihs =>
        intro acc
        rw [List.foldl_cons, ihs, ih, List.map_cons, listOf_cons, prT_cons, String.push_eq_append]
        simp only [String.append_assoc]
        rfl
    rw [printInto, Fin.foldl_eq_finRange_foldl, tail]
    simp only [ofTagged, listOf_cons, pr_cons, String.push_eq_append, String.append_assoc, kw,
      pr_atom, printTaggedAtom, List.ofFn_eq_map]
    rfl

theorem printInto_printTagged (t : Tree) : printInto false "" t = printTagged t := by
  simp [printInto_eq, printTagged]


/-! ## Proofs: spellable trees -/

/-- Printed S-expressions that the Lisp reader reads back: proper lists of
`symOk` symbols and UTF-8 strings; `tail` marks a list tail. -/
def Spelled : Bool → SExp → Prop
  | _, .nil => True
  | false, .atom (.sym s) => symOk s = true
  | false, .atom (.str bs) => Unicode.utf8 ((Unicode.utf8? bs).getD "") = bs
  | false, .atom (.id _) => False
  | true, .atom _ => False
  | _, .cons a d => Spelled false a ∧ Spelled true d

theorem spelled_listOf (xs : List SExp) : Spelled true (listOf xs) ↔ ∀ x ∈ xs, Spelled false x := by
  induction xs with
  | nil => simp [Spelled]
  | cons x xs ih => simp [Spelled, ih]

theorem spellable_spelled (q : Bool) (t : Tree) (h : spellable q t = true) :
    Spelled false (ofTagged q t) := by
  induction t generalizing q with
  | atom s =>
    cases q
    · simpa [spellable, ofTagged, Spelled] using h
    · simp [ofTagged, Spelled]
  | tag tag n cs ih =>
    simp only [spellable, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at h
    simp only [ofTagged, listOf_cons, kw, Spelled, h.1, true_and, spelled_listOf, List.mem_ofFn]
    rintro _ ⟨i, rfl⟩
    exact ih i _ (h.2 i)

theorem foldl_and (l : List Char) (p : Char → Bool) (b : Bool) :
    l.foldl (fun ok c => ok && p c) b = (b && l.all p) := by
  induction l generalizing b with
  | nil => simp
  | cons c l ih => simp [ih, Bool.and_assoc]

theorem symOk_iff {s : String} (h : symOk s = true) :
    s.toList ≠ [] ∧ s.toList ≠ ['.'] ∧ ∀ c ∈ s.toList, delimiter c = false ∧ c ≠ '"' := by
  simp only [symOk, String.foldl_eq_foldl_toList, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hl, hd⟩, ha⟩ := h
  rw [show (fun ok c => ok && !delimiter c && c != '"') =
    (fun ok c => ok && (!delimiter c && c != '"')) by funext ok c; rw [Bool.and_assoc],
    foldl_and] at ha
  refine ⟨?_, ?_, ?_⟩
  · intro he; apply hl; rw [← String.length_toList, he]; rfl
  · intro he; apply hd; rw [← String.ofList_toList (s := s), he]
  · have ha' : ∀ x ∈ s.toList, delimiter x = false ∧ ¬x = '"' := by simpa using ha
    exact ha'

/-! ## Proofs: the Lisp reader on canonical text -/


/-- The text after a datum starts with a delimiter, if any. -/
def Follow (r : Chars) : Prop := ∀ c, r.head? = some c → delimiter c = true

theorem wsFuel_stop {inp : Input} {c : Char} {r : Chars} (h : At inp (c :: r))
    (hs : space c = false) (hc : c ≠ ';') : ∀ k, wsFuel k false inp = inp
  | 0 => rfl
  | k + 1 => by simp [wsFuel, h.current, hs, hc]

theorem wsFuel_end {inp : Input} (h : At inp []) : ∀ k b, wsFuel k b inp = inp
  | 0, _ => rfl
  | k + 1, _ => by simp [wsFuel, h.current]

theorem ws_stop {inp : Input} {c : Char} {r : Chars} (h : At inp (c :: r))
    (hs : space c = false) (hc : c ≠ ';') : ws inp = inp :=
  wsFuel_stop h hs hc _

theorem ws_space {inp : Input} {c : Char} {r : Chars} (h : At inp (' ' :: c :: r))
    (hs : space c = false) (hc : c ≠ ';') : ws inp = inp.next := by
  simp only [ws, wsFuel, h.current, List.head?]
  simp [space, wsFuel_stop h.next hs hc]

theorem ws_newline {inp : Input} (h : At inp ['\n']) : (ws inp).current = none := by
  simp only [ws, wsFuel, h.current, List.head?]
  simp [space, wsFuel_end h.next, h.next.current]

theorem bare_go_tok (s r : Chars) (hs : ∀ c ∈ s, delimiter c = false) (hr : Follow r) :
    ∀ k inp, At inp (s ++ r) → s.length < k → ∃ out, bare.go k inp = (s, out) ∧ At out r := by
  induction s with
  | nil =>
    intro k inp h hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    refine ⟨inp, ?_, by simpa using h⟩
    cases r with
    | nil => simp [bare.go, (by simpa using h : At inp []).current]
    | cons c r => simp [bare.go, (by simpa using h : At inp (c :: r)).current, hr c rfl]
  | cons c s ih =>
    intro k inp h hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    obtain ⟨out, he, ha⟩ := ih (fun x hx => hs x (by simp [hx])) k inp.next h.next
      (by simp at hk; omega)
    exact ⟨out, by simp [bare.go, h.current, hs c (by simp), he], ha⟩

theorem bare_tok {s r : Chars} (hs : ∀ c ∈ s, delimiter c = false) (hr : Follow r)
    {inp : Input} (h : At inp (s ++ r)) : ∃ out, bare inp = (s, out) ∧ At out r :=
  bare_go_tok s r hs hr _ inp h (by have := h.length; simp at this; omega)

/-- The characters of a string-literal body, as the printer escapes them. -/
abbrev escC (c : Char) : Chars := (SExpPrinter.escapeChar c).toList

theorem quoted_esc (l r : Chars) :
    ∀ k inp, At inp (l.flatMap escC ++ '"' :: r) → l.length < k →
      ∃ out, quoted k inp = some (l, out) ∧ At out r := by
  induction l with
  | nil =>
    intro k inp h hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simp only [List.flatMap_nil, List.nil_append] at h
    exact ⟨inp.next, by simp [quoted, h.current], h.next⟩
  | cons c l ih =>
    intro k inp h hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hk' : l.length < k := by simp at hk; omega
    by_cases hsp : c = '\\' ∨ c = '"' ∨ c = '\n' ∨ c = '\r' ∨ c = '\t'
    · rcases hsp with rfl | rfl | rfl | rfl | rfl
      · have h' : At inp ('\\' :: '\\' :: (l.flatMap escC ++ '"' :: r)) := h
        obtain ⟨out, hq, ha⟩ := ih k inp.next.next h'.next.next hk'
        exact ⟨out, by simp [quoted, h'.current, h'.next.current, hq], ha⟩
      · have h' : At inp ('\\' :: '"' :: (l.flatMap escC ++ '"' :: r)) := h
        obtain ⟨out, hq, ha⟩ := ih k inp.next.next h'.next.next hk'
        exact ⟨out, by simp [quoted, h'.current, h'.next.current, hq], ha⟩
      · have h' : At inp ('\\' :: 'n' :: (l.flatMap escC ++ '"' :: r)) := h
        obtain ⟨out, hq, ha⟩ := ih k inp.next.next h'.next.next hk'
        exact ⟨out, by simp [quoted, h'.current, h'.next.current, hq], ha⟩
      · have h' : At inp ('\\' :: 'r' :: (l.flatMap escC ++ '"' :: r)) := h
        obtain ⟨out, hq, ha⟩ := ih k inp.next.next h'.next.next hk'
        exact ⟨out, by simp [quoted, h'.current, h'.next.current, hq], ha⟩
      · have h' : At inp ('\\' :: 't' :: (l.flatMap escC ++ '"' :: r)) := h
        obtain ⟨out, hq, ha⟩ := ih k inp.next.next h'.next.next hk'
        exact ⟨out, by simp [quoted, h'.current, h'.next.current, hq], ha⟩
    · have he : escC c = [c] := by
        simp only [escC]
        unfold SExpPrinter.escapeChar
        split <;> simp_all
      simp only [List.flatMap_cons, he, List.cons_append, List.nil_append] at h
      obtain ⟨out, hq, ha⟩ := ih k inp.next h.next hk'
      refine ⟨out, ?_, ha⟩
      have h1 : c ≠ '"' := fun e => hsp (Or.inr (Or.inl e))
      have h2 : c ≠ '\\' := fun e => hsp (Or.inl e)
      simp only [quoted, h.current, List.head?]
      simp [hq]


theorem delimiter_false {c : Char} (h : delimiter c = false) :
    space c = false ∧ c ≠ '(' ∧ c ≠ ')' ∧ c ≠ ';' := by
  simp only [delimiter, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem length_le_flatMap_escC (l : Chars) : l.length ≤ (l.flatMap escC).length := by
  induction l with
  | nil => simp
  | cons c l ih =>
    have : 1 ≤ (escC c).length := by
      simp only [escC]; unfold SExpPrinter.escapeChar; split <;> simp
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem toList_quote (s : String) :
    (SExpPrinter.quote s).toList = '"' :: (s.toList.flatMap escC ++ ['"']) := by
  simp [SExpPrinter.quote, String.toList_append, String.toList_join, List.flatMap_map]

/-- The first character of a printed spelled datum, and the one after a leading `.`. -/
theorem pr_head {x : SExp} (h : Spelled false x) :
    (∃ c rest, (pr x).toList = c :: rest ∧ space c = false ∧ c ≠ ';' ∧ c ≠ ')' ∧
      c ≠ '(' ∧ c ≠ '"' ∧ (c = '.' → ∃ c' rest', rest = c' :: rest' ∧ delimiter c' = false)) ∨
    (∃ rest, (pr x).toList = '(' :: rest) ∨ (∃ rest, (pr x).toList = '"' :: rest) := by
  match x, h with
  | .nil, _ => exact Or.inr (Or.inl ⟨[')'], by rw [pr_nil]; rfl⟩)
  | .cons a d, _ => exact Or.inr (Or.inl ⟨_, by rw [pr_cons]; simp [String.toList_append]; rfl⟩)
  | .atom (.str bs), _ => exact Or.inr (Or.inr ⟨_, by rw [pr_atom, printTaggedAtom, toList_quote]⟩)
  | .atom (.sym s), h =>
    left
    obtain ⟨hne, hdot, hall⟩ := symOk_iff h
    rw [pr_atom, printTaggedAtom]
    obtain ⟨c, rest, hs⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨hd, hq⟩ := hall c (by simp [hs])
    obtain ⟨h1, h2, h3, h4⟩ := delimiter_false hd
    refine ⟨c, rest, hs, h1, h4, h3, h2, hq, ?_⟩
    rintro rfl
    cases rest with
    | nil => exact absurd hs hdot
    | cons c' rest' => exact ⟨c', rest', rfl, (hall c' (by simp [hs])).1⟩

theorem follow_tail {d : SExp} (h : Spelled true d) (r : Chars) :
    Follow ((prT d).toList ++ ')' :: r) := by
  match d, h with
  | .nil, _ => intro c hc; simp [prT_nil] at hc; subst hc; rfl
  | .cons a d, _ =>
    intro c hc
    simp [prT_cons, String.toList_append] at hc
    subst hc; rfl

theorem expr_open {f : Nat} {inp : Input} {rest : Chars} (h : At (ws inp) ('(' :: rest)) :
    SExpParser.expr (f + 1) inp = SExpParser.list f [] (ws inp).next := by
  simp [SExpParser.expr, h.current]

theorem expr_quote {f : Nat} {inp : Input} {rest : Chars} (h : At (ws inp) ('"' :: rest)) :
    SExpParser.expr (f + 1) inp = (do
      let (token, rest) ← quoted f (ws inp).next
      some (.atom (.string (String.ofList token)), rest)) := by
  simp [SExpParser.expr, h.current]

theorem expr_bare {f : Nat} {inp : Input} {c : Char} {rest : Chars} (h : At (ws inp) (c :: rest))
    (h1 : c ≠ ')') (h2 : c ≠ '(') (h3 : c ≠ '"') :
    SExpParser.expr (f + 1) inp =
      let (token, rest) := bare (ws inp)
      if token.isEmpty then none else some (.atom (.symbol (String.ofList token)), rest) := by
  simp only [SExpParser.expr, h.current, List.head?]

theorem list_close {f : Nat} {acc : List (SExp2 Lexeme)} {inp : Input} {rest : Chars}
    (h : At (ws inp) (')' :: rest)) :
    SExpParser.list (f + 1) acc inp = some (acc.foldr .cons .nil, (ws inp).next) := by
  simp [SExpParser.list, h.current]

theorem list_step {f : Nat} {acc : List (SExp2 Lexeme)} {inp : Input} {c : Char} {rest : Chars}
    (h : At (ws inp) (c :: rest)) (hc : c ≠ ')')
    (hdot : c = '.' → ∃ c' rest', rest = c' :: rest' ∧ delimiter c' = false) :
    SExpParser.list (f + 1) acc inp = (do
      let (head, rest) ← SExpParser.expr f (ws inp)
      SExpParser.list f (acc ++ [head]) rest) := by
  simp only [SExpParser.list, h.current, List.head?]
  split
  · simp_all
  · simp_all
  · rename_i heq
    simp only [Option.some.injEq] at heq
    subst heq
    obtain ⟨c', rest', rfl, hd⟩ := hdot rfl
    have hm : dottedMarker (ws inp) = false := by
      simp [dottedMarker, h.current, h.next.current, hd]
    simp [hm]
  · rfl

theorem map_foldr_cons (vs : List (SExp2 Lexeme)) :
    (vs.foldr SExp2.cons SExp2.nil).map Lexeme.toAtom = listOf (vs.map (SExp2.map Lexeme.toAtom)) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [SExp2.map, ih]

/-- The Lisp reader reads a printed spelled datum back, and a printed list tail. -/
theorem parse_spelled (x : SExp) :
    (Spelled false x → ∀ fuel inp r, At inp ((pr x).toList ++ r) → Follow r →
      (pr x).toList.length < fuel →
      ∃ v out, SExpParser.expr fuel inp = some (v, out) ∧ v.map Lexeme.toAtom = x ∧ At out r) ∧
    (Spelled true x → ∀ fuel acc inp r, At inp ((prT x).toList ++ ')' :: r) →
      (prT x).toList.length < fuel →
      ∃ vs out, SExpParser.list fuel acc inp = some ((acc ++ vs).foldr .cons .nil, out) ∧
        listOf (vs.map (SExp2.map Lexeme.toAtom)) = x ∧ At out r) := by
  induction x with
  | nil =>
    refine ⟨fun _ fuel inp r h _ hl => ?_, fun _ fuel acc inp r h hl => ?_⟩
    · rw [pr_nil] at h hl
      have h' : At inp ('(' :: ')' :: r) := h
      obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by simp at hl; omega : fuel ≠ 0)
      obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by simp at hl; omega : f ≠ 0)
      have hw : ws inp = inp := ws_stop h' rfl (by decide)
      have hw' : ws inp.next = inp.next := ws_stop h'.next rfl (by decide)
      rw [expr_open (by rw [hw]; exact h'), hw, list_close (by rw [hw']; exact h'.next), hw']
      exact ⟨_, _, rfl, rfl, h'.next.next⟩
    · rw [prT_nil] at h hl
      have h' : At inp (')' :: r) := h
      obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by simp at hl; omega : fuel ≠ 0)
      have hw : ws inp = inp := ws_stop h' rfl (by decide)
      rw [list_close (by rw [hw]; exact h'), hw]
      exact ⟨[], _, by simp, by simp [listOf], h'.next⟩
  | atom a =>
    refine ⟨fun hx fuel inp r h hr hl => ?_, fun hx => by simp [Spelled] at hx⟩
    obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    match a, hx with
    | .sym s, hx =>
      obtain ⟨hne, -, hall⟩ := symOk_iff hx
      obtain ⟨c, rest, hs⟩ := List.exists_cons_of_ne_nil hne
      obtain ⟨h1, h2, h3, h4⟩ := delimiter_false (hall c (by simp [hs])).1
      rw [pr_atom, printTaggedAtom] at h
      have h' : At inp (c :: (rest ++ r)) := by rw [hs] at h; simpa using h
      have hw : ws inp = inp := ws_stop h' h1 h4
      rw [expr_bare (by rw [hw]; exact h') h3 h2 (hall c (by simp [hs])).2, hw]
      obtain ⟨out, hb, ha⟩ := bare_tok (fun c hc => (hall c hc).1) hr h
      simp only [hb, List.isEmpty_iff, hne, ite_false, String.ofList_toList]
      exact ⟨_, _, rfl, rfl, ha⟩
    | .str bs, hx =>
      rw [pr_atom, printTaggedAtom, toList_quote] at h hl
      have h' : At inp ('"' :: ((Unicode.utf8? bs).getD "").toList.flatMap escC ++ '"' :: r) := by
        simpa using h
      have hw : ws inp = inp := ws_stop h' rfl (by decide)
      rw [expr_quote (by rw [hw]; exact h'), hw]
      have hlen : (((Unicode.utf8? bs).getD "").toList).length < f := by
        have := length_le_flatMap_escC ((Unicode.utf8? bs).getD "").toList
        simp only [List.length_cons, List.length_append] at hl
        omega
      obtain ⟨out, hq, ha⟩ := quoted_esc _ r f inp.next h'.next hlen
      simp only [hq, Option.bind_eq_bind, Option.bind_some, String.ofList_toList]
      exact ⟨_, _, rfl, by simp only [SExp2.map, Lexeme.toAtom]; congr 2, ha⟩
    | .id _, hx => exact absurd hx (by simp [Spelled])
  | cons a d iha ihd =>
    have elem (ha : Spelled false a) (hd : Spelled true d) :
        ∀ fuel acc inp r, At (ws inp) ((pr a).toList ++ (prT d).toList ++ ')' :: r) →
          (pr a).toList.length + (prT d).toList.length + 1 < fuel →
          ∃ vs out, SExpParser.list fuel acc inp = some ((acc ++ vs).foldr .cons .nil, out) ∧
            listOf (vs.map (SExp2.map Lexeme.toAtom)) = .cons a d ∧ At out r := by
      intro fuel acc inp r h hl
      obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
      have hstep : SExpParser.list (f + 1) acc inp = (do
          let (head, rest) ← SExpParser.expr f (ws inp)
          SExpParser.list f (acc ++ [head]) rest) := by
        rcases pr_head ha with ⟨c, rest, hs, -, -, hc, -, -, hdot⟩ | ⟨rest, hs⟩ | ⟨rest, hs⟩
        · rw [hs] at h
          refine list_step (rest := rest ++ (prT d).toList ++ ')' :: r) (by simpa using h) hc ?_
          intro e
          obtain ⟨c', rest', rfl, hd'⟩ := hdot e
          exact ⟨c', rest' ++ (prT d).toList ++ ')' :: r, by simp, hd'⟩
        · rw [hs] at h
          exact list_step (rest := rest ++ (prT d).toList ++ ')' :: r) (by simpa using h)
            (by decide) (fun e => absurd e (by decide))
        · rw [hs] at h
          exact list_step (rest := rest ++ (prT d).toList ++ ')' :: r) (by simpa using h)
            (by decide) (fun e => absurd e (by decide))
      obtain ⟨v, out1, he, hv, ha1⟩ := iha.1 ha f (ws inp) ((prT d).toList ++ ')' :: r)
        (by simpa using h) (follow_tail hd r) (by omega)
      obtain ⟨vs, out, hl', hvs, ha2⟩ := ihd.2 hd f (acc ++ [v]) out1 r ha1 (by omega)
      refine ⟨v :: vs, out, ?_, ?_, ha2⟩
      · rw [hstep, he]
        simpa using hl'
      · simp [listOf, hv, ← hvs]
    refine ⟨fun hx fuel inp r h _ hl => ?_, fun hx fuel acc inp r h hl => ?_⟩
    · obtain ⟨ha, hd⟩ := hx
      rw [pr_cons] at h hl
      simp only [String.toList_append, List.append_assoc] at h hl
      have h' : At inp ('(' :: ((pr a).toList ++ ((prT d).toList ++ ')' :: r))) := by
        simpa using h
      obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by simp at hl; omega : fuel ≠ 0)
      have hw : ws inp = inp := ws_stop h' rfl (by decide)
      have hw' : ws inp.next = inp.next := by
        rcases pr_head ha with ⟨c, rest, hs, h1, h4, -⟩ | ⟨rest, hs⟩ | ⟨rest, hs⟩ <;>
          (rw [hs] at h'; first
            | exact ws_stop h'.next h1 h4
            | exact ws_stop h'.next rfl (by decide))
      rw [expr_open (by rw [hw]; exact h'), hw]
      obtain ⟨vs, out, hl', hvs, ha'⟩ := elem ha hd f [] inp.next r
        (by rw [hw']; simpa using h'.next) (by simp at hl; omega)
      refine ⟨_, out, hl', ?_, ha'⟩
      simpa [map_foldr_cons] using hvs
    · obtain ⟨ha, hd⟩ := hx
      rw [prT_cons] at h hl
      simp only [String.toList_append, List.append_assoc] at h hl
      have h' : At inp (' ' :: ((pr a).toList ++ ((prT d).toList ++ ')' :: r))) := by
        simpa using h
      have hw : ws inp = inp.next := by
        rcases pr_head ha with ⟨c, rest, hs, h1, h4, -⟩ | ⟨rest, hs⟩ | ⟨rest, hs⟩ <;>
          (rw [hs] at h'; first
            | exact ws_space h' h1 h4
            | exact ws_space h' rfl (by decide))
      exact elem ha hd fuel acc inp r (by rw [hw]; simpa using h'.next) (by simp at hl; omega)

/-- **The Lisp reader reads a printed spellable tree back.** -/
theorem parseDoc_printTagged {t : Tree} (h : spellable false t = true) :
    parseDoc? (printTagged t ++ "\n") = some (taggedDoc t) := by
  have hx := spellable_spelled false t h
  have hs : (printTagged t ++ "\n").toList = (pr (ofTagged false t)).toList ++ ['\n'] := by
    simp [printTagged, String.toList_append]
  have hst := At.start (printTagged t ++ "\n")
  rw [hs] at hst
  obtain ⟨v, out, he, hv, ha⟩ := (parse_spelled _).1 hx ((printTagged t ++ "\n").length + 1) _
    ['\n'] hst (by intro c hc; simp at hc; subst hc; rfl)
    (by rw [← String.length_toList, hs]; simp only [List.length_append, List.length_singleton]; omega)
  simp only [parseDoc?, parseLexemes?, he, Option.bind_eq_bind, Option.bind_some, ws_newline ha,
    Option.isNone_none, ite_true, Option.map_eq_map, Option.map_some, hv, taggedDoc]

/-! ## Proofs: digests and the reader -/

theorem length_digestHex (d : Cerberus.Digest) : (digestHex d).length = 2 * d.bytes.length := by
  simp only [digestHex, String.length_ofList, List.length_flatMap]
  have : ∀ b, (byteHex b).length = 2 := fun b => by simp [byteHex]
  simp [this, List.sum_replicate, Nat.mul_comm]

theorem digestChildOk_eq (t : Tree) :
    digestChildOk t = match digest.dec t with
      | some d => digestOk d
      | none => true := by
  unfold digestChildOk
  cases hs : Silmaril.TaggedCodec.Codec.str.dec t with
  | none => simp [digest, hs]
  | some s =>
    simp only
    split
    · rename_i hl
      cases hd : digest.dec t with
      | none => rfl
      | some d =>
        simp only [digest, hs, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff] at hd
        obtain ⟨bs, -, hd⟩ := hd
        split at hd
        · rename_i heq
          cases hd
          have := length_digestHex ⟨bs⟩
          rw [heq] at this
          simp only [Bool.or_eq_true, beq_iff_eq] at hl
          simp only at this
          rcases hl with hl | hl
          · have : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
            simp [digestOk, this]
          · have : bs.length = 16 := by omega
            simp [digestOk, this]
        · simp at hd
    · rfl

theorem digestProblems_eq_nil (t : Tree) :
    ∀ path, digestProblems path t = [] ↔ digestFine t = true := by
  induction t with
  | atom s => intro path; simp [digestProblems, digestFine]
  | tag tag n cs ih =>
    intro path
    simp only [digestProblems, digestFine, List.append_eq_nil_iff, Option.toList_eq_nil_iff,
      List.flatten_eq_nil_iff, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff,
      Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, ih]
    simp only [and_congr_left_iff]
    intro _
    unfold digestHere
    cases digestIndex tag with
    | none => simp
    | some index =>
      simp only [Option.bind_eq_bind, Option.bind_some, List.getElem?_ofFn]
      split
      · rename_i hlt
        rw [digestChildOk_eq]
        cases hdd : digest.dec (cs ⟨index, hlt⟩) <;> simp [hdd]
      · simp

theorem parseDocument_printTagged {t : Tree} (h : spellable false t = true) :
    parseDocument (printTagged t ++ "\n") = (do
      let doc ← document.decode t
      match digestProblems [] t ++ mapProblems doc.bindings ++ enumProblems doc.enumBindings with
      | e :: _ => throw e
      | [] => return doc) := by
  simp [parseDocument, parseDoc_printTagged h, taggedDoc?_taggedDoc]
  rfl

/-! ## The reader -/

/-- `Codec.WellFormed.parseDocument`, faster (`read_eq`). -/
def read (text : String) : Except DecodeError Document :=
  match readTree? text with
  | none => parseDocument text
  | some t =>
    if spellable false t && (printInto false "" t).push '\n' == text then
      match document.decode t with
      | .error e => .error e
      | .ok doc =>
        if digestFine t && (mapProblems doc.bindings ++ enumProblems doc.enumBindings).isEmpty then
          .ok doc
        else parseDocument text
    else parseDocument text

/-- **`read` is the checked codec.** -/
theorem read_eq (text : String) : read text = parseDocument text := by
  unfold read
  split
  · rfl
  · rename_i t _
    split
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨hs, hp⟩ := hc
      rw [printInto_printTagged, String.push_eq_append] at hp
      have hp' : printTagged t ++ "\n" = text := hp
      subst hp'
      rw [parseDocument_printTagged hs]
      cases hd : document.decode t with
      | error e => rfl
      | ok doc =>
        simp only
        split
        · rename_i hf
          simp only [Bool.and_eq_true, List.isEmpty_iff] at hf
          simp [(digestProblems_eq_nil t []).2 hf.1, hf.2, bind, Except.bind, pure, Except.pure]
        · rfl
    · rfl

end Silmaril.Compile.Core.Reader
