module

public import Silmaril.Semantics.CPort.Formats.SExp.EncodingSchemeDefs.Defs
public import Silmaril.Semantics.CPort.Formats.SExp.EncodingSchemeLex.Defs
public import Silmaril.Semantics.CPort.Formats.SExp.EncodingSchemeParse.Defs

/-!
# R7RS-style Scheme conventions as an S-expression encoding

`sexpScheme : EncRel String SExp` is a contrasting concrete syntax for the same
AST as the WAT conventions (`EncodingWat.lean`), following the lexical syntax
and external representations of R7RS-small (§2.2, §7.1.1, §7.1.2):

* whitespace: space, tab, line endings (`\n`, `\r`);
* `;` line comments (to a line ending or the end of input);
* nested block comments `#| … |#` (`<nested comment>`, with comment text not
  containing `#|` or `|#`, also across its boundaries: `NestedTail`);
* datum comments `#; <datum>` — tree-level atmosphere, skipped by the
  bracketing relation (`Skip`), so they may also nest (`#; #; a b`);
* strings with the R7RS escapes `\a \b \t \n \r \" \\ \|`, `\x<hex>;` and
  line continuations `\<intraline ws>*<line ending><intraline ws>*`; the string
  denotes a character sequence, stored UTF-8 encoded (`Atom.str`);
* `|…|` symbols (with the same escapes, except line continuations), giving
  `Atom.sym name`;
* the quote abbreviations `'d`, `` `d ``, `,d`, `,@d`, expanding to the lists
  `(quote d)`, `(quasiquote d)`, `(unquote d)`, `(unquote-splicing d)`;
* dotted pairs `(d₁ … dₙ . d)` (`n ≥ 1`), represented by `SExp2.cons` with a
  non-`nil` tail;
* every other datum (identifiers, numbers, booleans, characters `#\x`) is a
  *bare token*, a maximal run of non-delimiter characters, kept with its raw
  text as `Atom.sym`.

Simplifications (this is a contrasting relation, not a full R7RS reader): bare tokens are not validated against the R7RS
`<identifier>`/`<number>` grammars; `|abc|` and `abc` both give `sym "abc"`,
so the relation is not deterministic and also identifies `|1|` with `1`;
vectors `#(…)` and bytevectors `#u8(…)` are not supported (they have no
spelling); `#!fold-case` directives are not interpreted.

The definitions live in `EncodingSchemeDefs.lean`; the unambiguity of the
lexical grammar (`lex_functional`) is proved in `EncodingSchemeLex.lean` and
that of the datum grammar (`docRel_unique`) in `EncodingSchemeParse.lean`.
-/

@[expose] public section

namespace Silmaril.Formats.SExpEncoding.Scheme

open Silmaril

theorem lexRel_functional : lexRel.Functional :=
  fun _ _ _ h h' => lex_functional h h' rfl

theorem docRel_functional : docRel.Functional := docRel_unique

theorem sexpScheme_functional : sexpScheme.Functional :=
  lexRel_functional.comp docRel_functional

theorem sexpSchemeBytes_functional : sexpSchemeBytes.Functional :=
  Unicode.functional_push_utf8 sexpScheme_functional

/-- Not deterministic: `|a|` and `a` spell the same symbol. -/
theorem sexpScheme_not_deterministic : ¬ sexpScheme.Deterministic := by
  intro hdet
  have h1 : sexpScheme "a" (doc [kw "a"]) :=
    ⟨[.atom (.sym "a")],
      Lex.step (s := []) (c := ['a']) (rest := []) .nil
        (Or.inr ⟨Or.inl (by decide), rfl, delimNext_nil, by decide⟩) (Lex.done .nil),
      docRel_one (Datum.atom _)⟩
  have h2 : sexpScheme "|a|" (doc [kw "a"]) :=
    ⟨[.atom (.sym "a")],
      Lex.step (s := []) (c := ['|', 'a', '|']) (rest := []) .nil
        (Or.inl ⟨['a'], rfl, SymBody.char (by decide) (by decide) SymBody.nil⟩) (Lex.done .nil),
      docRel_one (Datum.atom _)⟩
  exact absurd (hdet h1 h2) (by decide)

/-! ## Example spellings -/

theorem sexpScheme_module : sexpScheme "(module)" (doc [listOf [kw "module"]]) :=
  ⟨[.lp, .atom (.sym "module"), .rp],
    Lex.step (s := []) (c := ['(']) (rest := "module)".toList) .nil rfl <|
    Lex.step (s := []) (c := "module".toList) (rest := [')']) .nil
      (Or.inr ⟨Or.inl (by decide), rfl, delimNext_cons (by decide), by decide⟩) <|
    Lex.step (s := []) (c := [')']) (rest := []) .nil rfl (Lex.done .nil),
    docRel_one (Datum.list (ts := [.atom (.sym "module")]) (s := []) (data_one (Datum.atom _))
      .nil)⟩

/-- The quote abbreviation. -/
theorem sexpScheme_quote : sexpScheme "'a" (doc [listOf [kw "quote", kw "a"]]) :=
  ⟨[.quote "quote", .atom (.sym "a")],
    Lex.step (s := []) (c := ['\'']) (rest := ['a']) .nil (Or.inl ⟨rfl, rfl⟩) <|
    Lex.step (s := []) (c := ['a']) (rest := []) .nil
      (Or.inr ⟨Or.inl (by decide), rfl, delimNext_nil, by decide⟩) (Lex.done .nil),
    docRel_one (Datum.quote (s := []) .nil (Datum.atom _))⟩

/-- A dotted pair. -/
theorem sexpScheme_dotted : sexpScheme "(a . b)" (doc [.cons (kw "a") (kw "b")]) :=
  ⟨[.lp, .atom (.sym "a"), .dot, .atom (.sym "b"), .rp],
    Lex.step (s := []) (c := ['(']) (rest := "a . b)".toList) .nil rfl <|
    Lex.step (s := []) (c := ['a']) (rest := " . b)".toList) .nil
      (Or.inr ⟨Or.inl (by decide), rfl, delimNext_cons (by decide), by decide⟩) <|
    Lex.step (s := [' ']) (c := ['.']) (rest := " b)".toList) space_one
      ⟨rfl, delimNext_cons (by decide)⟩ <|
    Lex.step (s := [' ']) (c := ['b']) (rest := [')']) space_one
      (Or.inr ⟨Or.inl (by decide), rfl, delimNext_cons (by decide), by decide⟩) <|
    Lex.step (s := []) (c := [')']) (rest := []) .nil rfl (Lex.done .nil),
    docRel_one (Datum.dotted (ts := [.atom (.sym "a")]) (s₁ := []) (s₂ := [])
      (data_one (Datum.atom _)) (by simp) .nil (Datum.atom _) .nil)⟩

end Silmaril.Formats.SExpEncoding.Scheme
