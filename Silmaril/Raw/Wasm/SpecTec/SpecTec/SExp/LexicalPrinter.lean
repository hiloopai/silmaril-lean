module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.SExp.Lexical

/-!
# `render` as a section of the `--ast` lexical convention

`Silmaril.SpecTec.SExp.Lexical` specifies how a `spectec --ast` stream is read
back — `Lexes` and `LexesStream` on character lists, packaged as
`lexicalRel : EncRel String SExp` and `streamRel : EncRel String (List SExp)` —
proves the convention unambiguous (`lexicalRel_functional`,
`streamRel_functional`), and proves the printer sound
(`pp_lexesPre`, `lexicalRel_render`, `lexesStream_outputScript`,
`streamRel_astFile`).

This module is the downstream half of that story: the `Lexes`-level
specializations the rest of the tree wants, and the placement of the whole
*family* of printers in the `EncRel` lattice.

## What is proved here

* `lexes_render`, `lexes_output`, `lexesStream_astFile`,
  `streamRel_outputScript` — the layout `Util.Sexpr.pp`
  (`spectec/src/util/sexpr.ml:15-23`) produces at **any** target width is read
  back as the S-expression it came from.  The target width is a parameter
  throughout: nothing below depends on `SExp.defaultWidth`.
* `lexes_render_unique`, `lexesStream_astFile_unique` — the retraction.
  Printing a `Printable` S-expression and lexing the result returns *that*
  S-expression, because `lexicalRel` is functional.  This is the precise sense
  in which `render width` is a section of `lexicalRel` over
  `SExp.Printable`.
* `renderRel`, `outputScriptRel`, `astFileRel` — the graphs of the three
  printers restricted to the printable arguments, and their placement:
  each is `Bijective` (functional *and* deterministic) and lies below the
  corresponding convention, as does their supremum over all widths
  (`iSup_renderRel_le_lexicalRel`).  The conventions themselves are *not*
  deterministic (`lexicalRel_not_deterministic` in `Lexical.lean`,
  `not_streamRel_deterministic` here): layout is free, so a width is a choice
  of spelling, not a property of the value.  Consequently no single printer
  can be an upper bound for the convention
  (`not_lexicalRel_le_ofFun`, `not_streamRel_le_ofFun`).
* A comparison section relating this convention to the other S-expression
  lexical conventions in the tree.

## Naming

`Lexical.lean` already declares `render_le_lexicalRel`,
`lexicalRel_encoderCorrectOn`, `astFile_le_streamRel` and a generalized
`lexesStream_outputScript` (which takes an arbitrary trailing layout run), so
those names are not redeclared here; the statements below are the ones that
were still missing.
-/

@[expose] public section

namespace Silmaril.SpecTec

/-! ## Printer soundness, at the level of `Lexes` -/

/-- A newline blocks a bare token, so it is always a legal right context for
one.  This is why the separator `Sexpr.output` writes
(`spectec/src/util/sexpr.ml:27`) keeps consecutive definitions apart. -/
theorem headNot_isBare_newline (l : List Char) : HeadNot IsBare ('\n' :: l) :=
  not_isBare_of_isSpace (Or.inr rfl)

/-- **Printer soundness.**  The layout `Util.Sexpr.pp` produces for a
`Printable` S-expression at any target `width`
(`spectec/src/util/sexpr.ml:15-23`) is read back as that S-expression.  This
is `lexicalRel_render` with `lexicalRel` unfolded. -/
theorem lexes_render (width : Nat) (e : SExp) (h : SExp.Printable e) :
    Lexes (SExp.render width e).toList e :=
  lexicalRel_render width e h

/-- **Soundness of `output`.**  `Sexpr.output`
(`spectec/src/util/sexpr.ml:25-28`) appends a newline, which is trailing
layout. -/
theorem lexes_output (width : Nat) (e : SExp) (h : SExp.Printable e) :
    Lexes (SExp.output width e).toList e := by
  have hpre := pp_lexesPre 0 width e h ['\n'] (headNot_isBare_newline [])
  have h' := Lexes.intro (w := []) spaces_nil (by decide : Spaces ['\n']) hpre
  simpa [SExp.output, SExp.render, String.toList_append] using h'

/-- **Soundness of `output_script`.**  The stream
`Backend_ast.Print.output_script` writes
(`spectec/src/backend-ast/print.ml:235`) is read back as the list of
S-expressions it was given.  This is the `tl = []` case of
`lexesStream_outputScript`. -/
theorem streamRel_outputScript (width : Nat) (es : List SExp)
    (h : SExp.PrintableList es) : LexesStream (SExp.outputScript width es).toList es := by
  simpa using lexesStream_outputScript width es h [] spaces_nil

/-- **Soundness of the `--ast` file.**  `spectec --ast -o FILE` writes
`output_script` followed by one more newline
(`spectec/src/exe-spectec/main.ml:256-257`); the extra newline is trailing
layout, so the file is read back as the same list of S-expressions.  This is
`streamRel_astFile` with `streamRel` unfolded. -/
theorem lexesStream_astFile (width : Nat) (es : List SExp)
    (h : SExp.PrintableList es) : LexesStream (SExp.astFile width es).toList es :=
  streamRel_astFile width es h

/-! ## The retraction

`lexicalRel` is functional and `render` is a correct encoder on `Printable`,
so printing and then lexing is the identity.  This is the statement that
`render width` is a *section* of the lexical relation. -/

/-- Lexing the output of `render` returns the S-expression that was printed. -/
theorem lexes_render_unique (width : Nat) (e e' : SExp) (h : SExp.Printable e)
    (h' : Lexes (SExp.render width e).toList e') : e' = e :=
  lexicalRel_functional h' (lexes_render width e h)

/-- Lexing the output of `output` returns the S-expression that was printed. -/
theorem lexes_output_unique (width : Nat) (e e' : SExp) (h : SExp.Printable e)
    (h' : Lexes (SExp.output width e).toList e') : e' = e :=
  lexicalRel_functional h' (lexes_output width e h)

/-- Lexing a printed `--ast` file returns the definitions that were printed. -/
theorem lexesStream_astFile_unique (width : Nat) (es es' : List SExp)
    (h : SExp.PrintableList es) (h' : LexesStream (SExp.astFile width es).toList es') :
    es' = es :=
  streamRel_functional h' (lexesStream_astFile width es h)

/-- Lexing a printed script returns the definitions that were printed. -/
theorem streamRel_outputScript_unique (width : Nat) (es es' : List SExp)
    (h : SExp.PrintableList es)
    (h' : LexesStream (SExp.outputScript width es).toList es') : es' = es :=
  streamRel_functional h' (streamRel_outputScript width es h)

/-- Two target widths produce two spellings of the same S-expression: the
width is a choice of layout, not of value.  Stated with `EncRel.Lift`. -/
theorem render_lift_eq (w₁ w₂ : Nat) (e : SExp) (h : SExp.Printable e) :
    lexicalRel.Lift Eq (SExp.render w₁ e) (SExp.render w₂ e) :=
  ⟨e, e, lexes_render w₁ e h, lexes_render w₂ e h, rfl⟩

/-! ## Placement in the lattice

In the style of `Silmaril/Formats/Json/Encoding.lean`: the printers are
*values* of type `EncRel`, so they can be compared with the convention they
implement. -/

/-- The graph of `render width`, restricted to the S-expressions it is
faithful on.  One encoding per target width. -/
def renderRel (width : Nat) : EncRel String SExp :=
  (EncRel.ofFun (SExp.render width)).restrict SExp.Printable

/-- The graph of `output_script` at a given width, restricted to printable
scripts. -/
def outputScriptRel (width : Nat) : EncRel String (List SExp) :=
  (EncRel.ofFun (SExp.outputScript width)).restrict SExp.PrintableList

/-- The graph of the whole `--ast` file at a given width, restricted to
printable scripts. -/
def astFileRel (width : Nat) : EncRel String (List SExp) :=
  (EncRel.ofFun (SExp.astFile width)).restrict SExp.PrintableList

/-- Each printer lies below the convention *and* inside the printable
fragment.  Sharper than `render_le_lexicalRel`, which forgets the
restriction. -/
theorem renderRel_le_restrict (width : Nat) :
    renderRel width ≤ lexicalRel.restrict SExp.Printable := by
  rintro s e ⟨rfl, hp⟩
  exact ⟨lexicalRel_render width e hp, hp⟩

/-- `output_script`'s graph lies below the stream convention. -/
theorem outputScript_le_streamRel (width : Nat) :
    (EncRel.ofFun (SExp.outputScript width)).restrict SExp.PrintableList ≤ streamRel := by
  rintro s es ⟨rfl, hp⟩
  exact streamRel_outputScript width es hp

/-- `output_script` is a correct encoder of printable scripts. -/
theorem streamRel_encoderCorrectOn_outputScript (width : Nat) :
    streamRel.EncoderCorrectOn SExp.PrintableList (SExp.outputScript width) :=
  fun es h => streamRel_outputScript width es h

/-- The `--ast` file printer is a correct encoder of printable scripts. -/
theorem streamRel_encoderCorrectOn_astFile (width : Nat) :
    streamRel.EncoderCorrectOn SExp.PrintableList (SExp.astFile width) :=
  fun es h => streamRel_astFile width es h

/-- Every width at once: the join of the whole family of printers is still a
sub-encoding of the convention. -/
theorem iSup_renderRel_le_lexicalRel : (⨆ width : Nat, renderRel width) ≤ lexicalRel :=
  iSup_le fun width => render_le_lexicalRel width

/-- The same for whole files. -/
theorem iSup_astFileRel_le_streamRel : (⨆ width : Nat, astFileRel width) ≤ streamRel :=
  iSup_le fun width => astFile_le_streamRel width

/-- The same for scripts. -/
theorem iSup_outputScriptRel_le_streamRel :
    (⨆ width : Nat, outputScriptRel width) ≤ streamRel :=
  iSup_le fun width => outputScript_le_streamRel width

/-- A single printer is deterministic: it picks one spelling. -/
theorem renderRel_deterministic (width : Nat) : (renderRel width).Deterministic :=
  (EncRel.ofFun_deterministic (SExp.render width)).anti (EncRel.restrict_le _ _)

/-- A single printer is functional, because the convention it implements
is. -/
theorem renderRel_functional (width : Nat) : (renderRel width).Functional :=
  lexicalRel_functional.anti (render_le_lexicalRel width)

/-- Each `renderRel width` is a partial bijection between printable
S-expressions and their layouts at that width. -/
theorem renderRel_bijective (width : Nat) : (renderRel width).Bijective :=
  ⟨renderRel_functional width, renderRel_deterministic width⟩

/-- The file printer is deterministic. -/
theorem astFileRel_deterministic (width : Nat) : (astFileRel width).Deterministic :=
  (EncRel.ofFun_deterministic (SExp.astFile width)).anti (EncRel.restrict_le _ _)

/-- The file printer is functional. -/
theorem astFileRel_functional (width : Nat) : (astFileRel width).Functional :=
  streamRel_functional.anti (astFile_le_streamRel width)

/-- Each `astFileRel width` is a partial bijection. -/
theorem astFileRel_bijective (width : Nat) : (astFileRel width).Bijective :=
  ⟨astFileRel_functional width, astFileRel_deterministic width⟩

/-- `output_script`'s graph is a partial bijection too. -/
theorem outputScriptRel_bijective (width : Nat) : (outputScriptRel width).Bijective :=
  ⟨streamRel_functional.anti (outputScript_le_streamRel width),
    (EncRel.ofFun_deterministic (SExp.outputScript width)).anti (EncRel.restrict_le _ _)⟩

/-! ### Totality on the printable fragment

`lexicalRel.Total` is false — an atom whose string is not a token has no
spelling at all (`not_printable_atom_empty`, `not_lexicalRel_empty`) — but the
convention is total on `Printable`, which `render` witnesses constructively. -/

/-- Every printable S-expression has a spelling. -/
theorem lexicalRel_total_on_printable (e : SExp) (h : SExp.Printable e) :
    ∃ s, lexicalRel s e :=
  ⟨SExp.render SExp.defaultWidth e, lexicalRel_render _ e h⟩

/-- Every printable script has a spelling. -/
theorem streamRel_total_on_printableList (es : List SExp) (h : SExp.PrintableList es) :
    ∃ s, streamRel s es :=
  ⟨SExp.astFile SExp.defaultWidth es, streamRel_astFile _ es h⟩

/-- Totality as an `EncRel` statement: reindexing the syntax along the
inclusion of the printable fragment makes the convention total. -/
theorem lexicalRel_comap_total :
    (lexicalRel.comap (Subtype.val : {e : SExp // SExp.Printable e} → SExp)).Total :=
  fun e => lexicalRel_total_on_printable e.1 e.2

/-- The same for whole files. -/
theorem streamRel_comap_total :
    (streamRel.comap (Subtype.val : {es : List SExp // SExp.PrintableList es} → List SExp)).Total :=
  fun es => streamRel_total_on_printableList es.1 es.2

/-- Printable S-expressions are in the image of the convention. -/
theorem printable_mem_lexicalRel_image {e : SExp} (h : SExp.Printable e) :
    e ∈ lexicalRel.image :=
  lexicalRel_total_on_printable e h

/-- Printed layouts are valid spellings. -/
theorem render_mem_lexicalRel_domain (width : Nat) {e : SExp} (h : SExp.Printable e) :
    SExp.render width e ∈ lexicalRel.domain :=
  ⟨e, lexicalRel_render width e h⟩

/-- Printed `--ast` files are valid streams. -/
theorem astFile_mem_streamRel_domain (width : Nat) {es : List SExp}
    (h : SExp.PrintableList es) : SExp.astFile width es ∈ streamRel.domain :=
  ⟨es, streamRel_astFile width es h⟩

/-! ### The convention is strictly above every printer -/

/-- The stream convention is not deterministic either: the `--ast` file of the
empty script is `"\n"`, and `""` spells the empty script just as well. -/
theorem not_streamRel_deterministic : ¬ streamRel.Deterministic := by
  intro hdet
  have h1 : streamRel "" ([] : List SExp) := LexesStream.nil (by decide)
  have h2 : streamRel "\n" ([] : List SExp) := LexesStream.nil (by decide)
  exact absurd (congrArg String.toList (hdet h1 h2)) (by decide)

/-- No total encoder can be an upper bound for the convention: that would make
it deterministic.  In particular `lexicalRel ≰ renderRel width`, so the
inequality `render_le_lexicalRel` is strict. -/
theorem not_lexicalRel_le_ofFun (enc : SExp → String) :
    ¬ lexicalRel ≤ EncRel.ofFun enc :=
  fun h => lexicalRel_not_deterministic ((EncRel.ofFun_deterministic enc).anti h)

/-- The same for whole files. -/
theorem not_streamRel_le_ofFun (enc : List SExp → String) :
    ¬ streamRel ≤ EncRel.ofFun enc :=
  fun h => not_streamRel_deterministic ((EncRel.ofFun_deterministic enc).anti h)

/-- `renderRel width < lexicalRel` strictly, for every width. -/
theorem renderRel_lt_lexicalRel (width : Nat) : renderRel width < lexicalRel := by
  refine lt_of_le_of_ne (render_le_lexicalRel width) fun h => ?_
  have hle : renderRel width ≤ EncRel.ofFun (SExp.render width) := EncRel.restrict_le _ _
  rw [h] at hle
  exact not_lexicalRel_le_ofFun _ hle

/-- `astFileRel width < streamRel` strictly, for every width. -/
theorem astFileRel_lt_streamRel (width : Nat) : astFileRel width < streamRel := by
  refine lt_of_le_of_ne (astFile_le_streamRel width) fun h => ?_
  have hle : astFileRel width ≤ EncRel.ofFun (SExp.astFile width) := EncRel.restrict_le _ _
  rw [h] at hle
  exact not_streamRel_le_ofFun _ hle

/-- Dually to `not_lexicalRel_le_ofFun`: functionality says the convention
*does* lie below the graph of some decoder, so a verified parser is possible
in principle.  (Building one is separate work; this existence statement is
classical.) -/
theorem exists_decoder_above_lexicalRel :
    ∃ dec : String → Option SExp, lexicalRel ≤ EncRel.ofDecoder dec :=
  EncRel.functional_iff_le_ofDecoder.mp lexicalRel_functional

/-- The same for whole files. -/
theorem exists_decoder_above_streamRel :
    ∃ dec : String → Option (List SExp), streamRel ≤ EncRel.ofDecoder dec :=
  EncRel.functional_iff_le_ofDecoder.mp streamRel_functional

/-! ## Comparison with the other S-expression conventions in this tree

`Lexical.lean`'s own comparison section lists the three conventions.  The
state of the tree, checked rather than assumed: **there is no
`EncRel String SExp` for WAT or for Scheme/Lisp anywhere in `Silmaril/`.**
`grep -rn "EncRel" Silmaril/Formats/SExp/` finds nothing at all, and outside
this SpecTec subtree the only `EncRel String _` definitions in the repository
are `base64Rel` (`Silmaril/Encoding/Base64.lean:223`), the generic
`BinarySyntax.latin1Rel` (`Silmaril/Encoding/SyntaxCarriers.lean:163`), and
the JSON family in `Silmaril/Formats/Json/`.  So there is nothing to compare
*as a lattice element*; naming an inequality would mean naming a relation that
does not exist.  What does exist is:

* `Silmaril/Formats/SExp/Parser.lean` — a total Lisp parser
  (`SExpParser.parseLexemes?`), not a relation.  Its whitespace class
  (`Parser.lean:38`) is `' '`, `'\t'`, `'\n'`, `'\r'`; `';'` starts a line
  comment (`Parser.lean:81`, where `delimiter` includes it); `'.'` in
  delimiter position is a dotted pair (`Parser.lean:83`); string escapes are
  *decoded*, so `\n` becomes a newline and the quotation marks are not part of
  the atom's value.
* `Silmaril/Wasm/Wat/Lexer.lean` — an elaboration-time (`meta`) WAT lexer
  returning `Except String`, again not a relation.  Its whitespace class
  (`Lexer.lean:50`) is the same four characters, `;;` starts a line comment
  and `(;` a nested block comment (`Lexer.lean:189-190`), identifiers are
  restricted to `idChar` (`Lexer.lean:52`), and atoms carry bytes, not text.
* `Silmaril/Formats/SExp/Rivest.lean` — Rivest canonical S-expressions, whose
  carrier is `Bytes`, with length-prefixed verbatim atoms and no layout at
  all.

Against those, the SpecTec convention is deliberately minimal:

* the only layout characters are `' '` and `'\n'` (`IsSpace`), because those
  are the only ones `Util.Sexpr.pp` emits (`spectec/src/util/sexpr.ml:21-22`);
  `'\t'` and `'\r'` are ordinary token characters here (`isBare_tab`,
  `isBare_cr`), where both other lexers treat them as whitespace;
* there are no comments, so a WAT or Lisp comment lexes as atoms
  (`lexicalRel_semicolons`);
* a bare atom is a maximal run of non-layout, non-parenthesis, non-quote
  characters, with no further character class — no `#` syntax, no `'`
  quotation, no `$` identifiers, no dotted pairs
  (`isBare_hash`, `isBare_dollar`, `isBare_apostrophe`, `isBare_dot` in
  `Lexical.lean`);
* a quoted atom keeps its own quotation marks and its OCaml escapes
  *verbatim*: `Backend_ast.Print.text`
  (`spectec/src/backend-ast/print.ml:12`) builds `Atom ("\"" ^ escaped t ^
  "\"")`, so the atom's string is the spelling, escapes and all
  (`lexicalRel_atom_quoted`, `lexicalRel_escaped_atom`).  Nothing is decoded,
  which is what makes the convention functional with no side conditions;
* a node's head is a *string*, not a nested expression, and it must follow the
  `(` immediately (`LexesPre.node_head_bare`); `( a b)` and `(1 2)` are not
  spellings of anything. -/

/-- `'\t'` is an ordinary bare character here, though it is whitespace for
both the WAT lexer (`Silmaril/Wasm/Wat/Lexer.lean:50`) and the Lisp parser
(`Silmaril/Formats/SExp/Parser.lean:38`). -/
theorem isBare_tab : IsBare '\t' := by decide

/-- `'\r'` is likewise an ordinary bare character. -/
theorem isBare_cr : IsBare '\r' := by decide

/-- A quoted token spells the atom that carries it; unlike the Lisp parser,
the quotation marks and escapes are part of the atom's string. -/
theorem lexicalRel_atom_quoted (s : String) (h : IsQuotedToken s) :
    lexicalRel s (.atom s) := by
  have hpre : LexesPre (s.toList ++ []) (.atom s) [] := .quoted h
  rw [List.append_nil] at hpre
  exact .intro (w := []) spaces_nil spaces_nil hpre

/-- A line comment in either of the other conventions is a single bare atom
here. -/
theorem lexicalRel_semicolons : lexicalRel "a;;b" (.atom "a;;b") :=
  lexicalRel_atom_bare _ (by decide)

/-- A tab inside a token does not end it. -/
theorem lexicalRel_tab : lexicalRel "a\tb" (.atom "a\tb") :=
  lexicalRel_atom_bare _ (by decide)

/-- The spelling of the escaped text `"a\n"` is the five-character string
`"a\n"` including its quotation marks, and that whole string is the atom
(`spectec/src/backend-ast/print.ml:12`). -/
theorem lexicalRel_escaped_atom : lexicalRel "\"a\\n\"" (.atom "\"a\\n\"") :=
  lexicalRel_atom_quoted _ (by decide)

/-- A node's head is a bare token that follows the `(` immediately: the second
character of any node spelling is a bare character
(`spectec/src/util/sexpr.ml:23`, where the rope is `"(" ^+ s ^+ …`).  There is
no room for layout, and no nested expression, in head position. -/
theorem LexesPre.node_head_bare {l : List Char} {t : String} {es : List SExp}
    {r : List Char} (h : LexesPre l (.node t es) r) :
    ∃ c rest, l = '(' :: c :: rest ∧ IsBare c := by
  rcases h.inv with ⟨s, -, -, -, hne⟩ | ⟨s, -, -, hne⟩ | ⟨t', es', body, ht, -, -, hl, -⟩
  · exact absurd hne (by simp)
  · exact absurd hne (by simp)
  · obtain ⟨c, cs, hc, hb⟩ := ht.head
    exact ⟨c, cs ++ body, by rw [hl, hc]; rfl, hb⟩

end Silmaril.SpecTec
