module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Grammar
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Text6x
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Text6x
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# The wasm-3.0 text format, and the carrier its grammar needs

`Silmaril/SpecTec/Errata/Text6x.lean` builds `wasm30text6x`, the pinned
wasm-3.0 script with the nine §6.x patches of `#677`.  This
file opens the text-format area against it.  Everything is relative to the pin
`608711107b7f1edb13efd57b7d79b49477462d36`.

## The carrier, and why `Sem/Grammar.lean`'s is the wrong one

`Sem/Grammar.lean` gives a `GramD` a denotation as an
`EncRel (List UInt8) Value`.  **That relation is empty on the whole of §6**,
for two independent reasons, and both are theorems here rather than remarks.

*The carrier.*  `grammar Tchar : char = U+0000 | … | U+10FFFF`
(`specification/wasm-3.0/6.0-text.lexical.spectec:7-8`) elaborates to two
`RangeG`s whose bounds are `0xD7FF`, `0xE000` and `0x10FFFF`.
`Sem.rangeSym` (`Sem/Grammar.lean:417`) sends a range outside `[0x00, 0xFF]`
to `Sym.alt []`, because the framework of `Silmaril/SpecTec/Grammar/Basic.lean`
fixes its terminals to be bytes (`Basic.lean:118,135`).  So
`gramRelSup_tchar_eq_bot`: the pinned `Tchar` denotes `⊥`, and so does every
§6 grammar that reaches a character.

*The arity.*  Independently of the carrier, `Sem.Act` makes a symbol
contribute a *list* of values, with `EpsG`, `SeqG` and `AltG` contributing the
empty list — the unit of the attribute monoid — rather than the unit *value*
of `TupT []`, which is the type `spectec/src/il/valid.ml:589-595` assigns
them.  An `AttrG (e, g)` therefore has no derivation unless `g` happens to
contribute exactly one value.  `Sem/Grammar.lean:129` records this and adds
"It does not occur in the pinned corpus either"; that is true of §5 and
**false of §6**.  A structural scan of `specs/spectec/wasm-3.0.ast` finds
seventeen grammars containing an `AttrG` whose body can never contribute one
value — `Tannot`, `Tblockchar`, `Tblockcomment`, `Teof`, `Texportdots`,
`Texportfuncdots_`, `Texportglobaldots_`, `Texportmemdots_`,
`Texporttabledots_`, `Texporttagdots_`, `TfNplain`, `Timportdots`,
`Tkeyword`, `Tlinecomment`, `Tnewline`, `TsNplain`, `TuNplain` — all of them
text grammars, none binary.  The reason is systematic: `short_prod`
(`spectec/src/frontend/parser.mly:137-140`) wraps *every* production written
without an explicit attribute in an `AttrG`, and §6 is written that way
throughout.  `not_gramRelSup_tnewline_crlf` is the smallest witness whose
terminals are all bytes: the pinned `Tnewline` has no byte derivation for
`U+000D U+000A`, although its other two productions are plain byte terminals
and the symbol is reachable over bytes.

**The decision.**  The carrier is `Codes := List Nat`, lists of Unicode
scalar values, with a fresh denotation `Derives` over it, and the bridge to
bytes is `EncRel.push` along UTF-8 (`Silmaril/Encoding/Relation.lean:100`),
packaged as `textByteRel`.  Three reasons:

1. `List Nat` is the IL's *own* terminal type.  `valid_sym` types `NumG` and
   `RangeG` as `NumT NatT` with the byte bound **commented out**
   (`spectec/src/il/valid.ml:582-587`), and the pinned stream relies on that:
   it contains `(range (num 0x00) (num 0xD7FF))`.  The byte carrier is the
   specialization §5 happens to live in, not the general case.
2. The framework's `Sym` hard-codes `UInt8` terminals, and this file may not
   edit it.  The alternative that would have reused it — decomposing a scalar
   `RangeG` into a union of byte-range sequences inside `Sym`, as a regex
   engine does — is possible, but it makes `Tchar`'s attribute a derived
   decode of one to four bytes and turns every lexical theorem into a
   statement about byte strings.  `valid.ml:596-601` says the symbol's value
   *is* the scalar; a denotation should say so too.
3. `push` is the right direction.  A text file is bytes, `Tsource = Tchar*`
   (`6.0-text.lexical.spectec:10-11`) is characters, and UTF-8 is the map
   between them; `utf8Codes_codes` checks that it agrees with
   `Silmaril/Encoding/Unicode.lean`'s `utf8` on every literal terminal, so a
   `TextG` means the same thing on both sides of the bridge.
   `textByteRel_blockcomment_semis_text6x` is the payoff: a statement about
   `List UInt8` in a place where `Sem.gramRelSup` has nothing to say.

`Derives` also repairs the arity problem, since it has to be re-derived
anyway: a symbol contributes **one value, of its own type** —
`TupT []`'s unit for `EpsG`/`SeqG`/`AltG` (`valid.ml:589-595`) and the text
for `TextG` (`valid.ml:588`).  Bindings still travel in the scope, through
`AttrG`'s `MatchExp`, so nothing is lost by dropping the list.  Clause for
clause `Derives` is otherwise `Sem.SymDerives`, and the correspondence is
spelled out on the inductive.

## The Silmaril side of §6, and why there is no equivalence theorem yet

`Equiv/BinaryValues.lean` and friends compare the elaborated §5 grammar
against `Silmaril/Wasm/Binary/Basic.lean`'s `Encodes` relations, which are
ordinary inductive `Prop`s.  §6 has no such counterpart.  Silmaril's text
layer is `Silmaril/Wasm/Wat/` — a lexer (`Wat/Lexer.lean`), a parser and a
name resolver behind the `wat3!` quotations — and every one of its thirteen
modules sits in a `public meta section`: it is an *elaboration-time* program
in `Except String`, run by a macro, with no `Prop`-level relation at all.
`docs/projects/wasm.md` says so outright ("The parser has not been proved
equivalent to the specification").  A grep for `Encodes` over
`Silmaril/Wasm/` finds only binary-format relations.

So the right counterpart does not exist yet, and the first job is the one
this file does: give the SpecTec text grammar a denotation that *could* be
compared — an `EncRel` over the carrier the grammar actually uses, and a
bridge from it to the byte strings a `.wat` file is made of.

## What is proved

* `gramRelSup_tchar_eq_bot`, `not_gramRelSup_tnewline_crlf` — the two
  obstacles, at the pinned and corrected scripts.
* `Derives`/`DerivesSeq`/`DerivesRounds`, `charRel`, `textByteRel`, and one
  inversion per constructor.
* `tchar_iff` and `tidchar_iff`: the pinned `Tchar` and `Tidchar` derive
  exactly the one-character strings `6.0-text.lexical.spectec:7-8` and
  `6.1-text.values.spectec:123-128` describe, with value `%(n)`, and
  `isChar_of_isIdChar`.
* **`#665`, both halves.**  `blockchar_lastNotSemi`: no
  `Tblockchar` derivation ends in `;`, because the three character
  productions end in a `Tchar` their premise forbids to be `;` and the fourth
  is a nested block comment, which ends in `)`.  Hence
  `not_derives_blockcomment_semis_wasm30`: the pinned `Tblockcomment` has **no
  derivation** for `test/core/comments.wast:26`'s `(;;;;;;;;;;;;;;)`.  And
  `derives_blockcomment_semis_text6x`: the corrected one does, with the
  `";"*` run the patch inserts taking all twelve.
* `tspace_one_item`: `Tspace` derives exactly *one* white-space item.  See
  below.

## A defect found on the way: the singleton-list cast on the left

`elab.ml:2020-2022` coerces `e : t` to type `t*` by wrapping it in a
one-element list, `Il.ListE [e']`, and `elab_exp` applies that coercion on
`~side:`Lhs`` as well, where the result is a *binding pattern* rather than a
computation.  A production written `| g*` with no attribute therefore
elaborates to `AttrG (ListE [x], IterG (g, List))`, and `match_list`
(`spectec/src/il/eval.ml:93-99`) makes that pattern match only a one-element
list: the iteration is forced to have exactly one round.

Six grammars of the pinned wasm-3.0 stream carry such a pattern —
`Tannotid`, `Tdecldots_`, `Treserved`, `Tsource`, `Tspace`, and `Ttoken`'s
`Tstring` production.  The consequences are severe and, as far as
we know, unreported: `Tsource = Tchar*` derives exactly one
character, so no text file longer than one character has a derivation;
`Tspace = (" " | Tformat | Tcomment | Tannot)*` derives exactly one
white-space item, so it is neither empty nor repeatable (`tspace_one_item`);
and `Treserved`'s `+` run collapses to one item, which happens to mask the
longest-match defect `#694` corrects but is not a fix for it.  This is an
elaborator defect, not a `.spectec` defect: the sources really do write `*`
and `+`.

## What is *not* proved

* The reference lexer is not modelled.  `Errata/Text6x.lean` records an
  exhaustive comparison of the corrected `Tblockcomment` against
  `interpreter/text/lexer.mll:902-907` over 1 398 101 bodies; nothing here
  replaces it.  What is proved is the *structural* reason the pinned grammar
  fails — `blockchar_lastNotSemi` — together with the decisive example in
  both directions.  Nesting, the other half of `#665`, is untouched.
* `Tstring`, `Tstringchar` (`#661`), `Tname`, `Tid`, `Tnum`, `Thexnum`,
  `Tfloat` and `Thexfloat` (`#662`, and `#803` for the
  `int`/`nat` narrowing) are not reached.  `Tid` and `Treserved` need
  `Tstring`, and `Tstring` needs `Tstringchar`'s `$utf8` call, which is a
  `DecD` the evaluator has to run.
* `Derives` is not proved *here* to agree with `Sem.gramRelSup` on grammars
  where both are non-trivial.  It cannot be, as stated: the two differ on the
  arity question by design.  `Equiv/TextBridge.lean` pins the exact
  relationship — `push utf8Codes` of `charRel` *is* `gramRelSup` on the ASCII,
  single-valued fragment, and the pinned `Tidchar` is in it.
* Nothing is claimed about `Sem.Act`'s treatment being *wrong* for §5: the
  seventeen grammars above are all text grammars, and `Equiv/BinaryValues.lean`
  and friends are unaffected.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv.Text

open Silmaril.SpecTec.IL hiding Id Prod Sym
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Grammar

set_option maxRecDepth 100000

/-! ## The byte denotation is empty on the text grammar -/

/-- `RangeG (NumG lo, NumG hi)` with a bound outside `[0x00, 0xFF]` has no
*byte* derivation: `Sem.rangeSym` sends it to `Sym.alt []`.  This is the
missing companion of `Sem.symDen_numG_of_not_lt`. -/
theorem symDen_rangeG_of_not_lt (env : Env) {lo hi : Nat} (h : ¬ (lo < 256 ∧ hi < 256)) :
    symDen env (.rangeG (.numG lo) (.numG hi)) = ⊥ := by
  have hb : rangeSym (.numG lo) (.numG hi) = (Grammar.Sym.alt [] : Grammar.Sym NT Act) := by
    simp [rangeSym, h]
  show denote (gramOf env) (rangeSym (.numG lo) (.numG hi)) = _
  rw [hb, denote_alt]
  rfl


/-! ## The §6.0 lexical grammars, as the stream spells them -/

/-- `<implicit-prod-result>`, the variable the parser introduces for a
production written without an attribute (`spectec/src/frontend/parser.mly:137`). -/
def implicitId : IL.Id := "<implicit-prod-result>"

/-- The value expression such a production gets: `short_prod` builds
`SynthP (AttrG (x, g), x, prems)` (`spectec/src/frontend/parser.mly:137-140`),
and elaboration casts `x` to the grammar's `TupT []` as the second component
of `(x, ())`. -/
def unitResult : Exp := .projE (.tupE [.varE implicitId, .tupE []]) 1

/-- A production written `| g  -- prems` whose grammar is `TupT []`-typed. -/
def shortProd (t : Typ) (g : IL.Sym) (prems : List Prem) : IL.Prod :=
  .prodD [.expP implicitId t] (.attrG (.varE implicitId) g) unitResult prems

/-- `shortProd` with the extra quantifier `c : char` that the
character-restricted productions of `Tlinechar` and `Tblockchar` carry. -/
def shortProdC (t : Typ) (g : IL.Sym) (prems : List Prem) : IL.Prod :=
  .prodD [.expP implicitId t, .expP "c" (.varT "char" [])]
    (.attrG (.varE implicitId) g) unitResult prems

/-- A production of a `char`-valued grammar: a single terminal, bound to the
implicit result and returned as the one-field variant `%(n)`. -/
def charProd (g : IL.Sym) : IL.Prod :=
  .prodD [.expP implicitId (.numT .natT)] (.attrG (.varE implicitId) g)
    (.caseE "%" (.tupE [.varE implicitId])) []

/-- A one-character terminal of the lexical grammar: a literal scalar
(`NumG`) or a scalar range (`RangeG`).  `Tchar`, `Tidchar` and the six
punctuation alternatives of the corrected `Treserved` are exactly lists of
these. -/
inductive Term where
  /-- `NumG n`. -/
  | lit (n : Nat)
  /-- `RangeG (NumG lo, NumG hi)`. -/
  | range (lo hi : Nat)
  deriving DecidableEq, Repr

/-- The IL symbol a `Term` is. -/
def Term.sym : Term → IL.Sym
  | .lit n => .numG n
  | .range lo hi => .rangeG (.numG lo) (.numG hi)

/-- The scalars a `Term` admits. -/
def Term.Mem : Term → Nat → Prop
  | .lit n, m => m = n
  | .range lo hi, m => lo ≤ m ∧ m ≤ hi

instance (τ : Term) (n : Nat) : Decidable (τ.Mem n) := by
  cases τ <;> unfold Term.Mem <;> infer_instance

/-- A grammar whose productions are one `charProd` per terminal. -/
def charProdsOf (τs : List Term) : List IL.Prod := τs.map fun τ => charProd τ.sym

/-- `grammar Tchar : char = U+0000 | ... | U+D7FF | U+E000 | ... | U+10FFFF`
(`specification/wasm-3.0/6.0-text.lexical.spectec:7-8`). -/
def tcharTerms : List Term := [.range 0x00 0xD7FF, .range 0xE000 0x10FFFF]

/-- `Tchar`, as elaborated. -/
def tcharProds : List IL.Prod := charProdsOf tcharTerms

/-- `grammar Tidchar : char`
(`specification/wasm-3.0/6.1-text.values.spectec:123-128`): three ranges and
twenty-three single characters. -/
def tidcharTerms : List Term :=
  [.range 0x30 0x39, .range 0x41 0x5A, .range 0x61 0x7A, .lit 0x21, .lit 0x23, .lit 0x24,
    .lit 0x25, .lit 0x26, .lit 0x27, .lit 0x2A, .lit 0x2B, .lit 0x2D, .lit 0x2E, .lit 0x2F,
    .lit 0x3A, .lit 0x3C, .lit 0x3D, .lit 0x3E, .lit 0x3F, .lit 0x40, .lit 0x5C, .lit 0x5E,
    .lit 0x5F, .lit 0x60, .lit 0x7C, .lit 0x7E]

/-- `Tidchar`, as elaborated. -/
def tidcharProds : List IL.Prod := charProdsOf tidcharTerms

/-- `c =/= %(a) /\ c =/= %(b)`, the premise shape of `Tlinechar` and
`Tblockchar`, with `c` compared against the one-field variant of a scalar. -/
def neTwo (a b : Nat) : Prem :=
  .ifPr (.binE .andOp .boolT
    (.cmpE .neOp .boolT (.varE "c") (.caseE "%" (.tupE [.numE (.natN a)])))
    (.cmpE .neOp .boolT (.varE "c") (.caseE "%" (.tupE [.numE (.natN b)]))))

/-- `grammar Tlinechar = c:Tchar -- if c =/= U+0A /\ c =/= U+0D`
(`specification/wasm-3.0/6.0-text.lexical.spectec:53-54`).  The pinned
premise projects out of the variant, `c!%.0 =/= 10`, rather than comparing
variants. -/
def tlinecharProds : List IL.Prod :=
  [shortProdC (.varT "char" []) (.attrG (.varE "c") (.varG "Tchar" []))
    [.ifPr (.binE .andOp .boolT
      (.cmpE .neOp .boolT (.projE (.uncaseE (.varE "c") "%") 0) (.numE (.natN 10)))
      (.cmpE .neOp .boolT (.projE (.uncaseE (.varE "c") "%") 0) (.numE (.natN 13))))]]

/-- `grammar Teof = ""` (`specification/wasm-3.0/6.0-text.lexical.spectec:51`). -/
def teofProds : List IL.Prod := [shortProd .textT (.textG "") []]

/-- `grammar Tnewline = U+0A | U+0D | U+0D U+0A`
(`specification/wasm-3.0/6.0-text.lexical.spectec:38-39`). -/
def tnewlineProds : List IL.Prod :=
  [shortProd (.numT .natT) (.numG 0x0A) [], shortProd (.numT .natT) (.numG 0x0D) [],
    shortProd (.tupT []) (.seqG [.seqG [.numG 0x0D], .seqG [.numG 0x0A]]) []]

/-- `grammar Tformat = Tnewline | U+09`
(`specification/wasm-3.0/6.0-text.lexical.spectec:35-36`). -/
def tformatProds : List IL.Prod :=
  [shortProd (.tupT []) (.varG "Tnewline" []) [], shortProd (.numT .natT) (.numG 0x09) []]

/-- `grammar Tcomment = Tlinecomment | Tblockcomment`
(`specification/wasm-3.0/6.0-text.lexical.spectec:44-45`). -/
def tcommentProds : List IL.Prod :=
  [shortProd (.tupT []) (.varG "Tlinecomment" []) [],
    shortProd (.tupT []) (.varG "Tblockcomment" []) []]

/-- `grammar Tlinecomment = ";;" Tlinechar* (Tnewline | Teof)`
(`specification/wasm-3.0/6.0-text.lexical.spectec:48-49`). -/
def tlinecommentProds : List IL.Prod :=
  [shortProd (.tupT [])
    (.seqG [.seqG [.textG ";;"], .seqG [.iterG (.varG "Tlinechar" []) (.mk .list [])],
      .altG [.varG "Tnewline" [], .varG "Teof" []]]) []]

/-- `grammar Tspace = (" " | Tformat | Tcomment | Tannot)*`
(`specification/wasm-3.0/6.0-text.lexical.spectec:32-33`).  The binding
pattern is `[x]`, a **singleton list**, not `x*`; see `tspace_iff`. -/
def tspaceProds : List IL.Prod :=
  [.prodD [.expP implicitId (.tupT [])]
    (.attrG (.listE [.varE implicitId])
      (.iterG (.altG [.seqG [.textG " "], .varG "Tformat" [], .varG "Tcomment" [],
        .varG "Tannot" []]) (.mk .list [])))
    unitResult []]

/-- `grammar Tblockcomment = "(;" Tblockchar* ";)"` as pinned
(`specification/wasm-3.0/6.0-text.lexical.spectec:56-57`). -/
def tblockcommentProds : List IL.Prod :=
  [shortProd (.tupT [])
    (.seqG [.seqG [.textG "(;"], .seqG [.iterG (.varG "Tblockchar" []) (.mk .list [])],
      .seqG [.textG ";)"]]) []]

/-- `Tblockcomment` with `#665`'s patch: a run of semicolons
may precede the closing delimiter. -/
def tblockcommentProdsC : List IL.Prod :=
  [shortProd (.tupT [])
    (.seqG [.seqG [.textG "(;"], .seqG [.iterG (.varG "Tblockchar" []) (.mk .list [])],
      .seqG [.iterG (.textG ";") (.mk .list [])], .seqG [.textG ";)"]]) []]

/-- `grammar Tblockchar` as pinned
(`specification/wasm-3.0/6.0-text.lexical.spectec:60-64`). -/
def tblockcharProds : List IL.Prod :=
  [shortProdC (.varT "char" []) (.attrG (.varE "c") (.varG "Tchar" [])) [neTwo 59 40],
    shortProdC (.tupT [])
      (.seqG [.seqG [.iterG (.textG ";") (.mk .list1 [])],
        .seqG [.attrG (.varE "c") (.varG "Tchar" [])]]) [neTwo 59 41],
    shortProdC (.tupT [])
      (.seqG [.seqG [.iterG (.textG "(") (.mk .list1 [])],
        .seqG [.attrG (.varE "c") (.varG "Tchar" [])]]) [neTwo 59 40],
    shortProd (.tupT []) (.varG "Tblockcomment" []) []]

/-- `Tblockchar` with `#665`'s patch: the semicolon run no
longer has to be followed by a non-`(` character, and the third and fourth
alternatives gain a `";"*` prefix. -/
def tblockcharProdsC : List IL.Prod :=
  [shortProdC (.varT "char" []) (.attrG (.varE "c") (.varG "Tchar" [])) [neTwo 59 40],
    shortProdC (.tupT [])
      (.seqG [.seqG [.iterG (.textG ";") (.mk .list1 [])],
        .seqG [.attrG (.varE "c") (.varG "Tchar" [])]])
      [.ifPr (.binE .andOp .boolT
        (.binE .andOp .boolT
          (.cmpE .neOp .boolT (.varE "c") (.caseE "%" (.tupE [.numE (.natN 59)])))
          (.cmpE .neOp .boolT (.varE "c") (.caseE "%" (.tupE [.numE (.natN 41)]))))
        (.cmpE .neOp .boolT (.varE "c") (.caseE "%" (.tupE [.numE (.natN 40)]))))],
    shortProdC (.tupT [])
      (.seqG [.seqG [.iterG (.textG ";") (.mk .list [])],
        .seqG [.iterG (.textG "(") (.mk .list1 [])],
        .seqG [.attrG (.varE "c") (.varG "Tchar" [])]]) [neTwo 59 40],
    shortProd (.tupT [])
      (.seqG [.seqG [.iterG (.textG ";") (.mk .list [])],
        .seqG [.iterG (.textG "(") (.mk .list [])], .varG "Tblockcomment" []]) []]

/-- `grammar Treserved` as pinned
(`specification/wasm-3.0/6.0-text.lexical.spectec:26-27`). -/
def treservedProds : List IL.Prod :=
  [.prodD [.expP implicitId (.tupT [])]
    (.attrG (.listE [.varE implicitId])
      (.iterG (.altG [.seqG [.varG "Tidchar" []], .seqG [.varG "Tstring" []],
        .seqG [.textG ","], .seqG [.textG ";"], .seqG [.textG "["], .seqG [.textG "]"],
        .seqG [.textG "{"], .seqG [.textG "}"]]) (.mk .list1 [])))
    unitResult []]

/-- `Treserved` with `#694`'s patch: the six punctuation
characters become alternatives of their own. -/
def treservedProdsC : List IL.Prod :=
  [.prodD [.expP implicitId (.tupT [])]
    (.attrG (.listE [.varE implicitId])
      (.iterG (.altG [.seqG [.varG "Tidchar" []], .seqG [.varG "Tstring" []]])
        (.mk .list1 [])))
    unitResult [],
    shortProd (.numT .natT) (.numG 0x2C) [], shortProd (.numT .natT) (.numG 0x3B) [],
    shortProd (.numT .natT) (.numG 0x5B) [], shortProd (.numT .natT) (.numG 0x5D) [],
    shortProd (.numT .natT) (.numG 0x7B) [], shortProd (.numT .natT) (.numG 0x7D) []]

/-! ### Provenance -/

/-- The pinned environment. -/
noncomputable abbrev envPinned : Env := envOfScript Specs.wasm30

/-- The corrected environment: `Errata.Text6x.wasm30text6x`, the pinned
wasm-3.0 script with the nine patches of `#677`. -/
noncomputable abbrev envCorrected : Env := envOfScript IL.Text6x.wasm30text6x

private theorem findGram_tchar_pinned :
    envPinned.findGram? "Tchar" = some ([], .varT "char" [], tcharProds) := rfl

private theorem findGram_tidchar_pinned :
    envPinned.findGram? "Tidchar" = some ([], .varT "char" [], tidcharProds) := rfl

private theorem findGram_tlinechar_pinned :
    envPinned.findGram? "Tlinechar" = some ([], .tupT [], tlinecharProds) := rfl

private theorem findGram_teof_pinned :
    envPinned.findGram? "Teof" = some ([], .tupT [], teofProds) := rfl

private theorem findGram_tnewline_pinned :
    envPinned.findGram? "Tnewline" = some ([], .tupT [], tnewlineProds) := rfl

private theorem findGram_tformat_pinned :
    envPinned.findGram? "Tformat" = some ([], .tupT [], tformatProds) := rfl

private theorem findGram_tcomment_pinned :
    envPinned.findGram? "Tcomment" = some ([], .tupT [], tcommentProds) := rfl

private theorem findGram_tlinecomment_pinned :
    envPinned.findGram? "Tlinecomment" = some ([], .tupT [], tlinecommentProds) := rfl

private theorem findGram_tspace_pinned :
    envPinned.findGram? "Tspace" = some ([], .tupT [], tspaceProds) := rfl

private theorem findGram_tblockcomment_pinned :
    envPinned.findGram? "Tblockcomment" = some ([], .tupT [], tblockcommentProds) := rfl

private theorem findGram_tblockchar_pinned :
    envPinned.findGram? "Tblockchar" = some ([], .tupT [], tblockcharProds) := rfl

private theorem findGram_treserved_pinned :
    envPinned.findGram? "Treserved" = some ([], .tupT [], treservedProds) := rfl

private theorem findGram_tchar_corrected :
    envCorrected.findGram? "Tchar" = some ([], .varT "char" [], tcharProds) := rfl

private theorem findGram_tidchar_corrected :
    envCorrected.findGram? "Tidchar" = some ([], .varT "char" [], tidcharProds) := rfl

private theorem findGram_tlinechar_corrected :
    envCorrected.findGram? "Tlinechar" = some ([], .tupT [], tlinecharProds) := rfl

private theorem findGram_teof_corrected :
    envCorrected.findGram? "Teof" = some ([], .tupT [], teofProds) := rfl

private theorem findGram_tnewline_corrected :
    envCorrected.findGram? "Tnewline" = some ([], .tupT [], tnewlineProds) := rfl

private theorem findGram_tformat_corrected :
    envCorrected.findGram? "Tformat" = some ([], .tupT [], tformatProds) := rfl

private theorem findGram_tcomment_corrected :
    envCorrected.findGram? "Tcomment" = some ([], .tupT [], tcommentProds) := rfl

private theorem findGram_tlinecomment_corrected :
    envCorrected.findGram? "Tlinecomment" = some ([], .tupT [], tlinecommentProds) := rfl

private theorem findGram_tspace_corrected :
    envCorrected.findGram? "Tspace" = some ([], .tupT [], tspaceProds) := rfl

private theorem findGram_tblockcomment_corrected :
    envCorrected.findGram? "Tblockcomment" = some ([], .tupT [], tblockcommentProdsC) := rfl

private theorem findGram_tblockchar_corrected :
    envCorrected.findGram? "Tblockchar" = some ([], .tupT [], tblockcharProdsC) := rfl

private theorem findGram_treserved_corrected :
    envCorrected.findGram? "Treserved" = some ([], .tupT [], treservedProdsC) := rfl


/-! ## Nothing in §6 has a byte derivation

Two independent obstacles, each a theorem. -/

/-- A `RangeG` whose bounds are not bytes derives nothing. -/
theorem not_symDerives_rangeG {env : Env} {ρ ρ' : VarEnv} {bs : Grammar.Bytes}
    {l : List Value} {lo hi : Nat} (h : ¬ (lo < 256 ∧ hi < 256)) :
    ¬ SymDerives env ρ (.rangeG (.numG lo) (.numG hi)) bs l ρ' := by
  rintro ⟨a, ha, -⟩
  rw [symDen_rangeG_of_not_lt env h] at ha
  exact ha

/-- The body of a production whose symbol is an `AttrG`, read off
`Sem.ProdDerives`: the inner symbol derives the same bytes and contributes
exactly one value. -/
theorem symDerives_of_prodDerives {env : Env} {ρ : VarEnv} {qs : List Param}
    {e ev : Exp} {g : IL.Sym} {prems : List Prem} {bs : Grammar.Bytes} {l : List Value}
    (h : ProdDerives env ρ [] [] (.prodD qs (.attrG e g) ev prems) bs l) :
    ∃ ρ₀ v ρ₁, SymDerives env ρ₀ (substSym [] g) bs [v] ρ₁ := by
  obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v, hws, hbp, hs, hpr, hev, hl⟩ := h
  obtain ⟨w, ρ₃, hw, hl₂, hm⟩ := symDerives_attrG.mp hs
  exact ⟨ρ₀, w, ρ₃, hw⟩

/-- **The carrier obstacle.**  `Tchar` has no byte derivation at all: both of
its productions are a scalar range above `0xFF`
(`specification/wasm-3.0/6.0-text.lexical.spectec:7-8`), and `Sem.rangeSym`
sends such a range to `Sym.alt []`.  Every §6 grammar that reaches a
character goes through `Tchar`, so the whole text format denotes `⊥` in
`Sem/Grammar.lean`'s `EncRel (List UInt8) Value`. -/
theorem gramRelSup_tchar_eq_bot {env : Env}
    (h : env.findGram? "Tchar" = some ([], .varT "char" [], tcharProds)) (ρ : VarEnv) :
    gramRelSup env ρ (.varG "Tchar" []) = ⊥ := by
  funext bs v
  refine propext ⟨fun hv => ?_, fun hv => hv.elim⟩
  obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp hv
  rw [symDerives_varG h] at hd
  obtain ⟨-, p, hp, hpd⟩ := hd
  have hcases : p = charProd (.rangeG (.numG 0x00) (.numG 0xD7FF)) ∨
      p = charProd (.rangeG (.numG 0xE000) (.numG 0x10FFFF)) := by
    simpa [tcharProds, charProdsOf, tcharTerms, Term.sym] using hp
  rcases hcases with rfl | rfl <;>
    · simp only [charProd] at hpd
      obtain ⟨ρ₀, w, ρ₁, hw⟩ := symDerives_of_prodDerives hpd
      exact not_symDerives_rangeG (by omega) hw

/-- The two-byte sequence `U+000D U+000A` contributes *two* values, so no
`AttrG` over it has a derivation. -/
theorem not_symDerives_crlf {env : Env} {ρ ρ' : VarEnv} {bs : Grammar.Bytes} {v : Value} :
    ¬ SymDerives env ρ (.seqG [.seqG [.numG 0x0D], .seqG [.numG 0x0A]]) bs [v] ρ' := by
  intro h
  obtain ⟨b₁, l₁, ρ₁, b₂, l₂, h₁, h₂, hb, hl⟩ := symDerives_seqG_cons.mp h
  obtain ⟨c₁, m₁, σ₁, c₂, m₂, k₁, k₂, hc, rfl⟩ := symDerives_seqG_cons.mp h₁
  obtain ⟨hd₁, rfl, hd₂⟩ := (symDerives_numG (n := 0x0D) (by omega)).mp k₁
  obtain ⟨he₁, rfl, he₂⟩ := symDerives_seqG_nil.mp k₂
  obtain ⟨c₃, m₃, σ₃, c₄, m₄, k₃, k₄, hf, rfl⟩ := symDerives_seqG_cons.mp h₂
  obtain ⟨hi₁, rfl, hi₂⟩ := symDerives_seqG_nil.mp k₄
  obtain ⟨c₅, m₅, σ₅, c₆, m₆, j₁, j₂, hj, rfl⟩ := symDerives_seqG_cons.mp k₃
  obtain ⟨hg₁, rfl, hg₂⟩ := (symDerives_numG (n := 0x0A) (by omega)).mp j₁
  obtain ⟨hk₁, rfl, hk₂⟩ := symDerives_seqG_nil.mp j₂
  simp at hl

/-- **The arity obstacle**, independent of the carrier.  `Sem/Grammar.lean`
gives `EpsG`, `SeqG` and `AltG` the *empty value list* — the unit of the
attribute monoid — rather than the unit *value* of `TupT []`, which is the
type `spectec/src/il/valid.ml:589-595` assigns them.  So `AttrG (e, g)` has no
derivation whenever `g` does not happen to contribute exactly one value, and
that is what every "short" production of §6 is: `short_prod`
(`spectec/src/frontend/parser.mly:137-140`) wraps the whole body in an
`AttrG`.

`Tnewline` (`specification/wasm-3.0/6.0-text.lexical.spectec:38-39`) is the
smallest witness whose terminals are all bytes, so the obstacle is visible
with no help from the carrier: its first two productions are single byte
terminals, and its third, `U+000D U+000A`, has no derivation. -/
theorem not_gramRelSup_tnewline_crlf {env : Env}
    (h : env.findGram? "Tnewline" = some ([], .tupT [], tnewlineProds)) (ρ : VarEnv)
    (v : Value) : ¬ gramRelSup env ρ (.varG "Tnewline" []) [0x0D, 0x0A] v := by
  intro hv
  obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp hv
  rw [symDerives_varG h] at hd
  obtain ⟨-, p, hp, hpd⟩ := hd
  have hcases : p = shortProd (.numT .natT) (.numG 0x0A) [] ∨
      p = shortProd (.numT .natT) (.numG 0x0D) [] ∨
      p = shortProd (.tupT []) (.seqG [.seqG [.numG 0x0D], .seqG [.numG 0x0A]]) [] := by
    simpa [tnewlineProds] using hp
  rcases hcases with rfl | rfl | rfl <;> simp only [shortProd] at hpd
  · obtain ⟨ρ₀, w, ρ₁, hw⟩ := symDerives_of_prodDerives hpd
    obtain ⟨hbs, -, -⟩ := (symDerives_numG (n := 0x0A) (by omega)).mp hw
    simp at hbs
  · obtain ⟨ρ₀, w, ρ₁, hw⟩ := symDerives_of_prodDerives hpd
    obtain ⟨hbs, -, -⟩ := (symDerives_numG (n := 0x0D) (by omega)).mp hw
    simp at hbs
  · obtain ⟨ρ₀, w, ρ₁, hw⟩ := symDerives_of_prodDerives hpd
    exact not_symDerives_crlf hw

/-! ## The character carrier

The denotation of §6, over `List Nat` rather than `List UInt8`. -/

/-- The carrier of the text grammar: a list of Unicode scalar values.  This
is the IL's own terminal type — `valid_sym` gives `NumG` and `RangeG` the type
`NumT NatT` with the byte bound *commented out*
(`spectec/src/il/valid.ml:582-601`), and the pinned stream uses it that way
(`(range (num 0x00) (num 0xD7FF))`). -/
abbrev Codes : Type := List Nat

/-- The scalar values of a literal terminal (`TextG`). -/
def codes (t : Text) : Codes := t.toList.map Char.toNat

/-- UTF-8, as a map of carriers `Codes → List UInt8`.  `EncRel.push` along
this is the bridge from the character denotation below to the byte world
`Sem/Grammar.lean` lives in. -/
def utf8Codes (cs : Codes) : Grammar.Bytes :=
  cs.flatMap fun n => String.utf8EncodeChar (Char.ofNat n)

/-- The carrier change is a monoid map, which is what makes it commute with
`SeqG`. -/
@[simp] theorem utf8Codes_append (cs ds : Codes) :
    utf8Codes (cs ++ ds) = utf8Codes cs ++ utf8Codes ds := List.flatMap_append

/-- `utf8Codes` agrees with `Silmaril/Encoding/Unicode.lean`'s `utf8` on the
scalars of a string, so a `TextG` terminal means the same thing on both sides
of the bridge. -/
theorem utf8Codes_codes (t : Text) : utf8Codes (codes t) = Unicode.utf8 t := by
  rw [Unicode.utf8_eq_flatMap, utf8Codes, codes, List.flatMap_map]
  refine List.flatMap_congr fun c _ => ?_
  rw [Char.ofNat_toNat]

mutual

/-- The denotation of an IL grammar symbol over **characters**:
`Derives env ρ g cs v ρ'` says that `g`, started in the scope `ρ`, derives the
scalar string `cs` with value `v` and leaves the scope `ρ'`.

Clause for clause this is `Sem.SymDerives` (`Sem/Grammar.lean`), with two
deliberate changes, both forced and both justified in the module docstring:

* the carrier is `Codes`, so `NumG n` is the scalar `n` for any `n` and
  `RangeG` is a scalar interval — `Sem.byteSym` and `Sem.rangeSym` send both
  to `Sym.alt []` outside `[0x00, 0xFF]`;
* a symbol contributes **one value, of its own type**, where `Sem.Act`
  contributes a list: `EpsG`, `SeqG` and `AltG` contribute the unit of
  `TupT []` and `TextG t` the text `t`, which is what
  `spectec/src/il/valid.ml:588-595` types them as.  Bindings still travel in
  the scope, through `AttrG`'s `MatchExp`, so nothing is lost by dropping the
  list. -/
inductive Derives (env : Env) : VarEnv → IL.Sym → Codes → Value → VarEnv → Prop where
  /-- `EpsG : TupT []` (`spectec/src/il/valid.ml:589`). -/
  | epsG {ρ : VarEnv} : Derives env ρ .epsG [] (.tuple []) ρ
  /-- `NumG n : NumT NatT` (`valid.ml:582-587`), a scalar terminal. -/
  | numG {ρ : VarEnv} {n : Nat} : Derives env ρ (.numG n) [n] (.num (.natN n)) ρ
  /-- `TextG t : TextT` (`valid.ml:588`). -/
  | textG {ρ : VarEnv} {t : Text} : Derives env ρ (.textG t) (codes t) (.text t) ρ
  /-- `RangeG (NumG lo, NumG hi) : NumT NatT` (`valid.ml:596-601`). -/
  | rangeG {ρ : VarEnv} {lo hi n : Nat} (h₁ : lo ≤ n) (h₂ : n ≤ hi) :
      Derives env ρ (.rangeG (.numG lo) (.numG hi)) [n] (.num (.natN n)) ρ
  /-- `SeqG gs : TupT []` (`valid.ml:590-592`): concatenation, with the scope
  threaded left to right. -/
  | seqG {ρ ρ' : VarEnv} {gs : List IL.Sym} {cs : Codes}
      (h : DerivesSeq env ρ gs cs ρ') : Derives env ρ (.seqG gs) cs (.tuple []) ρ'
  /-- `AltG gs : TupT []` (`valid.ml:593-595`). -/
  | altG {ρ ρ' : VarEnv} {g : IL.Sym} {gs : List IL.Sym} {cs : Codes} {v : Value}
      (hm : g ∈ gs) (h : Derives env ρ g cs v ρ') :
      Derives env ρ (.altG gs) cs (.tuple []) ρ'
  /-- `IterG (g, (it, ds)) : IterT (t, it)` (`valid.ml:602-605`), as
  `Sem.iterActFn`: rounds that restore the scope, an arity the iterator
  admits, and the domains bound outwards. -/
  | iterG {ρ ρ' : VarEnv} {g : IL.Sym} {it : Iter} {ds : List Dom} {cs : Codes}
      {rows : List (Value × List Value)}
      (h : DerivesRounds env ρ ds g rows cs)
      (hc : IterCount env ρ it rows.length)
      (hb : BindDoms env it ds (rows.map Prod.snd) ρ ρ') :
      Derives env ρ (.iterG g (.mk it ds)) cs (iterValue it (rows.map Prod.fst)) ρ'
  /-- `AttrG (e, g) : t` where `t` is `g`'s type, with `e` checked as a
  binding pattern (`valid.ml:606-608`, `~side:`Lhs``). -/
  | attrG {ρ ρ₁ ρ' : VarEnv} {e : Exp} {g : IL.Sym} {cs : Codes} {v : Value}
      (h : Derives env ρ g cs v ρ₁) (hm : MatchExp env ρ₁ e v ρ') :
      Derives env ρ (.attrG e g) cs v ρ'
  /-- `VarG (x, args)` (`valid.ml:578-581`) unfolded through one `ProdD`, in
  the order `valid_prod` checks it (`valid.ml:747-757`). -/
  | varG {ρ ρ₀ ρ₁ ρ₂ : VarEnv} {x : IL.Id} {args : List IL.Arg} {ps : List Param}
      {t : Typ} {prods : List IL.Prod} {qs : List Param} {g : IL.Sym} {e : Exp}
      {prems : List Prem} {ws : List ArgV} {cs : Codes} {v v₀ : Value}
      (hg : env.findGram? x = some (ps, t, prods))
      (hp : IL.Prod.prodD qs g e prems ∈ prods)
      (hw : EvalArgs env ρ args ws)
      (hbp : bindParams VarEnv.empty ps ws = some ρ₀)
      (hd : Derives env ρ₀ (substSym (gramArgSubst ps args) g) cs v₀ ρ₁)
      (hpr : PremsHold env ρ₁ prems ρ₂)
      (he : EvalExp env ρ₂ e v) :
      Derives env ρ (.varG x args) cs v ρ

/-- The factors of a `SeqG`, left to right, each starting in the scope the
previous one left. -/
inductive DerivesSeq (env : Env) : VarEnv → List IL.Sym → Codes → VarEnv → Prop where
  /-- The empty sequence. -/
  | nil {ρ : VarEnv} : DerivesSeq env ρ [] [] ρ
  /-- One factor, then the rest. -/
  | cons {ρ ρ₁ ρ' : VarEnv} {g : IL.Sym} {gs : List IL.Sym} {cs₁ cs₂ : Codes} {v : Value}
      (h : Derives env ρ g cs₁ v ρ₁) (hs : DerivesSeq env ρ₁ gs cs₂ ρ') :
      DerivesSeq env ρ (g :: gs) (cs₁ ++ cs₂) ρ'

/-- The rounds of an `IterG`.  Each round runs in — and restores — the scope
the iteration starts in (`Sem.roundActFn`), and reports its own value
together with the value each `iterexp` domain variable took in it. -/
inductive DerivesRounds (env : Env) :
    VarEnv → List Dom → IL.Sym → List (Value × List Value) → Codes → Prop where
  /-- No rounds. -/
  | nil {ρ : VarEnv} {ds : List Dom} {g : IL.Sym} : DerivesRounds env ρ ds g [] []
  /-- One round, then the rest. -/
  | cons {ρ ρ₁ : VarEnv} {ds : List Dom} {g : IL.Sym} {cs₁ cs₂ : Codes} {v : Value}
      {vs : List Value} {rows : List (Value × List Value)}
      (h : Derives env ρ g cs₁ v ρ₁)
      (hv : ds.mapM (fun d => ρ₁.findVal? (domVar d)) = some vs)
      (hs : DerivesRounds env ρ ds g rows cs₂) :
      DerivesRounds env ρ ds g ((v, vs) :: rows) (cs₁ ++ cs₂)

end

/-- The character denotation of a symbol, as an `EncRel Codes Value`, so that
the whole vocabulary of `Silmaril/Encoding/Lattice.lean` applies to it. -/
def charRel (env : Env) (ρ : VarEnv) (g : IL.Sym) : EncRel Codes Value :=
  fun cs v => ∃ ρ', Derives env ρ g cs v ρ'

/-- The byte relation of a text grammar: the character denotation pushed
forward along UTF-8.  This is the carrier change `EncRel.push` of
`Silmaril/Encoding/Relation.lean:100`, and the reason the text layer is not
`Sem.gramRelSup`: `gramRelSup_tchar_eq_bot` says that relation is empty. -/
def textByteRel (env : Env) (ρ : VarEnv) (g : IL.Sym) : EncRel Grammar.Bytes Value :=
  EncRel.push utf8Codes (charRel env ρ g)

/-- Unfolding `textByteRel`: a byte string spells a value exactly when it is
the UTF-8 encoding of a scalar string the grammar derives. -/
theorem textByteRel_iff {env : Env} {ρ : VarEnv} {g : IL.Sym} {bs : Grammar.Bytes}
    {v : Value} : textByteRel env ρ g bs v ↔ ∃ cs, utf8Codes cs = bs ∧ charRel env ρ g cs v :=
  Iff.rfl

/-! ### Inversions

One `iff` per constructor, so that a derivation can be taken apart as well as
built.  They are all immediate from the inductive. -/

/-- `EpsG`, inverted. -/
theorem derives_epsG_iff {env : Env} {ρ ρ' : VarEnv} {cs : Codes} {v : Value} :
    Derives env ρ .epsG cs v ρ' ↔ cs = [] ∧ v = .tuple [] ∧ ρ' = ρ := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩; exact .epsG

/-- A scalar terminal, inverted. -/
theorem derives_numG_iff {env : Env} {ρ ρ' : VarEnv} {cs : Codes} {v : Value} {n : Nat} :
    Derives env ρ (.numG n) cs v ρ' ↔ cs = [n] ∧ v = .num (.natN n) ∧ ρ' = ρ := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩; exact .numG

/-- A literal terminal, inverted. -/
theorem derives_textG_iff {env : Env} {ρ ρ' : VarEnv} {cs : Codes} {v : Value} {t : Text} :
    Derives env ρ (.textG t) cs v ρ' ↔ cs = codes t ∧ v = .text t ∧ ρ' = ρ := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩; exact .textG

/-- A scalar range, inverted. -/
theorem derives_rangeG_iff {env : Env} {ρ ρ' : VarEnv} {cs : Codes} {v : Value}
    {lo hi : Nat} :
    Derives env ρ (.rangeG (.numG lo) (.numG hi)) cs v ρ' ↔
      ∃ n, lo ≤ n ∧ n ≤ hi ∧ cs = [n] ∧ v = .num (.natN n) ∧ ρ' = ρ := by
  constructor
  · intro h; cases h with | rangeG h₁ h₂ => exact ⟨_, h₁, h₂, rfl, rfl, rfl⟩
  · rintro ⟨n, h₁, h₂, rfl, rfl, rfl⟩; exact .rangeG h₁ h₂

/-- A sequence, inverted. -/
theorem derives_seqG_iff {env : Env} {ρ ρ' : VarEnv} {cs : Codes} {v : Value}
    {gs : List IL.Sym} :
    Derives env ρ (.seqG gs) cs v ρ' ↔ v = .tuple [] ∧ DerivesSeq env ρ gs cs ρ' := by
  constructor
  · intro h; cases h with | seqG h => exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩; exact .seqG h

/-- An alternation, inverted. -/
theorem derives_altG_iff {env : Env} {ρ ρ' : VarEnv} {cs : Codes} {v : Value}
    {gs : List IL.Sym} :
    Derives env ρ (.altG gs) cs v ρ' ↔
      v = .tuple [] ∧ ∃ g ∈ gs, ∃ w, Derives env ρ g cs w ρ' := by
  constructor
  · intro h; cases h with | altG hm h => exact ⟨rfl, _, hm, _, h⟩
  · rintro ⟨rfl, g, hm, w, h⟩; exact .altG hm h

/-- An attributed symbol, inverted. -/
theorem derives_attrG_iff {env : Env} {ρ ρ' : VarEnv} {cs : Codes} {v : Value}
    {e : Exp} {g : IL.Sym} :
    Derives env ρ (.attrG e g) cs v ρ' ↔
      ∃ ρ₁, Derives env ρ g cs v ρ₁ ∧ MatchExp env ρ₁ e v ρ' := by
  constructor
  · intro h; cases h with | attrG h hm => exact ⟨_, h, hm⟩
  · rintro ⟨ρ₁, h, hm⟩; exact .attrG h hm

/-- An empty sequence, inverted. -/
theorem derivesSeq_nil_iff {env : Env} {ρ ρ' : VarEnv} {cs : Codes} :
    DerivesSeq env ρ [] cs ρ' ↔ cs = [] ∧ ρ' = ρ := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact .nil

/-- A non-empty sequence, inverted. -/
theorem derivesSeq_cons_iff {env : Env} {ρ ρ' : VarEnv} {cs : Codes} {g : IL.Sym}
    {gs : List IL.Sym} :
    DerivesSeq env ρ (g :: gs) cs ρ' ↔
      ∃ cs₁ cs₂ v ρ₁, Derives env ρ g cs₁ v ρ₁ ∧ DerivesSeq env ρ₁ gs cs₂ ρ' ∧
        cs = cs₁ ++ cs₂ := by
  constructor
  · intro h; cases h with | cons h hs => exact ⟨_, _, _, _, h, hs, rfl⟩
  · rintro ⟨cs₁, cs₂, v, ρ₁, h, hs, rfl⟩; exact .cons h hs

/-- No rounds, inverted. -/
theorem derivesRounds_nil_iff {env : Env} {ρ : VarEnv} {ds : List Dom} {g : IL.Sym}
    {cs : Codes} : DerivesRounds env ρ ds g [] cs ↔ cs = [] := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil

/-- One round and the rest, inverted. -/
theorem derivesRounds_cons_iff {env : Env} {ρ : VarEnv} {ds : List Dom} {g : IL.Sym}
    {cs : Codes} {r : Value × List Value} {rows : List (Value × List Value)} :
    DerivesRounds env ρ ds g (r :: rows) cs ↔
      ∃ cs₁ cs₂ ρ₁, Derives env ρ g cs₁ r.1 ρ₁ ∧
        ds.mapM (fun d => ρ₁.findVal? (domVar d)) = some r.2 ∧
        DerivesRounds env ρ ds g rows cs₂ ∧ cs = cs₁ ++ cs₂ := by
  constructor
  · intro h; cases h with | cons h hv hs => exact ⟨_, _, _, h, hv, hs, rfl⟩
  · obtain ⟨v, vs⟩ := r
    rintro ⟨cs₁, cs₂, ρ₁, h, hv, hs, rfl⟩
    exact .cons h hv hs

/-- Matching a fresh variable, inverted: the only outcome is the binding. -/
theorem matchExp_varE_elim {env : Env} {ρ ρ' : VarEnv} {x : IL.Id} {v : Value}
    (hn : ρ.findVal? x = none) (h : MatchExp env ρ (.varE x) v ρ') :
    ρ' = ρ.bindVal x v := by
  obtain ⟨n, h⟩ := h
  cases n with
  | zero => simp [matchExp] at h
  | succ n => simp [matchExp, hn] at h; exact h.symm

/-- A parameterless nonterminal, unfolded in both directions.  The grammar's
parameter list is empty, so the call's argument list is empty too, and the
production runs in the empty scope. -/
theorem derives_varG_iff {env : Env} {ρ ρ' : VarEnv} {x : IL.Id} {t : Typ}
    {prods : List IL.Prod} {cs : Codes} {v : Value}
    (hg : env.findGram? x = some ([], t, prods)) :
    Derives env ρ (.varG x []) cs v ρ' ↔ ρ' = ρ ∧ ∃ qs g e prems,
      IL.Prod.prodD qs g e prems ∈ prods ∧ ∃ ρ₁ ρ₂ v₀,
        Derives env VarEnv.empty (substSym [] g) cs v₀ ρ₁ ∧
        PremsHold env ρ₁ prems ρ₂ ∧ EvalExp env ρ₂ e v := by
  constructor
  · intro h
    cases h with
    | varG hg' hp hw hbp hd hpr he =>
        rw [hg] at hg'
        obtain ⟨rfl, -, rfl⟩ := Option.some.injEq .. ▸ hg'
        obtain rfl := evalArgs_nil_iff.mp hw
        obtain rfl := Option.some.inj hbp
        exact ⟨rfl, _, _, _, _, hp, _, _, _, hd, hpr, he⟩
  · rintro ⟨rfl, qs, g, e, prems, hp, ρ₁, ρ₂, v₀, hd, hpr, he⟩
    exact .varG hg hp (evalArgs_nil env ρ') rfl hd hpr he

/-! ## The lexical grammars, over characters -/

/-- A `Term` is closed under the grammar substitution, so the production body
a call unfolds to is the terminal itself. -/
@[simp] theorem substSym_term (τ : Term) : substSym [] τ.sym = τ.sym := by
  cases τ <;> rfl

/-- A `Term` derives exactly the one-character strings it admits. -/
theorem derives_term_iff {env : Env} {ρ ρ' : VarEnv} {cs : Codes} {v : Value} (τ : Term) :
    Derives env ρ τ.sym cs v ρ' ↔
      ∃ n, τ.Mem n ∧ cs = [n] ∧ v = .num (.natN n) ∧ ρ' = ρ := by
  cases τ with
  | lit m =>
      rw [show (Term.lit m).sym = .numG m from rfl, derives_numG_iff]
      constructor
      · rintro ⟨rfl, rfl, rfl⟩; exact ⟨m, rfl, rfl, rfl, rfl⟩
      · rintro ⟨n, rfl, rfl, rfl, rfl⟩; exact ⟨rfl, rfl, rfl⟩
  | range lo hi =>
      rw [show (Term.range lo hi).sym = .rangeG (.numG lo) (.numG hi) from rfl,
        derives_rangeG_iff]
      constructor
      · rintro ⟨n, h₁, h₂, rfl, rfl, rfl⟩; exact ⟨n, ⟨h₁, h₂⟩, rfl, rfl, rfl⟩
      · rintro ⟨n, ⟨h₁, h₂⟩, rfl, rfl, rfl⟩; exact ⟨n, h₁, h₂, rfl, rfl, rfl⟩

/-- Evaluating the pinned `%(x)` result expression, in both directions. -/
theorem evalExp_case_var_iff {env : Env} {ρ : VarEnv} {op : MixopS} {x : IL.Id}
    {w v : Value} (h : ρ.findVal? x = some w) :
    EvalExp env ρ (.caseE op (.tupE [.varE x])) v ↔ v = .case op (.tuple [w]) := by
  constructor
  · intro hv; exact hv.unique (evalExp_case_var h)
  · rintro rfl; exact evalExp_case_var h

/-- A `char`-valued lexical grammar — one `charProd` per terminal — derives
exactly the single characters its terminals admit, with the value `%(n)`.
This is `Tchar`, `Tidchar`, and nothing else in §6.0. -/
theorem derives_charProdsOf_iff {env : Env} {ρ ρ' : VarEnv} {x : IL.Id} {t : Typ}
    {cs : Codes} {v : Value} {τs : List Term}
    (hg : env.findGram? x = some ([], t, charProdsOf τs)) :
    Derives env ρ (.varG x []) cs v ρ' ↔
      ρ' = ρ ∧ ∃ n, (∃ τ ∈ τs, τ.Mem n) ∧ cs = [n] ∧ v = numCase n := by
  rw [derives_varG_iff hg]
  constructor
  · rintro ⟨rfl, qs, g, e, prems, hp, ρ₁, ρ₂, v₀, hd, hpr, he⟩
    obtain ⟨τ, hτ, hpe⟩ := List.mem_map.mp hp
    rw [charProd, IL.Prod.prodD.injEq] at hpe
    obtain ⟨-, rfl, rfl, rfl⟩ := hpe
    rw [show substSym [] (IL.Sym.attrG (.varE implicitId) τ.sym)
        = .attrG (.varE implicitId) τ.sym by rw [substSym, substSym_term],
      derives_attrG_iff] at hd
    obtain ⟨σ, hσ, hm⟩ := hd
    obtain ⟨n, hn, rfl, rfl, rfl⟩ := (derives_term_iff τ).mp hσ
    obtain rfl := matchExp_varE_elim rfl hm
    obtain rfl := premsHold_nil_iff.mp hpr
    rw [evalExp_case_var_iff (w := Value.num (.natN n)) rfl] at he
    exact ⟨rfl, n, ⟨τ, hτ, hn⟩, rfl, he⟩
  · rintro ⟨rfl, n, ⟨τ, hτ, hn⟩, rfl, rfl⟩
    refine ⟨rfl, _, _, _, _, List.mem_map.mpr ⟨τ, hτ, rfl⟩,
      VarEnv.empty.bindVal implicitId (.num (.natN n)),
      VarEnv.empty.bindVal implicitId (.num (.natN n)), .num (.natN n), ?_,
      premsHold_nil, ?_⟩
    · rw [show substSym [] (IL.Sym.attrG (.varE implicitId) τ.sym)
          = .attrG (.varE implicitId) τ.sym by rw [substSym, substSym_term],
        derives_attrG_iff]
      exact ⟨VarEnv.empty, (derives_term_iff τ).mpr ⟨n, hn, rfl, rfl, rfl⟩,
        matchExp_varE_of_none rfl⟩
    · exact evalExp_case_var rfl

/-- The Unicode scalar values, `6.0-text.lexical.spectec:7-8`'s `Tchar`. -/
def IsChar (n : Nat) : Prop := n ≤ 0xD7FF ∨ (0xE000 ≤ n ∧ n ≤ 0x10FFFF)

instance (n : Nat) : Decidable (IsChar n) := by unfold IsChar; infer_instance

/-- **`Tchar`.**  Over characters the pinned grammar says exactly what
`6.0-text.lexical.spectec:7-8` says: one scalar value, surrogates excluded,
with the `char` value `%(n)`.  Contrast `gramRelSup_tchar_eq_bot`. -/
theorem tchar_iff {env : Env} {ρ ρ' : VarEnv} {cs : Codes} {v : Value}
    (hg : env.findGram? "Tchar" = some ([], .varT "char" [], tcharProds)) :
    Derives env ρ (.varG "Tchar" []) cs v ρ' ↔
      ρ' = ρ ∧ ∃ n, IsChar n ∧ cs = [n] ∧ v = numCase n := by
  rw [tcharProds] at hg
  rw [derives_charProdsOf_iff hg]
  refine and_congr_right fun _ => exists_congr fun n => and_congr_left' ?_
  simp only [tcharTerms, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left, Term.Mem, IsChar]
  omega

/-- The identifier characters, `6.1-text.values.spectec:123-128`'s
`Tidchar`. -/
def IsIdChar (n : Nat) : Prop := ∃ τ ∈ tidcharTerms, τ.Mem n

instance (n : Nat) : Decidable (IsIdChar n) := by unfold IsIdChar; infer_instance

/-- **`Tidchar`.**  Over characters the pinned grammar derives exactly the
single identifier characters, with the value `%(n)`. -/
theorem tidchar_iff {env : Env} {ρ ρ' : VarEnv} {cs : Codes} {v : Value}
    (hg : env.findGram? "Tidchar" = some ([], .varT "char" [], tidcharProds)) :
    Derives env ρ (.varG "Tidchar" []) cs v ρ' ↔
      ρ' = ρ ∧ ∃ n, IsIdChar n ∧ cs = [n] ∧ v = numCase n :=
  derives_charProdsOf_iff (by rw [tidcharProds] at hg; exact hg)

/-- Every identifier character is a character: `Tidchar` refines `Tchar`.
Both sides are decidable, and the three ranges plus twenty-three literals are
all well inside `U+D7FF`. -/
theorem isChar_of_isIdChar {n : Nat} (h : IsIdChar n) : IsChar n := by
  simp only [IsIdChar, tidcharTerms, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left, Term.Mem] at h
  simp only [IsChar]
  omega

/-! ### Reading the `c =/= …` premises -/

/-- `Xl.Bool.bin_partial` never short-circuits a conjunction to `true`
(`spectec/src/xl/bool.ml:36-47`). -/
theorem boolShort_and_ne {v : Value} : boolShort .andOp v ≠ some (.bool true) := by
  cases v with
  | bool b => cases b <;> simp [boolShort]
  | num _ => simp [boolShort]
  | text _ => simp [boolShort]
  | tuple _ => simp [boolShort]
  | case _ _ => simp [boolShort]
  | struct _ => simp [boolShort]
  | list _ => simp [boolShort]
  | opt _ => simp [boolShort]

/-- A conjunction of two values is `true` only if both are
(`spectec/src/xl/bool.ml:29-34`). -/
theorem binValues_and_true {v₁ v₂ : Value} (h : binValues .andOp v₁ v₂ = .ok (.bool true)) :
    v₁ = .bool true ∧ v₂ = .bool true := by
  cases v₁ <;> cases v₂ <;> simp_all [binValues, boolBin, Num.bin]

/-- A conjunction that denotes `true` has both conjuncts `true`. -/
theorem evalExp_and_elim {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp}
    (h : EvalExp env ρ (.binE .andOp .boolT e₁ e₂) (.bool true)) :
    EvalExp env ρ e₁ (.bool true) ∧ EvalExp env ρ e₂ (.bool true) := by
  obtain ⟨v₁, h₁, hs⟩ := evalExp_binE_iff.mp h
  rcases hs with hs | ⟨-, v₂, h₂, hb⟩
  · exact absurd hs boolShort_and_ne
  · obtain ⟨rfl, rfl⟩ := binValues_and_true hb
    exact ⟨h₁, h₂⟩

/-- The value of the pinned `%(k)` literal. -/
theorem evalExp_case_num {env : Env} {ρ : VarEnv} {op : MixopS} {m : Num} :
    EvalExp env ρ (.caseE op (.tupE [.numE m])) (.case op (.tuple [.num m])) :=
  evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_iff.mpr
    ⟨_, evalExps_singleton (evalExp_numE_iff.mpr rfl), rfl⟩, rfl⟩

/-- The premise `c =/= %(k)`, read as a disequality on the value `c` is bound
to. -/
theorem ne_of_cmpNe {env : Env} {ρ : VarEnv} {x : IL.Id} {w : Value} {k : Nat}
    (hx : ρ.findVal? x = some w)
    (h : EvalExp env ρ
      (.cmpE .neOp .boolT (.varE x) (.caseE "%" (.tupE [.numE (.natN k)]))) (.bool true)) :
    w ≠ numCase k := by
  obtain ⟨v₁, v₂, h₁, h₂, hr⟩ := evalExp_cmpE_iff.mp h
  obtain rfl : v₁ = w := by
    have hv := evalExp_varE_iff.mp h₁; rw [hx] at hv; exact (Option.some.inj hv).symm
  obtain rfl : v₂ = numCase k := h₂.unique evalExp_case_num
  simpa [cmpValues] using hr

/-! ### Block comments: `#665`

`Tblockchar`'s three character productions all end in a `Tchar` that the
premise forbids to be `;`, and `Tblockcomment` ends in the literal `;)`.  So
**no `Tblockchar*` can end in a semicolon**, which is exactly why the pinned
`"(;" Tblockchar* ";)"` has no derivation for a comment body that does, and
`#665` is right. -/

/-- `cs` is non-empty and its last character is not `;`. -/
def LastNotSemi (cs : Codes) : Prop := ∃ l c, cs = l ++ [c] ∧ c ≠ 59

/-- A string all of whose characters are `;` does not satisfy `LastNotSemi`. -/
theorem not_lastNotSemi_of_all_semi {cs : Codes} (h : ∀ c ∈ cs, c = 59) :
    ¬ LastNotSemi cs := by
  rintro ⟨l, c, rfl, hc⟩
  exact hc (h c (by simp))

/-- `LastNotSemi` only looks at the end. -/
theorem lastNotSemi_append {cs ds : Codes} (h : LastNotSemi ds) :
    LastNotSemi (cs ++ ds) := by
  obtain ⟨l, c, rfl, hc⟩ := h
  exact ⟨cs ++ l, c, by rw [List.append_assoc], hc⟩

/-- A one-character string that is not `;`. -/
theorem lastNotSemi_singleton {n : Nat} (h : n ≠ 59) : LastNotSemi [n] :=
  ⟨[], n, rfl, h⟩

/-- `substSyms` distributes over `++`. -/
theorem substSyms_append (σ : List (IL.Id × IL.Sym)) (gs hs : List IL.Sym) :
    substSyms σ (gs ++ hs) = substSyms σ gs ++ substSyms σ hs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => rw [List.cons_append, substSyms, substSyms, ih, List.cons_append]

/-- A sequence whose last factor is the literal `;)` ends in `)`. -/
theorem derivesSeq_lastNotSemi {env : Env} :
    ∀ (gs : List IL.Sym) {ρ ρ' : VarEnv} {cs : Codes},
      DerivesSeq env ρ (gs ++ [.seqG [.textG ";)"]]) cs ρ' → LastNotSemi cs := by
  intro gs
  induction gs with
  | nil =>
      intro ρ ρ' cs h
      obtain ⟨c₁, c₂, w, σ, h₁, h₂, rfl⟩ := derivesSeq_cons_iff.mp h
      obtain ⟨-, h₁'⟩ := derives_seqG_iff.mp h₁
      obtain ⟨d₁, d₂, w₁, σ₁, he₁, he₂, rfl⟩ := derivesSeq_cons_iff.mp h₁'
      obtain ⟨rfl, -, -⟩ := derives_textG_iff.mp he₁
      obtain ⟨rfl, -⟩ := derivesSeq_nil_iff.mp he₂
      obtain ⟨rfl, -⟩ := derivesSeq_nil_iff.mp h₂
      exact ⟨[59], 41, rfl, by decide⟩
  | cons g gs ih =>
      intro ρ ρ' cs h
      obtain ⟨c₁, c₂, w, σ, h₁, h₂, rfl⟩ := derivesSeq_cons_iff.mp h
      exact lastNotSemi_append (ih h₂)

/-- **The shape of a block comment.**  Both the pinned and the corrected
`Tblockcomment` have a single production whose body is a sequence ending in
the literal `;)`, so every derivation ends in `)`.  No induction over the
grammar is needed: one unfolding suffices. -/
theorem blockcomment_lastNotSemi {env : Env} {ρ ρ' : VarEnv} {cs : Codes} {v : Value}
    {prods : List IL.Prod} {gs : List IL.Sym}
    (hg : env.findGram? "Tblockcomment" = some ([], .tupT [], prods))
    (hp : prods = [shortProd (.tupT []) (.seqG (gs ++ [.seqG [.textG ";)"]])) []])
    (h : Derives env ρ (.varG "Tblockcomment" []) cs v ρ') : LastNotSemi cs := by
  rw [derives_varG_iff hg, hp] at h
  obtain ⟨-, qs, g, e, prems, hm, ρ₁, ρ₂, v₀, hd, -, -⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rw [shortProd, IL.Prod.prodD.injEq] at hm
  obtain ⟨-, rfl, rfl, rfl⟩ := hm
  simp only [substSym, substSyms_append, substSyms] at hd
  obtain ⟨σ, hσ, -⟩ := derives_attrG_iff.mp hd
  obtain ⟨-, hs⟩ := derives_seqG_iff.mp hσ
  exact derivesSeq_lastNotSemi _ hs

/-- The empty scope binds nothing. -/
@[simp] theorem findVal_empty (x : IL.Id) : VarEnv.empty.findVal? x = none := rfl

/-- Reading a variable back out of the binding that introduced it. -/
@[simp] theorem findVal_bindVal_self (ρ : VarEnv) {x : IL.Id} (h : x ≠ "_") (v : Value) :
    (ρ.bindVal x v).findVal? x = some v := Map.find?_bind_self _ h _

/-- Reading a variable back out through a later, different binding. -/
@[simp] theorem findVal_bindVal_of_ne (ρ : VarEnv) {x y : IL.Id} (h : x ≠ y) (v : Value) :
    (ρ.bindVal x v).findVal? y = ρ.findVal? y := Map.find?_bind_of_ne _ h _

/-- `%(·)` is injective. -/
theorem numCase_inj {m n : Nat} (h : numCase m = numCase n) : m = n := by
  simpa [numCase] using h

/-- An iteration with no `iterexp` domains binds nothing outside itself. -/
theorem derives_seqG_iter_scope {env : Env} {ρ ρ' : VarEnv} {cs : Codes} {v : Value}
    {g : IL.Sym} {it : Iter}
    (h : Derives env ρ (.seqG [.iterG g (.mk it [])]) cs v ρ') : ρ' = ρ := by
  obtain ⟨-, hs⟩ := derives_seqG_iff.mp h
  obtain ⟨c₁, c₂, w, σ, h₁, h₂, -⟩ := derivesSeq_cons_iff.mp hs
  obtain ⟨-, rfl⟩ := derivesSeq_nil_iff.mp h₂
  cases h₁ with | iterG hr hcnt hb => exact hb

/-- The `c:Tchar` tail of `Tblockchar`'s second and third productions: it
derives one character and binds `c` to it. -/
theorem derivesSeq_cTchar {env : Env} {ρ ρ' : VarEnv} {cs : Codes}
    (hc : env.findGram? "Tchar" = some ([], .varT "char" [], tcharProds))
    (hn : ρ.findVal? "c" = none)
    (h : DerivesSeq env ρ [.seqG [.attrG (.varE "c") (.varG "Tchar" [])]] cs ρ') :
    ∃ n, cs = [n] ∧ ρ' = ρ.bindVal "c" (numCase n) := by
  obtain ⟨c₁, c₂, w, σ, h₁, h₂, rfl⟩ := derivesSeq_cons_iff.mp h
  obtain ⟨rfl, rfl⟩ := derivesSeq_nil_iff.mp h₂
  obtain ⟨-, h₁'⟩ := derives_seqG_iff.mp h₁
  obtain ⟨d₁, d₂, w₁, σ₁, he₁, he₂, rfl⟩ := derivesSeq_cons_iff.mp h₁'
  obtain ⟨rfl, rfl⟩ := derivesSeq_nil_iff.mp he₂
  obtain ⟨σ₂, hτ, hm⟩ := derives_attrG_iff.mp he₁
  obtain ⟨rfl, n, -, rfl, rfl⟩ := (tchar_iff hc).mp hτ
  obtain rfl := matchExp_varE_elim hn hm
  exact ⟨n, by simp, rfl⟩

/-- The body `";"+ c:Tchar` / `"("+ c:Tchar` of `Tblockchar`'s second and
third productions: the derived string ends in the character `c` is bound
to. -/
theorem derives_runTchar {env : Env} {ρ₁ : VarEnv} {cs : Codes} {v₀ : Value}
    {t : Text} {it : Iter}
    (hc : env.findGram? "Tchar" = some ([], .varT "char" [], tcharProds))
    (h : Derives env VarEnv.empty
      (.attrG (.varE implicitId)
        (.seqG [.seqG [.iterG (.textG t) (.mk it [])],
          .seqG [.attrG (.varE "c") (.varG "Tchar" [])]])) cs v₀ ρ₁) :
    ∃ pre n, cs = pre ++ [n] ∧ ρ₁.findVal? "c" = some (numCase n) := by
  obtain ⟨σ, hσ, hx⟩ := derives_attrG_iff.mp h
  obtain ⟨-, hs⟩ := derives_seqG_iff.mp hσ
  obtain ⟨c₁, c₂, w, σ₁, h₁, h₂, rfl⟩ := derivesSeq_cons_iff.mp hs
  obtain rfl := derives_seqG_iter_scope h₁
  obtain ⟨n, rfl, rfl⟩ := derivesSeq_cTchar hc rfl h₂
  obtain rfl := matchExp_varE_elim (by simp [implicitId]) hx
  exact ⟨c₁, n, rfl, by simp [implicitId]⟩

/-- **No `Tblockchar` ends in a semicolon.**  The three character
productions of `6.0-text.lexical.spectec:60-64` all end in a `Tchar` their
premise forbids to be `;`, and the fourth is a nested block comment, which
ends in `)`.

This is the content of `#665`: the pinned grammar reads
`"(;" Tblockchar* ";)"`, so a comment body ending in `;` cannot be derived. -/
theorem blockchar_lastNotSemi {env : Env} {ρ ρ' : VarEnv} {cs : Codes} {v : Value}
    (hc : env.findGram? "Tchar" = some ([], .varT "char" [], tcharProds))
    (hk : env.findGram? "Tblockcomment" = some ([], .tupT [], tblockcommentProds))
    (hb : env.findGram? "Tblockchar" = some ([], .tupT [], tblockcharProds))
    (h : Derives env ρ (.varG "Tblockchar" []) cs v ρ') : LastNotSemi cs := by
  rw [derives_varG_iff hb] at h
  obtain ⟨-, qs, g, e, prems, hm, ρ₁, ρ₂, v₀, hd, hpr, -⟩ := h
  simp only [tblockcharProds, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with hm | hm | hm | hm
  · rw [shortProdC, IL.Prod.prodD.injEq] at hm
    obtain ⟨-, rfl, rfl, rfl⟩ := hm
    simp only [substSym] at hd
    obtain ⟨σ, hσ, hx⟩ := derives_attrG_iff.mp hd
    obtain ⟨σ₂, hτ, hmc⟩ := derives_attrG_iff.mp hσ
    obtain ⟨rfl, n, -, rfl, rfl⟩ := (tchar_iff hc).mp hτ
    obtain rfl := matchExp_varE_elim rfl hmc
    obtain rfl := matchExp_varE_elim (by simp [implicitId]) hx
    rw [neTwo, premsHold_ifPr_iff] at hpr
    have hne := ne_of_cmpNe (w := numCase n) (by simp [implicitId])
      (evalExp_and_elim hpr.1).1
    exact lastNotSemi_singleton fun hn => hne (by rw [hn])
  · rw [shortProdC, IL.Prod.prodD.injEq] at hm
    obtain ⟨-, rfl, rfl, rfl⟩ := hm
    simp only [substSym] at hd
    obtain ⟨pre, n, rfl, hx⟩ := derives_runTchar hc hd
    rw [neTwo, premsHold_ifPr_iff] at hpr
    have hne := ne_of_cmpNe hx (evalExp_and_elim hpr.1).1
    exact lastNotSemi_append (lastNotSemi_singleton fun hn => hne (by rw [hn]))
  · rw [shortProdC, IL.Prod.prodD.injEq] at hm
    obtain ⟨-, rfl, rfl, rfl⟩ := hm
    simp only [substSym] at hd
    obtain ⟨pre, n, rfl, hx⟩ := derives_runTchar hc hd
    rw [neTwo, premsHold_ifPr_iff] at hpr
    have hne := ne_of_cmpNe hx (evalExp_and_elim hpr.1).1
    exact lastNotSemi_append (lastNotSemi_singleton fun hn => hne (by rw [hn]))
  · rw [shortProd, IL.Prod.prodD.injEq] at hm
    obtain ⟨-, rfl, rfl, rfl⟩ := hm
    simp only [substSym] at hd
    obtain ⟨σ, hσ, -⟩ := derives_attrG_iff.mp hd
    exact blockcomment_lastNotSemi (gs := [.seqG [.textG "(;"],
      .seqG [.iterG (.varG "Tblockchar" []) (.mk .list [])]]) hk rfl hσ

/-! ### The two halves of `#665`, as theorems -/

/-- A one-factor sequence holding a literal. -/
theorem derives_seqG_text {env : Env} {ρ ρ' : VarEnv} {cs : Codes} {v : Value} {t : Text}
    (h : Derives env ρ (.seqG [.textG t]) cs v ρ') : cs = codes t ∧ ρ' = ρ := by
  obtain ⟨-, hs⟩ := derives_seqG_iff.mp h
  obtain ⟨c₁, c₂, w, σ, h₁, h₂, rfl⟩ := derivesSeq_cons_iff.mp hs
  obtain ⟨rfl, rfl⟩ := derivesSeq_nil_iff.mp h₂
  obtain ⟨rfl, -, rfl⟩ := derives_textG_iff.mp h₁
  exact ⟨by simp, rfl⟩

/-- A one-factor sequence holding an iteration with no domains, with its
rounds exposed. -/
theorem derives_seqG_iter {env : Env} {ρ ρ' : VarEnv} {cs : Codes} {v : Value}
    {g : IL.Sym} {it : Iter}
    (h : Derives env ρ (.seqG [.iterG g (.mk it [])]) cs v ρ') :
    (∃ rows, DerivesRounds env ρ [] g rows cs) ∧ ρ' = ρ := by
  obtain ⟨-, hs⟩ := derives_seqG_iff.mp h
  obtain ⟨c₁, c₂, w, σ, h₁, h₂, rfl⟩ := derivesSeq_cons_iff.mp hs
  obtain ⟨rfl, rfl⟩ := derivesSeq_nil_iff.mp h₂
  cases h₁ with
  | iterG hr hcnt hb => exact ⟨⟨_, by simpa using hr⟩, hb⟩

/-- A non-empty run of `Tblockchar` rounds does not end in a semicolon. -/
theorem derivesRounds_blockchar_lastNotSemi {env : Env} {ρ : VarEnv}
    (hc : env.findGram? "Tchar" = some ([], .varT "char" [], tcharProds))
    (hk : env.findGram? "Tblockcomment" = some ([], .tupT [], tblockcommentProds))
    (hb : env.findGram? "Tblockchar" = some ([], .tupT [], tblockcharProds)) :
    ∀ (rows : List (Value × List Value)) (cs : Codes),
      DerivesRounds env ρ [] (.varG "Tblockchar" []) rows cs → rows ≠ [] → LastNotSemi cs := by
  intro rows
  induction rows with
  | nil => intro cs h hne; exact absurd rfl hne
  | cons r rows ih =>
      intro cs h _
      obtain ⟨cs₁, cs₂, ρ₁, h₁, -, hs, rfl⟩ := derivesRounds_cons_iff.mp h
      rcases rows with _ | ⟨r', rows'⟩
      · obtain rfl := derivesRounds_nil_iff.mp hs
        simpa using blockchar_lastNotSemi hc hk hb h₁
      · exact lastNotSemi_append (ih _ hs (by simp))

/-- `(;;;;;;;;;;;;;;)`, the block comment of `test/core/comments.wast:26`,
split as the pinned production would have to split it. -/
def commentsWast26 : Codes := codes "(;" ++ List.replicate 12 59 ++ codes ";)"

/-- It really is that comment. -/
theorem commentsWast26_eq : commentsWast26 = codes "(;;;;;;;;;;;;;;)" := rfl

/-- **`#665`, the negative half.**  The pinned `Tblockcomment` has no
derivation for `(;;;;;;;;;;;;;;)`: the body between the delimiters would have
to be twelve semicolons, and `blockchar_lastNotSemi` says no `Tblockchar*`
ends in one. -/
theorem not_derives_blockcomment_semis {env : Env} {ρ ρ' : VarEnv} {v : Value}
    (hc : env.findGram? "Tchar" = some ([], .varT "char" [], tcharProds))
    (hk : env.findGram? "Tblockcomment" = some ([], .tupT [], tblockcommentProds))
    (hb : env.findGram? "Tblockchar" = some ([], .tupT [], tblockcharProds)) :
    ¬ Derives env ρ (.varG "Tblockcomment" []) commentsWast26 v ρ' := by
  intro h
  rw [derives_varG_iff hk] at h
  obtain ⟨-, qs, g, e, prems, hm, ρ₁, ρ₂, v₀, hd, -, -⟩ := h
  simp only [tblockcommentProds, List.mem_cons, List.not_mem_nil, or_false] at hm
  rw [shortProd, IL.Prod.prodD.injEq] at hm
  obtain ⟨-, rfl, rfl, rfl⟩ := hm
  simp only [substSym] at hd
  obtain ⟨σ, hσ, -⟩ := derives_attrG_iff.mp hd
  obtain ⟨-, hs⟩ := derives_seqG_iff.mp hσ
  obtain ⟨a₁, a₂, w₁, σ₁, f₁, r₁, heq⟩ := derivesSeq_cons_iff.mp hs
  obtain ⟨rfl, rfl⟩ := derives_seqG_text f₁
  obtain ⟨b₁, b₂, w₂, σ₂, f₂, r₂, rfl⟩ := derivesSeq_cons_iff.mp r₁
  obtain ⟨⟨rows, hrows⟩, rfl⟩ := derives_seqG_iter f₂
  obtain ⟨d₁, d₂, w₃, σ₃, f₃, r₃, rfl⟩ := derivesSeq_cons_iff.mp r₂
  obtain ⟨rfl, rfl⟩ := derives_seqG_text f₃
  obtain ⟨rfl, -⟩ := derivesSeq_nil_iff.mp r₃
  have hb₁ : b₁ = List.replicate 12 59 := by
    simp only [commentsWast26, List.append_nil, ← List.append_assoc] at heq
    exact (List.append_cancel_left (List.append_cancel_right heq)).symm
  subst hb₁
  rcases rows with _ | ⟨r, rows⟩
  · exact absurd (derivesRounds_nil_iff.mp hrows) (by simp)
  · exact not_lastNotSemi_of_all_semi (fun c hcm => List.eq_of_mem_replicate hcm)
      (derivesRounds_blockchar_lastNotSemi hc hk hb _ _ hrows (by simp))

/-- A fixed round, repeated. -/
theorem derivesRounds_replicate {env : Env} {ρ : VarEnv} {g : IL.Sym} {cs₀ : Codes}
    {v : Value} (h : Derives env ρ g cs₀ v ρ) : ∀ k : Nat,
      DerivesRounds env ρ [] g (List.replicate k (v, []))
        (List.flatten (List.replicate k cs₀))
  | 0 => .nil
  | k + 1 => by
      rw [List.replicate_succ, List.replicate_succ, List.flatten_cons]
      exact .cons h rfl (derivesRounds_replicate h k)

/-- The pinned `(x, ())` result expression denotes the unit of `TupT []`. -/
theorem evalExp_unitResult {env : Env} {ρ : VarEnv} {w : Value}
    (h : ρ.findVal? implicitId = some w) : EvalExp env ρ unitResult (.tuple []) :=
  ⟨5, by simp [unitResult, evalExp, evalExps, h, Value.asTuple?]⟩

/-- **`#665`, the positive half.**  The corrected `Tblockcomment` *does*
derive `(;;;;;;;;;;;;;;)`: the `";"*` run the patch inserts before the closing
delimiter takes all twelve. -/
theorem derives_blockcomment_corrected_semis {env : Env} {ρ : VarEnv}
    (hk : env.findGram? "Tblockcomment" = some ([], .tupT [], tblockcommentProdsC)) :
    Derives env ρ (.varG "Tblockcomment" []) commentsWast26 (.tuple []) ρ := by
  have hopen : DerivesSeq env VarEnv.empty [IL.Sym.textG "(;"] (codes "(;" ++ [])
    VarEnv.empty := .cons .textG .nil
  have hclose : DerivesSeq env VarEnv.empty [IL.Sym.textG ";)"] (codes ";)" ++ [])
    VarEnv.empty := .cons .textG .nil
  have hbody : DerivesSeq env VarEnv.empty
      [IL.Sym.iterG (.varG "Tblockchar" []) (.mk .list [])] ([] ++ []) VarEnv.empty :=
    .cons (.iterG (rows := []) .nil trivial rfl) .nil
  have hsemis : DerivesSeq env VarEnv.empty [IL.Sym.iterG (.textG ";") (.mk .list [])]
      (List.flatten (List.replicate 12 (codes ";")) ++ []) VarEnv.empty :=
    .cons (.iterG (rows := List.replicate 12 (Value.text ";", []))
      (derivesRounds_replicate (Derives.textG (t := ";")) 12) trivial rfl) .nil
  have hseq := DerivesSeq.cons (Derives.seqG hopen)
    (DerivesSeq.cons (Derives.seqG hbody)
      (DerivesSeq.cons (Derives.seqG hsemis)
        (DerivesSeq.cons (Derives.seqG hclose) DerivesSeq.nil)))
  rw [derives_varG_iff hk]
  exact ⟨rfl, [.expP implicitId (.tupT [])],
    .attrG (.varE implicitId)
      (.seqG [.seqG [.textG "(;"], .seqG [.iterG (.varG "Tblockchar" []) (.mk .list [])],
        .seqG [.iterG (.textG ";") (.mk .list [])], .seqG [.textG ";)"]]),
    unitResult, [], (by simp [tblockcommentProdsC, shortProd]),
    VarEnv.empty.bindVal implicitId (.tuple []),
    VarEnv.empty.bindVal implicitId (.tuple []), .tuple [],
    Derives.attrG (Derives.seqG hseq) (matchExp_varE_of_none rfl), premsHold_nil,
    evalExp_unitResult (w := .tuple []) (by simp [implicitId])⟩

/-! ### `Tspace`, and the singleton-list cast

`elab.ml:2020-2022` coerces an expression of type `t` to one of type `t*` by
wrapping it in a **one-element list**, `ListE [e]`, and it does so on
`~side:`Lhs`` as well, where the result is a *pattern*.  A "short" production
whose body is an iteration therefore binds its implicit result against `[x]`,
which forces the iteration to have exactly one round.  Six §6 grammars are
affected; `Tspace` is the one that matters most, since `(" " | Tformat |
Tcomment | Tannot)*` becomes *exactly one* white-space item — in particular it
can no longer be empty. -/

/-- Matching `[x]` against a list value, inverted: the list must be a
singleton (`spectec/src/il/eval.ml:93-99`, `match_list`). -/
theorem matchExp_listE_var_elim {env : Env} {ρ ρ' : VarEnv} {x : IL.Id} {L : List Value}
    (h : MatchExp env ρ (.listE [.varE x]) (.list L) ρ') : ∃ u, L = [u] := by
  obtain ⟨n, h⟩ := h
  have h3 : matchExp (n + 3) env ρ (.listE [.varE x]) (.list L) = .ok ρ' :=
    matchExp_ok_of_le (by omega) h
  rcases L with _ | ⟨u, L⟩
  · simp [matchExp, matchExps, Value.asList?] at h3
  · rcases L with _ | ⟨u', L⟩
    · exact ⟨u, rfl⟩
    · simp [matchExp, matchExps, Value.asList?] at h3

/-- **`Tspace` is not a repetition.**  As elaborated, the pinned `Tspace`
derives exactly one of `" "`, `Tformat`, `Tcomment`, `Tannot` — never two, and
never none.  This is the singleton-list cast of `elab.ml:2020-2022`, not a
defect of the `.spectec` source, which really does write `( … )*`
(`6.0-text.lexical.spectec:32-33`). -/
theorem tspace_one_item {env : Env} {ρ ρ' : VarEnv} {cs : Codes} {v : Value}
    (hg : env.findGram? "Tspace" = some ([], .tupT [], tspaceProds))
    (h : Derives env ρ (.varG "Tspace" []) cs v ρ') :
    ∃ σ w, Derives env VarEnv.empty
      (.altG [.seqG [.textG " "], .varG "Tformat" [], .varG "Tcomment" [],
        .varG "Tannot" []]) cs w σ := by
  rw [derives_varG_iff hg] at h
  obtain ⟨-, qs, g, e, prems, hm, ρ₁, ρ₂, v₀, hd, -, -⟩ := h
  simp only [tspaceProds, List.mem_cons, List.not_mem_nil, or_false,
    IL.Prod.prodD.injEq] at hm
  obtain ⟨-, rfl, rfl, rfl⟩ := hm
  simp only [substSym] at hd
  obtain ⟨σ, hσ, hmatch⟩ := derives_attrG_iff.mp hd
  cases hσ with
  | @iterG σ₀ σ₁ g₀ it₀ ds₀ cs₀ rows hr hcnt hb =>
      obtain ⟨u, hu⟩ := matchExp_listE_var_elim hmatch
      rcases rows with _ | ⟨r, rows⟩
      · simp at hu
      · obtain ⟨cs₁, cs₂, τ, h₁, -, hs, rfl⟩ := derivesRounds_cons_iff.mp hr
        rcases rows with _ | ⟨r', rows'⟩
        · obtain rfl := derivesRounds_nil_iff.mp hs
          exact ⟨τ, r.1, by simpa [substSyms, substSym] using h₁⟩
        · simp at hu

/-! ## At the pinned and the corrected scripts

Everything above is stated for an environment that defines the §6.0 grammars
as the stream does.  Here it is discharged, by the `rfl`s against
`Specs.wasm30` and `Errata.Text6x.wasm30text6x` above. -/

/-- The whole text format denotes `⊥` over bytes, at the pinned script. -/
theorem gramRelSup_tchar_wasm30_eq_bot (ρ : VarEnv) :
    gramRelSup envPinned ρ (.varG "Tchar" []) = ⊥ :=
  gramRelSup_tchar_eq_bot findGram_tchar_pinned ρ

/-- …and at the corrected one: `#677` does not touch `Tchar`. -/
theorem gramRelSup_tchar_text6x_eq_bot (ρ : VarEnv) :
    gramRelSup envCorrected ρ (.varG "Tchar" []) = ⊥ :=
  gramRelSup_tchar_eq_bot findGram_tchar_corrected ρ

/-- `\r\n` is not a `Tnewline` over bytes, at the pinned script: the arity
obstacle, with no carrier involved. -/
theorem not_gramRelSup_tnewline_crlf_wasm30 (ρ : VarEnv) (v : Value) :
    ¬ gramRelSup envPinned ρ (.varG "Tnewline" []) [0x0D, 0x0A] v :=
  not_gramRelSup_tnewline_crlf findGram_tnewline_pinned ρ v

/-- **`Tchar`, at the pinned script.** -/
theorem tchar_wasm30_iff {ρ ρ' : VarEnv} {cs : Codes} {v : Value} :
    Derives envPinned ρ (.varG "Tchar" []) cs v ρ' ↔
      ρ' = ρ ∧ ∃ n, IsChar n ∧ cs = [n] ∧ v = numCase n :=
  tchar_iff findGram_tchar_pinned

/-- **`Tchar`, at the corrected script.** -/
theorem tchar_text6x_iff {ρ ρ' : VarEnv} {cs : Codes} {v : Value} :
    Derives envCorrected ρ (.varG "Tchar" []) cs v ρ' ↔
      ρ' = ρ ∧ ∃ n, IsChar n ∧ cs = [n] ∧ v = numCase n :=
  tchar_iff findGram_tchar_corrected

/-- **`Tidchar`, at the pinned script.** -/
theorem tidchar_wasm30_iff {ρ ρ' : VarEnv} {cs : Codes} {v : Value} :
    Derives envPinned ρ (.varG "Tidchar" []) cs v ρ' ↔
      ρ' = ρ ∧ ∃ n, IsIdChar n ∧ cs = [n] ∧ v = numCase n :=
  tidchar_iff findGram_tidchar_pinned

/-- **`Tidchar`, at the corrected script.** -/
theorem tidchar_text6x_iff {ρ ρ' : VarEnv} {cs : Codes} {v : Value} :
    Derives envCorrected ρ (.varG "Tidchar" []) cs v ρ' ↔
      ρ' = ρ ∧ ∃ n, IsIdChar n ∧ cs = [n] ∧ v = numCase n :=
  tidchar_iff findGram_tidchar_corrected

/-- **`#665` at the pinned wasm-3.0 script.**  `test/core/comments.wast:26`'s
`(;;;;;;;;;;;;;;)` has no derivation. -/
theorem not_derives_blockcomment_semis_wasm30 {ρ ρ' : VarEnv} {v : Value} :
    ¬ Derives envPinned ρ (.varG "Tblockcomment" []) commentsWast26 v ρ' :=
  not_derives_blockcomment_semis findGram_tchar_pinned findGram_tblockcomment_pinned
    findGram_tblockchar_pinned

/-- The same, as a statement about the character encoding relation. -/
theorem not_charRel_blockcomment_semis_wasm30 {ρ : VarEnv} {v : Value} :
    ¬ charRel envPinned ρ (.varG "Tblockcomment" []) commentsWast26 v := by
  rintro ⟨ρ', h⟩
  exact not_derives_blockcomment_semis_wasm30 h

/-- **`#665` at the corrected script.**  After the patch it does. -/
theorem derives_blockcomment_semis_text6x {ρ : VarEnv} :
    Derives envCorrected ρ (.varG "Tblockcomment" []) commentsWast26 (.tuple []) ρ :=
  derives_blockcomment_corrected_semis findGram_tblockcomment_corrected

/-- **The singleton-list cast at the pinned script.**  `Tspace`, as the
stream spells it, is one white-space item, not a run of them. -/
theorem tspace_one_item_wasm30 {ρ ρ' : VarEnv} {cs : Codes} {v : Value}
    (h : Derives envPinned ρ (.varG "Tspace" []) cs v ρ') :
    ∃ σ w, Derives envPinned VarEnv.empty
      (.altG [.seqG [.textG " "], .varG "Tformat" [], .varG "Tcomment" [],
        .varG "Tannot" []]) cs w σ :=
  tspace_one_item findGram_tspace_pinned h

/-- The same at the corrected script: `#677` does not touch `Tspace`. -/
theorem tspace_one_item_text6x {ρ ρ' : VarEnv} {cs : Codes} {v : Value}
    (h : Derives envCorrected ρ (.varG "Tspace" []) cs v ρ') :
    ∃ σ w, Derives envCorrected VarEnv.empty
      (.altG [.seqG [.textG " "], .varG "Tformat" [], .varG "Tcomment" [],
        .varG "Tannot" []]) cs w σ :=
  tspace_one_item findGram_tspace_corrected h

/-- The same, carried across the UTF-8 bridge: the corrected grammar derives
the *bytes* of `(;;;;;;;;;;;;;;)`.  This is `EncRel.push` doing its job — the
statement is about `List UInt8`, where `gramRelSup_tchar_text6x_eq_bot` says
`Sem.gramRelSup` has nothing to say at all. -/
theorem textByteRel_blockcomment_semis_text6x {ρ : VarEnv} :
    textByteRel envCorrected ρ (.varG "Tblockcomment" [])
      (Unicode.utf8 "(;;;;;;;;;;;;;;)") (.tuple []) :=
  ⟨commentsWast26, by rw [commentsWast26_eq, utf8Codes_codes],
    ⟨ρ, derives_blockcomment_semis_text6x⟩⟩

end Silmaril.SpecTec.Equiv.Text
