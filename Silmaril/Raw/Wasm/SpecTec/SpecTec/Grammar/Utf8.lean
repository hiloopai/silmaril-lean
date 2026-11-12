module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Grammar.Basic
public import Silmaril.Encoding.Unicode

/-!
# UTF-8 as an instance of the byte attribute-grammar framework

`Silmaril/SpecTec/Grammar/Basic.lean` is a generic framework of attribute
grammars over byte terminals, with LEB128 (`BuN(N)`) as its first worked
instance.  This file is the second one the plan of `docs/projects/spectec/README.md`
names: **UTF-8**, i.e. the `$cont`/`$utf8` group of
`specification/wasm-3.0/5.1-binary.values.spectec:48-64` at the pin
`608711107b7f1edb13efd57b7d79b49477462d36`.

## The productions

`$utf8` is declared as a *function* `char* -> byte*`, not as a `grammar`, but
its four single-character clauses (`:53-64`) are written in exactly the shape a
production has — a sequence of byte binders, a premise restricting the scalar
value, and a premise computing it — so they transcribe into `Sym` directly.
Each clause becomes a `Sym.attr` over a `Sym.seq` of `Sym.range` terminals:

| clause | source | symbol |
| --- | --- | --- |
| `$utf8(ch) = b` | `:53-55` | `utf8P1` |
| `$utf8(ch) = b_1 b_2` | `:56-58` | `utf8P2` |
| `$utf8(ch) = b_1 b_2 b_3` | `:59-61` | `utf8P3` |
| `$utf8(ch) = b_1 b_2 b_3 b_4` | `:62-64` | `utf8P4` |

and the list clause `$utf8(ch*) = $concat_(byte, $utf8(ch)*)` (`:52`) becomes
`Sym.star (Sym.nt .char)`.  The attribute algebra is `Attr.list UInt8.toNat`,
as for LEB128: a derivation accumulates the numbers its terminals contribute,
and a clause's value expression is the `Sym.attr` that replaces them by the one
scalar value they denote.

Two premises are carried by the terminal ranges rather than by the value
expression, exactly as `lebP1`/`lebP2` carry `n < 2^7` and `n >= 2^7`:

* `$cont(b)` is defined on `0x80 < b < 0xC0` (`:49`), so a continuation byte is
  `Sym.range contLo 0xBF`.  `contLo` is a *parameter* here: `0x81` is the
  pinned reading and `0x80` the one erratum `#655` installs.
* the leading byte of each clause lies in `0x00..0x7F`, `0xC0..0xDF`,
  `0xE0..0xEF` and `0xF0..0xFF`.  The lower bounds are SpecTec's partial
  subtractions `b_1 - 0xC0`, `b_1 - 0xE0`, `b_1 - 0xF0` made explicit (the same
  reading `Silmaril/Wasm/Binary/Basic.lean:48-51` documents); the upper bounds
  are *forced* by the clause's own range premise, and `denote_of_utf8Char`
  below derives them rather than assuming them.  Putting them in the terminal
  makes the four clauses visibly separated, which is what the functionality
  section below needs.

## What is proved

* `denote_char_iff_utf8Char` — the denotation of the corrected grammar at
  `.char` is `Silmaril.Wasm.Binary.Utf8Char`, in both directions;
  `denote_chars_iff_utf8` lifts it to `Silmaril.Wasm.Binary.Utf8`.
* `grin_disagreement_pinned` — the pinned grammar and `Utf8Char` **disagree**:
  the pinned four-byte premise `U+10000 <= ch < U+11000` (`:63`, `#656`)
  rejects U+1F601, which `Utf8Char` accepts.  The counterexample is chosen so
  that `#655` is not implicated: no byte of its spelling is `0x80`, so it is
  rejected by `utf8Gram 0x80 0x11000` too (`grin_disagreement_655`), and the
  blame falls on `#656` alone.  `denote_pinned_lt_11000` is the general form:
  the pinned grammar spells *no* scalar value from U+11000 up.
* `denote_char_mono` and `denote_pinned_lt_fixed` — the pinned grammar derives
  *strictly fewer* characters than the corrected one.
* `altSeparated_utf8CharProds`, `unambiguous_utf8_char`,
  `functional_utf8_chars` — the framework's decidable leading-byte condition
  applies, so the generic lemmas alone give unambiguity; `utf8Char_prefixFree`
  and `utf8_functional` then reprove two results of
  `Silmaril/Wasm/Binary/Basic.lean` (one of which is `private` there) from the
  framework.

## Not here

`Bname` (`:66-67`) is `b*:Blist(Bbyte) => name -- if $utf8(name) = b*`, so it
needs `Blist`, hence the `Bu32` nonterminal of the LEB128 instance, inside the
same grammar.  The two instances use different nonterminal types (`Nat` there,
`Utf8Nt` here); joining them is a matter of taking the sum, but it is a
different piece of work and nothing below depends on it.
-/

@[expose] public section

namespace Silmaril.SpecTec.Grammar

open Silmaril.Wasm.Binary

section Utf8

-- `denote_of_utf8Char` and `utf8Char_of_denote` discharge four clauses at once
-- behind `<;>`, which needs more elaboration depth than the default 512.
set_option maxRecDepth 4000

/-! ## The grammar -/

/-- The nonterminals of the UTF-8 grammar: one scalar value, and a sequence of
them.  `$cont` is not among them — it is a `def`, not a `grammar`, and its
graph is a byte interval, so it is inlined as a `Sym.range`. -/
inductive Utf8Nt where
  /-- `$utf8(ch)` for a single scalar value (`5.1-binary.values.spectec:53-64`). -/
  | char
  /-- `$utf8(ch*)` (`5.1-binary.values.spectec:52`). -/
  | chars
  deriving DecidableEq, Inhabited

/-- The attribute algebra of the UTF-8 grammar: a derivation accumulates the
numbers its terminals contribute, as for LEB128 (`lebAlg`). -/
def utf8Alg : Attr (List Nat) := Attr.list UInt8.toNat

/-- A sequence of byte-interval terminals, one per entry of `rs`: the body of
every `$utf8` clause has this shape. -/
def utf8RangeSeq (rs : List (UInt8 × UInt8)) : Sym Utf8Nt (List Nat) :=
  .seq (rs.map fun p => .range p.1 p.2)

/-- What `utf8RangeSeq rs` denotes: one byte from each interval, and the list of
their values as the attribute. -/
def utf8RangesRel : List (UInt8 × UInt8) → EncRel Bytes (List Nat)
  | [] => fun bs ns => bs = [] ∧ ns = []
  | p :: rs => fun bs ns => ∃ (b : UInt8) (bs' : Bytes) (ns' : List Nat),
      p.1 ≤ b ∧ b ≤ p.2 ∧ utf8RangesRel rs bs' ns' ∧ bs = b :: bs' ∧ ns = b.toNat :: ns'

/-- `ch = $(2^6*(b_1 - 0xC0) + $cont(b_2))`
(`5.1-binary.values.spectec:58`). -/
def utf8Val2 (b₁ b₂ : Nat) : Nat := 2 ^ 6 * (b₁ - 0xC0) + (b₂ - 0x80)

/-- `ch = $(2^12*(b_1 - 0xE0) + 2^6*$cont(b_2) + $cont(b_3))`
(`5.1-binary.values.spectec:61`). -/
def utf8Val3 (b₁ b₂ b₃ : Nat) : Nat :=
  2 ^ 12 * (b₁ - 0xE0) + 2 ^ 6 * (b₂ - 0x80) + (b₃ - 0x80)

/-- `ch = $(2^18*(b_1 - 0xF0) + 2^12*$cont(b_2) + 2^6*$cont(b_3) + $cont(b_4))`
(`5.1-binary.values.spectec:64`). -/
def utf8Val4 (b₁ b₂ b₃ b₄ : Nat) : Nat :=
  2 ^ 18 * (b₁ - 0xF0) + 2 ^ 12 * (b₂ - 0x80) + 2 ^ 6 * (b₃ - 0x80) + (b₄ - 0x80)

/-- The value expression of `def $utf8(ch) = b -- if ch < U+0080 -- if ch = b`
(`:53-55`).  Both premises are in the terminal: `ch = b` makes the attribute the
byte itself, and `ch < U+0080` is the interval `0x00..0x7F`. -/
def utf8Act1 : List Nat → Option (List Nat)
  | [b] => some [b]
  | _ => none

/-- The value expression of the two-byte clause (`:56-58`).  The upper bound
`ch < U+0800` is implied by the terminals (`0x40*0x1F + 0x3F = 0x7FF`), so only
`U+0080 <= ch` is left as a side condition. -/
def utf8Act2 : List Nat → Option (List Nat)
  | [b₁, b₂] => if 0x80 ≤ utf8Val2 b₁ b₂ then some [utf8Val2 b₁ b₂] else none
  | _ => none

/-- The value expression of the three-byte clause (`:59-61`).  The surrogate
gap `U+D800..U+DFFF` is not implied by any terminal, so the whole disjunction
stays here. -/
def utf8Act3 : List Nat → Option (List Nat)
  | [b₁, b₂, b₃] =>
      if 0x800 ≤ utf8Val3 b₁ b₂ b₃ ∧ utf8Val3 b₁ b₂ b₃ < 0xD800 ∨
          0xE000 ≤ utf8Val3 b₁ b₂ b₃ ∧ utf8Val3 b₁ b₂ b₃ < 0x10000
        then some [utf8Val3 b₁ b₂ b₃] else none
  | _ => none

/-- The value expression of the four-byte clause (`:62-64`), with the upper
bound of `-- if U+10000 <= ch < U+11000` as the parameter `hi`: `0x11000` is
what `:63` says and `0x110000` is what `#656` corrects it to. -/
def utf8Act4 (hi : Nat) : List Nat → Option (List Nat)
  | [b₁, b₂, b₃, b₄] =>
      if 0x10000 ≤ utf8Val4 b₁ b₂ b₃ b₄ ∧ utf8Val4 b₁ b₂ b₃ b₄ < hi
        then some [utf8Val4 b₁ b₂ b₃ b₄] else none
  | _ => none

/-- `def $utf8(ch) = b -- if ch < U+0080 -- if ch = b` (`:53-55`). -/
def utf8P1 : Sym Utf8Nt (List Nat) := .attr utf8Act1 (utf8RangeSeq [(0x00, 0x7F)])

/-- `def $utf8(ch) = b_1 b_2` (`:56-58`), with `contLo` the lower bound of
`$cont` (`:49`). -/
def utf8P2 (contLo : UInt8) : Sym Utf8Nt (List Nat) :=
  .attr utf8Act2 (utf8RangeSeq [(0xC0, 0xDF), (contLo, 0xBF)])

/-- `def $utf8(ch) = b_1 b_2 b_3` (`:59-61`). -/
def utf8P3 (contLo : UInt8) : Sym Utf8Nt (List Nat) :=
  .attr utf8Act3 (utf8RangeSeq [(0xE0, 0xEF), (contLo, 0xBF), (contLo, 0xBF)])

/-- `def $utf8(ch) = b_1 b_2 b_3 b_4` (`:62-64`), with `hi` the upper bound of
its range premise. -/
def utf8P4 (contLo : UInt8) (hi : Nat) : Sym Utf8Nt (List Nat) :=
  .attr (utf8Act4 hi) (utf8RangeSeq [(0xF0, 0xFF), (contLo, 0xBF), (contLo, 0xBF), (contLo, 0xBF)])

/-- The four clauses of `$utf8(ch)`, as the alternative productions of
`Utf8Nt.char`. -/
def utf8CharProds (contLo : UInt8) (hi : Nat) : List (Sym Utf8Nt (List Nat)) :=
  [utf8P1, utf8P2 contLo, utf8P3 contLo, utf8P4 contLo hi]

/-- The production table: `$utf8(ch)` has four clauses, `$utf8(ch*)` is their
`$concat_` (`:52`). -/
def utf8Prods (contLo : UInt8) (hi : Nat) : Utf8Nt → List (Sym Utf8Nt (List Nat))
  | .char => utf8CharProds contLo hi
  | .chars => [.star (.nt .char)]

/-- The UTF-8 grammar, parameterised by the two bounds the errata of
`#650` move. -/
def utf8Gram (contLo : UInt8) (hi : Nat) : Gram Utf8Nt (List Nat) :=
  ⟨utf8Alg, utf8Prods contLo hi⟩

/-- The grammar as `5.1-binary.values.spectec:48-64` is pinned: `$cont` lower
bound `0x80 < b` (`:49`) and four-byte upper bound `U+11000` (`:63`). -/
def utf8GramPinned : Gram Utf8Nt (List Nat) := utf8Gram 0x81 0x11000

/-- The pinned grammar with `#655` applied and `#656` *not*: `$cont` is
`0x80 <= b < 0xC0`, the four-byte range still ends at `U+11000`.  This is the
grammar the disagreement below is stated against, so that the blame falls on
`#656` alone. -/
def utf8Gram655 : Gram Utf8Nt (List Nat) := utf8Gram 0x80 0x11000

/-- The grammar `Silmaril.SpecTec.IL.Binary51` produces: both `#655` and `#656`
applied. -/
def utf8GramFixed : Gram Utf8Nt (List Nat) := utf8Gram 0x80 0x110000

/-! ## The denotation of the clause bodies -/

/-- Every `utf8Gram` has the same attribute algebra. -/
@[simp] theorem alg_utf8Gram (contLo : UInt8) (hi : Nat) : (utf8Gram contLo hi).alg = utf8Alg :=
  rfl

/-- A sequence of byte-interval terminals denotes `utf8RangesRel`: this is the one
induction that every clause below reuses. -/
theorem denote_utf8RangeSeq {G : Gram Utf8Nt (List Nat)} (hG : G.alg = utf8Alg)
    (rs : List (UInt8 × UInt8)) : denote G (utf8RangeSeq rs) = utf8RangesRel rs := by
  induction rs with
  | nil =>
    simp only [utf8RangeSeq, List.map_nil, denote_seq, appendAll_nil, hG]
    rfl
  | cons p rs ih =>
    have hcons : denote G (utf8RangeSeq (p :: rs))
        = appendRel G.alg (rangeRel G.alg p.1 p.2) (denote G (utf8RangeSeq rs)) := by
      simp only [utf8RangeSeq, List.map_cons, denote_seq, appendAll_cons, denote_range]
    ext bs ns
    rw [hcons, ih, hG]
    constructor
    · rintro ⟨b₁, a₁, b₂, a₂, ⟨b, hlo, hhi, rfl, rfl⟩, h₂, rfl, rfl⟩
      exact ⟨b, b₂, a₂, hlo, hhi, h₂, rfl, rfl⟩
    · rintro ⟨b, bs', ns', hlo, hhi, h, rfl, rfl⟩
      exact ⟨[b], [b.toNat], bs', ns', ⟨b, hlo, hhi, rfl, rfl⟩, h, rfl, rfl⟩


/-! ## The denotation of each clause -/

/-- `$utf8(ch) = b -- if ch < U+0080` (`:53-55`). -/
theorem denote_utf8P1_iff {contLo : UInt8} {hi : Nat} {bs : Bytes} {a : List Nat} :
    denote (utf8Gram contLo hi) utf8P1 bs a ↔
      ∃ b : UInt8, b ≤ 0x7F ∧ bs = [b] ∧ a = [b.toNat] := by
  rw [utf8P1, denote_attr, denote_utf8RangeSeq (alg_utf8Gram contLo hi)]
  constructor
  · rintro ⟨a', ⟨b, bs', ns', -, hb, ⟨rfl, rfl⟩, rfl, rfl⟩, hact⟩
    exact ⟨b, hb, rfl, by simpa [utf8Act1] using hact.symm⟩
  · rintro ⟨b, hb, rfl, rfl⟩
    exact ⟨[b.toNat], ⟨b, [], [], zero_le_uint8 b, hb, ⟨rfl, rfl⟩, rfl, rfl⟩, rfl⟩

/-- `$utf8(ch) = b_1 b_2` (`:56-58`). -/
theorem denote_utf8P2_iff {contLo : UInt8} {hi : Nat} {bs : Bytes} {a : List Nat} :
    denote (utf8Gram contLo hi) (utf8P2 contLo) bs a ↔
      ∃ b₁ b₂ : UInt8, 0xC0 ≤ b₁ ∧ b₁ ≤ 0xDF ∧ contLo ≤ b₂ ∧ b₂ ≤ 0xBF ∧ bs = [b₁, b₂] ∧
        0x80 ≤ utf8Val2 b₁.toNat b₂.toNat ∧ a = [utf8Val2 b₁.toNat b₂.toNat] := by
  rw [utf8P2, denote_attr, denote_utf8RangeSeq (alg_utf8Gram contLo hi)]
  constructor
  · rintro ⟨a', ⟨b₁, _, _, h₁, h₂, ⟨b₂, _, _, h₃, h₄, ⟨rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩, hact⟩
    refine ⟨b₁, b₂, h₁, h₂, h₃, h₄, rfl, ?_, ?_⟩ <;>
      · simp only [utf8Act2] at hact
        split at hact
        · simp_all
        · exact absurd hact (by simp)
  · rintro ⟨b₁, b₂, h₁, h₂, h₃, h₄, rfl, hv, rfl⟩
    exact ⟨[b₁.toNat, b₂.toNat],
      ⟨b₁, _, _, h₁, h₂, ⟨b₂, [], [], h₃, h₄, ⟨rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩,
      by simp [utf8Act2, hv]⟩

/-- `$utf8(ch) = b_1 b_2 b_3` (`:59-61`). -/
theorem denote_utf8P3_iff {contLo : UInt8} {hi : Nat} {bs : Bytes} {a : List Nat} :
    denote (utf8Gram contLo hi) (utf8P3 contLo) bs a ↔
      ∃ b₁ b₂ b₃ : UInt8, 0xE0 ≤ b₁ ∧ b₁ ≤ 0xEF ∧ contLo ≤ b₂ ∧ b₂ ≤ 0xBF ∧
        contLo ≤ b₃ ∧ b₃ ≤ 0xBF ∧ bs = [b₁, b₂, b₃] ∧
        (0x800 ≤ utf8Val3 b₁.toNat b₂.toNat b₃.toNat ∧
            utf8Val3 b₁.toNat b₂.toNat b₃.toNat < 0xD800 ∨
          0xE000 ≤ utf8Val3 b₁.toNat b₂.toNat b₃.toNat ∧
            utf8Val3 b₁.toNat b₂.toNat b₃.toNat < 0x10000) ∧
        a = [utf8Val3 b₁.toNat b₂.toNat b₃.toNat] := by
  rw [utf8P3, denote_attr, denote_utf8RangeSeq (alg_utf8Gram contLo hi)]
  constructor
  · rintro ⟨a', ⟨b₁, _, _, h₁, h₂, ⟨b₂, _, _, h₃, h₄,
      ⟨b₃, _, _, h₅, h₆, ⟨rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩, hact⟩
    refine ⟨b₁, b₂, b₃, h₁, h₂, h₃, h₄, h₅, h₆, rfl, ?_, ?_⟩ <;>
      · simp only [utf8Act3] at hact
        split at hact
        · simp_all
        · exact absurd hact (by simp)
  · rintro ⟨b₁, b₂, b₃, h₁, h₂, h₃, h₄, h₅, h₆, rfl, hv, rfl⟩
    exact ⟨[b₁.toNat, b₂.toNat, b₃.toNat],
      ⟨b₁, _, _, h₁, h₂, ⟨b₂, _, _, h₃, h₄,
        ⟨b₃, [], [], h₅, h₆, ⟨rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩,
      by simp [utf8Act3, hv]⟩

/-- `$utf8(ch) = b_1 b_2 b_3 b_4` (`:62-64`).  The clause's upper bound `hi` is
the only thing `#656` changes. -/
theorem denote_utf8P4_iff {contLo : UInt8} {hi : Nat} {bs : Bytes} {a : List Nat} :
    denote (utf8Gram contLo hi) (utf8P4 contLo hi) bs a ↔
      ∃ b₁ b₂ b₃ b₄ : UInt8, 0xF0 ≤ b₁ ∧ contLo ≤ b₂ ∧ b₂ ≤ 0xBF ∧ contLo ≤ b₃ ∧ b₃ ≤ 0xBF ∧
        contLo ≤ b₄ ∧ b₄ ≤ 0xBF ∧ bs = [b₁, b₂, b₃, b₄] ∧
        0x10000 ≤ utf8Val4 b₁.toNat b₂.toNat b₃.toNat b₄.toNat ∧
        utf8Val4 b₁.toNat b₂.toNat b₃.toNat b₄.toNat < hi ∧
        a = [utf8Val4 b₁.toNat b₂.toNat b₃.toNat b₄.toNat] := by
  rw [utf8P4, denote_attr, denote_utf8RangeSeq (alg_utf8Gram contLo hi)]
  constructor
  · rintro ⟨a', ⟨b₁, _, _, h₁, -, ⟨b₂, _, _, h₃, h₄, ⟨b₃, _, _, h₅, h₆,
      ⟨b₄, _, _, h₇, h₈, ⟨rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩, hact⟩
    refine ⟨b₁, b₂, b₃, b₄, h₁, h₃, h₄, h₅, h₆, h₇, h₈, rfl, ?_, ?_, ?_⟩ <;>
      · simp only [utf8Act4] at hact
        split at hact
        · simp_all
        · exact absurd hact (by simp)
  · rintro ⟨b₁, b₂, b₃, b₄, h₁, h₃, h₄, h₅, h₆, h₇, h₈, rfl, hlo, hhi, rfl⟩
    exact ⟨[b₁.toNat, b₂.toNat, b₃.toNat, b₄.toNat],
      ⟨b₁, _, _, h₁, le_FF_uint8 b₁, ⟨b₂, _, _, h₃, h₄, ⟨b₃, _, _, h₅, h₆,
        ⟨b₄, [], [], h₇, h₈, ⟨rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩, rfl, rfl⟩,
      by simp [utf8Act4, hlo, hhi]⟩

/-- `$utf8(ch)` is the join of its four clauses. -/
theorem denote_char_alt {contLo : UInt8} {hi : Nat} {bs : Bytes} {a : List Nat} :
    denote (utf8Gram contLo hi) (.nt .char) bs a ↔
      denote (utf8Gram contLo hi) utf8P1 bs a ∨
      denote (utf8Gram contLo hi) (utf8P2 contLo) bs a ∨
      denote (utf8Gram contLo hi) (utf8P3 contLo) bs a ∨
      denote (utf8Gram contLo hi) (utf8P4 contLo hi) bs a := by
  rw [denote_nt]
  show supList ((utf8CharProds contLo hi).map (denote (utf8Gram contLo hi))) bs a ↔ _
  simp [utf8CharProds]

/-- `$utf8(ch*) = $concat_(byte, $utf8(ch)*)` (`:52`) is the Kleene closure of
`$utf8(ch)`. -/
theorem denote_chars (contLo : UInt8) (hi : Nat) :
    denote (utf8Gram contLo hi) (.nt .chars)
      = kleene utf8Alg (denote (utf8Gram contLo hi) (.nt .char)) := by
  rw [denote_nt]
  show supList ([Sym.star (.nt .char)].map (denote (utf8Gram contLo hi))) = _
  simp [supList, denote_star]

/-! ## Agreement with `Silmaril.Wasm.Binary.Utf8Char`

`Silmaril/Wasm/Binary/Basic.lean:159-173` transcribes the same four clauses as
an inductive relation between a `Char` and its spelling, already carrying both
corrections (`Silmaril/Wasm/Binary/Basic.lean:19-24`).  So it is the *corrected*
grammar that it should agree with, and it does. -/

/-- The `toNat` of every byte constant the productions mention; the arithmetic
below is all `omega` over these. -/
private theorem byteConsts :
    (0x7F : UInt8).toNat = 127 ∧ (0x80 : UInt8).toNat = 128 ∧ (0xBF : UInt8).toNat = 191 ∧
      (0xC0 : UInt8).toNat = 192 ∧ (0xDF : UInt8).toNat = 223 ∧ (0xE0 : UInt8).toNat = 224 ∧
      (0xEF : UInt8).toNat = 239 ∧ (0xF0 : UInt8).toNat = 240 := by decide

/-- Every `Utf8Char` spelling is derived by the corrected grammar, with the
scalar value as its attribute. -/
theorem denote_of_utf8Char {c : Char} {bs : Bytes} (h : Utf8Char c bs) :
    denote utf8GramFixed (.nt .char) bs [c.toNat] := by
  obtain ⟨c7F, c80, cBF, cC0, cDF, cE0, cEF, cF0⟩ := byteConsts
  rw [utf8GramFixed, denote_char_alt]
  cases h with
  | one b hlt he =>
    exact Or.inl (denote_utf8P1_iff.mpr
      ⟨b, UInt8.le_iff_toNat_le.mpr (by omega), rfl, by rw [he]⟩)
  | two b₁ b₂ hlo hhi h₁ h₂ he =>
    obtain ⟨hc1, hc2⟩ := h₂
    simp only [Nat.reducePow] at he
    refine Or.inr (Or.inl (denote_utf8P2_iff.mpr ⟨b₁, b₂, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩)) <;>
      simp only [utf8Val2, Nat.reducePow, UInt8.le_iff_toNat_le, List.cons.injEq, and_true] <;>
      omega
  | three b₁ b₂ b₃ hrange h₁ h₂ h₃ he =>
    obtain ⟨hc1, hc2⟩ := h₂
    obtain ⟨hd1, hd2⟩ := h₃
    simp only [Nat.reducePow] at he
    refine Or.inr (Or.inr (Or.inl (denote_utf8P3_iff.mpr
      ⟨b₁, b₂, b₃, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩))) <;>
      simp only [utf8Val3, Nat.reducePow, UInt8.le_iff_toNat_le, List.cons.injEq, and_true] <;>
      omega
  | four b₁ b₂ b₃ b₄ hlo hhi h₁ h₂ h₃ h₄ he =>
    obtain ⟨hc1, hc2⟩ := h₂
    obtain ⟨hd1, hd2⟩ := h₃
    obtain ⟨he1, he2⟩ := h₄
    simp only [Nat.reducePow] at he
    refine Or.inr (Or.inr (Or.inr (denote_utf8P4_iff.mpr
      ⟨b₁, b₂, b₃, b₄, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩))) <;>
      simp only [utf8Val4, Nat.reducePow, UInt8.le_iff_toNat_le, List.cons.injEq, and_true] <;>
      omega

/-- Pick the `Char` a derivation's attribute names, given that the attribute is
a scalar value.  `Silmaril.Unicode.charToNat_ofNat` is what makes the choice. -/
private theorem exists_char {n : Nat} (hv : n < 0xD800 ∨ (0xDFFF < n ∧ n < 0x110000))
    {bs : Bytes} (hc : ∀ c : Char, c.toNat = n → Utf8Char c bs) :
    ∃ c : Char, [n] = [c.toNat] ∧ Utf8Char c bs :=
  ⟨Char.ofNat n, by rw [Unicode.charToNat_ofNat hv], hc _ (Unicode.charToNat_ofNat hv)⟩

/-- Every derivation of the corrected grammar is a `Utf8Char` derivation: its
attribute is a single scalar value, and it spells that value. -/
theorem utf8Char_of_denote {bs : Bytes} {a : List Nat}
    (h : denote utf8GramFixed (.nt .char) bs a) :
    ∃ c : Char, a = [c.toNat] ∧ Utf8Char c bs := by
  obtain ⟨c7F, c80, cBF, cC0, cDF, cE0, cEF, cF0⟩ := byteConsts
  rw [utf8GramFixed, denote_char_alt] at h
  rcases h with h | h | h | h
  · obtain ⟨b, hb, rfl, rfl⟩ := denote_utf8P1_iff.mp h
    rw [UInt8.le_iff_toNat_le] at hb
    exact exists_char (Or.inl (by omega)) (fun c hc => Utf8Char.one b (by omega) hc)
  · obtain ⟨b₁, b₂, h₁, h₂, h₃, h₄, rfl, hv, rfl⟩ := denote_utf8P2_iff.mp h
    rw [UInt8.le_iff_toNat_le] at h₁ h₂ h₃ h₄
    simp only [utf8Val2, Nat.reducePow] at hv ⊢
    refine exists_char (Or.inl (by omega)) (fun c hc => ?_)
    exact Utf8Char.two b₁ b₂ (by omega) (by omega) (by omega) ⟨by omega, by omega⟩
      (by (try simp only [Nat.reducePow]); omega)
  · obtain ⟨b₁, b₂, b₃, h₁, h₂, h₃, h₄, h₅, h₆, rfl, hv, rfl⟩ := denote_utf8P3_iff.mp h
    rw [UInt8.le_iff_toNat_le] at h₁ h₂ h₃ h₄ h₅ h₆
    simp only [utf8Val3, Nat.reducePow] at hv ⊢
    refine exists_char (by omega) (fun c hc => ?_)
    exact Utf8Char.three b₁ b₂ b₃ (by omega) (by omega) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (by (try simp only [Nat.reducePow]); omega)
  · obtain ⟨b₁, b₂, b₃, b₄, h₁, h₂, h₃, h₄, h₅, h₆, h₇, rfl, hlo, hhi, rfl⟩ :=
      denote_utf8P4_iff.mp h
    rw [UInt8.le_iff_toNat_le] at h₁ h₂ h₃ h₄ h₅ h₆ h₇
    simp only [utf8Val4, Nat.reducePow] at hlo hhi ⊢
    refine exists_char (Or.inr ⟨by omega, by omega⟩) (fun c hc => ?_)
    exact Utf8Char.four b₁ b₂ b₃ b₄ (by omega) (by omega) (by omega) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by (try simp only [Nat.reducePow]); omega)

/-- **The corrected grammar is `Silmaril.Wasm.Binary.Utf8Char`**, in both
directions: the denotation of `$utf8(ch)` relates exactly the byte strings and
scalar values that `Silmaril/Wasm/Binary/Basic.lean:159-173` relates. -/
theorem denote_char_iff_utf8Char (c : Char) (bs : Bytes) :
    denote utf8GramFixed (.nt .char) bs [c.toNat] ↔ Utf8Char c bs := by
  refine ⟨fun h => ?_, denote_of_utf8Char⟩
  obtain ⟨c', he, hu⟩ := utf8Char_of_denote h
  have : c = c' := Char.ext (UInt32.toNat_inj.mp (by simpa using he))
  exact this ▸ hu

/-! ## Agreement with `Silmaril.Wasm.Binary.Utf8`

`$utf8(ch*) = $concat_(byte, $utf8(ch)*)` (`:52`) is `Sym.star`, whose
denotation is the Kleene closure; `Silmaril.Wasm.Binary.Utf8` is the same
concatenation written as `Seq`. -/

/-- Every `Utf8` spelling is derived by the corrected grammar at `chars`, with
the list of scalar values as its attribute. -/
theorem denote_chars_of_utf8 {cs : List Char} {bs : Bytes} (h : Utf8 cs bs) :
    denote utf8GramFixed (.nt .chars) bs (cs.map Char.toNat) := by
  have h' : Seq (fun b c => Utf8Char c b) bs cs := h
  clear h
  rw [utf8GramFixed, denote_chars]
  induction h' with
  | nil => exact kleene_apply.mpr ⟨0, rfl, rfl⟩
  | @cons b bs' c cs' hb _ ih =>
    obtain ⟨k, hk⟩ := kleene_apply.mp ih
    exact kleene_apply.mpr ⟨k + 1, b, [c.toNat], bs', cs'.map Char.toNat,
      denote_of_utf8Char hb, hk, rfl, rfl⟩

/-- Every derivation of the corrected grammar at `chars` is a `Utf8`
derivation. -/
theorem utf8_of_denote_chars {bs : Bytes} {ns : List Nat}
    (h : denote utf8GramFixed (.nt .chars) bs ns) :
    ∃ cs : List Char, ns = cs.map Char.toNat ∧ Utf8 cs bs := by
  rw [utf8GramFixed, denote_chars] at h
  obtain ⟨k, hk⟩ := kleene_apply.mp h
  clear h
  induction k generalizing bs ns with
  | zero =>
    obtain ⟨rfl, rfl⟩ := hk
    exact ⟨[], rfl, Seq.nil⟩
  | succ k ih =>
    obtain ⟨b₁, a₁, b₂, a₂, h₁, h₂, rfl, rfl⟩ := hk
    obtain ⟨c, rfl, hc⟩ := utf8Char_of_denote h₁
    obtain ⟨cs, rfl, hcs⟩ := ih h₂
    exact ⟨c :: cs, rfl, Seq.cons hc hcs⟩

/-- `List.map Char.toNat` is injective: scalar values name their characters. -/
private theorem map_toNat_inj {cs cs' : List Char}
    (h : cs.map Char.toNat = cs'.map Char.toNat) : cs = cs' := by
  induction cs generalizing cs' with
  | nil => cases cs' <;> simp_all
  | cons c cs ih =>
    cases cs' with
    | nil => simp at h
    | cons c' cs' =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [Char.ext (UInt32.toNat_inj.mp h.1), ih h.2]

/-- **The corrected grammar is `Silmaril.Wasm.Binary.Utf8`**, in both
directions. -/
theorem denote_chars_iff_utf8 (cs : List Char) (bs : Bytes) :
    denote utf8GramFixed (.nt .chars) bs (cs.map Char.toNat) ↔ Utf8 cs bs := by
  refine ⟨fun h => ?_, denote_chars_of_utf8⟩
  obtain ⟨cs', he, hu⟩ := utf8_of_denote_chars h
  exact map_toNat_inj he ▸ hu

/-! ## The known erratum: `#656`

`5.1-binary.values.spectec:63` reads `-- if U+10000 <= ch < U+11000` in the
four-byte clause of `$utf8`; the bound is one hex digit short.
`Silmaril/SpecTec/Errata/Binary51.lean` patches the elaborated `69632` to
`1114112`, and `Silmaril/Wasm/Binary/Basic.lean:22-24` records the same
correction.  So the agreement proved above is an agreement with the
*corrected* grammar, and against the pinned one it has to fail.  Here is a
witness.

U+1F601 is chosen rather than, say, U+1F600 because none of its four bytes is
`0x80`: `#655` (the `$cont` lower bound, `:49`) therefore plays no part,
and `not_denote_grinChar_pinned` is proved for *every* `contLo`, in particular
for the `0x80` that `#655` installs.  The disagreement is `#656` alone. -/

/-- U+1F601, `GRINNING FACE WITH SMILING EYES`: a scalar value in
`[U+11000, U+110000)`, the interval `5.1-binary.values.spectec:63` loses. -/
def grinChar : Char := Char.ofNat 0x1F601

/-- The UTF-8 spelling of `grinChar`.  No byte of it is `0x80`. -/
def grinBytes : Bytes := [0xF0, 0x9F, 0x98, 0x81]

/-- `grinChar` really is U+1F601. -/
theorem grinChar_toNat : grinChar.toNat = 0x1F601 :=
  Unicode.charToNat_ofNat (Or.inr (by decide))

/-- `0x80` does not occur in `grinBytes`, so `#655` is not implicated
in the disagreement below. -/
theorem grinBytes_no_cont_80 : (0x80 : UInt8) ∉ grinBytes := by decide

/-- `Silmaril.Wasm.Binary.Utf8Char` accepts `grinBytes` as `grinChar`. -/
theorem utf8Char_grinChar : Utf8Char grinChar grinBytes := by
  show Utf8Char grinChar [0xF0, 0x9F, 0x98, 0x81]
  refine Utf8Char.four 0xF0 0x9F 0x98 0x81 ?_ ?_ (by decide) ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ ?_ <;> rw [grinChar_toNat] <;> decide

/-- So does the corrected grammar. -/
theorem denote_grinChar_fixed :
    denote utf8GramFixed (.nt .char) grinBytes [grinChar.toNat] :=
  denote_of_utf8Char utf8Char_grinChar

/-- **The pinned grammar rejects it** — whatever `$cont` bound is used, so the
blame is on `5.1-binary.values.spectec:63` alone.  Note the statement is not
"derives a different value" but "derives nothing": the first three clauses
cannot spell four bytes, and the fourth is cut off at `U+11000`. -/
theorem not_denote_grinChar_pinned (contLo : UInt8) (a : List Nat) :
    ¬ denote (utf8Gram contLo 0x11000) (.nt .char) grinBytes a := by
  rw [denote_char_alt]
  rintro (h | h | h | h)
  · obtain ⟨b, -, hb, -⟩ := denote_utf8P1_iff.mp h
    exact absurd hb (by simp [grinBytes])
  · obtain ⟨b₁, b₂, -, -, -, -, hb, -⟩ := denote_utf8P2_iff.mp h
    exact absurd hb (by simp [grinBytes])
  · obtain ⟨b₁, b₂, b₃, -, -, -, -, -, -, hb, -⟩ := denote_utf8P3_iff.mp h
    exact absurd hb (by simp [grinBytes])
  · obtain ⟨b₁, b₂, b₃, b₄, -, -, -, -, -, -, -, hb, -, hhi, -⟩ := denote_utf8P4_iff.mp h
    simp only [grinBytes, List.cons.injEq, and_true] at hb
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hb
    exact absurd hhi (by decide)

/-- **The general form of the erratum.**  Under the pinned bound of
`5.1-binary.values.spectec:63`, the grammar derives no scalar value at or above
U+11000 at all: the first three clauses cannot reach that high, and the fourth
is cut off there.  This holds for every `$cont` bound, so it is `#656` alone. -/
theorem denote_pinned_lt_11000 {contLo : UInt8} {bs : Bytes} {n : Nat}
    (h : denote (utf8Gram contLo 0x11000) (.nt .char) bs [n]) : n < 0x11000 := by
  obtain ⟨c7F, c80, cBF, cC0, cDF, cE0, cEF, cF0⟩ := byteConsts
  rw [denote_char_alt] at h
  rcases h with h | h | h | h
  · obtain ⟨b, hb, -, ha⟩ := denote_utf8P1_iff.mp h
    rw [UInt8.le_iff_toNat_le] at hb
    simp only [List.cons.injEq, and_true] at ha
    omega
  · obtain ⟨b₁, b₂, -, h₂, -, h₄, -, -, ha⟩ := denote_utf8P2_iff.mp h
    rw [UInt8.le_iff_toNat_le] at h₂ h₄
    simp only [List.cons.injEq, and_true, utf8Val2, Nat.reducePow] at ha
    omega
  · obtain ⟨b₁, b₂, b₃, -, -, -, -, -, -, -, hv, ha⟩ := denote_utf8P3_iff.mp h
    simp only [List.cons.injEq, and_true, utf8Val3, Nat.reducePow] at ha
    simp only [utf8Val3, Nat.reducePow] at hv
    omega
  · obtain ⟨b₁, b₂, b₃, b₄, -, -, -, -, -, -, -, -, -, hhi, ha⟩ := denote_utf8P4_iff.mp h
    simp only [List.cons.injEq, and_true, utf8Val4, Nat.reducePow] at ha
    simp only [utf8Val4, Nat.reducePow] at hhi
    omega

/-- No scalar value from U+11000 up is spelled by the pinned grammar. -/
theorem not_denote_pinned_of_11000_le {contLo : UInt8} {c : Char} (hc : 0x11000 ≤ c.toNat)
    {bs : Bytes} : ¬ denote (utf8Gram contLo 0x11000) (.nt .char) bs [c.toNat] :=
  fun h => absurd (denote_pinned_lt_11000 h) (by omega)

/-- **The disagreement, for every scalar value `#656` loses**: `Utf8Char`
spells it, the pinned grammar does not.  `grin_disagreement_pinned` is the
instance at U+1F601. -/
theorem denote_fixed_not_pinned {c : Char} (hc : 0x11000 ≤ c.toNat) {bs : Bytes}
    (h : Utf8Char c bs) :
    denote utf8GramFixed (.nt .char) bs [c.toNat] ∧
      ¬ denote utf8GramPinned (.nt .char) bs [c.toNat] :=
  ⟨denote_of_utf8Char h, not_denote_pinned_of_11000_le hc⟩

/-- **The disagreement, as the pinned source stands.** -/
theorem grin_disagreement_pinned :
    Utf8Char grinChar grinBytes ∧ ∀ a, ¬ denote utf8GramPinned (.nt .char) grinBytes a :=
  ⟨utf8Char_grinChar, not_denote_grinChar_pinned 0x81⟩

/-- **The disagreement with `#655` already applied**: still there, so it
is `#656` that causes it. -/
theorem grin_disagreement_655 :
    Utf8Char grinChar grinBytes ∧ ∀ a, ¬ denote utf8Gram655 (.nt .char) grinBytes a :=
  ⟨utf8Char_grinChar, not_denote_grinChar_pinned 0x80⟩

/-- `≤` on `UInt8`, transitively. -/
private theorem uint8_le_trans {a b c : UInt8} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  UInt8.le_iff_toNat_le.mpr
    (Nat.le_trans (UInt8.le_iff_toNat_le.mp h₁) (UInt8.le_iff_toNat_le.mp h₂))

/-- Lowering the `$cont` bound and raising the four-byte bound only adds
derivations: the two errata are both *relaxations*. -/
theorem denote_char_mono {contLo contLo' : UInt8} {hi hi' : Nat} (hlo : contLo' ≤ contLo)
    (hhi : hi ≤ hi') :
    denote (utf8Gram contLo hi) (.nt .char) ≤ denote (utf8Gram contLo' hi') (.nt .char) := by
  intro bs a h
  rw [denote_char_alt] at h ⊢
  rcases h with h | h | h | h
  · exact Or.inl (denote_utf8P1_iff.mpr (denote_utf8P1_iff.mp h))
  · obtain ⟨b₁, b₂, h₁, h₂, h₃, h₄, hb, hv, ha⟩ := denote_utf8P2_iff.mp h
    exact Or.inr (Or.inl (denote_utf8P2_iff.mpr
      ⟨b₁, b₂, h₁, h₂, uint8_le_trans hlo h₃, h₄, hb, hv, ha⟩))
  · obtain ⟨b₁, b₂, b₃, h₁, h₂, h₃, h₄, h₅, h₆, hb, hv, ha⟩ := denote_utf8P3_iff.mp h
    exact Or.inr (Or.inr (Or.inl (denote_utf8P3_iff.mpr
      ⟨b₁, b₂, b₃, h₁, h₂, uint8_le_trans hlo h₃, h₄, uint8_le_trans hlo h₅, h₆, hb, hv, ha⟩)))
  · obtain ⟨b₁, b₂, b₃, b₄, h₁, h₂, h₃, h₄, h₅, h₆, h₇, hb, hv, hu, ha⟩ :=
      denote_utf8P4_iff.mp h
    exact Or.inr (Or.inr (Or.inr (denote_utf8P4_iff.mpr
      ⟨b₁, b₂, b₃, b₄, h₁, uint8_le_trans hlo h₂, h₃, uint8_le_trans hlo h₄, h₅,
        uint8_le_trans hlo h₆, h₇, hb, hv, Nat.lt_of_lt_of_le hu hhi, ha⟩)))

/-- **The pinned grammar derives strictly fewer characters than the corrected
one.**  `≤` is `denote_char_mono`; `≠` is `grin_disagreement_pinned`. -/
theorem denote_pinned_lt_fixed :
    denote utf8GramPinned (.nt .char) < denote utf8GramFixed (.nt .char) := by
  refine lt_of_le_of_ne (denote_char_mono (by decide) (by decide)) (fun he => ?_)
  have hd := denote_grinChar_fixed
  rw [← he] at hd
  exact not_denote_grinChar_pinned 0x81 _ hd

/-! ## Functionality, from the framework's decidable conditions

The four clauses have separated leading-byte intervals — `0x00..0x7F`,
`0xC0..0xDF`, `0xE0..0xEF`, `0xF0..0xFF` — and each clause is a concatenation
of byte intervals, hence prefix-free factor by factor.  Those are exactly the
hypotheses of `altSeparated` and `Unambiguous.appendAll`, so the generic
lemmas of `Silmaril/SpecTec/Grammar/Basic.lean` give unambiguity with no
UTF-8-specific argument at all. -/

/-- The denotation of `utf8P1`, as an equation. -/
theorem denote_utf8P1_eq (contLo : UInt8) (hi : Nat) :
    denote (utf8Gram contLo hi) utf8P1
      = EncRel.mapPartial utf8Act1 (utf8RangesRel [(0x00, 0x7F)]) := by
  rw [utf8P1, denote_attr, denote_utf8RangeSeq (alg_utf8Gram contLo hi)]

/-- The denotation of `utf8P2`, as an equation. -/
theorem denote_utf8P2_eq (contLo : UInt8) (hi : Nat) :
    denote (utf8Gram contLo hi) (utf8P2 contLo)
      = EncRel.mapPartial utf8Act2 (utf8RangesRel [(0xC0, 0xDF), (contLo, 0xBF)]) := by
  rw [utf8P2, denote_attr, denote_utf8RangeSeq (alg_utf8Gram contLo hi)]

/-- The denotation of `utf8P3`, as an equation. -/
theorem denote_utf8P3_eq (contLo : UInt8) (hi : Nat) :
    denote (utf8Gram contLo hi) (utf8P3 contLo)
      = EncRel.mapPartial utf8Act3
          (utf8RangesRel [(0xE0, 0xEF), (contLo, 0xBF), (contLo, 0xBF)]) := by
  rw [utf8P3, denote_attr, denote_utf8RangeSeq (alg_utf8Gram contLo hi)]

/-- The denotation of `utf8P4`, as an equation. -/
theorem denote_utf8P4_eq (contLo : UInt8) (hi : Nat) :
    denote (utf8Gram contLo hi) (utf8P4 contLo hi)
      = EncRel.mapPartial (utf8Act4 hi)
          (utf8RangesRel [(0xF0, 0xFF), (contLo, 0xBF), (contLo, 0xBF), (contLo, 0xBF)]) := by
  rw [utf8P4, denote_attr, denote_utf8RangeSeq (alg_utf8Gram contLo hi)]

/-- A sequence of byte intervals is unambiguous: every factor is, and
`Unambiguous.appendAll` does the rest. -/
theorem unambiguous_utf8RangesRel (rs : List (UInt8 × UInt8)) : Unambiguous (utf8RangesRel rs) := by
  rw [← denote_utf8RangeSeq (G := utf8Gram 0 0) rfl, utf8RangeSeq]
  refine unambiguous_denote_seq _ (fun g hg => ?_)
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hg
  rw [denote_range]
  exact unambiguous_rangeRel _ _ _

/-- **The decidable condition applies**: the four clauses of `$utf8(ch)` have
pairwise disjoint leading-byte intervals, for every value of the two bounds the
errata move. -/
theorem altSeparated_utf8CharProds (contLo : UInt8) (hi : Nat) :
    altSeparated (utf8CharProds contLo hi) = true := by
  simp only [altSeparated, utf8CharProds, utf8P1, utf8P2, utf8P3, utf8P4, utf8RangeSeq,
    List.map_cons, List.map_nil, leadRange?, List.all_cons, List.all_nil]
  decide

/-- `$utf8(ch)` is unambiguous — prefix-free and functional — by the framework's
generic lemmas alone. -/
theorem unambiguous_utf8_char (contLo : UInt8) (hi : Nat) :
    Unambiguous (denote (utf8Gram contLo hi) (.nt .char)) := by
  refine unambiguous_denote_nt _ (altSeparated_utf8CharProds contLo hi) (fun g hg => ?_)
  have hg' : g ∈ utf8CharProds contLo hi := hg
  simp only [utf8CharProds, List.mem_cons, List.not_mem_nil, or_false] at hg'
  rcases hg' with rfl | rfl | rfl | rfl
  · rw [denote_utf8P1_eq]; exact (unambiguous_utf8RangesRel _).mapPartial _
  · rw [denote_utf8P2_eq]; exact (unambiguous_utf8RangesRel _).mapPartial _
  · rw [denote_utf8P3_eq]; exact (unambiguous_utf8RangesRel _).mapPartial _
  · rw [denote_utf8P4_eq]; exact (unambiguous_utf8RangesRel _).mapPartial _

/-- Hence `$utf8(ch)` is `Functional`: a byte string determines at most one
scalar value.  This is the claim the decidable conditions were for. -/
theorem functional_utf8_char (contLo : UInt8) (hi : Nat) :
    (denote (utf8Gram contLo hi) (.nt .char)).Functional :=
  (unambiguous_utf8_char contLo hi).functional

/-- No clause of `$utf8(ch)` spells the empty byte string: every one of them has
a known leading-byte interval. -/
theorem nonNullable_utf8_char (contLo : UInt8) (hi : Nat) :
    NonNullable (denote (utf8Gram contLo hi) (.nt .char)) := by
  rw [denote_nt]
  refine NonNullable.supList (fun E hE => ?_)
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hE
  obtain ⟨p, hp⟩ := altSeparated_leadRange (altSeparated_utf8CharProds contLo hi) hg
  exact nonNullable_of_leadRange _ hp

/-- `$utf8(ch*)` is functional: a byte string determines the sequence of scalar
values it spells.  (It is not prefix-free: `ε` is a spelling.) -/
theorem functional_utf8_chars (contLo : UInt8) (hi : Nat) :
    (denote (utf8Gram contLo hi) (.nt .chars)).Functional := by
  rw [denote_chars]
  exact functional_kleene (unambiguous_utf8_char contLo hi) (nonNullable_utf8_char contLo hi)

/-! ### Comparison with `Silmaril/Wasm/Binary/Basic.lean`

That file proves the same two facts by hand, through a `utf8Len` case analysis
(`Silmaril/Wasm/Binary/Basic.lean:530-573`); `Utf8Char.prefixFree` is `private`
there, so the first statement below is new as well as re-proved. -/

/-- `Silmaril.Wasm.Binary.Utf8Char` is prefix-free, from `unambiguous_utf8_char`
and nothing else.  The hand-written proof is the `private`
`Silmaril.Wasm.Binary.Utf8Char.prefixFree`. -/
theorem utf8Char_prefixFree : Wasm.Binary.PrefixFree (fun b c => Utf8Char c b) := by
  intro b b' r r' c c' h h' he
  obtain ⟨hb, ha, -⟩ := (unambiguous_utf8_char 0x80 0x110000).split
    (denote_of_utf8Char h) (denote_of_utf8Char h') he
  exact ⟨hb, Char.ext (UInt32.toNat_inj.mp (by simpa using ha))⟩

/-- `Silmaril.Wasm.Binary.Utf8.functional`, re-proved through the framework. -/
theorem utf8_functional : Wasm.Binary.Functional (fun b (cs : List Char) => Utf8 cs b) := by
  intro b cs cs' h h'
  exact map_toNat_inj (functional_utf8_chars 0x80 0x110000
    (denote_chars_of_utf8 h) (denote_chars_of_utf8 h'))

/-! ## Worked examples -/

/-- The leading-byte intervals `altSeparated_utf8CharProds` checks. -/
example : (utf8CharProds 0x80 0x110000).map leadRange?
    = [some (0x00, 0x7F), some (0xC0, 0xDF), some (0xE0, 0xEF), some (0xF0, 0xFF)] := by
  decide

/-- U+20AC EURO SIGN is `E2 82 AC`, and the corrected grammar derives it. -/
example : denote utf8GramFixed (.nt .char) [0xE2, 0x82, 0xAC] [0x20AC] := by
  have h : (Char.ofNat 0x20AC).toNat = 0x20AC := Unicode.charToNat_ofNat (Or.inl (by decide))
  have hc : Utf8Char (Char.ofNat 0x20AC) [0xE2, 0x82, 0xAC] :=
    Utf8Char.three 0xE2 0x82 0xAC (Or.inl ⟨by rw [h]; decide, by rw [h]; decide⟩)
      (by decide) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by rw [h]; decide)
  have hd := denote_of_utf8Char hc
  rwa [h] at hd

/-- The pinned grammar still derives it: `#656` only loses scalar values
at or above U+11000, and `#655` only those whose spelling contains `0x80`. -/
example : denote utf8GramPinned (.nt .char) [0xE2, 0x82, 0xAC] [0x20AC] :=
  denote_char_alt.mpr (Or.inr (Or.inr (Or.inl (denote_utf8P3_iff.mpr
    ⟨0xE2, 0x82, 0xAC, by decide, by decide, by decide, by decide, by decide, by decide,
      rfl, by decide, by decide⟩))))

/-- The corrected grammar spells the two-character string `"h€"` at `chars`. -/
example : denote utf8GramFixed (.nt .chars) [0x68, 0xE2, 0x82, 0xAC]
    [0x68, 0x20AC] := by
  have h : (Char.ofNat 0x20AC).toNat = 0x20AC := Unicode.charToNat_ofNat (Or.inl (by decide))
  have h' : (Char.ofNat 0x68).toNat = 0x68 := Unicode.charToNat_ofNat (Or.inl (by decide))
  have h1 : Utf8Char (Char.ofNat 0x68) [0x68] :=
    Utf8Char.one 0x68 (by rw [h']; decide) (by rw [h']; decide)
  have h2 : Utf8Char (Char.ofNat 0x20AC) [0xE2, 0x82, 0xAC] :=
    Utf8Char.three 0xE2 0x82 0xAC (Or.inl ⟨by rw [h]; decide, by rw [h]; decide⟩)
      (by decide) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by rw [h]; decide)
  have hu : Utf8 [Char.ofNat 0x68, Char.ofNat 0x20AC] [0x68, 0xE2, 0x82, 0xAC] :=
    Seq.cons (b := [0x68]) (bs := [0xE2, 0x82, 0xAC]) h1
      (Seq.cons (b := [0xE2, 0x82, 0xAC]) (bs := []) h2 Seq.nil)
  have hd := denote_chars_of_utf8 hu
  rwa [List.map_cons, List.map_cons, List.map_nil, h, h'] at hd


end Utf8

end Silmaril.SpecTec.Grammar
