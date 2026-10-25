module

public import Silmaril.Encoding.Unicode

/-!
# Text and binary syntax: source together with its parse

A *text syntax* for `α` is a functional encoding `String ⇀ α` (each text has at
most one parse); a *binary syntax* is a functional encoding
`List UInt8 ⇀ α`.  Both are registered as typeclasses, `TextSyntax α` and
`BinarySyntax α`, so that the types

* `WithText α`   — a text together with its abstract syntax tree, and
* `WithBinary α` — a byte string together with its abstract syntax tree

can be written without naming the relation.  They are the graphs of the
relations (`Encoded`), so a value is a triple `⟨text, ast, valid⟩`.  Since the
relation is functional, **the projection to the text (resp. bytes) is an
injection** (`WithText.text_injective`, `WithText.textEmbedding`,
`WithBinary.bytes_injective`, `WithBinary.bytesEmbedding`): a `WithText α` is
determined by its text, and equality is decidable from `DecidableEq String`
alone.

Smart constructors build values from a sound decoder (`ofDecoder?`, and the
total `parse` on valid spellings given a complete decoder).  Values move
between the two carriers keeping the AST (`WithText.toBinaryOf`,
`WithBinary.toTextOf`), and UTF-8 maps a `WithText α` injectively to an encoded
value of the UTF-8 byte relation (`WithText.utf8`); `TextSyntax.utf8Binary`
packages that relation as a `BinarySyntax`.

The classes live in namespace `Silmaril` (not `Silmaril.Encoding`, which is
reserved for the class-based byte encoding interface).  The Wasm instances
`WasmText`/`WasmBinary` are in `Silmaril.Encoding.Wasm`; JSON and CBOR instances
are in `Silmaril.Formats.Json.EncodingSyntax` and
`Silmaril.Formats.Cbor.EncodingSyntax`.
-/

@[expose] public section

namespace Silmaril

/-- A text syntax for `α`: a functional encoding of `α` in Unicode text. -/
class TextSyntax (α : Type) where
  /-- The text encoding relation, bundled with its functionality. -/
  rel : FunEncRel String α

/-- A binary syntax for `α`: a functional encoding of `α` in byte strings. -/
class BinarySyntax (α : Type) where
  /-- The byte encoding relation, bundled with its functionality. -/
  rel : FunEncRel (List UInt8) α

/-- A text together with its abstract syntax tree. -/
abbrev WithText (α : Type) [TextSyntax α] := (TextSyntax.rel (α := α)).Encoded

/-- A byte string together with its abstract syntax tree. -/
abbrev WithBinary (α : Type) [BinarySyntax α] := (BinarySyntax.rel (α := α)).Encoded

/-! ## `WithText` -/

namespace WithText

variable {α : Type} [TextSyntax α]

/-- The text spells the AST. -/
theorem valid (x : WithText α) : (TextSyntax.rel (α := α)).rel x.text x.ast :=
  Encoded.valid x

/-- **The projection to the text is injective.** -/
theorem text_injective : Function.Injective (fun x : WithText α => x.text) :=
  (TextSyntax.rel (α := α)).text_injective

/-- The text projection as an embedding. -/
def textEmbedding : WithText α ↪ String :=
  (TextSyntax.rel (α := α)).textEmbedding

@[simp] theorem textEmbedding_apply (x : WithText α) : textEmbedding x = x.text := rfl

theorem ext_iff_text {x y : WithText α} : x = y ↔ x.text = y.text :=
  ⟨congrArg _, fun h => text_injective h⟩

theorem ext_text {x y : WithText α} (h : x.text = y.text) : x = y :=
  ext_iff_text.mpr h

/-- The AST is a function of the text. -/
theorem ast_eq_of_text_eq {x y : WithText α} (h : x.text = y.text) : x.ast = y.ast :=
  congrArg Encoded.ast (ext_text h)

/-- Equality is decided by comparing texts. -/
instance (priority := high) instDecidableEq : DecidableEq (WithText α) := fun x y =>
  decidable_of_iff (x.text = y.text) ext_iff_text.symm

theorem text_range :
    Set.range (fun x : WithText α => x.text) = (TextSyntax.rel (α := α)).rel.domain :=
  Encoded.text_range

/-! ### Smart constructors -/

/-- Parse a text with a sound decoder, keeping the text. -/
def ofDecoder? (dec : String → Option α)
    (h : (TextSyntax.rel (α := α)).rel.DecoderSound dec) (s : String) :
    Option (WithText α) :=
  match hd : dec s with
  | some a => some ⟨s, a, h s a hd⟩
  | none => none

theorem ofDecoder?_eq_some_iff {dec : String → Option α}
    {h : (TextSyntax.rel (α := α)).rel.DecoderSound dec} {s : String} {x : WithText α} :
    ofDecoder? dec h s = some x ↔ x.text = s ∧ dec s = some x.ast := by
  unfold ofDecoder?
  split
  · rename_i a hd
    constructor
    · rintro ⟨⟩; exact ⟨rfl, hd⟩
    · rintro ⟨rfl, hx⟩
      cases Option.some.inj (hd.symm.trans hx)
      rfl
  · rename_i hd
    constructor
    · intro h; cases h
    · rintro ⟨_, hx⟩
      cases hd.symm.trans hx

theorem ofDecoder?_isSome {dec : String → Option α}
    {h : (TextSyntax.rel (α := α)).rel.DecoderSound dec} {s : String} :
    (ofDecoder? dec h s).isSome = (dec s).isSome := by
  unfold ofDecoder?
  split <;> rename_i hd <;> exact (congrArg Option.isSome hd).symm

/-- With a complete decoder, every value is recovered from its text. -/
theorem ofDecoder?_text {dec : String → Option α}
    (h : (TextSyntax.rel (α := α)).rel.DecoderSound dec)
    (hc : (TextSyntax.rel (α := α)).rel.DecoderComplete dec) (x : WithText α) :
    ofDecoder? dec h x.text = some x :=
  ofDecoder?_eq_some_iff.mpr ⟨rfl, hc _ _ x.valid⟩

/-- With a complete decoder, parsing is total on the valid spellings. -/
def parse (dec : String → Option α)
    (h : (TextSyntax.rel (α := α)).rel.DecoderSound dec)
    (hc : (TextSyntax.rel (α := α)).rel.DecoderComplete dec) (s : String)
    (hs : (TextSyntax.rel (α := α)).rel.Encodable s) : WithText α :=
  ⟨s, (dec s).get (by obtain ⟨a, ha⟩ := hs; rw [hc s a ha]; rfl),
    h _ _ (Option.some_get _).symm⟩

@[simp] theorem parse_text {dec : String → Option α}
    {h : (TextSyntax.rel (α := α)).rel.DecoderSound dec}
    {hc : (TextSyntax.rel (α := α)).rel.DecoderComplete dec} {s : String}
    {hs : (TextSyntax.rel (α := α)).rel.Encodable s} : (parse dec h hc s hs).text = s := rfl

theorem parse_eq {dec : String → Option α}
    (h : (TextSyntax.rel (α := α)).rel.DecoderSound dec)
    (hc : (TextSyntax.rel (α := α)).rel.DecoderComplete dec) (x : WithText α) :
    parse dec h hc x.text ⟨x.ast, x.valid⟩ = x :=
  ext_text rfl

theorem ofDecoder?_eq_parse {dec : String → Option α}
    (h : (TextSyntax.rel (α := α)).rel.DecoderSound dec)
    (hc : (TextSyntax.rel (α := α)).rel.DecoderComplete dec) {s : String}
    (hs : (TextSyntax.rel (α := α)).rel.Encodable s) :
    ofDecoder? dec h s = some (parse dec h hc s hs) :=
  ofDecoder?_text h hc (parse dec h hc s hs)

/-! ### UTF-8 -/

/-- The UTF-8 bytes of a text, with the same AST: an encoded value of the
UTF-8 pushforward of the text relation. -/
def utf8 (x : WithText α) :
    Encoded ((TextSyntax.rel (α := α)).rel.push Unicode.utf8) :=
  Encoded.push Unicode.utf8 x

@[simp] theorem utf8_text (x : WithText α) : (utf8 x).text = Unicode.utf8 x.text := rfl

@[simp] theorem utf8_ast (x : WithText α) : (utf8 x).ast = x.ast := rfl

/-- UTF-8 is an equivalence onto the encoded values of the UTF-8 relation. -/
noncomputable def utf8Equiv :
    WithText α ≃ Encoded ((TextSyntax.rel (α := α)).rel.push Unicode.utf8) :=
  Encoded.pushEquiv Unicode.utf8_injective

theorem utf8Equiv_apply (x : WithText α) : utf8Equiv x = utf8 x := rfl

theorem utf8_injective : Function.Injective (utf8 (α := α)) :=
  (utf8Equiv (α := α)).injective

end WithText

/-! ## `WithBinary` -/

namespace WithBinary

variable {α : Type} [BinarySyntax α]

/-- The byte spelling. -/
abbrev bytes (x : WithBinary α) : List UInt8 := Encoded.text x

/-- The bytes spell the AST. -/
theorem valid (x : WithBinary α) : (BinarySyntax.rel (α := α)).rel x.bytes x.ast :=
  Encoded.valid x

/-- **The projection to the bytes is injective.** -/
theorem bytes_injective : Function.Injective (bytes (α := α)) :=
  (BinarySyntax.rel (α := α)).text_injective

/-- The byte projection as an embedding. -/
def bytesEmbedding : WithBinary α ↪ List UInt8 :=
  (BinarySyntax.rel (α := α)).textEmbedding

@[simp] theorem bytesEmbedding_apply (x : WithBinary α) : bytesEmbedding x = x.bytes := rfl

theorem ext_iff_bytes {x y : WithBinary α} : x = y ↔ x.bytes = y.bytes :=
  ⟨congrArg _, fun h => bytes_injective h⟩

theorem ext_bytes {x y : WithBinary α} (h : x.bytes = y.bytes) : x = y :=
  ext_iff_bytes.mpr h

/-- The AST is a function of the bytes. -/
theorem ast_eq_of_bytes_eq {x y : WithBinary α} (h : x.bytes = y.bytes) : x.ast = y.ast :=
  congrArg Encoded.ast (ext_bytes h)

/-- Equality is decided by comparing byte strings. -/
instance (priority := high) instDecidableEq : DecidableEq (WithBinary α) := fun x y =>
  decidable_of_iff (x.bytes = y.bytes) ext_iff_bytes.symm

theorem bytes_range :
    Set.range (bytes (α := α)) = (BinarySyntax.rel (α := α)).rel.domain :=
  Encoded.text_range

/-! ### Smart constructors -/

/-- Parse a byte string with a sound decoder, keeping the bytes. -/
def ofDecoder? (dec : List UInt8 → Option α)
    (h : (BinarySyntax.rel (α := α)).rel.DecoderSound dec) (b : List UInt8) :
    Option (WithBinary α) :=
  match hd : dec b with
  | some a => some ⟨b, a, h b a hd⟩
  | none => none

theorem ofDecoder?_eq_some_iff {dec : List UInt8 → Option α}
    {h : (BinarySyntax.rel (α := α)).rel.DecoderSound dec} {b : List UInt8}
    {x : WithBinary α} :
    ofDecoder? dec h b = some x ↔ x.bytes = b ∧ dec b = some x.ast := by
  unfold ofDecoder?
  split
  · rename_i a hd
    constructor
    · rintro ⟨⟩; exact ⟨rfl, hd⟩
    · rintro ⟨rfl, hx⟩
      cases Option.some.inj (hd.symm.trans hx)
      rfl
  · rename_i hd
    constructor
    · intro h; cases h
    · rintro ⟨_, hx⟩
      cases hd.symm.trans hx

theorem ofDecoder?_isSome {dec : List UInt8 → Option α}
    {h : (BinarySyntax.rel (α := α)).rel.DecoderSound dec} {b : List UInt8} :
    (ofDecoder? dec h b).isSome = (dec b).isSome := by
  unfold ofDecoder?
  split <;> rename_i hd <;> exact (congrArg Option.isSome hd).symm

/-- With a complete decoder, every value is recovered from its bytes. -/
theorem ofDecoder?_bytes {dec : List UInt8 → Option α}
    (h : (BinarySyntax.rel (α := α)).rel.DecoderSound dec)
    (hc : (BinarySyntax.rel (α := α)).rel.DecoderComplete dec) (x : WithBinary α) :
    ofDecoder? dec h x.bytes = some x :=
  ofDecoder?_eq_some_iff.mpr ⟨rfl, hc _ _ x.valid⟩

/-- With a complete decoder, parsing is total on the valid spellings. -/
def parse (dec : List UInt8 → Option α)
    (h : (BinarySyntax.rel (α := α)).rel.DecoderSound dec)
    (hc : (BinarySyntax.rel (α := α)).rel.DecoderComplete dec) (b : List UInt8)
    (hb : (BinarySyntax.rel (α := α)).rel.Encodable b) : WithBinary α :=
  ⟨b, (dec b).get (by obtain ⟨a, ha⟩ := hb; rw [hc b a ha]; rfl),
    h _ _ (Option.some_get _).symm⟩

@[simp] theorem parse_bytes {dec : List UInt8 → Option α}
    {h : (BinarySyntax.rel (α := α)).rel.DecoderSound dec}
    {hc : (BinarySyntax.rel (α := α)).rel.DecoderComplete dec} {b : List UInt8}
    {hb : (BinarySyntax.rel (α := α)).rel.Encodable b} :
    (parse dec h hc b hb).bytes = b := rfl

theorem parse_eq {dec : List UInt8 → Option α}
    (h : (BinarySyntax.rel (α := α)).rel.DecoderSound dec)
    (hc : (BinarySyntax.rel (α := α)).rel.DecoderComplete dec) (x : WithBinary α) :
    parse dec h hc x.bytes ⟨x.ast, x.valid⟩ = x :=
  ext_bytes rfl

theorem ofDecoder?_eq_parse {dec : List UInt8 → Option α}
    (h : (BinarySyntax.rel (α := α)).rel.DecoderSound dec)
    (hc : (BinarySyntax.rel (α := α)).rel.DecoderComplete dec) {b : List UInt8}
    (hb : (BinarySyntax.rel (α := α)).rel.Encodable b) :
    ofDecoder? dec h b = some (parse dec h hc b hb) :=
  ofDecoder?_bytes h hc (parse dec h hc b hb)

end WithBinary

/-! ## Transport between text and binary syntax -/

namespace WithText

variable {α : Type} [TextSyntax α] [BinarySyntax α]

/-- Re-spell a text as bytes with an encoder that is correct on every AST
that has a text spelling; the AST is kept. -/
def toBinaryOf (enc : α → List UInt8)
    (h : ∀ a, a ∈ (TextSyntax.rel (α := α)).rel.image →
      (BinarySyntax.rel (α := α)).rel (enc a) a)
    (x : WithText α) : WithBinary α :=
  ⟨enc x.ast, x.ast, h _ ⟨x.text, x.valid⟩⟩

@[simp] theorem toBinaryOf_ast {enc : α → List UInt8}
    {h : ∀ a, a ∈ (TextSyntax.rel (α := α)).rel.image →
      (BinarySyntax.rel (α := α)).rel (enc a) a}
    (x : WithText α) : (toBinaryOf enc h x).ast = x.ast := rfl

@[simp] theorem toBinaryOf_bytes {enc : α → List UInt8}
    {h : ∀ a, a ∈ (TextSyntax.rel (α := α)).rel.image →
      (BinarySyntax.rel (α := α)).rel (enc a) a}
    (x : WithText α) : (toBinaryOf enc h x).bytes = enc x.ast := rfl

end WithText

namespace WithBinary

variable {α : Type} [TextSyntax α] [BinarySyntax α]

/-- Re-spell bytes as text with a printer that is correct on every AST that
has a byte spelling; the AST is kept. -/
def toTextOf (print : α → String)
    (h : ∀ a, a ∈ (BinarySyntax.rel (α := α)).rel.image →
      (TextSyntax.rel (α := α)).rel (print a) a)
    (x : WithBinary α) : WithText α :=
  ⟨print x.ast, x.ast, h _ ⟨x.bytes, x.valid⟩⟩

@[simp] theorem toTextOf_ast {print : α → String}
    {h : ∀ a, a ∈ (BinarySyntax.rel (α := α)).rel.image →
      (TextSyntax.rel (α := α)).rel (print a) a}
    (x : WithBinary α) : (toTextOf print h x).ast = x.ast := rfl

@[simp] theorem toTextOf_text {print : α → String}
    {h : ∀ a, a ∈ (BinarySyntax.rel (α := α)).rel.image →
      (TextSyntax.rel (α := α)).rel (print a) a}
    (x : WithBinary α) : (toTextOf print h x).text = print x.ast := rfl

end WithBinary

/-! ## UTF-8 binary syntax of a text syntax -/

/-- The UTF-8 pushforward of a text syntax, as a functional byte encoding. -/
def TextSyntax.utf8Rel (α : Type) [TextSyntax α] : FunEncRel (List UInt8) α :=
  ⟨(TextSyntax.rel (α := α)).rel.push Unicode.utf8,
    Unicode.functional_push_utf8 (TextSyntax.rel (α := α)).functional⟩

/-- The UTF-8 binary syntax induced by a text syntax (not an instance: a
format may have a byte syntax other than UTF-8 text). -/
abbrev TextSyntax.utf8Binary (α : Type) [TextSyntax α] : BinarySyntax α :=
  ⟨TextSyntax.utf8Rel α⟩

/-- Under the UTF-8 binary syntax, `WithText.utf8` lands in `WithBinary`. -/
def WithText.toUtf8Binary {α : Type} [TextSyntax α] (x : WithText α) :
    @WithBinary α (TextSyntax.utf8Binary α) :=
  WithText.utf8 x

theorem WithText.toUtf8Binary_injective {α : Type} [TextSyntax α] :
    Function.Injective (WithText.toUtf8Binary (α := α)) :=
  WithText.utf8_injective

/-- Equality of `WithText`/`WithBinary` values needs no `DecidableEq α`. -/
example {α : Type} [TextSyntax α] : DecidableEq (WithText α) := inferInstance

example {α : Type} [BinarySyntax α] : DecidableEq (WithBinary α) := inferInstance

end Silmaril
