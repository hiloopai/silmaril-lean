module

public import Silmaril.Encoding.Syntax
public import Silmaril.Encoding.Unicode

/-!
# Text/binary syntax: other carriers and generic constructors

Extends `Silmaril.Encoding.Syntax` with

* **UTF-16** byte syntaxes of a text syntax (`TextSyntax.utf16Rel`,
  `TextSyntax.utf16Binary`, `WithText.utf16`, `WithText.toUtf16Binary`), with
  injectivity and the equivalence `WithText.utf16Equiv`;
* **decoder lifts**: a sound (complete) text decoder composed with
  `Unicode.utf8?` / `Unicode.utf16?` is a sound (complete) decoder for the
  UTF-8 / UTF-16 byte syntax;
* the **Latin-1** text syntax of a binary syntax (`BinarySyntax.latin1Text`,
  `WithBinary.toLatin1Text`), total and injective;
* **generic constructors** `TextSyntax.ofDecoder` / `BinarySyntax.ofDecoder`
  (the graph of a decoder), with `WithText α ≃ {s // (dec s).isSome}`;
* **AST transport**: `TextSyntax.comap` (along an injective map),
  `TextSyntax.map` (along any map), `TextSyntax.ofEquiv` with the
  text-preserving `WithText.ofEquiv`, and the same for `BinarySyntax`;
* **transcoding**: UTF-8 bytes of a text, decoded and re-encoded as UTF-16LE,
  are its UTF-16LE bytes (`WithBinary.transcodeUtf8ToUtf16LE_toUtf8Binary`),
  matching `Unicode.transcode_utf8` at the level of relations
  (`TextSyntax.utf16Rel_false_eq_transcode`).

None of the derived syntaxes are instances: they are `abbrev`s to be used with
`@WithText α (…)` / `@WithBinary α (…)` or `letI`.
-/

@[expose] public section

namespace Silmaril

/-! ## UTF-16 binary syntax of a text syntax -/

/-- The UTF-16 pushforward of a text syntax, as a functional byte encoding. -/
def TextSyntax.utf16Rel (α : Type) [TextSyntax α] (bigEndian : Bool) :
    FunEncRel (List UInt8) α :=
  ⟨(TextSyntax.rel (α := α)).rel.push (Unicode.utf16 bigEndian),
    (TextSyntax.rel (α := α)).functional.push (Unicode.utf16_injective _)⟩

/-- The UTF-16 binary syntax induced by a text syntax (not an instance). -/
abbrev TextSyntax.utf16Binary (α : Type) [TextSyntax α] (bigEndian : Bool) :
    BinarySyntax α :=
  ⟨TextSyntax.utf16Rel α bigEndian⟩

namespace WithText

variable {α : Type} [TextSyntax α]

/-- The UTF-16 bytes of a text, with the same AST. -/
def utf16 (bigEndian : Bool) (x : WithText α) :
    Encoded ((TextSyntax.rel (α := α)).rel.push (Unicode.utf16 bigEndian)) :=
  Encoded.push (Unicode.utf16 bigEndian) x

@[simp] theorem utf16_text (bigEndian : Bool) (x : WithText α) :
    (utf16 bigEndian x).text = Unicode.utf16 bigEndian x.text := rfl

@[simp] theorem utf16_ast (bigEndian : Bool) (x : WithText α) :
    (utf16 bigEndian x).ast = x.ast := rfl

/-- UTF-16 is an equivalence onto the encoded values of the UTF-16 relation. -/
noncomputable def utf16Equiv (bigEndian : Bool) :
    WithText α ≃ Encoded ((TextSyntax.rel (α := α)).rel.push (Unicode.utf16 bigEndian)) :=
  Encoded.pushEquiv (Unicode.utf16_injective bigEndian)

theorem utf16Equiv_apply (bigEndian : Bool) (x : WithText α) :
    utf16Equiv bigEndian x = utf16 bigEndian x := rfl

theorem utf16_injective (bigEndian : Bool) : Function.Injective (utf16 (α := α) bigEndian) :=
  (utf16Equiv (α := α) bigEndian).injective

/-- Under the UTF-16 binary syntax, `WithText.utf16` lands in `WithBinary`. -/
def toUtf16Binary (bigEndian : Bool) (x : WithText α) :
    @WithBinary α (TextSyntax.utf16Binary α bigEndian) :=
  utf16 bigEndian x

@[simp] theorem toUtf16Binary_bytes (bigEndian : Bool) (x : WithText α) :
    @WithBinary.bytes α (TextSyntax.utf16Binary α bigEndian) (toUtf16Binary bigEndian x) =
      Unicode.utf16 bigEndian x.text := rfl

@[simp] theorem toUtf16Binary_ast (bigEndian : Bool) (x : WithText α) :
    (toUtf16Binary bigEndian x).ast = x.ast := rfl

theorem toUtf16Binary_injective (bigEndian : Bool) :
    Function.Injective (toUtf16Binary (α := α) bigEndian) :=
  utf16_injective bigEndian

/-- `toUtf16Binary` as an equivalence. -/
noncomputable def toUtf16BinaryEquiv (bigEndian : Bool) :
    WithText α ≃ @WithBinary α (TextSyntax.utf16Binary α bigEndian) :=
  utf16Equiv bigEndian

theorem toUtf16BinaryEquiv_apply (bigEndian : Bool) (x : WithText α) :
    toUtf16BinaryEquiv bigEndian x = toUtf16Binary bigEndian x := rfl

@[simp] theorem toUtf8Binary_bytes (x : WithText α) :
    @WithBinary.bytes α (TextSyntax.utf8Binary α) (toUtf8Binary x) = Unicode.utf8 x.text := rfl

@[simp] theorem toUtf8Binary_ast (x : WithText α) : (toUtf8Binary x).ast = x.ast := rfl

/-- `toUtf8Binary` as an equivalence. -/
noncomputable def toUtf8BinaryEquiv :
    WithText α ≃ @WithBinary α (TextSyntax.utf8Binary α) :=
  utf8Equiv

theorem toUtf8BinaryEquiv_apply (x : WithText α) : toUtf8BinaryEquiv x = toUtf8Binary x := rfl

end WithText

/-! ## Decoder lifts along UTF-8 / UTF-16 -/

namespace TextSyntax

variable {α : Type} [TextSyntax α]

/-- A sound text decoder after UTF-8 decoding is sound for the UTF-8 syntax. -/
theorem utf8_decoderSound {dec : String → Option α}
    (h : (TextSyntax.rel (α := α)).rel.DecoderSound dec) :
    (TextSyntax.utf8Rel α).rel.DecoderSound (fun b => Unicode.utf8? b >>= dec) := by
  intro b a hb
  obtain ⟨s, hs, ha⟩ := Option.bind_eq_some_iff.mp hb
  exact ⟨s, Unicode.utf8?_eq_some_iff.mp hs, h s a ha⟩

/-- A complete text decoder after UTF-8 decoding is complete for the UTF-8 syntax. -/
theorem utf8_decoderComplete {dec : String → Option α}
    (h : (TextSyntax.rel (α := α)).rel.DecoderComplete dec) :
    (TextSyntax.utf8Rel α).rel.DecoderComplete (fun b => Unicode.utf8? b >>= dec) := by
  rintro _ a ⟨s, rfl, ha⟩
  show Unicode.utf8? (Unicode.utf8 s) >>= dec = some a
  rw [Unicode.utf8?_utf8]
  exact h s a ha

/-- A sound text decoder after UTF-16 decoding is sound for the UTF-16 syntax. -/
theorem utf16_decoderSound (bigEndian : Bool) {dec : String → Option α}
    (h : (TextSyntax.rel (α := α)).rel.DecoderSound dec) :
    (TextSyntax.utf16Rel α bigEndian).rel.DecoderSound
      (fun b => Unicode.utf16? bigEndian b >>= dec) := by
  intro b a hb
  obtain ⟨s, hs, ha⟩ := Option.bind_eq_some_iff.mp hb
  exact ⟨s, (Unicode.utf16?_eq_some_iff bigEndian).mp hs, h s a ha⟩

/-- A complete text decoder after UTF-16 decoding is complete for the UTF-16
syntax. -/
theorem utf16_decoderComplete (bigEndian : Bool) {dec : String → Option α}
    (h : (TextSyntax.rel (α := α)).rel.DecoderComplete dec) :
    (TextSyntax.utf16Rel α bigEndian).rel.DecoderComplete
      (fun b => Unicode.utf16? bigEndian b >>= dec) := by
  rintro _ a ⟨s, rfl, ha⟩
  show Unicode.utf16? bigEndian (Unicode.utf16 bigEndian s) >>= dec = some a
  rw [Unicode.utf16?_utf16]
  exact h s a ha

end TextSyntax

/-! ## Latin-1 text syntax of a binary syntax -/

/-- The Latin-1 pushforward of a binary syntax: every byte string is read as
the text of the same code points (total and injective). -/
def BinarySyntax.latin1Rel (α : Type) [BinarySyntax α] : FunEncRel String α :=
  ⟨(BinarySyntax.rel (α := α)).rel.push Unicode.latin1,
    (BinarySyntax.rel (α := α)).functional.push Unicode.latin1_injective⟩

/-- The Latin-1 text syntax induced by a binary syntax (not an instance). -/
abbrev BinarySyntax.latin1Text (α : Type) [BinarySyntax α] : TextSyntax α :=
  ⟨BinarySyntax.latin1Rel α⟩

namespace WithBinary

variable {α : Type} [BinarySyntax α]

/-- Read the bytes as Latin-1 text, keeping the AST. -/
def toLatin1Text (x : WithBinary α) : @WithText α (BinarySyntax.latin1Text α) :=
  Encoded.push Unicode.latin1 x

@[simp] theorem toLatin1Text_text (x : WithBinary α) :
    (toLatin1Text x).text = Unicode.latin1 x.bytes := rfl

@[simp] theorem toLatin1Text_ast (x : WithBinary α) : (toLatin1Text x).ast = x.ast := rfl

/-- `toLatin1Text` as an equivalence. -/
noncomputable def toLatin1TextEquiv : WithBinary α ≃ @WithText α (BinarySyntax.latin1Text α) :=
  Encoded.pushEquiv Unicode.latin1_injective

theorem toLatin1TextEquiv_apply (x : WithBinary α) : toLatin1TextEquiv x = toLatin1Text x :=
  rfl

theorem toLatin1Text_injective : Function.Injective (toLatin1Text (α := α)) :=
  (toLatin1TextEquiv (α := α)).injective

end WithBinary

/-! ## Generic constructors from a decoder -/

/-- `Option.get` of a value known to be `some s` is `s`. -/
theorem option_get_eq_of_eq_some {σ : Type} {o : Option σ} {s : σ} (h : o.isSome = true)
    (e : o = some s) : o.get h = s := by
  subst e; rfl

/-- The text syntax given by the graph of a decoder. -/
abbrev TextSyntax.ofDecoder {α : Type} (dec : String → Option α) : TextSyntax α :=
  ⟨⟨EncRel.ofDecoder dec, EncRel.ofDecoder_functional dec⟩⟩

/-- The binary syntax given by the graph of a decoder. -/
abbrev BinarySyntax.ofDecoder {α : Type} (dec : List UInt8 → Option α) : BinarySyntax α :=
  ⟨⟨EncRel.ofDecoder dec, EncRel.ofDecoder_functional dec⟩⟩

/-- Under `TextSyntax.ofDecoder dec`, a text with its AST is exactly a text
accepted by `dec`. -/
def TextSyntax.ofDecoderEquiv {α : Type} (dec : String → Option α) :
    @WithText α (TextSyntax.ofDecoder dec) ≃ {s : String // (dec s).isSome} where
  toFun x := ⟨x.text, by
    have h : dec x.text = some x.ast := x.3
    rw [h]; rfl⟩
  invFun s := ⟨s.1, (dec s.1).get s.2, (Option.some_get s.2).symm⟩
  left_inv x := Encoded.ext rfl (option_get_eq_of_eq_some _ x.3)
  right_inv _ := rfl

@[simp] theorem TextSyntax.ofDecoderEquiv_apply {α : Type} (dec : String → Option α)
    (x : @WithText α (TextSyntax.ofDecoder dec)) :
    (TextSyntax.ofDecoderEquiv dec x).1 = x.text := rfl

/-- The decoder is sound and complete for its own syntax. -/
theorem TextSyntax.ofDecoder_decoderSound {α : Type} (dec : String → Option α) :
    (@TextSyntax.rel α (TextSyntax.ofDecoder dec)).rel.DecoderSound dec :=
  fun _ _ h => h

theorem TextSyntax.ofDecoder_decoderComplete {α : Type} (dec : String → Option α) :
    (@TextSyntax.rel α (TextSyntax.ofDecoder dec)).rel.DecoderComplete dec :=
  fun _ _ h => h

/-- Under `BinarySyntax.ofDecoder dec`, bytes with their AST are exactly byte
strings accepted by `dec`. -/
def BinarySyntax.ofDecoderEquiv {α : Type} (dec : List UInt8 → Option α) :
    @WithBinary α (BinarySyntax.ofDecoder dec) ≃ {b : List UInt8 // (dec b).isSome} where
  toFun x := ⟨x.text, by
    have h : dec x.text = some x.ast := x.3
    rw [h]; rfl⟩
  invFun b := ⟨b.1, (dec b.1).get b.2, (Option.some_get b.2).symm⟩
  left_inv x := Encoded.ext rfl (option_get_eq_of_eq_some _ x.3)
  right_inv _ := rfl

@[simp] theorem BinarySyntax.ofDecoderEquiv_apply {α : Type} (dec : List UInt8 → Option α)
    (x : @WithBinary α (BinarySyntax.ofDecoder dec)) :
    (BinarySyntax.ofDecoderEquiv dec x).1 = x.text := rfl

theorem BinarySyntax.ofDecoder_decoderSound {α : Type} (dec : List UInt8 → Option α) :
    (@BinarySyntax.rel α (BinarySyntax.ofDecoder dec)).rel.DecoderSound dec :=
  fun _ _ h => h

theorem BinarySyntax.ofDecoder_decoderComplete {α : Type} (dec : List UInt8 → Option α) :
    (@BinarySyntax.rel α (BinarySyntax.ofDecoder dec)).rel.DecoderComplete dec :=
  fun _ _ h => h

/-! ## Transport along the AST -/

/-- Functional encodings stay functional when the syntax is pushed along any
map: if `s` spells `a` and `a'` then `a = a'`, hence `f a = f a'`. -/
theorem EncRel.Functional.map {σ α β : Type} {E : EncRel σ α} (hE : E.Functional)
    (f : α → β) : (EncRel.map f E).Functional := by
  rintro s _ _ ⟨a, ha, rfl⟩ ⟨a', ha', rfl⟩
  rw [hE ha ha']

/-- Reindexing the syntax along an injective map preserves functionality. -/
theorem EncRel.Functional.comap {σ α β : Type} {E : EncRel σ α} (hE : E.Functional)
    {f : β → α} (hf : Function.Injective f) : (EncRel.comap f E).Functional :=
  fun _ _ _ h h' => hf (hE h h')

namespace TextSyntax

/-- Reindex a text syntax along an injective map `f : β → α`: a text spells
`b` when it spells `f b`.  (Injectivity is needed: otherwise a text spelling
`f b = f b'` would have two parses.) -/
abbrev comap {α β : Type} [TextSyntax α] (f : β → α) (hf : Function.Injective f) :
    TextSyntax β :=
  ⟨⟨EncRel.comap f (TextSyntax.rel (α := α)).rel,
    (TextSyntax.rel (α := α)).functional.comap hf⟩⟩

/-- Push a text syntax along any map `f : α → β`: a text spells `f a` when it
spells `a`.  Functional unconditionally. -/
abbrev map {α β : Type} [TextSyntax α] (f : α → β) : TextSyntax β :=
  ⟨⟨EncRel.map f (TextSyntax.rel (α := α)).rel,
    (TextSyntax.rel (α := α)).functional.map f⟩⟩

/-- Transport a text syntax along an equivalence `e : β ≃ α`. -/
abbrev ofEquiv {α β : Type} [TextSyntax α] (e : β ≃ α) : TextSyntax β :=
  comap e e.injective

end TextSyntax

namespace WithText

variable {α β : Type} [TextSyntax α]

/-- Re-index a reindexed value: same text, AST mapped by `f`. -/
def ofComap (f : β → α) (hf : Function.Injective f)
    (x : @WithText β (TextSyntax.comap f hf)) : WithText α :=
  ⟨x.text, f x.ast, x.3⟩

/-- Push a value along `f`: same text, AST mapped by `f`. -/
def map (f : α → β) (x : WithText α) : @WithText β (TextSyntax.map f) :=
  ⟨x.text, f x.ast, x.ast, x.valid, rfl⟩

@[simp] theorem map_text (f : α → β) (x : WithText α) : (map f x).text = x.text := rfl

@[simp] theorem map_ast (f : α → β) (x : WithText α) : (map f x).ast = f x.ast := rfl

/-- `map f` is a bijection: values over `β` are determined by their text. -/
noncomputable def mapEquiv (f : α → β) : WithText α ≃ @WithText β (TextSyntax.map f) :=
  Equiv.ofBijective (map f)
    ⟨fun x y h => ext_text (congrArg Encoded.text h :),
      by rintro ⟨s, _, a, ha, rfl⟩; exact ⟨⟨s, a, ha⟩, rfl⟩⟩

/-- Transport along an equivalence, preserving the text. -/
def ofEquiv (e : β ≃ α) : @WithText β (TextSyntax.ofEquiv e) ≃ WithText α where
  toFun x := ⟨x.text, e x.ast, x.3⟩
  invFun y := ⟨y.text, e.symm y.ast, by
    show (TextSyntax.rel (α := α)).rel y.text (e (e.symm y.ast))
    rw [e.apply_symm_apply]; exact y.valid⟩
  left_inv x := Encoded.ext rfl (e.symm_apply_apply x.ast)
  right_inv y := ext_text rfl

@[simp] theorem ofEquiv_text (e : β ≃ α) (x : @WithText β (TextSyntax.ofEquiv e)) :
    (ofEquiv e x).text = x.text := rfl

@[simp] theorem ofEquiv_ast (e : β ≃ α) (x : @WithText β (TextSyntax.ofEquiv e)) :
    (ofEquiv e x).ast = e x.ast := rfl

@[simp] theorem ofEquiv_symm_text (e : β ≃ α) (y : WithText α) :
    ((ofEquiv e).symm y).text = y.text := rfl

end WithText

namespace BinarySyntax

/-- Reindex a binary syntax along an injective map. -/
abbrev comap {α β : Type} [BinarySyntax α] (f : β → α) (hf : Function.Injective f) :
    BinarySyntax β :=
  ⟨⟨EncRel.comap f (BinarySyntax.rel (α := α)).rel,
    (BinarySyntax.rel (α := α)).functional.comap hf⟩⟩

/-- Push a binary syntax along any map.  Functional unconditionally. -/
abbrev map {α β : Type} [BinarySyntax α] (f : α → β) : BinarySyntax β :=
  ⟨⟨EncRel.map f (BinarySyntax.rel (α := α)).rel,
    (BinarySyntax.rel (α := α)).functional.map f⟩⟩

/-- Transport a binary syntax along an equivalence `e : β ≃ α`. -/
abbrev ofEquiv {α β : Type} [BinarySyntax α] (e : β ≃ α) : BinarySyntax β :=
  comap e e.injective

end BinarySyntax

namespace WithBinary

variable {α β : Type} [BinarySyntax α]

/-- Re-index a reindexed value: same bytes, AST mapped by `f`. -/
def ofComap (f : β → α) (hf : Function.Injective f)
    (x : @WithBinary β (BinarySyntax.comap f hf)) : WithBinary α :=
  ⟨x.text, f x.ast, x.3⟩

/-- Push a value along `f`: same bytes, AST mapped by `f`. -/
def map (f : α → β) (x : WithBinary α) : @WithBinary β (BinarySyntax.map f) :=
  ⟨x.bytes, f x.ast, x.ast, x.valid, rfl⟩

@[simp] theorem map_bytes (f : α → β) (x : WithBinary α) :
    @bytes β (BinarySyntax.map f) (map f x) = x.bytes := rfl

@[simp] theorem map_ast (f : α → β) (x : WithBinary α) : (map f x).ast = f x.ast := rfl

/-- `map f` is a bijection. -/
noncomputable def mapEquiv (f : α → β) : WithBinary α ≃ @WithBinary β (BinarySyntax.map f) :=
  Equiv.ofBijective (map f)
    ⟨fun x y h => ext_bytes (congrArg Encoded.text h :),
      by rintro ⟨s, _, a, ha, rfl⟩; exact ⟨⟨s, a, ha⟩, rfl⟩⟩

/-- Transport along an equivalence, preserving the bytes. -/
def ofEquiv (e : β ≃ α) : @WithBinary β (BinarySyntax.ofEquiv e) ≃ WithBinary α where
  toFun x := ⟨x.text, e x.ast, x.3⟩
  invFun y := ⟨y.bytes, e.symm y.ast, by
    show (BinarySyntax.rel (α := α)).rel y.bytes (e (e.symm y.ast))
    rw [e.apply_symm_apply]; exact y.valid⟩
  left_inv x := Encoded.ext rfl (e.symm_apply_apply x.ast)
  right_inv y := ext_bytes rfl

@[simp] theorem ofEquiv_bytes (e : β ≃ α) (x : @WithBinary β (BinarySyntax.ofEquiv e)) :
    (ofEquiv e x).bytes = @bytes β (BinarySyntax.ofEquiv e) x := rfl

@[simp] theorem ofEquiv_ast (e : β ≃ α) (x : @WithBinary β (BinarySyntax.ofEquiv e)) :
    (ofEquiv e x).ast = e x.ast := rfl

@[simp] theorem ofEquiv_symm_bytes (e : β ≃ α) (y : WithBinary α) :
    @bytes β (BinarySyntax.ofEquiv e) ((ofEquiv e).symm y) = y.bytes := rfl

end WithBinary

/-! ## Transcoding UTF-8 to UTF-16LE -/

/-- At the level of relations: decoding the UTF-8 syntax and encoding UTF-16LE
gives the UTF-16LE syntax (cf. `Unicode.transcode_utf8`). -/
theorem TextSyntax.utf16Rel_false_eq_transcode (α : Type) [TextSyntax α] :
    (TextSyntax.utf16Rel α false).rel =
      ((TextSyntax.utf8Rel α).rel.pushPartial Unicode.utf8?).push (Unicode.utf16 false) := by
  show _ = EncRel.push _ (EncRel.pushPartial _ (EncRel.push Unicode.utf8 _))
  rw [EncRel.pushPartial_push_of_leftInverse Unicode.utf8?_utf8]
  rfl

namespace WithBinary

variable {α : Type} [TextSyntax α]

/-- UTF-8 bytes of a text syntax decode to some text. -/
theorem utf8?_isSome (y : @WithBinary α (TextSyntax.utf8Binary α)) :
    (Unicode.utf8? (@bytes α (TextSyntax.utf8Binary α) y)).isSome := by
  obtain ⟨s, hs, _⟩ := y.3
  show (Unicode.utf8? y.text).isSome
  rw [← hs, Unicode.utf8?_utf8]; rfl

/-- Transcode a UTF-8 value to UTF-16LE: decode UTF-8, encode UTF-16LE, keep
the AST. -/
def transcodeUtf8ToUtf16LE (y : @WithBinary α (TextSyntax.utf8Binary α)) :
    @WithBinary α (TextSyntax.utf16Binary α false) :=
  ⟨Unicode.utf16 false ((Unicode.utf8? y.text).get (utf8?_isSome y)), y.ast, by
    obtain ⟨s, hs, h⟩ := y.3
    exact ⟨s, congrArg (Unicode.utf16 false)
      (option_get_eq_of_eq_some _ (Unicode.utf8?_eq_some_iff.mpr hs)).symm, h⟩⟩

@[simp] theorem transcodeUtf8ToUtf16LE_ast (y : @WithBinary α (TextSyntax.utf8Binary α)) :
    (transcodeUtf8ToUtf16LE y).ast = y.ast := rfl

/-- **Transcoding**: UTF-8 bytes of a text, transcoded to UTF-16LE, are the
UTF-16LE bytes of the text. -/
theorem transcodeUtf8ToUtf16LE_toUtf8Binary (x : WithText α) :
    transcodeUtf8ToUtf16LE (WithText.toUtf8Binary x) = WithText.toUtf16Binary false x := by
  apply @ext_bytes α (TextSyntax.utf16Binary α false)
  exact congrArg (Unicode.utf16 false) (option_get_eq_of_eq_some _ (Unicode.utf8?_utf8 x.text))

/-- Byte-level form of transcoding. -/
theorem utf8?_toUtf8Binary_map_utf16 (x : WithText α) :
    (Unicode.utf8? (@bytes α (TextSyntax.utf8Binary α) (WithText.toUtf8Binary x))).map
        (Unicode.utf16 false) =
      some (@bytes α (TextSyntax.utf16Binary α false) (WithText.toUtf16Binary false x)) := by
  show (Unicode.utf8? (Unicode.utf8 x.text)).map (Unicode.utf16 false) = _
  rw [Unicode.utf8?_utf8]; rfl

end WithBinary

end Silmaril
