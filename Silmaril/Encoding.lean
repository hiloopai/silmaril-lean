module

public import Silmaril.Data.ByteArray

/-! # Binary encodings as relations

An `Encoding α` is a specification: the relation `Encodes b a` holds when the
byte string `b` is a well-formed encoding of the abstract syntax `a`. It is a
relation, not a function, because binary formats such as WebAssembly's admit
several encodings of one value (non-minimal LEB128, optional sections, …).
Decoders and encoders are then *specified* against the relation
(`DecoderSound`, `DecoderCompleteOn`, `EncoderCorrectOn`).

## Representation

The relation is stated on `List UInt8`. Grammar productions compose by list
concatenation, which is structural and convenient for inductive definitions and
their proofs, whereas `ByteArray` is an array wrapper without useful
definitional concatenation. Decoders and encoders, which are executable, take
and produce `ByteArray`; `EncodesBytes` is the bridge (`b.data.toList`).

## Lifting relations on syntax to bytes

`Lift R b b'` holds when `b` and `b'` encode syntax related by `R`. When the
encoding is `Functional` (bytes determine syntax), `Lift` preserves partial
equivalences and refinement preorders (the latter restricted to encodable
bytes), and translation validation of a byte-level transformation reduces to a
syntax-level check through a sound decoder (`lift_of_decode`).
-/

@[expose] public section

namespace Silmaril

/-- A byte-level encoding relation for the abstract syntax `α`. -/
class Encoding (α : Type) where
  /-- `Encodes b a`: the byte string `b` is a well-formed encoding of `a`. -/
  Encodes : List UInt8 → α → Prop

namespace Encoding

variable {α β : Type}

section
variable [Encoding α]

/-- The `ByteArray` view of the encoding relation. -/
def EncodesBytes (b : ByteArray) (a : α) : Prop := Encodes b.data.toList a

/-- The byte string has at least one decoding. -/
def Encodable (α : Type) [Encoding α] (b : List UInt8) : Prop := ∃ a : α, Encodes b a

variable (α) in
/-- Bytes determine the syntax: at most one abstract value per byte string. -/
def Functional : Prop := ∀ ⦃b : List UInt8⦄ ⦃a a' : α⦄, Encodes b a → Encodes b a' → a = a'

variable (α) in
/-- Every value has at least one encoding. -/
def Total : Prop := ∀ a : α, ∃ b, Encodes b a

/-- A decoder is sound when every value it returns is encoded by its input. -/
def DecoderSound (dec : ByteArray → Option α) : Prop :=
  ∀ b a, dec b = some a → EncodesBytes b a

/-- A decoder is complete on `F` when it decodes every encoding of a value satisfying `F`. -/
def DecoderCompleteOn (F : α → Prop) (dec : ByteArray → Option α) : Prop :=
  ∀ b a, F a → EncodesBytes b a → dec b = some a

/-- An encoder is correct on `F` when it emits a valid encoding of each value satisfying `F`.
Encoders cannot be total in general (e.g. vectors longer than `2^32` have no encoding). -/
def EncoderCorrectOn (F : α → Prop) (enc : α → ByteArray) : Prop :=
  ∀ a, F a → EncodesBytes (enc a) a

/-- An encoder correct on every value. -/
def EncoderCorrect (enc : α → ByteArray) : Prop := EncoderCorrectOn (fun _ => True) enc

/-- Bytes related by `R` through their decodings. -/
def Lift (R : α → α → Prop) (b b' : List UInt8) : Prop :=
  ∃ a a', Encodes b a ∧ Encodes b' a' ∧ R a a'

/-- A partial equivalence relation: symmetric and transitive, not necessarily reflexive. -/
structure IsPER (R : α → α → Prop) : Prop where
  symm : ∀ ⦃a b⦄, R a b → R b a
  trans : ∀ ⦃a b c⦄, R a b → R b c → R a c

/-- A preorder (reflexive, transitive), e.g. a refinement relation. -/
structure IsPreorder (R : α → α → Prop) : Prop where
  refl : ∀ a, R a a
  trans : ∀ ⦃a b c⦄, R a b → R b c → R a c

/-- A preorder restricted to a carrier: reflexive on `S`, transitive everywhere. -/
structure IsPreorderOn (S : List UInt8 → Prop) (R : List UInt8 → List UInt8 → Prop) : Prop where
  refl : ∀ b, S b → R b b
  trans : ∀ ⦃a b c⦄, R a b → R b c → R a c

theorem Lift.mono {R S : α → α → Prop} (h : ∀ a a', R a a' → S a a') {b b' : List UInt8}
    (hl : Lift R b b') : Lift S b b' := by
  obtain ⟨a, a', ha, ha', hr⟩ := hl
  exact ⟨a, a', ha, ha', h _ _ hr⟩

/-- Under functionality, `Lift R` is decided by the unique decodings. -/
theorem Lift.iff_of_encodes (hF : Functional α) {R : α → α → Prop} {b b' : List UInt8}
    {a a' : α} (ha : Encodes b a) (ha' : Encodes b' a') : Lift R b b' ↔ R a a' := by
  constructor
  · rintro ⟨c, c', hc, hc', hr⟩
    rwa [hF ha hc, hF ha' hc']
  · exact fun hr => ⟨a, a', ha, ha', hr⟩

/-- Functionality makes the lift of a PER a PER on bytes. -/
theorem Lift.isPER (hF : Functional α) {R : α → α → Prop} (hR : IsPER R) :
    IsPER (Lift R) where
  symm := by
    rintro b b' ⟨a, a', ha, ha', hr⟩
    exact ⟨a', a, ha', ha, hR.symm hr⟩
  trans := by
    rintro b b' b'' ⟨a, a', ha, ha', hr⟩ ⟨c, c', hc, hc', hr'⟩
    rw [hF hc ha'] at hr'
    exact ⟨a, c', ha, hc', hR.trans hr hr'⟩

/-- Functionality makes the lift of a preorder a preorder on encodable bytes. -/
theorem Lift.isPreorderOn (hF : Functional α) {R : α → α → Prop} (hR : IsPreorder R) :
    IsPreorderOn (Encodable α) (Lift R) where
  refl := by
    rintro b ⟨a, ha⟩
    exact ⟨a, a, ha, ha, hR.refl a⟩
  trans := by
    rintro b b' b'' ⟨a, a', ha, ha', hr⟩ ⟨c, c', hc, hc', hr'⟩
    rw [hF hc ha'] at hr'
    exact ⟨a, c', ha, hc', hR.trans hr hr'⟩

/-- Syntactic equality lifts to "same decoding", a PER on bytes. -/
theorem Lift.eq_isPER (hF : Functional α) : IsPER (Lift (α := α) Eq) :=
  Lift.isPER hF ⟨fun _ _ h => h.symm, fun _ _ _ h h' => h.trans h'⟩

/-- Translation validation: decode both byte strings with a sound decoder and check
`R` on the results; the bytes are then related by `Lift R`. -/
theorem lift_of_decode {dec : ByteArray → Option α} (hdec : DecoderSound dec)
    {R : α → α → Prop} {b b' : ByteArray} {a a' : α}
    (hb : dec b = some a) (hb' : dec b' = some a') (hr : R a a') :
    Lift R b.data.toList b'.data.toList :=
  ⟨a, a', hdec b a hb, hdec b' a' hb', hr⟩

/-- A sound decoder that is complete on `F` decides the encoding relation on `F`. -/
theorem decode_eq_some_iff {dec : ByteArray → Option α} {F : α → Prop}
    (hs : DecoderSound dec) (hc : DecoderCompleteOn F dec) {b : ByteArray} {a : α} (ha : F a) :
    dec b = some a ↔ EncodesBytes b a :=
  ⟨hs b a, hc b a ha⟩

/-- Encoding then decoding returns the value, for a correct encoder and a decoder
complete on its domain. -/
theorem decode_encode {dec : ByteArray → Option α} {enc : α → ByteArray} {F : α → Prop}
    (he : EncoderCorrectOn F enc) (hc : DecoderCompleteOn F dec) {a : α} (ha : F a) :
    dec (enc a) = some a :=
  hc _ _ ha (he a ha)

/-- A sound decoder for a functional encoding returns the only possible value. -/
theorem decode_unique (hF : Functional α) {dec : ByteArray → Option α} (hs : DecoderSound dec)
    {b : ByteArray} {a a' : α} (hd : dec b = some a) (he : EncodesBytes b a') : a = a' :=
  hF (hs b a hd) he

end

/-! ## Embeddings between encodings

An embedding `f : α → β` *agrees* with the encodings on `P` when every encoding of
`a` (with `P a`) is also an encoding of `f a`. Then lifted relations transport. -/

section
variable [Encoding α] [Encoding β]

/-- The embedding `f` agrees with the encodings on syntax satisfying `P`. -/
def Agrees (P : α → Prop) (f : α → β) : Prop :=
  ∀ ⦃b a⦄, Encodes b a → P a → Encodes b (f a)

/-- Pulling `R` back along `f` and lifting over `α` lands inside the lift over `β`. -/
theorem Lift.of_agrees {P : α → Prop} {f : α → β} (hf : Agrees P f) {R : β → β → Prop}
    {b b' : List UInt8} (h : Lift (fun a a' => P a ∧ P a' ∧ R (f a) (f a')) b b') :
    Lift R b b' := by
  obtain ⟨a, a', ha, ha', hp, hp', hr⟩ := h
  exact ⟨f a, f a', hf ha hp, hf ha' hp', hr⟩

/-- On bytes that decode (over `α`) to syntax satisfying `P`, lifting commutes with
the embedding: relating the `β`-decodings is relating the images of the `α`-decodings. -/
theorem Lift.agrees_iff (hFα : Functional α) (hFβ : Functional β) {P : α → Prop} {f : α → β}
    (hf : Agrees P f) {R : β → β → Prop} {b b' : List UInt8} {a a' : α}
    (ha : Encodes b a) (ha' : Encodes b' a') (hp : P a) (hp' : P a') :
    Lift R b b' ↔ Lift (α := α) (fun x y => R (f x) (f y)) b b' := by
  rw [Lift.iff_of_encodes hFβ (hf ha hp) (hf ha' hp'), Lift.iff_of_encodes hFα ha ha']

/-- Agreement plus functionality of the target pins down the target decoding. -/
theorem Agrees.decode_eq (hFβ : Functional β) {P : α → Prop} {f : α → β} (hf : Agrees P f)
    {b : List UInt8} {a : α} {c : β} (ha : Encodes b a) (hp : P a) (hc : Encodes b c) :
    c = f a :=
  hFβ hc (hf ha hp)

end

end Encoding
end Silmaril
