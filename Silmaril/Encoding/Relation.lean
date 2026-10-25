module

public import Mathlib.Data.Set.Basic
public import Mathlib.Logic.Relation

/-!
# Encoding relations as values

An encoding of abstract syntax `α` in a carrier `σ` (bytes, Unicode text,
natural numbers, …) is a relation `E : EncRel σ α`: `E s a` holds when the
carrier value `s` is a well-formed spelling of `a`.  Unlike the typeclass
presentation (`Silmaril.Encoding`, one encoding per syntax type), encodings
here are *values*, so several encodings of the same syntax type — a general
grammar, its canonical form, a profile — can be compared, combined and
transported.  `Lattice.lean` orders them, `Per.lean` studies the equivalence
they induce on the carrier, and `Category.lean` organizes them into
categories.

Encoders and decoders are specified *against* a relation
(`DecoderSound`, `DecoderCompleteOn`, `EncoderCorrectOn`), exactly as in the
class-based interface; the bridge from that interface is `Encoding.rel :=
fun b a => Encoding.Encodes b a` (`Silmaril.Encoding.Bridge`), where the two
sets of notions are shown to coincide.

Carrier change (`push`, `pull`, and their partial versions) is the
"change of representation" operation: UTF-8 maps text encodings to byte
encodings, and so on.
-/

@[expose] public section

namespace Silmaril

/-- An encoding relation: `E s a` means that the carrier value `s` encodes the
abstract value `a`.  The carrier `σ` comes first, so `EncRel (List UInt8) α`
reads "byte encodings of `α`". -/
def EncRel (σ α : Type) : Type := σ → α → Prop

namespace EncRel

variable {σ σ' σ'' α β γ : Type}

@[ext] theorem ext {E F : EncRel σ α} (h : ∀ s a, E s a ↔ F s a) : E = F :=
  funext fun s => funext fun a => propext (h s a)

/-! ## Basic predicates -/

section Predicates

variable (E : EncRel σ α)

/-- The carrier determines the syntax: at most one abstract value per spelling. -/
def Functional : Prop := ∀ ⦃s : σ⦄ ⦃a a' : α⦄, E s a → E s a' → a = a'

/-- The syntax determines the carrier: at most one spelling per abstract value
(a canonical or deterministic encoding). -/
def Deterministic : Prop := ∀ ⦃s s' : σ⦄ ⦃a : α⦄, E s a → E s' a → s = s'

/-- Every abstract value has at least one spelling. -/
def Total : Prop := ∀ a : α, ∃ s, E s a

/-- Every carrier value is a valid spelling of something. -/
def Surjective : Prop := ∀ s : σ, ∃ a, E s a

/-- The carrier value has at least one decoding. -/
def Encodable (s : σ) : Prop := ∃ a, E s a

/-- The valid spellings. -/
def domain : Set σ := {s | E.Encodable s}

/-- The abstract values that have a spelling. -/
def image : Set α := {a | ∃ s, E s a}

/-- A functional, deterministic encoding is a partial bijection. -/
def Bijective : Prop := E.Functional ∧ E.Deterministic

end Predicates

/-! ## Constructions -/

/-- Restrict an encoding to abstract values satisfying `P`. -/
def restrict (E : EncRel σ α) (P : α → Prop) : EncRel σ α := fun s a => E s a ∧ P a

/-- Restrict an encoding to carrier values satisfying `Q`. -/
def restrictCarrier (E : EncRel σ α) (Q : σ → Prop) : EncRel σ α := fun s a => Q s ∧ E s a

/-- Reindex the syntax along `f : β → α`: `b` is spelled like `f b`. -/
def comap (f : β → α) (E : EncRel σ α) : EncRel σ β := fun s b => E s (f b)

/-- Push the syntax along `f : α → β`: `s` spells `b` when it spells some
preimage of `b`.  This is the left adjoint of `comap f`. -/
def map (f : α → β) (E : EncRel σ α) : EncRel σ β := fun s b => ∃ a, E s a ∧ f a = b

/-- Push the syntax along a partial map (Kleisli style). -/
def mapPartial (f : α → Option β) (E : EncRel σ α) : EncRel σ β :=
  fun s b => ∃ a, E s a ∧ f a = some b

/-- Carrier change along `g : σ → σ'` (pushforward, written `g_!`):
`s'` spells `a` when it is the image of a spelling of `a`. -/
def push (g : σ → σ') (E : EncRel σ α) : EncRel σ' α := fun s' a => ∃ s, g s = s' ∧ E s a

/-- Carrier pullback along `g : σ → σ'` (written `g^*`): `s` spells `a` when
`g s` does.  Right adjoint of `push g`. -/
def pull (g : σ → σ') (E : EncRel σ' α) : EncRel σ α := fun s a => E (g s) a

/-- Universal pushforward along `g`: every preimage of `s'` spells `a`.
Right adjoint of `pull g`. -/
def pushAll (g : σ → σ') (E : EncRel σ α) : EncRel σ' α := fun s' a => ∀ s, g s = s' → E s a

/-- Pushforward along a partial carrier map (e.g. a partial decoder from bytes
to text). -/
def pushPartial (g : σ → Option σ') (E : EncRel σ α) : EncRel σ' α :=
  fun s' a => ∃ s, g s = some s' ∧ E s a

/-- Pullback along a partial carrier map: `s` spells `a` when `g s` is defined
and spells `a`. -/
def pullPartial (g : σ → Option σ') (E : EncRel σ' α) : EncRel σ α :=
  fun s a => ∃ s', g s = some s' ∧ E s' a

/-- Weak pullback along a partial map: wherever `g s` is defined, it spells `a`
(vacuous outside the domain of `g`).  Right adjoint of `pushPartial g`. -/
def pullPartialAll (g : σ → Option σ') (E : EncRel σ' α) : EncRel σ α :=
  fun s a => ∀ s', g s = some s' → E s' a

/-- The graph of a total encoder. -/
def ofFun (enc : α → σ) : EncRel σ α := fun s a => enc a = s

/-- The graph of a partial encoder. -/
def ofPartialFun (enc : α → Option σ) : EncRel σ α := fun s a => enc a = some s

/-- The graph of a decoder. -/
def ofDecoder (dec : σ → Option α) : EncRel σ α := fun s a => dec s = some a

/-- Sequential composition: spell `a : α` in an intermediate carrier `τ`, then
spell that intermediate value in `σ`.  (Used for layered formats.) -/
def comp {τ : Type} (F : EncRel σ τ) (E : EncRel τ α) : EncRel σ α :=
  fun s a => ∃ t, F s t ∧ E t a

/-! ## Encoder and decoder specifications -/

section Specs

variable (E : EncRel σ α)

/-- Every value returned by the decoder is encoded by its input. -/
def DecoderSound (dec : σ → Option α) : Prop := ∀ s a, dec s = some a → E s a

/-- The decoder decodes every spelling of every value satisfying `P`. -/
def DecoderCompleteOn (P : α → Prop) (dec : σ → Option α) : Prop :=
  ∀ s a, P a → E s a → dec s = some a

/-- The decoder decodes every spelling. -/
def DecoderComplete (dec : σ → Option α) : Prop := ∀ s a, E s a → dec s = some a

/-- The encoder emits a valid spelling of each value satisfying `P`. -/
def EncoderCorrectOn (P : α → Prop) (enc : α → σ) : Prop := ∀ a, P a → E (enc a) a

/-- The encoder emits a valid spelling of every value. -/
def EncoderCorrect (enc : α → σ) : Prop := ∀ a, E (enc a) a

/-- A partial encoder only emits valid spellings. -/
def PartialEncoderSound (enc : α → Option σ) : Prop := ∀ a s, enc a = some s → E s a

/-- Carrier values related by `R` through their decodings. -/
def Lift (R : α → α → Prop) (s s' : σ) : Prop := ∃ a a', E s a ∧ E s' a' ∧ R a a'

end Specs

/-! ## Elementary facts -/

section Facts

variable {E F : EncRel σ α}

theorem ofDecoder_functional (dec : σ → Option α) : (ofDecoder dec).Functional := by
  intro s a a' h h'
  exact Option.some.inj (h.symm.trans h')

theorem ofFun_deterministic (enc : α → σ) : (ofFun enc).Deterministic := by
  intro s s' a h h'
  exact h.symm.trans h'

theorem ofFun_total (enc : α → σ) : (ofFun enc).Total := fun a => ⟨enc a, rfl⟩

theorem ofPartialFun_deterministic (enc : α → Option σ) :
    (ofPartialFun enc).Deterministic := by
  intro s s' a h h'
  exact Option.some.inj (h.symm.trans h')

theorem Functional.decode_unique (hF : E.Functional) {dec : σ → Option α}
    (hs : E.DecoderSound dec) {s : σ} {a a' : α} (hd : dec s = some a) (he : E s a') :
    a = a' :=
  hF (hs s a hd) he

theorem decode_encode {dec : σ → Option α} {enc : α → σ} {P : α → Prop}
    (he : E.EncoderCorrectOn P enc) (hc : E.DecoderCompleteOn P dec) {a : α} (ha : P a) :
    dec (enc a) = some a :=
  hc _ _ ha (he a ha)

theorem decode_eq_some_iff {dec : σ → Option α} {P : α → Prop}
    (hs : E.DecoderSound dec) (hc : E.DecoderCompleteOn P dec) {s : σ} {a : α} (ha : P a) :
    dec s = some a ↔ E s a :=
  ⟨hs s a, hc s a ha⟩

/-- A functional encoding with a sound decoder that succeeds on every spelling
has a complete decoder. -/
theorem Functional.decoderComplete (hF : E.Functional) {dec : σ → Option α}
    (hs : E.DecoderSound dec) (hdef : ∀ s, E.Encodable s → (dec s).isSome) :
    E.DecoderComplete dec := by
  intro s a h
  obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp (hdef s ⟨a, h⟩)
  rw [ha', hF (hs s a' ha') h]

theorem Lift.mono {R S : α → α → Prop} (h : ∀ a a', R a a' → S a a') {s s' : σ}
    (hl : E.Lift R s s') : E.Lift S s s' := by
  obtain ⟨a, a', ha, ha', hr⟩ := hl
  exact ⟨a, a', ha, ha', h _ _ hr⟩

theorem Lift.iff_of_encodes (hF : E.Functional) {R : α → α → Prop} {s s' : σ} {a a' : α}
    (ha : E s a) (ha' : E s' a') : E.Lift R s s' ↔ R a a' := by
  constructor
  · rintro ⟨c, c', hc, hc', hr⟩
    rwa [hF ha hc, hF ha' hc']
  · exact fun hr => ⟨a, a', ha, ha', hr⟩

/-- Translation validation through a sound decoder. -/
theorem lift_of_decode {dec : σ → Option α} (hdec : E.DecoderSound dec)
    {R : α → α → Prop} {s s' : σ} {a a' : α}
    (hs : dec s = some a) (hs' : dec s' = some a') (hr : R a a') : E.Lift R s s' :=
  ⟨a, a', hdec s a hs, hdec s' a' hs', hr⟩

@[simp] theorem pull_id (E : EncRel σ α) : pull id E = E := rfl

@[simp] theorem comap_id (E : EncRel σ α) : comap id E = E := rfl

theorem pull_pull (g : σ → σ') (h : σ' → σ'') (E : EncRel σ'' α) :
    pull g (pull h E) = pull (h ∘ g) E := rfl

theorem comap_comap (f : β → α) (f' : γ → β) (E : EncRel σ α) :
    comap f' (comap f E) = comap (f ∘ f') E := rfl

theorem push_push (g : σ → σ') (h : σ' → σ'') (E : EncRel σ α) :
    push h (push g E) = push (h ∘ g) E := by
  ext s'' a
  constructor
  · rintro ⟨s', rfl, s, rfl, hs⟩
    exact ⟨s, rfl, hs⟩
  · rintro ⟨s, rfl, hs⟩
    exact ⟨g s, rfl, s, rfl, hs⟩

@[simp] theorem push_id (E : EncRel σ α) : push id E = E := by
  ext s a
  constructor
  · rintro ⟨s, rfl, hs⟩; exact hs
  · intro h; exact ⟨s, rfl, h⟩

/-- Carrier change and syntax reindexing commute. -/
theorem pull_comap (g : σ → σ') (f : β → α) (E : EncRel σ' α) :
    pull g (comap f E) = comap f (pull g E) := rfl

theorem push_comap (g : σ → σ') (f : β → α) (E : EncRel σ α) :
    push g (comap f E) = comap f (push g E) := rfl

/-- Partial pushforward is total pushforward into `Option σ'` followed by
pullback along `some` (the Kleisli decomposition). -/
theorem pushPartial_eq (g : σ → Option σ') (E : EncRel σ α) :
    pushPartial g E = pull some (push g E) := rfl

/-- Partial pullback is total pullback of the `some`-pushforward. -/
theorem pullPartial_eq (g : σ → Option σ') (E : EncRel σ' α) :
    pullPartial g E = pull g (push some E) := by
  ext s a
  constructor
  · rintro ⟨s', hs, h⟩; exact ⟨s', hs.symm, h⟩
  · rintro ⟨s', hs, h⟩; exact ⟨s', hs.symm, h⟩

/-- A total map is a partial map that is always defined. -/
theorem pushPartial_some_comp (g : σ → σ') (E : EncRel σ α) :
    pushPartial (some ∘ g) E = push g E := by
  ext s' a
  simp [pushPartial, push]

theorem pullPartial_some_comp (g : σ → σ') (E : EncRel σ' α) :
    pullPartial (some ∘ g) E = pull g E := by
  ext s a
  simp [pullPartial, pull]

/-- The pullback of a functional encoding is functional. -/
theorem Functional.pull {F' : EncRel σ' α} (hF' : F'.Functional) (g : σ → σ') :
    (EncRel.pull g F').Functional :=
  fun _ _ _ h h' => hF' h h'

theorem Functional.pullPartial {F' : EncRel σ' α} (hF' : F'.Functional)
    (g : σ → Option σ') : (EncRel.pullPartial g F').Functional := by
  rintro s a a' ⟨t, ht, h⟩ ⟨t', ht', h'⟩
  rw [ht] at ht'
  cases ht'
  exact hF' h h'

/-- Pushforward along an injective map preserves functionality. -/
theorem Functional.push (hE : E.Functional) {g : σ → σ'} (hg : Function.Injective g) :
    (EncRel.push g E).Functional := by
  rintro s' a a' ⟨s, rfl, h⟩ ⟨t, ht, h'⟩
  exact hE h (hg ht ▸ h')

theorem Deterministic.push (hE : E.Deterministic) (g : σ → σ') :
    (EncRel.push g E).Deterministic := by
  rintro s' t' a ⟨s, rfl, h⟩ ⟨t, rfl, h'⟩
  rw [hE h h']

theorem Total.push (hE : E.Total) (g : σ → σ') : (EncRel.push g E).Total := by
  intro a
  obtain ⟨s, h⟩ := hE a
  exact ⟨g s, s, rfl, h⟩

/-- Pullback along an injective map preserves determinism. -/
theorem Deterministic.pull {F' : EncRel σ' α} (hF : F'.Deterministic)
    {g : σ → σ'} (hg : Function.Injective g) : (EncRel.pull g F').Deterministic :=
  fun _ _ _ h h' => hg (hF h h')

/-- Injective pushforward followed by pullback is the identity. -/
theorem pull_push_of_injective {g : σ → σ'} (hg : Function.Injective g) (E : EncRel σ α) :
    pull g (push g E) = E := by
  ext s a
  constructor
  · rintro ⟨t, ht, h⟩; exact hg ht ▸ h
  · intro h; exact ⟨s, rfl, h⟩

/-- Pushforward along `g` followed by partial pushforward along a left inverse
`g?` of `g` is the identity (e.g. UTF-8 encode, then UTF-8 decode). -/
theorem pushPartial_push_of_leftInverse {g : σ → σ'} {g? : σ' → Option σ}
    (hg : ∀ s, g? (g s) = some s) (E : EncRel σ α) :
    pushPartial g? (push g E) = E := by
  ext s a
  constructor
  · rintro ⟨t, ht, s₀, rfl, h⟩
    rw [hg s₀] at ht
    cases ht
    exact h
  · intro h
    exact ⟨g s, hg s, s, rfl, h⟩

/-- When `g?` is a partial inverse of `g` (`g? t = some s ↔ g s = t`), the
pushforward along `g` equals the partial pullback along `g?`.  For UTF-8 this
says: the byte spellings of a text format are exactly the well-formed UTF-8
byte strings whose decoding is a text spelling. -/
theorem push_eq_pullPartial {g : σ → σ'} {g? : σ' → Option σ}
    (hg : ∀ s t, g? t = some s ↔ g s = t) (E : EncRel σ α) :
    push g E = pullPartial g? E := by
  ext t a
  constructor
  · rintro ⟨s, rfl, h⟩; exact ⟨s, (hg s (g s)).mpr rfl, h⟩
  · rintro ⟨s, hs, h⟩; exact ⟨s, (hg s t).mp hs, h⟩

end Facts

end EncRel

end Silmaril
