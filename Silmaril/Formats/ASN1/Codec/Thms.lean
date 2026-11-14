module

public import Silmaril.Formats.ASN1.Codec.Defs
import Silmaril.Proofs.Formats.ASN1.Codec

/-!
# ASN.1 codecs: laws

* `Codec.dec_sound`, `Codec.dec_complete`, `Codec.enc_correct`,
  `Codec.rel_functional`, `Codec.rel_deterministic`: a lawful codec's decoder
  and encoder against its relation, and the relation is a partial bijection;
* `Codec.lawful_*`: every combinator of `Codec.Defs` preserves lawfulness,
  under the side conditions that make the schema unambiguous (`orElse`,
  `optField`) or the representation change invertible (`iso`);
* `Codec.TagIs` and `Codec.HeadNot` lemmas discharge the `optField` side
  conditions structurally;
* `Codec.derCodec_rel_eq`: the DER relation of a schema is `derRel` composed
  with the schema relation.
-/

@[expose] public section

namespace Silmaril.Formats.ASN1

open Silmaril

namespace Codec

variable {σ α β γ : Type}

/-! ## Laws of a lawful codec -/

theorem Lawful.dec_eq_some_iff {c : Codec σ α} (hc : c.Lawful) {s : σ} {a : α} :
    c.dec s = some a ↔ c.rel s a :=
  ⟨hc.enc_dec, fun ⟨h, e⟩ => e ▸ hc.dec_enc a h⟩

theorem dec_sound {c : Codec σ α} (hc : c.Lawful) : c.rel.DecoderSound c.dec :=
  fun _ _ h => hc.enc_dec h

theorem dec_complete {c : Codec σ α} (hc : c.Lawful) : c.rel.DecoderComplete c.dec :=
  fun _ _ h => hc.dec_eq_some_iff.mpr h

theorem enc_correct (c : Codec σ α) : c.rel.EncoderCorrectOn c.WF c.enc := fun _ h => ⟨h, rfl⟩

theorem rel_functional {c : Codec σ α} (hc : c.Lawful) : c.rel.Functional := fun _ _ _ h h' =>
  Option.some.inj ((dec_complete hc _ _ h).symm.trans (dec_complete hc _ _ h'))

theorem rel_deterministic (c : Codec σ α) : c.rel.Deterministic := fun _ _ _ h h' =>
  h.2.symm.trans h'.2

theorem enc_injective {c : Codec σ α} (hc : c.Lawful) {a a' : α} (h : c.WF a) (h' : c.WF a')
    (e : c.enc a = c.enc a') : a = a' :=
  rel_functional hc ⟨h, rfl⟩ ⟨h', e.symm⟩

/-! ## Combinators preserve lawfulness -/

theorem lawful_iso {c : Codec σ α} (hc : c.Lawful) {f : α → β} {g : β → α}
    (hgf : ∀ a, c.WF a → g (f a) = a) (hfg : ∀ b, c.WF (g b) → f (g b) = b) :
    (c.iso f g).Lawful :=
  Proofs.Formats.ASN1.lawful_iso hc hgf hfg

theorem lawful_refine {c : Codec σ α} (hc : c.Lawful) (P : α → Prop) [DecidablePred P] :
    (c.refine P).Lawful :=
  Proofs.Formats.ASN1.lawful_refine hc P

theorem lawful_orElse {c₁ : Codec σ α} {c₂ : Codec σ β} (h₁ : c₁.Lawful) (h₂ : c₂.Lawful)
    (h : ∀ b, c₂.WF b → c₁.dec (c₂.enc b) = none) : (c₁.orElse c₂).Lawful :=
  Proofs.Formats.ASN1.lawful_orElse h₁ h₂ h

theorem lawful_any : any.Lawful := Proofs.Formats.ASN1.lawful_any

theorem lawful_prim (t : Tag) {c : Codec (List UInt8) α} (hc : c.Lawful) : (prim t c).Lawful :=
  Proofs.Formats.ASN1.lawful_prim t hc

theorem lawful_cons (t : Tag) {c : Codec (List Value) α} (hc : c.Lawful) : (cons t c).Lawful :=
  Proofs.Formats.ASN1.lawful_cons t hc

theorem lawful_nil : nil.Lawful := Proofs.Formats.ASN1.lawful_nil

theorem lawful_field {c : Codec Value α} {rest : Codec (List Value) β} (hc : c.Lawful)
    (hr : rest.Lawful) : (field c rest).Lawful :=
  Proofs.Formats.ASN1.lawful_field hc hr

/-- An `OPTIONAL` component is unambiguous when its tag is fixed and the rest
cannot start with that tag. -/
theorem lawful_optField {t : Tag} {c : Codec Value α} {rest : Codec (List Value) β}
    (hc : c.Lawful) (hr : rest.Lawful) (htag : c.TagIs t) (hrest : rest.HeadNot t) :
    (optField t c rest).Lawful :=
  Proofs.Formats.ASN1.lawful_optField hc hr htag hrest

theorem lawful_optLast {c : Codec Value α} (hc : c.Lawful) : (optLast c).Lawful :=
  Proofs.Formats.ASN1.lawful_optLast hc

theorem lawful_seqOf {c : Codec Value α} (hc : c.Lawful) : (seqOf c).Lawful :=
  Proofs.Formats.ASN1.lawful_seqOf hc

theorem lawful_setOf {c : Codec Value α} (hc : c.Lawful) : (setOf c).Lawful :=
  Proofs.Formats.ASN1.lawful_setOf hc

theorem lawful_explicit (n : Nat) {c : Codec Value α} (hc : c.Lawful) : (explicit n c).Lawful :=
  Proofs.Formats.ASN1.lawful_explicit n hc

theorem lawful_defaulted [DecidableEq α] (d : α) {c : Codec σ (Option α × γ)} (hc : c.Lawful) :
    (defaulted d c).Lawful :=
  Proofs.Formats.ASN1.lawful_defaulted d hc

theorem lawful_derCodec {c : Codec Value α} (hc : c.Lawful) : (derCodec c).Lawful :=
  Proofs.Formats.ASN1.lawful_derCodec hc

/-! ## Tags of components -/

theorem tagIs_prim (t : Tag) (c : Codec (List UInt8) α) : (prim t c).TagIs t := fun _ _ => rfl

theorem tagIs_cons (t : Tag) (c : Codec (List Value) α) : (cons t c).TagIs t := fun _ _ => rfl

theorem tagIs_explicit (n : Nat) (c : Codec Value α) : (explicit n c).TagIs (Tag.context n) :=
  fun _ _ => rfl

theorem tagIs_iso {c : Codec Value α} {t : Tag} (h : c.TagIs t) (f : α → β) (g : β → α) :
    (c.iso f g).TagIs t := fun b hb => h (g b) hb

theorem tagIs_refine {c : Codec Value α} {t : Tag} (h : c.TagIs t) (P : α → Prop)
    [DecidablePred P] : (c.refine P).TagIs t := fun a ha => h a ha.1

theorem headNot_nil (t : Tag) : nil.HeadNot t := fun _ _ _ hv => by cases hv

theorem headNot_field {c : Codec Value α} {t : Tag} (h : ∀ a, c.WF a → (c.enc a).tag ≠ t)
    (rest : Codec (List Value) β) : (field c rest).HeadNot t :=
  Proofs.Formats.ASN1.headNot_field h rest

theorem headNot_field_of_tagIs {c : Codec Value α} {t t' : Tag} (h : c.TagIs t') (hne : t' ≠ t)
    (rest : Codec (List Value) β) : (field c rest).HeadNot t :=
  headNot_field (fun a ha => h a ha ▸ hne) rest

theorem headNot_optField {t t' : Tag} {c : Codec Value α} {rest : Codec (List Value) β}
    (htag : c.TagIs t') (hne : t' ≠ t) (h : rest.HeadNot t) :
    (optField t' c rest).HeadNot t :=
  Proofs.Formats.ASN1.headNot_optField htag hne h

theorem headNot_optLast {c : Codec Value α} {t : Tag} (h : ∀ a, c.WF a → (c.enc a).tag ≠ t) :
    (optLast c).HeadNot t :=
  Proofs.Formats.ASN1.headNot_optLast h

theorem headNot_iso {c : Codec (List Value) α} {t : Tag} (h : c.HeadNot t) (f : α → β)
    (g : β → α) : (c.iso f g).HeadNot t := fun b hb => h (g b) hb

theorem headNot_refine {c : Codec (List Value) α} {t : Tag} (h : c.HeadNot t) (P : α → Prop)
    [DecidablePred P] : (c.refine P).HeadNot t := fun a ha => h a ha.1

theorem headNot_defaulted [DecidableEq α] {d : α} {c : Codec (List Value) (Option α × γ)}
    {t : Tag} (h : c.HeadNot t) : (defaulted d c).HeadNot t :=
  headNot_iso (headNot_refine h _) _ _

/-! ## DER octets -/

/-- The DER relation of a schema is DER composed with the schema relation. -/
theorem derCodec_rel_iff (c : Codec Value α) (s : List UInt8) (a : α) :
    (derCodec c).rel s a ↔ EncRel.comp derRel c.rel s a :=
  Proofs.Formats.ASN1.derCodec_rel_iff c s a

theorem derCodec_rel_eq (c : Codec Value α) : (derCodec c).rel = EncRel.comp derRel c.rel :=
  EncRel.ext fun s a => derCodec_rel_iff c s a

end Codec

end Silmaril.Formats.ASN1
