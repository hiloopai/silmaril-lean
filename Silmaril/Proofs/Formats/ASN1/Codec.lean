module

public import Silmaril.Formats.ASN1.Codec.Defs
import Silmaril.Formats.ASN1.Der.Thms

/-! Proofs for `Silmaril.Formats.ASN1.Codec.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.ASN1

open Silmaril Silmaril.Formats.ASN1 Silmaril.Formats.ASN1.Codec

variable {σ α β γ : Type}

theorem lawful_iso {c : Codec σ α} (hc : c.Lawful) {f : α → β} {g : β → α}
    (hgf : ∀ a, c.WF a → g (f a) = a) (hfg : ∀ b, c.WF (g b) → f (g b) = b) :
    (c.iso f g).Lawful where
  dec_enc b h := by simp [iso, hc.dec_enc _ h, hfg b h]
  enc_dec {s b} h := by
    simp only [iso, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    obtain ⟨hwf, rfl⟩ := hc.enc_dec ha
    constructor
    · show c.WF (g (f a)); rw [hgf a hwf]; exact hwf
    · show c.enc (g (f a)) = c.enc a; rw [hgf a hwf]

theorem lawful_refine {c : Codec σ α} (hc : c.Lawful) (P : α → Prop) [DecidablePred P] :
    (c.refine P).Lawful where
  dec_enc a h := by simp [refine, hc.dec_enc a h.1, h.2]
  enc_dec {s a} h := by
    simp only [refine] at h
    split at h
    · rename_i a' ha'
      split_ifs at h with hp
      cases h
      exact ⟨⟨(hc.enc_dec ha').1, hp⟩, (hc.enc_dec ha').2⟩
    · cases h

theorem lawful_orElse {c₁ : Codec σ α} {c₂ : Codec σ β} (h₁ : c₁.Lawful) (h₂ : c₂.Lawful)
    (h : ∀ b, c₂.WF b → c₁.dec (c₂.enc b) = none) : (c₁.orElse c₂).Lawful where
  dec_enc x hx := by
    cases x with
    | inl a => simp [orElse, h₁.dec_enc a hx]
    | inr b => simp [orElse, h b hx, h₂.dec_enc b hx]
  enc_dec {s x} hd := by
    simp only [orElse] at hd
    split at hd
    · rename_i a ha
      cases hd
      exact h₁.enc_dec ha
    · simp only [Option.map_eq_some_iff] at hd
      obtain ⟨b, hb, rfl⟩ := hd
      exact h₂.enc_dec hb

theorem lawful_any : any.Lawful where
  dec_enc _ _ := rfl
  enc_dec h := by cases h; exact ⟨trivial, rfl⟩

theorem lawful_prim (t : Tag) {c : Codec (List UInt8) α} (hc : c.Lawful) : (prim t c).Lawful where
  dec_enc a h := by simp [prim, hc.dec_enc a h]
  enc_dec {v a} h := by
    cases v with
    | prim t' b =>
        simp only [prim] at h
        split_ifs at h with ht
        subst ht
        obtain ⟨hwf, rfl⟩ := hc.enc_dec h
        exact ⟨hwf, rfl⟩
    | cons _ _ => cases h

theorem lawful_cons (t : Tag) {c : Codec (List Value) α} (hc : c.Lawful) : (cons t c).Lawful where
  dec_enc a h := by simp [cons, hc.dec_enc a h]
  enc_dec {v a} h := by
    cases v with
    | cons t' vs =>
        simp only [cons] at h
        split_ifs at h with ht
        subst ht
        obtain ⟨hwf, rfl⟩ := hc.enc_dec h
        exact ⟨hwf, rfl⟩
    | prim _ _ => cases h

theorem lawful_nil : nil.Lawful where
  dec_enc _ _ := rfl
  enc_dec {vs u} h := by
    cases vs with
    | nil => exact ⟨trivial, rfl⟩
    | cons _ _ => cases h

theorem lawful_field {c : Codec Value α} {rest : Codec (List Value) β} (hc : c.Lawful)
    (hr : rest.Lawful) : (field c rest).Lawful where
  dec_enc p h := by simp [field, hc.dec_enc _ h.1, hr.dec_enc _ h.2]
  enc_dec {vs p} h := by
    cases vs with
    | nil => cases h
    | cons v vs =>
        simp only [field] at h
        split at h
        · rename_i a b ha hb
          cases h
          obtain ⟨h₁, rfl⟩ := hc.enc_dec ha
          obtain ⟨h₂, rfl⟩ := hr.enc_dec hb
          exact ⟨⟨h₁, h₂⟩, rfl⟩
        · cases h

theorem lawful_optField {t : Tag} {c : Codec Value α} {rest : Codec (List Value) β}
    (hc : c.Lawful) (hr : rest.Lawful) (htag : c.TagIs t) (hrest : rest.HeadNot t) :
    (optField t c rest).Lawful where
  dec_enc p h := by
    obtain ⟨o, b⟩ := p
    cases o with
    | some a =>
        have := htag a (h.1 a rfl)
        simp [optField, this, hc.dec_enc a (h.1 a rfl), hr.dec_enc b h.2]
    | none =>
        simp only [optField]
        cases hb : rest.enc b with
        | nil => simp [← hb, hr.dec_enc b h.2]
        | cons v vs =>
            have hv : v.tag ≠ t := hrest b h.2 v (by simp [hb])
            simp [hv, ← hb, hr.dec_enc b h.2]
  enc_dec {vs p} h := by
    cases vs with
    | nil =>
        simp only [optField, Option.map_eq_some_iff] at h
        obtain ⟨b, hb, rfl⟩ := h
        obtain ⟨hwf, he⟩ := hr.enc_dec hb
        exact ⟨⟨by simp, hwf⟩, he⟩
    | cons v vs =>
        simp only [optField] at h
        split_ifs at h with ht
        · split at h
          · rename_i a b ha hb
            cases h
            obtain ⟨h₁, rfl⟩ := hc.enc_dec ha
            obtain ⟨h₂, rfl⟩ := hr.enc_dec hb
            exact ⟨⟨by simpa using h₁, h₂⟩, rfl⟩
          · cases h
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨b, hb, rfl⟩ := h
          obtain ⟨hwf, he⟩ := hr.enc_dec hb
          exact ⟨⟨by simp, hwf⟩, he⟩

theorem lawful_optLast {c : Codec Value α} (hc : c.Lawful) : (optLast c).Lawful where
  dec_enc o h := by
    cases o with
    | none => rfl
    | some a => simp [optLast, hc.dec_enc a (h a rfl)]
  enc_dec {vs o} h := by
    match vs, h with
    | [], h => cases h; exact ⟨fun _ h => (by cases h), rfl⟩
    | [v], h =>
        simp only [optLast, Option.map_eq_some_iff] at h
        obtain ⟨a, ha, rfl⟩ := h
        obtain ⟨hwf, rfl⟩ := hc.enc_dec ha
        exact ⟨fun _ h => (by cases h; exact hwf), rfl⟩

theorem lawful_seqOf {c : Codec Value α} (hc : c.Lawful) : (seqOf c).Lawful where
  dec_enc l h := by
    change decAll c.dec (l.map c.enc) = some l
    induction l with
    | nil => rfl
    | cons a l ih =>
        simp only [List.map_cons, decAll, hc.dec_enc a (h a (by simp)),
          ih (fun x hx => h x (by simp [hx]))]
  enc_dec {vs l} h := by
    change decAll c.dec vs = some l at h
    change (∀ a ∈ l, c.WF a) ∧ l.map c.enc = vs
    induction vs generalizing l with
    | nil => cases h; exact ⟨by simp, rfl⟩
    | cons v vs ih =>
        simp only [decAll] at h
        split at h
        · rename_i a as ha has
          cases h
          obtain ⟨h₁, rfl⟩ := hc.enc_dec ha
          obtain ⟨h₂, rfl⟩ := ih has
          refine ⟨?_, rfl⟩
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact h₁
          · exact h₂ x hx
        · cases h

theorem lawful_derCodec {c : Codec Value α} (hc : c.Lawful) : (derCodec c).Lawful where
  dec_enc a h := by simp [derCodec, decode_encode h.2, hc.dec_enc a h.1]
  enc_dec {s a} h := by
    simp only [derCodec] at h
    split at h
    · rename_i v hv
      obtain ⟨hwf, rfl⟩ := hc.enc_dec h
      obtain ⟨hvwf, he⟩ := (derRel_iff _ _).mp (decode_sound _ _ hv)
      exact ⟨⟨hwf, hvwf⟩, he⟩
    · cases h

theorem lawful_explicit (n : Nat) {c : Codec Value α} (hc : c.Lawful) : (explicit n c).Lawful :=
  lawful_cons _ (lawful_iso (lawful_field hc lawful_nil) (fun _ _ => rfl) (fun _ _ => rfl))

theorem lawful_setOf {c : Codec Value α} (hc : c.Lawful) : (setOf c).Lawful :=
  lawful_refine (lawful_seqOf hc) _

theorem lawful_defaulted [DecidableEq α] (d : α) {c : Codec σ (Option α × γ)} (hc : c.Lawful) :
    (defaulted d c).Lawful := by
  refine lawful_iso (lawful_refine hc _) ?_ ?_
  · rintro ⟨o, g⟩ ⟨-, ho⟩
    cases o with
    | none => simp
    | some a => simp only at ho; simp [show a ≠ d from fun h => ho (h ▸ rfl)]
  · rintro ⟨a, g⟩ -
    by_cases h : a = d <;> simp [h]

theorem headNot_field {c : Codec Value α} {t : Tag} (h : ∀ a, c.WF a → (c.enc a).tag ≠ t)
    (rest : Codec (List Value) β) : (field c rest).HeadNot t := by
  rintro ⟨a, b⟩ hp v hv
  simp only [field, List.head?_cons, Option.mem_def, Option.some.injEq] at hv
  subst hv
  exact h a hp.1

theorem headNot_optField {t t' : Tag} {c : Codec Value α} {rest : Codec (List Value) β}
    (htag : c.TagIs t') (hne : t' ≠ t) (h : rest.HeadNot t) :
    (optField t' c rest).HeadNot t := by
  rintro ⟨o, b⟩ hp v hv
  cases o with
  | some a =>
      simp only [optField, List.head?_cons, Option.mem_def, Option.some.injEq] at hv
      subst hv
      rw [htag a (hp.1 a rfl)]
      exact hne
  | none => exact h b hp.2 v hv

theorem headNot_optLast {c : Codec Value α} {t : Tag} (h : ∀ a, c.WF a → (c.enc a).tag ≠ t) :
    (optLast c).HeadNot t := by
  intro o ho v hv
  cases o with
  | none => simp [optLast] at hv
  | some a =>
      simp only [optLast, List.head?_cons, Option.mem_def, Option.some.injEq] at hv
      subst hv
      exact h a (ho a rfl)

theorem derCodec_rel_iff (c : Codec Value α) (s : List UInt8) (a : α) :
    (derCodec c).rel s a ↔ EncRel.comp derRel c.rel s a := by
  constructor
  · rintro ⟨⟨hwf, hvwf⟩, rfl⟩
    exact ⟨c.enc a, (derRel_iff _ _).mpr ⟨hvwf, rfl⟩, hwf, rfl⟩
  · rintro ⟨v, hv, hwf, rfl⟩
    obtain ⟨hvwf, rfl⟩ := (derRel_iff _ _).mp hv
    exact ⟨⟨hwf, hvwf⟩, rfl⟩

end Silmaril.Proofs.Formats.ASN1
