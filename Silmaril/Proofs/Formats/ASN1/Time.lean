module

public import Silmaril.Formats.ASN1.Time.Defs
import Silmaril.Formats.ASN1.Codec.Thms

/-! Proofs for `Silmaril.Formats.ASN1.Time.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.ASN1

open Silmaril Silmaril.Formats.ASN1 Silmaril.Formats.ASN1.Content

theorem readDigit_digit {k : Nat} (hk : k < 10) : readDigit (digit k) = some k := by
  have : (digit k).toNat = 48 + k := by simp [digit]; omega
  unfold readDigit
  rw [this]
  simp only [show 48 ≤ 48 + k by omega, show 48 + k ≤ 57 by omega, and_self, ↓reduceIte,
    Nat.add_sub_cancel_left]

theorem read2_digit {n : Nat} (h : n < 100) : read2 (digit (n / 10)) (digit (n % 10)) = some n := by
  simp only [read2, readDigit_digit (show n / 10 < 10 by omega), readDigit_digit (show n % 10 < 10 by omega),
    Option.some.injEq]
  omega

theorem read2_eq_some {a b : UInt8} {n : Nat} (h : read2 a b = some n) :
    n < 100 ∧ digit (n / 10) = a ∧ digit (n % 10) = b := by
  simp only [read2, readDigit] at h
  split at h
  · rename_i x y hx hy
    cases h
    split_ifs at hx with ha
    cases hx
    split_ifs at hy with hb
    cases hy
    refine ⟨by omega, ?_, ?_⟩
    · apply UInt8.toNat_inj.mp; simp [digit]; omega
    · apply UInt8.toNat_inj.mp; simp [digit]; omega
  · cases h

theorem readTail_timeTail (t : DateTime) (h : t.valid = true) : readTail t.year (timeTail t) = some t := by
  simp only [DateTime.valid, decide_eq_true_eq] at h
  simp only [timeTail, digits2, List.cons_append, List.nil_append, readTail,
    read2_digit (show t.month < 100 by omega), read2_digit (show t.day < 100 by
      have : DateTime.daysInMonth t.year t.month ≤ 31 := by
        unfold DateTime.daysInMonth; split_ifs <;> omega
      omega),
    read2_digit (show t.hour < 100 by omega), read2_digit (show t.minute < 100 by omega),
    read2_digit (show t.second < 100 by omega), ↓reduceIte]

theorem readTail_eq_some {y : Nat} {bs : List UInt8} {t : DateTime} (h : readTail y bs = some t) :
    t.year = y ∧ timeTail t = bs := by
  match bs, h with
  | [m₁, m₂, d₁, d₂, h₁, h₂, i₁, i₂, s₁, s₂, z], h =>
      simp only [readTail] at h
      split at h
      · rename_i mo dd hh mi ss hmo hdd hhh hmi hss
        split_ifs at h with hz
        cases h
        obtain ⟨-, e₁, e₂⟩ := read2_eq_some hmo
        obtain ⟨-, e₃, e₄⟩ := read2_eq_some hdd
        obtain ⟨-, e₅, e₆⟩ := read2_eq_some hhh
        obtain ⟨-, e₇, e₈⟩ := read2_eq_some hmi
        obtain ⟨-, e₉, e₁₀⟩ := read2_eq_some hss
        exact ⟨rfl, by simp [timeTail, digits2, e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉, e₁₀, hz]⟩
      · cases h

theorem lawful_utcTime : Content.utcTime.Lawful where
  dec_enc t h := by
    simp only [Content.utcTime, utcOK, Bool.and_eq_true, decide_eq_true_eq] at h
    have hy : (if t.year % 100 < 50 then 2000 + t.year % 100 else 1900 + t.year % 100) =
        t.year := by
      split_ifs <;> omega
    simp only [Content.utcTime, utcContent, digits2, List.cons_append, List.nil_append,
      utcOfContent?, read2_digit (show t.year % 100 < 100 by omega)]
    rw [hy, readTail_timeTail t h.1]
    simp [utcOK, h.1, h.2]
  enc_dec {bs t} h := by
    match bs, h with
    | y₁ :: y₂ :: tail, h =>
        simp only [Content.utcTime, utcOfContent?] at h
        split at h
        · rename_i yy hyy
          split at h
          · rename_i t' ht'
            split_ifs at h with hok
            cases h
            obtain ⟨hlt, e₁, e₂⟩ := read2_eq_some hyy
            obtain ⟨hyear, htail⟩ := readTail_eq_some ht'
            refine ⟨hok, ?_⟩
            have : t.year % 100 = yy := by rw [hyear]; split_ifs <;> omega
            show utcContent t = _
            rw [utcContent, this, htail, digits2, e₁, e₂]
            rfl
          · cases h
        · cases h

theorem lawful_generalizedTime : Content.generalizedTime.Lawful where
  dec_enc t h := by
    simp only [Content.generalizedTime, generalizedOK, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Content.generalizedTime, generalizedContent, digits2, List.cons_append,
      List.nil_append, generalizedOfContent?, read2_digit (show t.year / 100 < 100 by omega),
      read2_digit (show t.year % 100 < 100 by omega)]
    rw [show 100 * (t.year / 100) + t.year % 100 = t.year by omega, readTail_timeTail t h.1]
    simp [generalizedOK, h.1, h.2]
  enc_dec {bs t} h := by
    match bs, h with
    | c₁ :: c₂ :: y₁ :: y₂ :: tail, h =>
        simp only [Content.generalizedTime, generalizedOfContent?] at h
        split at h
        · rename_i cc yy hcc hyy
          split at h
          · rename_i t' ht'
            split_ifs at h with hok
            cases h
            obtain ⟨hlt₁, e₁, e₂⟩ := read2_eq_some hcc
            obtain ⟨hlt₂, e₃, e₄⟩ := read2_eq_some hyy
            obtain ⟨hyear, htail⟩ := readTail_eq_some ht'
            refine ⟨hok, ?_⟩
            have h₁ : t.year / 100 = cc := by omega
            have h₂ : t.year % 100 = yy := by omega
            show generalizedContent t = _
            rw [generalizedContent, h₁, h₂, htail, digits2, digits2, e₁, e₂, e₃, e₄]
            rfl
          · cases h
        · cases h

theorem lawful_time : time.Lawful :=
  Codec.lawful_iso
    (Codec.lawful_orElse (Codec.lawful_prim _ lawful_utcTime)
      (Codec.lawful_prim _ lawful_generalizedTime)
      (fun _ _ => rfl))
    (fun x _ => by cases x <;> rfl) (fun x _ => by cases x <;> rfl)

end Silmaril.Proofs.Formats.ASN1
