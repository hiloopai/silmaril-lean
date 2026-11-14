module

public import Silmaril.Formats.ASN1.Digits.Defs

/-! Proofs for `Silmaril.Formats.ASN1.Digits.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Formats.ASN1

open Silmaril.Formats.ASN1

/-- Induction from the right end of a list. -/
theorem list_snoc_induction {α : Type} {motive : List α → Prop} (nil : motive [])
    (snoc : ∀ l a, motive l → motive (l ++ [a])) (l : List α) : motive l := by
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact nil
  | cons a r ih => simpa using snoc _ a ih

/-! ## Generic digits -/

theorem ofDigitsBE_append_singleton (b : Nat) (l : List Nat) (d : Nat) :
    ofDigitsBE b (l ++ [d]) = ofDigitsBE b l * b + d := by
  simp [ofDigitsBE, List.foldl_append]

theorem digitsBE_zero (b : Nat) : digitsBE b 0 = [] := by
  rw [digitsBE]; simp

theorem digitsBE_of_pos {b n : Nat} (hb : 1 < b) (hn : n ≠ 0) :
    digitsBE b n = digitsBE b (n / b) ++ [n % b] := by
  rw [digitsBE]; simp [hn, show ¬ b ≤ 1 by omega]

theorem digitsBE_eq_nil_iff {b n : Nat} (hb : 1 < b) : digitsBE b n = [] ↔ n = 0 := by
  constructor
  · intro h
    refine Classical.byContradiction fun hn => ?_
    rw [digitsBE_of_pos hb hn] at h
    simp at h
  · rintro rfl
    exact digitsBE_zero b

theorem ofDigitsBE_digitsBE {b : Nat} (hb : 1 < b) (n : Nat) :
    ofDigitsBE b (digitsBE b n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
      by_cases hn : n = 0
      · subst hn; simp [digitsBE_zero, ofDigitsBE]
      · rw [digitsBE_of_pos hb hn, ofDigitsBE_append_singleton,
          ih _ (Nat.div_lt_self (by omega) hb)]
        exact Nat.div_add_mod' n b

theorem lt_of_mem_digitsBE {b n d : Nat} (hb : 1 < b) (h : d ∈ digitsBE b n) : d < b := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
      by_cases hn : n = 0
      · subst hn; simp [digitsBE_zero] at h
      · rw [digitsBE_of_pos hb hn] at h
        simp only [List.mem_append, List.mem_singleton] at h
        rcases h with h | rfl
        · exact ih _ (Nat.div_lt_self (by omega) hb) h
        · exact Nat.mod_lt _ (by omega)

theorem head?_digitsBE_ne_zero {b : Nat} (hb : 1 < b) (n : Nat) :
    (digitsBE b n).head? ≠ some 0 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
      by_cases hn : n = 0
      · subst hn; simp [digitsBE_zero]
      · rw [digitsBE_of_pos hb hn]
        by_cases hq : n / b = 0
        · rw [hq, digitsBE_zero]
          have : n < b := by rcases Nat.div_eq_zero_iff.mp hq with h | h <;> omega
          simp [Nat.mod_eq_of_lt this, hn]
        · have hne : digitsBE b (n / b) ≠ [] := fun h => hq ((digitsBE_eq_nil_iff hb).mp h)
          obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
          have := ih _ (Nat.div_lt_self (by omega) hb)
          rw [hx] at this ⊢
          simpa using this

/-- A digit list whose value is zero has only zero digits. -/
theorem eq_zero_of_foldl_eq_zero {b : Nat} (hb : 1 ≤ b) :
    ∀ (l : List Nat) (acc : Nat), l.foldl (fun a d => a * b + d) acc = 0 →
      acc = 0 ∧ ∀ d ∈ l, d = 0
  | [], acc, h => by simpa using h
  | d :: l, acc, h => by
      simp only [List.foldl_cons] at h
      have ⟨h₁, h₂⟩ := eq_zero_of_foldl_eq_zero hb l _ h
      have hacc : acc * b = 0 := by omega
      refine ⟨?_, ?_⟩
      · rcases Nat.mul_eq_zero.mp hacc with h | h
        · exact h
        · omega
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · omega
        · exact h₂ x hx

theorem digitsBE_ofDigitsBE {b : Nat} (hb : 1 < b) {l : List Nat}
    (hl : ∀ d ∈ l, d < b) (h0 : l.head? ≠ some 0) : digitsBE b (ofDigitsBE b l) = l := by
  induction l using list_snoc_induction with
  | nil => simp [digitsBE_zero, ofDigitsBE]
  | snoc l d ih =>
      rw [ofDigitsBE_append_singleton]
      have hd : d < b := hl d (by simp)
      by_cases hn : ofDigitsBE b l * b + d = 0
      · exfalso
        have hz := eq_zero_of_foldl_eq_zero (b := b) (by omega) (l ++ [d]) 0
          (by rw [← ofDigitsBE, ofDigitsBE_append_singleton]; exact hn)
        cases l with
        | nil => simp_all
        | cons x l => exact h0 (by simp [hz.2 x (by simp)])
      · rw [digitsBE_of_pos hb hn]
        have hdiv : (ofDigitsBE b l * b + d) / b = ofDigitsBE b l := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hd]; simp
        have hmod : (ofDigitsBE b l * b + d) % b = d := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hd]
        rw [hdiv, hmod]
        congr 1
        apply ih
        · intro x hx; exact hl x (by simp [hx])
        · cases l with
          | nil => simp
          | cons x l => simpa using h0

/-! ## Base 256 -/

theorem toNat_toUInt8 (n : Nat) : (n.toUInt8).toNat = n % 256 := by simp

theorem toUInt8_toNat (a : UInt8) : a.toNat.toUInt8 = a := by simp

theorem toNat_lt_256 (a : UInt8) : a.toNat < 256 := UInt8.toNat_lt_size a

theorem beNat_eq (l : List UInt8) : beNat l = ofDigitsBE 256 (l.map UInt8.toNat) := by
  simp [beNat, ofDigitsBE, List.foldl_map]

theorem map_toNat_beBytes (n : Nat) : (beBytes n).map UInt8.toNat = digitsBE 256 n := by
  simp only [beBytes, List.map_map]
  conv => rhs; rw [← List.map_id (digitsBE 256 n)]
  apply List.map_congr_left
  intro d hd
  have := lt_of_mem_digitsBE (by omega) hd
  simp [Nat.mod_eq_of_lt this]

theorem beNat_beBytes (n : Nat) : beNat (beBytes n) = n := by
  rw [beNat_eq, map_toNat_beBytes, ofDigitsBE_digitsBE (by omega)]

theorem head?_beBytes_ne_zero (n : Nat) : (beBytes n).head? ≠ some 0 := by
  intro h
  have := head?_digitsBE_ne_zero (b := 256) (by omega) n
  rw [← map_toNat_beBytes, List.head?_map, h] at this
  exact this rfl

theorem beBytes_eq_nil_iff (n : Nat) : beBytes n = [] ↔ n = 0 := by
  simp [beBytes, digitsBE_eq_nil_iff (b := 256) (by omega)]

theorem map_toNat_injective {l l' : List UInt8} (h : l.map UInt8.toNat = l'.map UInt8.toNat) :
    l = l' := by
  induction l generalizing l' with
  | nil => cases l' <;> simp_all
  | cons a l ih =>
      cases l' with
      | nil => simp at h
      | cons a' l' =>
          simp only [List.map_cons, List.cons.injEq] at h
          rw [UInt8.toNat_inj.mp h.1, ih h.2]

theorem beBytes_beNat {l : List UInt8} (h0 : l.head? ≠ some 0) : beBytes (beNat l) = l := by
  apply map_toNat_injective
  rw [map_toNat_beBytes, beNat_eq]
  apply digitsBE_ofDigitsBE (by omega)
  · intro d hd
    simp only [List.mem_map] at hd
    obtain ⟨x, -, rfl⟩ := hd
    exact UInt8.toNat_lt_size x
  · rw [List.head?_map]
    cases hl : l.head? with
    | none => simp
    | some x =>
        simp only [Option.map_some, ne_eq, Option.some.injEq]
        intro hx
        exact h0 (by rw [hl]; congr; exact UInt8.toNat_inj.mp (by simpa using hx))

/-! ## Base 128 -/

theorem base128_ne_nil (n : Nat) : base128 n ≠ [] := by simp [base128]

theorem toNat_toUInt8_add_128 {x : Nat} (hx : x < 128) :
    ((x + 128).toUInt8).toNat = x + 128 := by
  simp only [toNat_toUInt8]; omega

theorem base128Octets_iff (n : Nat) (ds : List UInt8) :
    Base128Octets n ds ↔ ds = base128 n := by
  constructor
  · rintro ⟨hi, lo, rfl, hhi, hlo, hhead, rfl⟩
    have hlt : ∀ d ∈ hi.map (fun d => d.toNat - 128), d < 128 := by
      intro d hd
      simp only [List.mem_map] at hd
      obtain ⟨x, -, rfl⟩ := hd
      have := UInt8.toNat_lt_size x
      have : UInt8.size = 256 := rfl
      omega
    have h0 : (hi.map (fun d => d.toNat - 128)).head? ≠ some 0 := by
      cases hh : hi with
      | nil => simp
      | cons x xs =>
          simp only [List.map_cons, List.head?_cons, ne_eq, Option.some.injEq]
          intro hx
          have hx128 := hhi x (by simp [hh])
          apply hhead
          rw [hh]
          simp only [List.head?_cons, Option.some.injEq]
          exact UInt8.toNat_inj.mp (by simp; omega)
    rw [ofDigitsBE_append_singleton]
    unfold base128
    have hdiv : (ofDigitsBE 128 (hi.map (fun d => d.toNat - 128)) * 128 + lo.toNat) / 128 =
        ofDigitsBE 128 (hi.map (fun d => d.toNat - 128)) := by omega
    have hmod : (ofDigitsBE 128 (hi.map (fun d => d.toNat - 128)) * 128 + lo.toNat) % 128 =
        lo.toNat := by omega
    rw [hdiv, hmod, digitsBE_ofDigitsBE (by omega) hlt h0]
    simp only [List.map_map, toUInt8_toNat]
    congr 1
    conv => lhs; rw [← List.map_id hi]
    apply List.map_congr_left
    intro x hx
    have := hhi x hx
    have := UInt8.toNat_lt_size x
    have : UInt8.size = 256 := rfl
    apply UInt8.toNat_inj.mp
    simp only [id, Function.comp, toNat_toUInt8]
    omega
  · rintro rfl
    refine ⟨(digitsBE 128 (n / 128)).map (fun d => (d + 128).toUInt8), (n % 128).toUInt8, rfl,
      ?_, ?_, ?_, ?_⟩
    · intro d hd
      simp only [List.mem_map] at hd
      obtain ⟨x, hx, rfl⟩ := hd
      rw [toNat_toUInt8_add_128 (lt_of_mem_digitsBE (by omega) hx)]; omega
    · simp only [toNat_toUInt8]; omega
    · have h0 := head?_digitsBE_ne_zero (b := 128) (by omega) (n / 128)
      cases hd : digitsBE 128 (n / 128) with
      | nil => simp
      | cons x xs =>
          have hx : x < 128 := lt_of_mem_digitsBE (by omega) (by rw [hd]; simp)
          rw [hd] at h0
          simp only [List.head?_cons, ne_eq, Option.some.injEq] at h0
          simp only [List.map_cons, List.head?_cons, ne_eq, Option.some.injEq]
          intro h
          have := congrArg UInt8.toNat h
          rw [toNat_toUInt8_add_128 hx] at this
          simp at this; omega
    · rw [ofDigitsBE_append_singleton]
      have : (List.map (fun d => d.toNat - 128)
          (List.map (fun d => (d + 128).toUInt8) (digitsBE 128 (n / 128)))) =
          digitsBE 128 (n / 128) := by
        rw [List.map_map]
        conv => rhs; rw [← List.map_id (digitsBE 128 (n / 128))]
        apply List.map_congr_left
        intro x hx
        simp only [Function.comp, id]
        rw [toNat_toUInt8_add_128 (lt_of_mem_digitsBE (by omega) hx)]; omega
      rw [this, ofDigitsBE_digitsBE (by omega)]
      simp only [toNat_toUInt8]
      omega

theorem readBase128Aux_eq_some {acc n : Nat} {s r : List UInt8} :
    readBase128Aux acc s = some (n, r) ↔
      ∃ hi lo, s = hi ++ lo :: r ∧ (∀ d ∈ hi, 128 ≤ d.toNat) ∧ lo.toNat < 128 ∧
        n = (hi.map (fun d => d.toNat - 128)).foldl (fun a d => a * 128 + d) acc * 128 +
          lo.toNat := by
  induction s generalizing acc with
  | nil =>
      simp only [readBase128Aux, reduceCtorEq, false_iff, not_exists, not_and]
      intro hi lo h
      cases hi <;> simp at h
  | cons b s ih =>
      simp only [readBase128Aux]
      by_cases hb : b.toNat < 128
      · simp only [hb, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
        constructor
        · rintro ⟨rfl, rfl⟩
          exact ⟨[], b, rfl, by simp, hb, by simp⟩
        · rintro ⟨hi, lo, hs, hhi, hlo, rfl⟩
          cases hi with
          | nil =>
              simp only [List.nil_append, List.cons.injEq] at hs
              obtain ⟨rfl, rfl⟩ := hs
              simp
          | cons x xs =>
              simp only [List.cons_append, List.cons.injEq] at hs
              obtain ⟨rfl, -⟩ := hs
              exact absurd (hhi b (by simp)) (by omega)
      · simp only [hb, ↓reduceIte]
        rw [ih]
        constructor
        · rintro ⟨hi, lo, rfl, hhi, hlo, rfl⟩
          refine ⟨b :: hi, lo, rfl, ?_, hlo, by simp⟩
          intro d hd
          simp only [List.mem_cons] at hd
          rcases hd with rfl | hd
          · omega
          · exact hhi d hd
        · rintro ⟨hi, lo, hs, hhi, hlo, rfl⟩
          cases hi with
          | nil =>
              simp only [List.nil_append, List.cons.injEq] at hs
              obtain ⟨rfl, -⟩ := hs
              omega
          | cons x xs =>
              simp only [List.cons_append, List.cons.injEq] at hs
              obtain ⟨rfl, rfl⟩ := hs
              exact ⟨xs, lo, rfl, fun d hd => hhi d (by simp [hd]), hlo, by simp⟩

theorem readBase128_eq_some {n : Nat} {s r : List UInt8} :
    readBase128 s = some (n, r) ↔ s = base128 n ++ r := by
  constructor
  · intro h
    cases s with
    | nil => simp [readBase128] at h
    | cons b s =>
        simp only [readBase128] at h
        by_cases hb : b = 0x80
        · simp [hb] at h
        simp only [hb, ↓reduceIte] at h
        obtain ⟨hi, lo, hs, hhi, hlo, rfl⟩ := readBase128Aux_eq_some.mp h
        have hoct : Base128Octets
            ((hi.map (fun d => d.toNat - 128)).foldl (fun a d => a * 128 + d) 0 * 128 + lo.toNat)
            (hi ++ [lo]) := by
          refine ⟨hi, lo, rfl, hhi, hlo, ?_, ?_⟩
          · cases hi with
            | nil => simp
            | cons x xs =>
                simp only [List.cons_append, List.cons.injEq] at hs
                simp [← hs.1, hb]
          · rw [ofDigitsBE_append_singleton]; rfl
        have := (base128Octets_iff _ _).mp hoct
        rw [hs, ← this]
        simp
  · intro h
    obtain ⟨hi, lo, hds, hhi, hlo, hhead, hn⟩ := (base128Octets_iff n _).mpr rfl
    rw [hds] at h
    have hs : s = hi ++ lo :: r := by simp [h]
    have haux : readBase128Aux 0 s = some (n, r) := by
      rw [readBase128Aux_eq_some]
      refine ⟨hi, lo, hs, hhi, hlo, ?_⟩
      rw [hn, ofDigitsBE_append_singleton]; rfl
    cases hsx : s with
    | nil => simp [hs] at hsx
    | cons b s' =>
        rw [hsx] at haux
        simp only [readBase128]
        have hb : b ≠ 0x80 := by
          cases hi with
          | nil =>
              simp only [List.nil_append, hsx, List.cons.injEq] at hs
              rw [hs.1]; intro h; rw [h] at hlo; simp at hlo
          | cons x xs =>
              simp only [List.cons_append, hsx, List.cons.injEq] at hs
              rw [hs.1]; simpa using hhead
        simp [hb, haux]

end Silmaril.Proofs.Formats.ASN1
