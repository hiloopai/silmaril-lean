module

public import Silmaril.Net.Http.Abnf.Defs

@[expose] public section

/-!
# ABNF core rules over octets: theorems

PROVED (standard axioms):

* `Derives` inversion for terminals, `anyOf`, character classes (`derives_cls_iff`) and
  repetition (`derives_repetition_iff`: a repetition derives exactly the concatenations of
  derivations of its body);
* `Single body e p`: the expression `e` derives exactly the one-octet strings `[b]` with
  `p b`. Closed under alternation (`Single.alternative`); repetitions of a single-octet rule
  derive exactly the strings all of whose octets satisfy `p` (`Single.repetition_iff`,
  `Single.oneOrMore_iff`);
* the core rules are single-octet rules of their checks: `single_alpha`, `single_digit`,
  `single_hexdig`, `single_vchar`, `single_obsText`, `single_range`.
-/

namespace Silmaril.Net.Http.Abnf

open Silmaril.Formats.Grammar.Ebnf

variable {N : Type} {body : N → Expr UInt8 N}

theorem derives_terminal_iff {T M : Type} {bd : M → Expr T M} (t : T) (xs : List T) :
    Derives bd (.terminal t) xs ↔ xs = [t] := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .terminal t

theorem derives_anyOf_iff (l : List UInt8) (xs : List UInt8) :
    Derives body (anyOf l) xs ↔ ∃ b ∈ l, xs = [b] := by
  induction l with
  | nil => simp only [anyOf, Derives.empty_iff, List.not_mem_nil, false_and, exists_false]
  | cons b bs ih =>
    simp only [anyOf, Derives.alternative_iff, derives_terminal_iff, ih, List.mem_cons,
      exists_eq_or_imp]

theorem mem_allOctets (b : UInt8) : b ∈ allOctets := by
  simp only [allOctets, List.mem_map, List.mem_range]
  exact ⟨b.toNat, b.toNat_lt, UInt8.ofNat_toNat⟩

theorem derives_cls_iff (p : UInt8 → Bool) (xs : List UInt8) :
    Derives body (cls p) xs ↔ ∃ b, p b = true ∧ xs = [b] := by
  simp only [cls, derives_anyOf_iff, List.mem_filter, mem_allOctets, true_and]

/-- A repetition derivation splits into derivations of its body. -/
theorem repetition_parts {T M : Type} {bd : M → Expr T M} {e r : Expr T M} {xs : List T}
    (h : Derives bd r xs) (hr : r = .repetition e) :
    ∃ parts : List (List T), (∀ p ∈ parts, Derives bd e p) ∧ parts.flatten = xs := by
  induction h with
  | nil => exact ⟨[], by simp, rfl⟩
  | @cons e' x y ha _ _ ihb =>
    cases hr
    obtain ⟨parts, hp, hflat⟩ := ihb rfl
    refine ⟨x :: parts, fun p hmem => ?_, by simp [hflat]⟩
    rcases List.mem_cons.mp hmem with rfl | hmem
    exacts [ha, hp p hmem]
  | _ => cases hr

/-- Derivations of the body concatenate to a repetition derivation. -/
theorem repetition_of_parts {T M : Type} {bd : M → Expr T M} {e : Expr T M}
    (parts : List (List T)) (hp : ∀ p ∈ parts, Derives bd e p) :
    Derives bd (.repetition e) parts.flatten := by
  induction parts with
  | nil => exact .nil
  | cons p ps ih =>
    have hhead : Derives bd e p := hp p (List.mem_cons_self ..)
    have htail : Derives bd (.repetition e) ps.flatten :=
      ih (fun q hq => hp q (List.mem_cons_of_mem _ hq))
    simpa only [List.flatten_cons] using Derives.cons hhead htail

/-- A repetition derives exactly the concatenations of derivations of its body
(RFC 5234 §3.6: `*rule`). -/
theorem derives_repetition_iff {T M : Type} {bd : M → Expr T M} (e : Expr T M) (xs : List T) :
    Derives bd (.repetition e) xs ↔
      ∃ parts : List (List T), (∀ p ∈ parts, Derives bd e p) ∧ parts.flatten = xs := by
  constructor
  · intro h; exact repetition_parts h rfl
  · rintro ⟨parts, hp, rfl⟩; exact repetition_of_parts parts hp

/-- `e` derives exactly the one-octet strings `[b]` with `p b`. -/
def Single (body : N → Expr UInt8 N) (e : Expr UInt8 N) (p : UInt8 → Bool) : Prop :=
  ∀ xs, Derives body e xs ↔ ∃ b, p b = true ∧ xs = [b]

theorem single_cls (p : UInt8 → Bool) : Single body (cls p) p := derives_cls_iff p

theorem single_terminal (t : UInt8) : Single body (.terminal t) (· == t) := by
  intro xs
  simp only [derives_terminal_iff, beq_iff_eq]
  exact ⟨fun h => ⟨t, rfl, h⟩, fun ⟨_, hb, h⟩ => hb ▸ h⟩

theorem Single.alternative {a b : Expr UInt8 N} {p q : UInt8 → Bool}
    (ha : Single body a p) (hb : Single body b q) :
    Single body (.alternative a b) (fun x => p x || q x) := by
  intro xs
  simp only [Derives.alternative_iff, ha xs, hb xs, Bool.or_eq_true]
  constructor
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨x, Or.inl hx, rfl⟩
    · exact ⟨x, Or.inr hx, rfl⟩
  · rintro ⟨x, hx | hx, rfl⟩
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩

theorem Single.congr {e : Expr UInt8 N} {p q : UInt8 → Bool} (h : Single body e p)
    (hpq : ∀ x, p x = q x) : Single body e q := by
  intro xs; simp only [h xs, hpq]

/-- `*rule` of a single-octet rule: the strings all of whose octets satisfy the rule. -/
theorem Single.repetition_iff {e : Expr UInt8 N} {p : UInt8 → Bool} (h : Single body e p)
    (xs : List UInt8) : Derives body (.repetition e) xs ↔ xs.all p = true := by
  rw [derives_repetition_iff]
  constructor
  · rintro ⟨parts, hp, rfl⟩
    simp only [List.all_eq_true, List.mem_flatten]
    rintro x ⟨q, hq, hx⟩
    obtain ⟨b, hb, rfl⟩ := (h q).mp (hp q hq)
    simpa [List.mem_singleton.mp hx] using hb
  · intro hall
    have hflat : ∀ ys : List UInt8, (ys.map (fun x => [x])).flatten = ys := by
      intro ys
      clear hall
      induction ys with
      | nil => rfl
      | cons a as ih => rw [List.map_cons, List.flatten_cons, ih]; rfl
    refine ⟨xs.map (fun x => [x]), ?_, hflat xs⟩
    simp only [List.mem_map]
    rintro q ⟨x, hx, rfl⟩
    exact (h [x]).mpr ⟨x, (List.all_eq_true.mp hall) x hx, rfl⟩

/-- `1*rule` of a single-octet rule: the non-empty strings all of whose octets satisfy it. -/
theorem Single.oneOrMore_iff {e : Expr UInt8 N} {p : UInt8 → Bool} (h : Single body e p)
    (xs : List UInt8) : Derives body (Expr.oneOrMore e) xs ↔ xs ≠ [] ∧ xs.all p = true := by
  show Derives body (.sequence e (.repetition e)) xs ↔ _
  simp only [Derives.sequence_iff, h.repetition_iff]
  constructor
  · rintro ⟨l, r, rfl, hl, hr⟩
    obtain ⟨b, hb, rfl⟩ := (h l).mp hl
    simp [hb, hr]
  · rintro ⟨hne, hall⟩
    obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hne
    simp only [List.all_cons, Bool.and_eq_true] at hall
    exact ⟨[b], bs, rfl, (h [b]).mpr ⟨b, hall.1, rfl⟩, hall.2⟩

theorem single_range (lo hi : UInt8) : Single body (range lo hi) (inRange lo hi) :=
  single_cls _

theorem single_alpha : Single body alpha isAlpha :=
  (single_range _ _).alternative (single_range _ _)

theorem single_digit : Single body digit isDigit := single_range _ _

theorem single_hexdig : Single body hexdig isHexDig := by
  have h := (single_digit (body := body)).alternative
    ((single_range 0x41 0x46).alternative (single_range 0x61 0x66))
  exact h.congr (fun x => by simp only [isHexDig, Bool.or_assoc])

theorem single_vchar : Single body vchar isVchar := single_range _ _

theorem single_obsText : Single body obsText isObsText := single_range _ _

theorem single_wsp : Single body (.alternative sp htab) isWsp :=
  ((single_terminal 0x20).alternative (single_terminal 0x09)).congr (fun _ => rfl)

theorem ows_iff (xs : List UInt8) : Derives body ows xs ↔ xs.all isWsp = true :=
  single_wsp.repetition_iff xs

/-! ## Case -/

theorem lower_append (xs ys : List UInt8) : lower (xs ++ ys) = lower xs ++ lower ys :=
  List.map_append

theorem lower_lower (xs : List UInt8) : lower (lower xs) = lower xs := by
  simp only [lower, List.map_map]
  congr 1
  funext b
  simp only [Function.comp, lowerOctet, inRange]
  by_cases h : (65 ≤ b ∧ b ≤ 90)
  · have h2 : ¬ (65 ≤ b + 32 ∧ b + 32 ≤ 90) := by
      intro h'
      simp only [UInt8.le_iff_toNat_le, UInt8.toNat_add] at h h'
      have h65 : (65 : UInt8).toNat = 65 := rfl
      have h90 : (90 : UInt8).toNat = 90 := rfl
      have h32 : (32 : UInt8).toNat = 32 := rfl
      omega
    simp [h, h2]
  · simp [h]

theorem eqIgnoreCase_refl (xs : List UInt8) : eqIgnoreCase xs xs = true := by
  simp [eqIgnoreCase]

theorem eqIgnoreCase_comm (xs ys : List UInt8) : eqIgnoreCase xs ys = eqIgnoreCase ys xs := by
  rw [Bool.eq_iff_iff]
  simp only [eqIgnoreCase, beq_iff_eq]
  exact eq_comm

end Silmaril.Net.Http.Abnf
