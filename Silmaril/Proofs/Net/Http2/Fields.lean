module

public import Silmaril.Net.Http2.Fields.Defs

/-!
# HTTP/2 field sections: proofs

For `Silmaril.Net.Http2.Fields.Thms` (RFC 9113 §8.2).
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Http2

open Silmaril.Net.Hpack Silmaril.Net.Http2

theorem breakColon_append {n : List UInt8} (h : colon ∉ n) (rest : List UInt8) :
    breakColon (n ++ colon :: rest) = (n, rest) := by
  induction n with
  | nil => simp [breakColon]
  | cons b bs ih =>
    have hb : b ≠ colon := fun hb => h (hb ▸ List.mem_cons_self)
    have hbs : colon ∉ bs := fun hm => h (List.mem_cons_of_mem _ hm)
    simp only [List.cons_append, breakColon, beq_iff_eq, hb, ↓reduceIte, ih hbs]

theorem colon_not_mem_name {e : Entry} (h : validRegular e = true) : colon ∉ e.name := by
  simp only [validRegular, validName, isPseudo, Bool.and_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, ht⟩, -⟩, hp⟩, -⟩, -⟩ := h
  intro hm
  cases hn : e.name with
  | nil => simp [hn] at hm
  | cons c cs =>
    rw [hn] at hm ht hp
    simp only [List.head?_cons, Option.some.injEq] at hp
    simp only [List.tail_cons, List.contains_eq_any_beq, List.any_eq_false, beq_iff_eq] at ht
    rcases List.mem_cons.mp hm with h1 | h1
    · exact hp h1.symm
    · exact ht _ h1 rfl

theorem breakColon_h1Line {e : Entry} (h : validRegular e = true) :
    breakColon (h1Line e) = (e.name, 0x20 :: e.value) := by
  have := breakColon_append (colon_not_mem_name h) (0x20 :: e.value)
  simpa [h1Line] using this

theorem crlf_not_mem_h1Line {e : Entry} (h : validRegular e = true) :
    (0x0d : UInt8) ∉ h1Line e ∧ (0x0a : UInt8) ∉ h1Line e ∧ (0x00 : UInt8) ∉ h1Line e := by
  simp only [validRegular, validName, validValue, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨-, hn⟩, -⟩, ⟨⟨hv, -⟩, -⟩⟩, -⟩, -⟩, -⟩ := h
  have hname : ∀ b ∈ e.name, b ≠ 0x0d ∧ b ≠ 0x0a ∧ b ≠ 0x00 := by
    intro b hb
    have := hn b hb
    simp only [isNameOctet, Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not,
      Bool.and_eq_false_iff] at this
    refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> exact this.1.1 (by decide)
  have hval : ∀ b ∈ e.value, b ≠ 0x0d ∧ b ≠ 0x0a ∧ b ≠ 0x00 := by
    intro b hb
    have := hv b hb
    simp only [bne_iff_ne, ne_eq] at this
    exact ⟨this.2, this.1.2, this.1.1⟩
  simp only [h1Line, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨⟨⟨fun hm => (hname _ hm).1 rfl, by decide, by decide⟩, fun hm => (hval _ hm).1 rfl⟩,
    ⟨⟨fun hm => (hname _ hm).2.1 rfl, by decide, by decide⟩, fun hm => (hval _ hm).2.1 rfl⟩,
    ⟨⟨fun hm => (hname _ hm).2.2 rfl, by decide, by decide⟩, fun hm => (hval _ hm).2.2 rfl⟩⟩

theorem validRequest_regular {fs : List Entry} (h : validRequest fs = true) {e : Entry}
    (he : e ∈ fs) (hp : isPseudo e = false) : validRegular e = true := by
  simp only [validRequest, validSection, Bool.and_eq_true, List.all_eq_true] at h
  have := h.1.2 e he
  simpa [hp] using this

theorem validResponse_regular {fs : List Entry} (h : validResponse fs = true) {e : Entry}
    (he : e ∈ fs) (hp : isPseudo e = false) : validRegular e = true := by
  simp only [validResponse, validSection, Bool.and_eq_true, List.all_eq_true] at h
  have := h.1.2 e he
  simpa [hp] using this

theorem validRegular_not_connectionSpecific {e : Entry} (h : validRegular e = true) :
    e.name ∉ connectionSpecific := by
  simp only [validRegular, Bool.and_eq_true, Bool.not_eq_true'] at h
  intro hm
  have := List.contains_iff_mem.mpr hm
  rw [h.1.2] at this
  cases this

end Silmaril.Proofs.Net.Http2
