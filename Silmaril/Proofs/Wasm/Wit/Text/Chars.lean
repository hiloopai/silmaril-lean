module

public import Silmaril.Proofs.Wasm.Wit.Text.Basic
public import Silmaril.Wasm.Wit.Name.Thms

/-!
# WIT text: valid names are printable

* `idOk_of_validId`: a valid identifier (`ValidId`) is one the lexer reads back
  (`idOk`);
* `verOk_of_valid`: a valid SemVer version is one the printer spells (`verOk`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Text

theorem wordCont_of_plainChar {c : Char} (h : plainChar c = true) : wordCont c = true := by
  simp only [plainChar, wordCont, isLetter, isDigitC, Char.isUpper, Char.isLower, Char.isDigit,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h ⊢
  simp only [Char.le_def, ge_iff_le, UInt32.le_iff_toNat_le, Char.ext_iff, ← UInt32.toNat_inj] at h ⊢
  have : ('0' : Char).val.toNat = 48 := rfl
  have : ('9' : Char).val.toNat = 57 := rfl
  have : ('a' : Char).val.toNat = 97 := rfl
  have : ('z' : Char).val.toNat = 122 := rfl
  have : ('A' : Char).val.toNat = 65 := rfl
  have : ('Z' : Char).val.toNat = 90 := rfl
  have : ('-' : Char).val.toNat = 45 := rfl
  omega

theorem wordCont_of_semverChar {c : Char} (h : semverChar c = true) : wordCont c = true := by
  simp only [semverChar, wordCont, isLetter, isDigitC, Char.isAlphanum, Char.isAlpha, Char.isUpper,
    Char.isLower, Char.isDigit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h ⊢
  simp only [Char.le_def, ge_iff_le, UInt32.le_iff_toNat_le, Char.ext_iff, ← UInt32.toNat_inj] at h ⊢
  have : ('0' : Char).val.toNat = 48 := rfl
  have : ('9' : Char).val.toNat = 57 := rfl
  have : ('a' : Char).val.toNat = 97 := rfl
  have : ('z' : Char).val.toNat = 122 := rfl
  have : ('A' : Char).val.toNat = 65 := rfl
  have : ('Z' : Char).val.toNat = 90 := rfl
  have : ('-' : Char).val.toNat = 45 := rfl
  omega

theorem isLetter_of_head {c : Char} (h : c.isLower ∨ c.isUpper) : isLetter c = true := by
  simp only [isLetter, Char.isUpper, Char.isLower, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at h ⊢
  simp only [Char.le_def, ge_iff_le, UInt32.le_iff_toNat_le] at h ⊢
  exact h

/-- **A valid identifier is printable.** -/
theorem idOk_of_validId {s : Name} (h : ValidId s) : idOk s = true := by
  obtain ⟨c, cs, hs, hc⟩ := validId_head h
  have hp := plain_of_validId h
  unfold idOk
  rw [hs]
  simp only [Bool.and_eq_true, List.all_eq_true]
  exact ⟨isLetter_of_head hc, fun d hd => wordCont_of_plainChar (hp d (by rw [hs]; exact List.mem_cons_of_mem _ hd))⟩

/-- **A valid version is printable.** -/
theorem verOk_of_valid {v : Version} (h : v.Valid) : verOk v = true := by
  simp only [verOk, List.all_eq_true, List.mem_append, Bool.and_eq_true, Bool.not_eq_true',
    List.isEmpty_eq_false_iff]
  intro s hs
  have hb : ValidBuildId s := hs.elim (fun hp => (h.1 s hp).1) (fun hb => h.2 s hb)
  exact ⟨hb.1, fun c hc => wordCont_of_semverChar (hb.2 c hc)⟩

end Silmaril.Wasm.Wit.Text
