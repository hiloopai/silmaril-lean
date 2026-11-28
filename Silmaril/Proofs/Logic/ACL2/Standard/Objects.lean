module

public import Silmaril.Logic.ACL2.Standard.Objects.Defs
import Init.Data.Rat.Lemmas

@[expose] public section

namespace Silmaril.Proofs.Logic.ACL2.Standard.Objects

open Silmaril.Logic.ACL2.Standard

private theorem char_toNat (c : Character) : c.toChar.toNat = c.val := by
  have valid : c.val.isValidChar := Or.inl (by have := c.isLt; omega)
  rw [Character.toChar, Char.ofNat, dite_eq_left valid]
  rfl

private theorem toChar_ofChar? {c : Char} {b : Character} (h : Character.ofChar? c = some b) :
    b.toChar = c := by
  unfold Character.ofChar? at h
  split at h
  · cases h
    exact Char.ofNat_toNat c
  · contradiction

private theorem decodeChars {cs : List Char} {bs : ByteString}
    (h : cs.mapM Character.ofChar? = some bs) : bs.map Character.toChar = cs := by
  induction cs generalizing bs with
  | nil => simpa using h.symm
  | cons c cs ih =>
    cases hc : Character.ofChar? c with
    | none => simp [hc] at h
    | some b =>
      cases hs : cs.mapM Character.ofChar? with
      | none => simp [hc, hs] at h
      | some bs' =>
        have hbs : b :: bs' = bs := by simpa [hc, hs] using h
        rw [← hbs, List.map_cons, toChar_ofChar? hc, ih hs]

theorem byteString_roundtrip (s : ByteString) : ByteString.ofString? s.toLeanString = some s := by
  simp only [ByteString.ofString?, ByteString.toLeanString, String.toList_ofList]
  induction s with
  | nil => rfl
  | cons c cs ih =>
      simp [Character.ofChar?, char_toNat, c.isLt, ih]

theorem symbol_roundtrip (s : Symbol) : Symbol.ofName? s.toName = some s := by
  simp [Symbol.ofName?, Symbol.toName, byteString_roundtrip, s.package_ne_empty]

theorem byteString_ofString {s : String} {bs : ByteString} (h : ByteString.ofString? s = some bs) :
    bs.toLeanString = s := by
  rw [← String.toList_inj, ByteString.toLeanString, String.toList_ofList]
  exact decodeChars h

theorem symbol_toName {n : Silmaril.Logic.ACL2.Name} {s : Symbol}
    (h : Symbol.ofName? n = some s) : s.toName = n := by
  unfold Symbol.ofName? at h
  cases hp : ByteString.ofString? n.package with
  | none => simp [hp] at h
  | some pkg =>
    cases hs : ByteString.ofString? n.symbol with
    | none => simp [hp, hs] at h
    | some spelling =>
      by_cases hn : pkg = []
      · simp [hp, hs, hn] at h
      · have he : (⟨pkg, spelling, hn⟩ : Symbol) = s := by simpa [hp, hs, hn] using h
        rw [← he]
        cases n
        simp only [Symbol.toName]
        rw [byteString_ofString hp, byteString_ofString hs]

theorem cons_car_cdr (x : Object) :
    .cons x.car x.cdr = if x.consp then x else Object.cons Object.nil Object.nil := by
  cases x <;> rfl

theorem equal_eq_truth (x y : Object) : x.equal y = Object.truth ↔ x = y := by
  have htn : Object.truth ≠ Object.nil := by decide
  by_cases h : x = y <;> simp [Object.equal, Object.ofBool, h, Ne.symm htn]

theorem equal_eq_nil (x y : Object) : x.equal y = Object.nil ↔ x ≠ y := by
  have htn : Object.truth ≠ Object.nil := by decide
  by_cases h : x = y <;> simp [Object.equal, Object.ofBool, h, htn]

theorem append_atom {x : Object} (h : x.consp = false) (y : Object) : x.append y = y := by
  cases x <;> first | rfl | contradiction

theorem append_assoc (x y z : Object) : (x.append y).append z = x.append (y.append z) := by
  induction x <;> simp_all [Object.append]

theorem listFix_of_trueListp {x : Object} (h : x.trueListp = true) : x.listFix = x := by
  induction x <;> simp_all [Object.trueListp, Object.listFix, Object.append]

theorem trueListp_listFix (x : Object) : x.listFix.trueListp = true := by
  induction x <;> simp_all [Object.trueListp, Object.listFix, Object.append] <;> rfl

theorem symbolName_of_nonsymbol {x : Object} (h : x.symbolp = false) :
    x.symbolName = .string [] := by
  cases x <;> first | rfl | contradiction

theorem symbolPackageName_of_nonsymbol {x : Object} (h : x.symbolp = false) :
    x.symbolPackageName = .string [] := by
  cases x <;> first | rfl | contradiction

theorem charCode_of_noncharacter {x : Object} (h : x.characterp = false) :
    x.charCode = Object.integer 0 := by
  cases x <;> first | rfl | contradiction

theorem integerValue?_eq_some_iff (x : Object) (n : Int) :
    x.integerValue? = some n ↔ x = Object.integer n := by
  constructor
  · intro h
    cases x with
    | rational q =>
      simp only [Object.integerValue?] at h
      split at h
      · next hd => exact congrArg Object.rational (Rat.ext (Option.some.inj h) hd)
      · contradiction
    | _ => contradiction
  · rintro rfl
    rfl

theorem codeChar_charCode (c : Character) : (Object.character c).charCode.codeChar = .character c := by
  simp [Object.charCode, Object.codeChar, Object.integerValue?, Object.integer, c.isLt]

theorem codeChar_of_outside {n : Int} (h : n < 0 ∨ 256 ≤ n) :
    (Object.integer n).codeChar = .character 0 := by
  have invalid : ¬ (0 ≤ n ∧ n.toNat < 256) := by omega
  change Object.character (if h : 0 ≤ n ∧ n.toNat < 256 then ⟨n.toNat, h.2⟩ else 0) = _
  rw [dite_eq_right invalid]

theorem characterList_ofList (s : ByteString) :
    (Object.ofList (s.map Object.character)).characterList = s := by
  induction s with
  | nil => rfl
  | cons c cs ih => simpa [Object.ofList, Object.characterList] using congrArg (List.cons c) ih

theorem coerceList_roundtrip (s : ByteString) (target : Object)
    (h : target ≠ .symbol Symbol.list) :
    ((Object.string s).coerce (.symbol Symbol.list)).coerce target = .string s := by
  simp [Object.coerce, h, characterList_ofList]

theorem real_ofParts (r i : Rat) : (Object.ofParts r i).real = r := by
  unfold Object.ofParts
  split <;> rfl

theorem imag_ofParts (r i : Rat) : (Object.ofParts r i).imag = i := by
  by_cases h : i = 0 <;> simp [Object.ofParts, Object.imag, h]

theorem ofParts_real_imag (x : Object) : Object.ofParts x.real x.imag = x.fix := by
  cases x <;> simp [Object.real, Object.imag, Object.ofParts, Object.fix, Object.numberp,
    Object.rationalp, Object.complexRationalp, Object.integer, *] <;> rfl

private theorem parts_of_nonnumeric {x : Object} (h : x.numberp = false) :
    x.real = 0 ∧ x.imag = 0 := by
  cases x <;> first | exact ⟨rfl, rfl⟩ | contradiction

theorem binaryAdd_of_nonnumeric_left {x : Object} (h : x.numberp = false) (y : Object) :
    x.binaryAdd y = y.fix := by
  obtain ⟨hr, hi⟩ := parts_of_nonnumeric h
  simpa [Object.binaryAdd, hr, hi, Rat.zero_add] using ofParts_real_imag y

theorem binaryAdd_of_nonnumeric_right (x : Object) {y : Object} (h : y.numberp = false) :
    x.binaryAdd y = x.fix := by
  obtain ⟨hr, hi⟩ := parts_of_nonnumeric h
  simpa [Object.binaryAdd, hr, hi, Rat.add_zero] using ofParts_real_imag x

theorem binaryMul_of_nonnumeric_left {x : Object} (h : x.numberp = false) (y : Object) :
    x.binaryMul y = Object.integer 0 := by
  obtain ⟨hr, hi⟩ := parts_of_nonnumeric h
  simp [Object.binaryMul, hr, hi, Rat.zero_mul, Rat.sub_self,
    Rat.zero_add, Object.ofParts, Object.integer]
  rfl

theorem binaryMul_of_nonnumeric_right (x : Object) {y : Object} (h : y.numberp = false) :
    x.binaryMul y = Object.integer 0 := by
  obtain ⟨hr, hi⟩ := parts_of_nonnumeric h
  simp [Object.binaryMul, hr, hi, Rat.mul_zero, Rat.sub_self,
    Rat.zero_add, Object.ofParts, Object.integer]
  rfl

theorem unaryMinus_of_nonnumeric {x : Object} (h : x.numberp = false) :
    x.unaryMinus = Object.integer 0 := by
  obtain ⟨hr, hi⟩ := parts_of_nonnumeric h
  simp [Object.unaryMinus, hr, hi, Object.ofParts, Object.integer]
  rfl

theorem less_of_nonnumeric_left {x : Object} (h : x.numberp = false) (y : Object) :
    x.less y = (Object.integer 0).less y := by
  obtain ⟨hr, hi⟩ := parts_of_nonnumeric h
  have hreal : (Object.integer 0).real = 0 := rfl
  have himag : (Object.integer 0).imag = 0 := rfl
  simp only [Object.less, hr, hi, hreal, himag]

theorem less_of_nonnumeric_right (x : Object) {y : Object} (h : y.numberp = false) :
    x.less y = x.less (Object.integer 0) := by
  obtain ⟨hr, hi⟩ := parts_of_nonnumeric h
  have hreal : (Object.integer 0).real = 0 := rfl
  have himag : (Object.integer 0).imag = 0 := rfl
  simp only [Object.less, hr, hi, hreal, himag]

theorem zp_eq_nil_iff (x : Object) :
    x.zp = Object.nil ↔ ∃ n : Int, 0 < n ∧ x = Object.integer n := by
  have htn : Object.truth ≠ Object.nil := by decide
  cases h : x.integerValue? with
  | none =>
    simp only [Object.zp, h, htn, false_iff, not_exists]
    intro n hn
    have hc := (integerValue?_eq_some_iff x n).2 hn.2
    simp [h] at hc
  | some n =>
    rw [(integerValue?_eq_some_iff x n).1 h] at *
    have hinj (m : Int) : Rat.ofInt n = Rat.ofInt m ↔ n = m := Rat.intCast_inj
    simp [Object.zp, Object.integerValue?, Object.integer, Object.ofBool, htn, hinj]

theorem decrement_integer (n : Int) : (Object.integer n).decrement = Object.integer (n - 1) := by
  have hadd := Rat.intCast_add n (-1)
  change Rat.ofInt (n + -1) = Rat.ofInt n + Rat.ofInt (-1) at hadd
  simp [Object.decrement, Object.binaryAdd, Object.real, Object.imag, Object.integer,
    Rat.zero_add, Object.ofParts, Int.sub_eq_add_neg, hadd]

theorem natRank_decrement_lt {x : Object} (h : x.zp = Object.nil) :
    x.decrement.natRank < x.natRank := by
  obtain ⟨n, hn, rfl⟩ := (zp_eq_nil_iff x).1 h
  rw [decrement_integer]
  change (n - 1).toNat < n.toNat
  omega

theorem acl2Count_cdr_lt {x : Object} (h : x.consp = true) :
    x.cdr.acl2Count < x.acl2Count := by
  cases x <;> try contradiction
  simp only [Object.cdr, Object.acl2Count]
  omega

end Silmaril.Proofs.Logic.ACL2.Standard.Objects
