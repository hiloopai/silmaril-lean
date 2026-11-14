module

public import Silmaril.Wasi.Versions.HttpRfc.Defs

@[expose] public section

/-!
# The WASI `fields` checks against the RFC 9110 field grammar

PROVED (standard axioms):

* **`tcharB_iff`, `tokenB_iff`, `fieldValueB_iff`**: the decision procedures equal the ABNF
  grammars of RFC 9110 §5.6.2 (`tchar`, `token`) and §5.5 (`field-value`).
* **`nameOk_iff`**: the WASI name check `Net.nameOk` (of `HttpHdr`, used by the theory
  `hdrTh` and the host `hdrImpl`) holds exactly on RFC 9110 `field-name`s (§5.1). In
  particular `Net.tchar` is RFC 9110 `tchar` (`tchar_iff`): `Char.isAlphanum` is ASCII.
* **`valueOk_iff`**: the WASI value check `Net.valueOk` is exactly the RFC 9110 §5.5
  "invalid and dangerous" rule (no CR, LF or NUL), **not** the `field-value` grammar:
  * `fieldValue_valueOk`: every `field-value` passes it;
  * **refuted** (`valueOk_not_fieldValue`): the converse fails, e.g. on a leading space
    `" a"`, a lone space, the control octet `0x01` and `DEL` (`0x7F`), which WASI accepts
    and the grammar rejects. This matches the WIT's own wording ("syntactically invalid") only
    up to that rule; implementations differ beyond it (see `HttpHdr`).
* **`low_eq_iff`**: `Net.low` (the case-insensitive comparison of `fields`) identifies two
  names exactly when they are equal after ASCII folding (`FoldEq`, RFC 9110 §5.1), for every
  string, not only tokens.
* **`combine_fieldValue`**: the RFC 9110 §5.3 combination of nonempty `field-value`s is a
  `field-value`; `combinedOf_fieldValue`: so is the combined value of a name in WASI `fields`
  whose values are nonempty `field-value`s.
-/

namespace Silmaril.Wasi.Versions.HttpRfc

open Silmaril.Wasi.Versions.Net (tchar nameOk valueOk low valsOfName Fields)

/-! ## Tokens -/

theorem tcharB_iff (n : Nat) : tcharB n = true ↔ Tchar n := by
  simp only [tcharB, Tchar, IsDigit, IsAlpha, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, List.contains_iff_mem]
  tauto

theorem tokenB_iff (w : List Char) : tokenB w = true ↔ Token w := by
  induction w with
  | nil => exact ⟨fun h => by simp [tokenB] at h, fun h => nomatch h⟩
  | cons c w ih =>
    constructor
    · intro h
      have hc : Tchar c.toNat := (tcharB_iff _).1 (by simp_all [tokenB])
      cases w with
      | nil => exact .one hc
      | cons d w' => exact .cons hc (ih.1 (by simp_all [tokenB]))
    · intro h
      cases h with
      | one hc => simpa [tokenB] using (tcharB_iff _).2 hc
      | cons hc hw =>
        have hw' : tokenB w = true := ih.2 hw
        simp only [tokenB, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
          List.all_eq_true] at hw' ⊢
        exact ⟨by simp, by simpa using ⟨(tcharB_iff _).2 hc, hw'.2⟩⟩

/-- The code point of an ASCII character literal. -/
theorem char_mem_iff (c : Char) (l : List Char) : c ∈ l ↔ c.toNat ∈ l.map Char.toNat := by
  constructor
  · exact fun h => List.mem_map_of_mem h
  · intro h
    obtain ⟨d, hd, he⟩ := List.mem_map.1 h
    have hdc : d = c := Char.toNat_inj.1 he
    exact hdc ▸ hd

/-- A `Char` comparison with a literal is a comparison of code points. -/
theorem val_le_iff (c : Char) (n : UInt32) : c.val ≤ n ↔ c.toNat ≤ n.toNat :=
  UInt32.le_iff_toNat_le

theorem le_val_iff (c : Char) (n : UInt32) : n ≤ c.val ↔ n.toNat ≤ c.toNat :=
  UInt32.le_iff_toNat_le

theorem isUpper_eq (c : Char) : c.isUpper = (65 ≤ c.toNat && c.toNat ≤ 90) := by
  have hA : 'A'.val = 65 := rfl
  have hZ : 'Z'.val = 90 := rfl
  unfold Char.isUpper
  rw [hA, hZ, Bool.eq_iff_iff]
  simp only [ge_iff_le, decide_eq_true_eq, Bool.and_eq_true, le_val_iff, val_le_iff]
  rfl

theorem isLower_eq (c : Char) : c.isLower = (97 ≤ c.toNat && c.toNat ≤ 122) := by
  have ha : 'a'.val = 97 := rfl
  have hz : 'z'.val = 122 := rfl
  unfold Char.isLower
  rw [ha, hz, Bool.eq_iff_iff]
  simp only [ge_iff_le, decide_eq_true_eq, Bool.and_eq_true, le_val_iff, val_le_iff]
  rfl

theorem isDigit_eq (c : Char) : c.isDigit = (48 ≤ c.toNat && c.toNat ≤ 57) := by
  have h0 : '0'.val = 48 := rfl
  have h9 : '9'.val = 57 := rfl
  unfold Char.isDigit
  rw [h0, h9, Bool.eq_iff_iff]
  simp only [ge_iff_le, decide_eq_true_eq, Bool.and_eq_true, le_val_iff, val_le_iff]
  rfl

theorem tchar_eq (c : Char) : tchar c = tcharB c.toNat := by
  have hp : ("!#$%&'*+-.^_`|~".toList.map Char.toNat) = tcharPunct := by decide
  have hm : ("!#$%&'*+-.^_`|~".toList.contains c) = tcharPunct.contains c.toNat := by
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, char_mem_iff, hp]
  simp only [tchar, tcharB, hm, Char.isAlphanum, Char.isAlpha, isUpper_eq, isLower_eq,
    isDigit_eq]
  generalize tcharPunct.contains c.toNat = p
  generalize (65 ≤ c.toNat && c.toNat ≤ 90) = u
  generalize (97 ≤ c.toNat && c.toNat ≤ 122) = l
  generalize (48 ≤ c.toNat && c.toNat ≤ 57) = d
  cases p <;> cases u <;> cases l <;> cases d <;> rfl

/-- **The WASI `tchar` is RFC 9110 `tchar`.** -/
theorem tchar_iff (c : Char) : tchar c = true ↔ Tchar c.toNat := by
  rw [tchar_eq, tcharB_iff]

/-- **The WASI field-name check is RFC 9110 `field-name`** (§5.1, §5.6.2). -/
theorem nameOk_iff (n : List Char) : nameOk n = true ↔ FieldName n := by
  rw [FieldName, ← tokenB_iff]
  have h : tchar = fun c => tcharB c.toNat := funext tchar_eq
  simp only [nameOk, tokenB, h]

/-! ## Field values -/

theorem fieldVCharB_iff (b : BitVec 8) : fieldVCharB b = true ↔ FieldVChar b := by
  have h := b.isLt
  simp only [fieldVCharB, FieldVChar, IsVChar, IsObsText, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  omega

theorem fieldInnerB_iff (b : BitVec 8) : fieldInnerB b = true ↔ FieldInner b := by
  simp only [fieldInnerB, FieldInner, Bool.or_eq_true, beq_iff_eq, fieldVCharB_iff, or_assoc]

theorem fieldVChar_inner {b : BitVec 8} (h : FieldVChar b) : fieldInnerB b = true :=
  (fieldInnerB_iff b).2 (.inr (.inr h))

theorem fvb_all {v : List (BitVec 8)} (h : fieldValueB v = true) :
    ∀ x ∈ v, fieldInnerB x = true := by
  simp only [fieldValueB, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1.1

theorem fvb_head {x : BitVec 8} {l : List (BitVec 8)} (h : fieldValueB (x :: l) = true) :
    fieldVCharB x = true := by
  simp only [fieldValueB, Bool.and_eq_true, List.head?_cons, Option.all_some] at h
  exact h.1.2

theorem fvb_last {y : BitVec 8} {l : List (BitVec 8)} (h : fieldValueB (l ++ [y]) = true) :
    fieldVCharB y = true := by
  simp only [fieldValueB, Bool.and_eq_true, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, List.head?_cons,
    Option.all_some] at h
  exact h.2

theorem vchar_inner {b : BitVec 8} (h : fieldVCharB b = true) : fieldInnerB b = true :=
  fieldVChar_inner ((fieldVCharB_iff b).1 h)

/-- The check of a value of the form `c :: mid ++ [d]`. -/
theorem fvb_wrap (c d : BitVec 8) (mid : List (BitVec 8)) :
    fieldValueB (c :: mid ++ [d]) = true ↔
      fieldVCharB c = true ∧ (∀ x ∈ mid, fieldInnerB x = true) ∧ fieldVCharB d = true := by
  constructor
  · intro h
    have hall := fvb_all h
    exact ⟨fvb_head h, fun x hx => hall x (by simp [hx]), fvb_last h⟩
  · rintro ⟨hc, hm, hd⟩
    have hall : ∀ x ∈ c :: mid ++ [d], fieldInnerB x = true := by
      intro x hx
      simp only [List.cons_append, List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | hx | hx
      · exact vchar_inner hc
      · exact hm x hx
      · have hxd : x = d := by simpa using hx
        exact hxd ▸ vchar_inner hd
    simp only [fieldValueB, Bool.and_eq_true, List.all_eq_true, List.cons_append,
      List.head?_cons, Option.all_some, List.reverse_cons, List.reverse_append,
      List.reverse_nil, List.nil_append, List.head?_cons]
    exact ⟨⟨by simpa using hall, hc⟩, hd⟩

theorem fvb_single (c : BitVec 8) : fieldValueB [c] = true ↔ fieldVCharB c = true := by
  constructor
  · exact fvb_head
  · intro h
    simp [fieldValueB, h, vchar_inner h]

theorem fieldContent_check {a : List (BitVec 8)} (h : FieldContent a) :
    fieldValueB a = true ∧ a ≠ [] := by
  cases h with
  | one hc => exact ⟨(fvb_single _).2 ((fieldVCharB_iff _).2 hc), by simp⟩
  | wrap hc _ hmid hd =>
    refine ⟨(fvb_wrap _ _ _).2 ⟨(fieldVCharB_iff _).2 hc, fun x hx => ?_, (fieldVCharB_iff _).2 hd⟩,
      by simp⟩
    exact (fieldInnerB_iff x).2 (hmid x hx)

theorem fieldValueB_append {a b : List (BitVec 8)} (ha : fieldValueB a = true)
    (hb : fieldValueB b = true) : fieldValueB (a ++ b) = true := by
  rcases a with _ | ⟨x, a'⟩
  · simpa using hb
  rcases List.eq_nil_or_concat b with rfl | ⟨b', y, rfl⟩
  · simpa using ha
  have hb' : fieldValueB (b' ++ [y]) = true := by simpa using hb
  have he : x :: a' ++ b'.concat y = x :: (a' ++ b') ++ [y] := by simp
  rw [he, fvb_wrap]
  have hal := fvb_all ha
  have hbl := fvb_all hb'
  refine ⟨fvb_head ha, fun z hz => ?_, fvb_last hb'⟩
  rcases List.mem_append.1 hz with hz | hz
  · exact hal z (by simp [hz])
  · exact hbl z (by simp [hz])

theorem fieldValue_check {v : List (BitVec 8)} (h : FieldValue v) : fieldValueB v = true := by
  induction h with
  | nil => rfl
  | app hc _ ih => exact fieldValueB_append (fieldContent_check hc).1 ih

/-- A one-octet value. -/
theorem fieldValue_single {c : BitVec 8} (hc : FieldVChar c) : FieldValue [c] := by
  simpa using FieldValue.app (.one hc) .nil

theorem fieldValue_of_check {v : List (BitVec 8)} (h : fieldValueB v = true) :
    FieldValue v := by
  rcases v with _ | ⟨c, rest⟩
  · exact .nil
  rcases List.eq_nil_or_concat rest with rfl | ⟨mid, d, rfl⟩
  · exact fieldValue_single ((fieldVCharB_iff c).1 ((fvb_single c).1 h))
  have h' : fieldVCharB c = true ∧ (∀ x ∈ mid, fieldInnerB x = true) ∧ fieldVCharB d = true :=
    (fvb_wrap c d mid).1 (by simpa using h)
  have hc : FieldVChar c := (fieldVCharB_iff c).1 h'.1
  have hd : FieldVChar d := (fieldVCharB_iff d).1 h'.2.2
  rcases mid with _ | ⟨m, ms⟩
  · simpa using FieldValue.app (.one hc) (fieldValue_single hd)
  · have hin : ∀ x ∈ m :: ms, FieldInner x := fun x hx => (fieldInnerB_iff x).1 (h'.2.1 x hx)
    simpa using FieldValue.app (.wrap hc (List.cons_ne_nil m ms) hin hd) .nil

/-- **The decision procedure is the `field-value` grammar** (RFC 9110 §5.5). -/
theorem fieldValueB_iff (v : List (BitVec 8)) : fieldValueB v = true ↔ FieldValue v :=
  ⟨fieldValue_of_check, fieldValue_check⟩

instance (v : List (BitVec 8)) : Decidable (FieldValue v) :=
  decidable_of_iff _ (fieldValueB_iff v)

instance (w : List Char) : Decidable (Token w) := decidable_of_iff _ (tokenB_iff w)

/-! ## The WASI value check -/

/-- **The WASI field-value check is the RFC 9110 §5.5 CR/LF/NUL rule.** -/
theorem valueOk_iff (v : List (BitVec 8)) : valueOk v = true ↔ NoCrLfNul v := by
  simp only [valueOk, NoCrLfNul, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq]
  refine forall_congr' fun b => imp_congr_right fun _ => ?_
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩
    exact ⟨fun h => h0 (BitVec.eq_of_toNat_eq h), fun h => h1 (BitVec.eq_of_toNat_eq h),
      fun h => h2 (BitVec.eq_of_toNat_eq h)⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨⟨fun h => h0 (by simp [h]), fun h => h1 (by simp [h])⟩, fun h => h2 (by simp [h])⟩

/-- **Every RFC 9110 `field-value` passes the WASI check.** -/
theorem fieldValue_valueOk {v : List (BitVec 8)} (h : FieldValue v) : valueOk v = true := by
  have hb := fvb_all ((fieldValueB_iff v).2 h)
  refine (valueOk_iff v).2 fun b hbv => ?_
  have hi : fieldInnerB b = true := hb b hbv
  simp only [fieldInnerB, fieldVCharB, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
    decide_eq_true_eq] at hi
  omega

/-- **Refuted: the WASI value check is not the `field-value` grammar.** It accepts a leading
space, a lone space, the control octet `0x01` and `DEL`, which RFC 9110 §5.5 does not. -/
theorem valueOk_not_fieldValue :
    valueOk [0x20, 0x61] = true ∧ ¬ FieldValue [0x20, 0x61] ∧
    valueOk [0x20] = true ∧ ¬ FieldValue [0x20] ∧
    valueOk [0x01] = true ∧ ¬ FieldValue [0x01] ∧
    valueOk [0x7F] = true ∧ ¬ FieldValue [0x7F] := by
  decide

/-- The converse holds on values without other control octets, leading or trailing
whitespace: `valueOk` and the grammar differ exactly by those. -/
theorem not_valueOk_imp (v : List (BitVec 8)) (h : valueOk v = false) : ¬ FieldValue v :=
  fun hv => by simp [fieldValue_valueOk hv] at h

/-! ## Case-insensitive names -/

theorem toLower_toNat (c : Char) : (Char.toLower c).toNat = foldN c.toNat := by
  have hA : 'A'.val = 65 := rfl
  have hZ : 'Z'.val = 90 := rfl
  have ha : 'a'.val = 97 := rfl
  have hlt : c.toNat < 4294967296 := c.val.toNat_lt
  unfold Char.toLower foldN
  by_cases h : 0x41 ≤ c.toNat ∧ c.toNat ≤ 0x5A
  · have h' : c.val ≥ 'A'.val ∧ c.val ≤ 'Z'.val := by
      rw [hA, hZ, ge_iff_le, le_val_iff, val_le_iff]; exact h
    rw [dite_eq_left h', ite_eq_left h]
    show (c.val + ('a'.val - 'A'.val)).toNat = c.toNat + 0x20
    rw [ha, hA, UInt32.toNat_add]
    show (c.toNat + 32) % 4294967296 = c.toNat + 32
    omega
  · have h' : ¬ (c.val ≥ 'A'.val ∧ c.val ≤ 'Z'.val) := by
      rw [hA, hZ, ge_iff_le, le_val_iff, val_le_iff]; exact h
    rw [dite_eq_right h', ite_eq_right h]

/-- **`Net.low` compares names case-insensitively in the sense of RFC 9110 §5.1.** -/
theorem low_eq_iff (a b : List Char) : low a = low b ↔ FoldEq a b := by
  have hc : ∀ l : List Char, l.map (foldN ∘ Char.toNat) = (low l).map Char.toNat := by
    intro l; simp [low, Function.comp_def, toLower_toNat]
  rw [FoldEq, hc, hc]
  exact ⟨congrArg _, fun h => List.map_injective_iff.2 (fun _ _ h => Char.toNat_inj.1 h) h⟩

/-! ## Field-line combination -/

theorem fieldValueB_comma {v w : List (BitVec 8)} (hv : fieldValueB v = true) (hv0 : v ≠ [])
    (hw : fieldValueB w = true) (hw0 : w ≠ []) : fieldValueB (v ++ commaSp ++ w) = true := by
  rcases v with _ | ⟨x, v'⟩
  · exact absurd rfl hv0
  rcases List.eq_nil_or_concat w with rfl | ⟨w', y, rfl⟩
  · exact absurd rfl hw0
  have hw' : fieldValueB (w' ++ [y]) = true := by simpa using hw
  have he : x :: v' ++ commaSp ++ w'.concat y = x :: (v' ++ commaSp ++ w') ++ [y] := by simp
  rw [he, fvb_wrap]
  have hvl := fvb_all hv
  have hwl := fvb_all hw'
  refine ⟨fvb_head hv, fun z hz => ?_, fvb_last hw'⟩
  rcases List.mem_append.1 hz with hz | hz
  · rcases List.mem_append.1 hz with hz | hz
    · exact hvl z (by simp [hz])
    · simp only [commaSp, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl <;> decide
  · exact hwl z (by simp [hz])

theorem combine_ne_nil {vs : List (List (BitVec 8))} (h : ∀ v ∈ vs, v ≠ []) (hne : vs ≠ []) :
    combine vs ≠ [] := by
  match vs, h, hne with
  | [v], h, _ => exact h v (by simp)
  | v :: w :: rest, h, _ => simp [combine, h v (by simp)]

/-- **The combination of nonempty field values is a field value** (RFC 9110 §5.3, §5.5). -/
theorem combine_fieldValue (vs : List (List (BitVec 8)))
    (h : ∀ v ∈ vs, FieldValue v ∧ v ≠ []) : FieldValue (combine vs) := by
  rw [← fieldValueB_iff]
  induction vs with
  | nil => rfl
  | cons v rest ih =>
    have hv : fieldValueB v = true ∧ v ≠ [] :=
      ⟨(fieldValueB_iff v).2 (h v (by simp)).1, (h v (by simp)).2⟩
    have hr : ∀ u ∈ rest, FieldValue u ∧ u ≠ [] := fun u hu => h u (by simp [hu])
    rcases rest with _ | ⟨w, rest'⟩
    · exact hv.1
    · show fieldValueB (v ++ commaSp ++ combine (w :: rest')) = true
      exact fieldValueB_comma hv.1 hv.2 (ih hr)
        (combine_ne_nil (fun u hu => (hr u hu).2) (List.cons_ne_nil _ _))

/-- **The combined value of a name in WASI `fields`** is a `field-value` when each of the
name's values is a nonempty `field-value`. -/
theorem combinedOf_fieldValue (m : Fields) (n : List Char)
    (h : ∀ v ∈ valsOfName m n, FieldValue v ∧ v ≠ []) : FieldValue (combinedOf m n) :=
  combine_fieldValue _ h

end Silmaril.Wasi.Versions.HttpRfc
