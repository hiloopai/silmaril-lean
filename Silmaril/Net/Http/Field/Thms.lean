module

public import Silmaril.Net.Http.Field.Defs
public import Silmaril.Net.Http.Abnf.Thms

@[expose] public section

/-!
# HTTP fields: theorems

PROVED (standard axioms):

* **`token_iff`**: `token` (RFC 9110 §5.6.2, `1*tchar`) derives exactly the octet strings
  accepted by `isToken`; `single_tchar`: `tchar` is the single-octet rule of `isTchar`;
* **`fieldValue_iff`**: `field-value` (§5.5) derives exactly the octet strings accepted by
  `isFieldValue`;
* `isFieldValue_append`, `isFieldValue_commaSp`: valid values are closed under concatenation and
  under prefixing `", "` to a non-empty value; **`isFieldValue_combine`**: combining valid
  field line values (§5.3) gives a valid field value;
* `isSafeValue_of_isFieldValue`: a `field-value` has no NUL, CR or LF;
* section algebra: `values_append`, `values_remove_self`, `values_remove_of_ne`,
  `has_iff_values`, `fieldValue?_append_self`.
-/

namespace Silmaril.Net.Http.Field

open Silmaril.Formats.Grammar.Ebnf
open Silmaril.Net.Http.Abnf

variable {N : Type} {body : N → Expr UInt8 N}

/-! ## Tokens -/

theorem single_tchar : Single body tchar isTchar := by
  intro xs
  simp only [tchar, Derives.alternative_iff, derives_anyOf_iff, single_digit xs, single_alpha xs,
    isTchar, Bool.or_eq_true, List.contains_iff_mem]
  constructor
  · rintro (⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩)
    · exact ⟨b, Or.inl (Or.inl hb), rfl⟩
    · exact ⟨b, Or.inl (Or.inr hb), rfl⟩
    · exact ⟨b, Or.inr hb, rfl⟩
  · rintro ⟨b, (hb | hb) | hb, rfl⟩
    · exact Or.inl ⟨b, hb, rfl⟩
    · exact Or.inr (Or.inl ⟨b, hb, rfl⟩)
    · exact Or.inr (Or.inr ⟨b, hb, rfl⟩)

/-- **`token = 1*tchar` is decided by `isToken`** (RFC 9110 §5.6.2). -/
theorem token_iff (xs : List UInt8) : Derives body token xs ↔ isToken xs = true := by
  rw [token, single_tchar.oneOrMore_iff]
  simp only [isToken, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff]

/-- `field-name = token` (§5.1). -/
theorem fieldName_iff (xs : List UInt8) : Derives body fieldName xs ↔ isToken xs = true :=
  token_iff xs

/-! ## Characters -/

theorem asciiOctets?_eq_some {s : List Char} (h : s.all (fun c => c.toNat < 128) = true) :
    asciiOctets? s = some (s.map (fun c => c.toNat.toUInt8)) := by
  simp [asciiOctets?, h]

theorem all_isTcharChar_of_ascii : ∀ {s : List Char},
    s.all (fun c => decide (c.toNat < 128)) = true →
      s.all (fun c => isTchar c.toNat.toUInt8) = s.all isTcharChar
  | [], _ => rfl
  | c :: cs, h => by
    have hc : c.toNat < 128 := by simp only [List.all_cons, Bool.and_eq_true] at h; simpa using h.1
    have hcs : cs.all (fun c => decide (c.toNat < 128)) = true := by
      simp only [List.all_cons, Bool.and_eq_true] at h; exact h.2
    simp [isTcharChar, hc, all_isTcharChar_of_ascii hcs]

theorem all_isTcharChar_eq_false {s : List Char} {c : Char} (hc : c ∈ s) (hlt : ¬ c.toNat < 128) :
    s.all isTcharChar = false := by
  rw [Bool.eq_false_iff]
  intro hall
  have hcc : isTcharChar c = true := List.all_eq_true.mp hall c hc
  simp [isTcharChar, hlt] at hcc

/-- A string is a token exactly when it is non-empty and its characters are `tchar`s. -/
theorem isTokenChars_iff (s : List Char) :
    isTokenChars s = (!s.isEmpty && s.all isTcharChar) := by
  unfold isTokenChars asciiOctets?
  by_cases h : s.all (fun c => decide (c.toNat < 128)) = true
  · have hall := all_isTcharChar_of_ascii h
    simp only [h, ite_true, isToken, List.isEmpty_map, List.all_map, Function.comp_def, hall]
  · have hex : ∃ c ∈ s, ¬ c.toNat < 128 := by simpa using h
    obtain ⟨c, hc, hlt⟩ := hex
    have hne : s.isEmpty = false := by cases s <;> simp_all
    simp [h, hne, all_isTcharChar_eq_false hc hlt]

/-- The ASCII characters whose code is a `tchar`, decided over the 128 ASCII codes. -/
theorem isTcharChar_ascii : ∀ n < 128,
    isTcharChar (Char.ofNat n) =
      ((Char.ofNat n).isAlphanum || "!#$%&'*+-.^_`|~".toList.contains (Char.ofNat n)) := by
  decide +kernel

theorem isAlphanum_lt {c : Char} (h : c.isAlphanum = true) : c.toNat < 128 := by
  have h' : ('A'.val.toNat ≤ c.val.toNat ∧ c.val.toNat ≤ 'Z'.val.toNat ∨
      'a'.val.toNat ≤ c.val.toNat ∧ c.val.toNat ≤ 'z'.val.toNat) ∨
      '0'.val.toNat ≤ c.val.toNat ∧ c.val.toNat ≤ '9'.val.toNat := by
    simpa only [Char.isAlphanum, Char.isAlpha, Char.isUpper, Char.isLower, Char.isDigit,
      Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, UInt32.le_iff_toNat_le] using h
  have hz : 'z'.val.toNat = 122 := rfl
  have hZ : 'Z'.val.toNat = 90 := rfl
  have h9 : '9'.val.toNat = 57 := rfl
  have hv : c.toNat = c.val.toNat := rfl
  omega

/-- **`tchar` on characters is "alphanumeric or one of ``!#$%&'*+-.^_`|~``"**, the definition
used by `Silmaril.Wasi.Versions.HttpHdr.tchar` (Lean's `Char.isAlphanum` is ASCII-only). -/
theorem isTcharChar_eq (c : Char) :
    isTcharChar c = (c.isAlphanum || "!#$%&'*+-.^_`|~".toList.contains c) := by
  by_cases hc : c.toNat < 128
  · have h := isTcharChar_ascii c.toNat hc
    rwa [Char.ofNat_toNat] at h
  · have h1 : isTcharChar c = false := by simp [isTcharChar, hc]
    have h2 : c.isAlphanum = false := by
      rw [Bool.eq_false_iff]; exact fun ha => hc (isAlphanum_lt ha)
    have h3 : "!#$%&'*+-.^_`|~".toList.contains c = false := by
      rw [Bool.eq_false_iff]
      intro hm
      have hmem : c ∈ "!#$%&'*+-.^_`|~".toList := by simpa using hm
      have hall : ∀ d ∈ "!#$%&'*+-.^_`|~".toList, d.toNat < 128 := by decide
      exact hc (hall c hmem)
    rw [h1, h2, h3]; rfl

/-! ## Field values -/

theorem single_fieldVchar : Single body fieldVchar isFieldVchar :=
  single_vchar.alternative single_obsText

theorem single_fieldChar : Single body fieldChar isFieldChar :=
  single_wsp.alternative single_fieldVchar

theorem isFieldChar_of_vchar {b : UInt8} (h : isFieldVchar b = true) : isFieldChar b = true := by
  simp [isFieldChar, h]

theorem optional_iff (e : Expr UInt8 N) (xs : List UInt8) :
    Derives body (Expr.optional e) xs ↔ xs = [] ∨ Derives body e xs := by
  simp only [Expr.optional, Derives.alternative_iff, Derives.epsilon_iff]

/-- Option `all` of `or`. -/
theorem option_all_or {p : UInt8 → Bool} {a b : Option UInt8} (ha : a.all p = true)
    (hb : b.all p = true) : (a.or b).all p = true := by
  cases a <;> simpa using ‹_›

theorem isFieldValue_append {a b : List UInt8} (ha : isFieldValue a = true)
    (hb : isFieldValue b = true) : isFieldValue (a ++ b) = true := by
  simp only [isFieldValue, Bool.and_eq_true] at ha hb ⊢
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [List.all_append, ha.1.1, hb.1.1, Bool.and_self]
  · rw [List.head?_append]; exact option_all_or ha.1.2 hb.1.2
  · rw [List.getLast?_append]; exact option_all_or hb.2 ha.2

theorem isFieldValue_singleton {x : UInt8} (h : isFieldVchar x = true) :
    isFieldValue [x] = true := by
  simp [isFieldValue, h, isFieldChar_of_vchar h]

theorem getLast?_cons_snoc (x z : UInt8) (m : List UInt8) :
    (x :: (m ++ [z])).getLast? = some z := by
  have h : x :: (m ++ [z]) = (x :: m) ++ [z] := rfl
  rw [h, List.getLast?_append]; rfl

/-- The values of `field-content`. -/
theorem fieldContent_sound {c : List UInt8} (h : Derives body fieldContent c) :
    c ≠ [] ∧ isFieldValue c = true := by
  obtain ⟨l, r, rfl, hl, hr⟩ := (Derives.sequence_iff _ _ _).mp h
  obtain ⟨x, hx, rfl⟩ := (single_fieldVchar l).mp hl
  rcases (optional_iff _ r).mp hr with rfl | hr
  · exact ⟨List.cons_ne_nil _ _, isFieldValue_singleton hx⟩
  · obtain ⟨m, z, rfl, hm, hz⟩ := (Derives.sequence_iff _ _ _).mp hr
    obtain ⟨hmne, hmall⟩ := (single_fieldChar.oneOrMore_iff m).mp hm
    obtain ⟨z, hzv, rfl⟩ := (single_fieldVchar z).mp hz
    refine ⟨List.cons_ne_nil _ _, ?_⟩
    simp [isFieldValue, getLast?_cons_snoc, hx, hzv, hmall, isFieldChar_of_vchar hx,
      isFieldChar_of_vchar hzv]

theorem fieldContent_single {x : UInt8} (hx : isFieldVchar x = true) :
    Derives body fieldContent [x] := by
  have hl : Derives body fieldVchar [x] := (single_fieldVchar [x]).mpr ⟨x, hx, rfl⟩
  have hr : Derives body (Expr.optional (.sequence (Expr.oneOrMore fieldChar) fieldVchar)) [] :=
    (optional_iff _ _).mpr (Or.inl rfl)
  unfold fieldContent
  simpa using Derives.sequence hl hr

theorem fieldContent_long {x z : UInt8} {m : List UInt8} (hx : isFieldVchar x = true)
    (hm : m ≠ []) (hmall : m.all isFieldChar = true) (hz : isFieldVchar z = true) :
    Derives body fieldContent (x :: (m ++ [z])) := by
  have hl : Derives body fieldVchar [x] := (single_fieldVchar [x]).mpr ⟨x, hx, rfl⟩
  have hmd : Derives body (Expr.oneOrMore fieldChar) m :=
    (single_fieldChar.oneOrMore_iff m).mpr ⟨hm, hmall⟩
  have hzd : Derives body fieldVchar [z] := (single_fieldVchar [z]).mpr ⟨z, hz, rfl⟩
  have hr : Derives body (Expr.optional (.sequence (Expr.oneOrMore fieldChar) fieldVchar))
      (m ++ [z]) := (optional_iff _ _).mpr (Or.inr (Derives.sequence hmd hzd))
  unfold fieldContent
  simpa using Derives.sequence hl hr

/-- `x m z` with `field-vchar`s `x`, `z` is one or two `field-content`s. -/
theorem fieldValue_complete_snoc {x z : UInt8} {m : List UInt8} (hx : isFieldVchar x = true)
    (hz : isFieldVchar z = true) (hmall : m.all isFieldChar = true) :
    ∃ parts : List (List UInt8), (∀ p ∈ parts, Derives body fieldContent p) ∧
      parts.flatten = x :: (m ++ [z]) := by
  by_cases hm : m = []
  · have hparts : ∀ p ∈ [[x], [z]], Derives body fieldContent p := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact fieldContent_single hx
      · rw [List.mem_singleton.mp hp']; exact fieldContent_single hz
    exact ⟨[[x], [z]], hparts, by simp [hm]⟩
  · exact ⟨[x :: (m ++ [z])], by simpa using fieldContent_long hx hm hmall hz, by simp⟩

/-- A valid value is a concatenation of `field-content`s. -/
theorem fieldValue_complete {v : List UInt8} (hv : isFieldValue v = true) :
    ∃ parts : List (List UInt8), (∀ p ∈ parts, Derives body fieldContent p) ∧
      parts.flatten = v := by
  rcases v with _ | ⟨x, t⟩
  · exact ⟨[], by simp, rfl⟩
  have hv' : ((x :: t).all isFieldChar = true ∧ isFieldVchar x = true) ∧
      (x :: t).getLast?.all isFieldVchar = true := by simpa [isFieldValue] using hv
  rcases List.eq_nil_or_concat t with rfl | ⟨m, z, ht⟩
  · exact ⟨[[x]], by simpa using fieldContent_single hv'.1.2, by simp⟩
  have ht' : t = m ++ [z] := by rw [ht, List.concat_eq_append]
  have hz : isFieldVchar z = true := by simpa [ht', getLast?_cons_snoc] using hv'.2
  have h1 : (x :: (m ++ [z])).all isFieldChar = true := ht' ▸ hv'.1.1
  have hmall : m.all isFieldChar = true := by
    have h2 := List.all_eq_true.mp h1
    exact List.all_eq_true.mpr (fun b hb => h2 b (by simp [hb]))
  rw [ht']
  exact fieldValue_complete_snoc hv'.1.2 hz hmall

/-- **`field-value = *field-content` is decided by `isFieldValue`** (RFC 9110 §5.5). -/
theorem fieldValue_iff (v : List UInt8) : Derives body fieldValue v ↔ isFieldValue v = true := by
  rw [fieldValue, derives_repetition_iff]
  constructor
  · rintro ⟨parts, hp, rfl⟩
    induction parts with
    | nil => rfl
    | cons p ps ih =>
      have hp1 : isFieldValue p = true := (fieldContent_sound (hp p (List.mem_cons_self ..))).2
      have hps : isFieldValue ps.flatten = true :=
        ih (fun q hq => hp q (List.mem_cons_of_mem _ hq))
      simpa only [List.flatten_cons] using isFieldValue_append hp1 hps
  · exact fieldValue_complete

/-- `", "` before a non-empty valid value keeps it valid. -/
theorem isFieldValue_commaSp {b : List UInt8} (hb : isFieldValue b = true) (hne : b ≠ []) :
    isFieldValue (commaSp ++ b) = true := by
  simp only [isFieldValue, Bool.and_eq_true] at hb ⊢
  obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hlast : (commaSp ++ y :: ys).getLast? = (y :: ys).getLast? := by
    rw [List.getLast?_append]
    cases h : (y :: ys).getLast? with
    | none => simp at h
    | some a => rfl
  refine ⟨⟨?_, rfl⟩, ?_⟩
  · simp only [commaSp, List.all_append, hb.1.1, Bool.and_true]; rfl
  · rw [hlast]; exact hb.2

/-- **Combining valid field line values gives a valid field value** (RFC 9110 §5.3). -/
theorem isFieldValue_combine {vs : List (List UInt8)} (h : ∀ v ∈ vs, isFieldValue v = true) :
    isFieldValue (combine vs) = true := by
  unfold combine
  have hf : ∀ v ∈ vs.filter (· ≠ []), isFieldValue v = true ∧ v ≠ [] := by
    intro v hv
    obtain ⟨hmem, hne⟩ := List.mem_filter.mp hv
    exact ⟨h v hmem, by simpa using hne⟩
  generalize vs.filter (· ≠ []) = ws at hf
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    show isFieldValue (commaSp.intercalate (w :: ws)) = true
    have hw := hf w (List.mem_cons_self ..)
    have hws : ∀ v ∈ ws, isFieldValue v = true ∧ v ≠ [] :=
      fun v hv => hf v (List.mem_cons_of_mem _ hv)
    rcases ws with _ | ⟨w', ws'⟩
    · simpa using hw.1
    · show isFieldValue (commaSp.intercalate (w :: w' :: ws')) = true
      have hrest : isFieldValue (commaSp.intercalate (w' :: ws')) = true := ih hws
      have hw' : w' ≠ [] := (hws w' (List.mem_cons_self ..)).2
      have hne : commaSp.intercalate (w' :: ws') ≠ [] := by
        rcases ws' with _ | ⟨u, us⟩
        · simpa using hw'
        · rw [List.intercalate_cons_cons]; simp [hw']
      rw [List.intercalate_cons_cons, List.append_assoc]
      exact isFieldValue_append hw.1 (isFieldValue_commaSp hrest hne)

/-- A `field-value` has no NUL, CR or LF (RFC 9110 §5.5). -/
theorem safe_of_fieldChar : ∀ b ∈ allOctets, isFieldChar b = true →
    (b != 0x00 && b != 0x0A && b != 0x0D) = true := by decide

theorem isSafeValue_of_isFieldValue {v : List UInt8} (h : isFieldValue v = true) :
    isSafeValue v = true := by
  simp only [isFieldValue, Bool.and_eq_true, List.all_eq_true] at h
  simp only [isSafeValue, List.all_eq_true]
  exact fun b hb => safe_of_fieldChar b (mem_allOctets b) (h.1.1 b hb)

/-! ## Sections -/

theorem values_append (s t : Section) (n : List UInt8) :
    Section.values (s ++ t) n = s.values n ++ t.values n := by
  simp [Section.values, Section.lines, List.filter_append]

theorem values_remove_self (s : Section) (n : List UInt8) : (s.remove n).values n = [] := by
  simp [Section.values, Section.lines, Section.remove, List.filter_filter]

theorem values_remove_of_ne (s : Section) {n m : List UInt8} (h : eqIgnoreCase n m = false) :
    (s.remove n).values m = s.values m := by
  simp only [Section.values, Section.lines, Section.remove, List.filter_filter]
  congr 2
  funext l
  cases hl : eqIgnoreCase l.name m with
  | false => simp
  | true =>
    have hlm : lower l.name = lower m := by simpa [eqIgnoreCase] using hl
    have hnm : lower n ≠ lower m := by simpa [eqIgnoreCase] using h
    simp [eqIgnoreCase, hlm, Ne.symm hnm]

theorem has_iff_values (s : Section) (n : List UInt8) : s.has n = true ↔ s.values n ≠ [] := by
  simp [Section.has, Section.values, Section.lines, List.filter_eq_nil_iff]

theorem fieldValue?_append_self (s : Section) (n v : List UInt8) :
    (s.append n v).fieldValue? n = some (combine (s.values n ++ [v])) := by
  simp [Section.fieldValue?, Section.append, Section.has, Section.values,
    Section.lines, eqIgnoreCase_refl]

/-! ## Combining a whole section (§5.3) -/

theorem eqIgnoreCase_iff (x y : List UInt8) : eqIgnoreCase x y = true ↔ lower x = lower y := by
  simp [eqIgnoreCase]

theorem eqIgnoreCase_trans {x y z : List UInt8} (h₁ : eqIgnoreCase x y = true)
    (h₂ : eqIgnoreCase y z = true) : eqIgnoreCase x z = true := by
  rw [eqIgnoreCase_iff] at *; exact h₁.trans h₂

/-- The values of a name depend only on its lower case. -/
theorem values_congr (s : Section) {m n : List UInt8} (h : eqIgnoreCase m n = true) :
    s.values m = s.values n := by
  have hl : lower m = lower n := (eqIgnoreCase_iff m n).mp h
  simp only [Section.values, Section.lines, eqIgnoreCase, hl]

theorem has_congr (s : Section) {m n : List UInt8} (h : eqIgnoreCase m n = true) :
    s.has m = s.has n := by
  have hl : lower m = lower n := (eqIgnoreCase_iff m n).mp h
  simp only [Section.has, eqIgnoreCase, hl]

theorem find?_filter_of_imp {p q : List UInt8 → Bool} (hpq : ∀ y, p y = true → q y = true)
    (l : List (List UInt8)) : (l.filter q).find? p = l.find? p := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    by_cases hp : p y = true
    · simp [hpq y hp, hp]
    · by_cases hq : q y = true <;> simp [hq, hp, ih]

/-- The names equal to `n` among the deduplicated names: the first occurrence, if any. -/
theorem filter_dedupNames (n : List UInt8) : ∀ xs : List (List UInt8),
    (dedupNames xs).filter (eqIgnoreCase · n) = ((xs.find? (eqIgnoreCase · n)).map ([·])).getD []
  | [] => by simp [dedupNames]
  | x :: xs => by
    have ih := filter_dedupNames n (xs.filter (fun y => !eqIgnoreCase y x))
    rw [dedupNames, List.filter_cons]
    by_cases hx : eqIgnoreCase x n = true
    · have hnone : (xs.filter (fun y => !eqIgnoreCase y x)).find? (eqIgnoreCase · n) = none := by
        rw [List.find?_eq_none]
        intro y hy hyn
        have hyx : eqIgnoreCase y x = false := by simpa using (List.mem_filter.mp hy).2
        have hxn' : eqIgnoreCase n x = true := by rwa [eqIgnoreCase_comm]
        simp [eqIgnoreCase_trans hyn hxn'] at hyx
      simp [hx, ih, hnone]
    · have himp : ∀ y, eqIgnoreCase y n = true → (!eqIgnoreCase y x) = true := by
        intro y hyn
        by_cases hyx : eqIgnoreCase y x = true
        · have hxn : eqIgnoreCase x n = true :=
            eqIgnoreCase_trans (by rwa [eqIgnoreCase_comm]) hyn
          exact absurd hxn hx
        · simpa using hyx
      simp [hx, ih, find?_filter_of_imp himp]
termination_by xs => xs.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem combine_singleton (v : List UInt8) : combine [v] = v := by
  by_cases hv : v = [] <;> simp [combine, hv]

theorem has_iff_find? (s : Section) (n : List UInt8) :
    s.has n = true ↔ ((s.map Line.name).find? (eqIgnoreCase · n)).isSome := by
  simp [Section.has, List.find?_isSome]

/-- **Combining every field line of a section keeps every field value** (§5.3: a recipient
MAY combine field lines "without changing the semantics of the message"). -/
theorem fieldValue?_combineAll (s : Section) (n : List UInt8) :
    s.combineAll.fieldValue? n = s.fieldValue? n := by
  have hvals : s.combineAll.values n =
      ((s.names.filter (eqIgnoreCase · n)).map (fun m => combine (s.values m))) := by
    simp [Section.combineAll, Section.values, Section.lines, List.filter_map, Function.comp_def]
  have hf := filter_dedupNames n (s.map Line.name)
  unfold Section.fieldValue?
  cases hfind : (s.map Line.name).find? (eqIgnoreCase · n) with
  | none =>
    have hs : s.has n = false := by simpa [hfind] using (has_iff_find? s n).not
    have hc : s.combineAll.values n = [] := by
      rw [hvals, Section.names, hf, hfind]; rfl
    have hcs : s.combineAll.has n = false := by
      simpa [hc] using (has_iff_values s.combineAll n).not
    simp [hs, hcs]
  | some m =>
    have hm : eqIgnoreCase m n = true := List.find?_some (p := (eqIgnoreCase · n)) hfind
    have hs : s.has n = true := (has_iff_find? s n).mpr (by simp [hfind])
    have hc : s.combineAll.values n = [combine (s.values n)] := by
      rw [hvals, Section.names, hf, hfind]
      simp [values_congr s hm]
    have hcs : s.combineAll.has n = true := (has_iff_values _ n).mpr (by simp [hc])
    simp [hs, hcs, hc, combine_singleton]

theorem mem_dedupNames {y : List UInt8} : ∀ xs : List (List UInt8), y ∈ dedupNames xs → y ∈ xs
  | [] => by simp [dedupNames]
  | x :: xs => by
    rw [dedupNames, List.mem_cons]
    rintro (rfl | hy)
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_filter.mp (mem_dedupNames _ hy)).1
termination_by xs => xs.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- Combining a valid section gives a valid section. -/
theorem isValid_combineAll {s : Section} (h : s.isValid = true) : s.combineAll.isValid = true := by
  have hlines : ∀ l ∈ s, l.isValid = true := List.all_eq_true.mp h
  simp only [Section.isValid, Section.combineAll, List.all_map, List.all_eq_true]
  intro n hn
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp (mem_dedupNames _ hn)
  have hv : ∀ v ∈ s.values l.name, isFieldValue v = true := by
    intro v hv
    obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hv
    have hvalid := hlines l' (List.mem_filter.mp hl').1
    simp only [Line.isValid, Bool.and_eq_true] at hvalid
    exact hvalid.2
  have hname : isToken l.name = true := by
    have hvalid := hlines l hl
    simp only [Line.isValid, Bool.and_eq_true] at hvalid
    exact hvalid.1
  simp [Line.isValid, hname, isFieldValue_combine hv]

/-! ## Vectors -/

/-- The octets of an ASCII string literal. -/
private abbrev lit (s : String) : List UInt8 := s.toList.map (fun c => c.toNat.toUInt8)

example : isToken (lit "Content-Type") = true := by decide
example : isToken (lit "X-Custom_Header.v2~!") = true := by decide
example : isToken (lit "Bad Name") = false := by decide
example : isToken (lit "a:b") = false := by decide
example : isToken [] = false := by decide
example : isFieldValue (lit "text/html; charset=utf-8") = true := by decide
example : isFieldValue (lit "a\tb") = true := by decide
example : isFieldValue (lit " leading") = false := by decide
example : isFieldValue (lit "trailing ") = false := by decide
example : isFieldValue [0x61, 0x0A, 0x62] = false := by decide
example : isFieldValue [0x80, 0xFF] = true := by decide
example : isSafeValue (lit " leading") = true := by decide
example : combine [lit "a", [], lit "b"] = lit "a, b" := by decide

end Silmaril.Net.Http.Field
