module

public import Silmaril.Raw.Wasm.Component.ABI.String

/-!
# Properties of canonical ABI strings

Round trips and length bounds for the codecs of `ABI/String.lean`, and soundness
of the Python `definitions.py` (`a25fc0b`) store algorithms' buffer sizes.

* Codecs: `utf8Decode?_eq_some_iff`, `utf16Decode?_eq_some_iff` (decoding succeeds
  exactly on encodings, so decode ∘ encode = id and decoding is injective),
  `latin1Decode_latin1Encode` and `latin1Encode_latin1Decode`.
* Tagged lengths: `untagUtf16_tagUtf16`, `isUtf16Tagged_tagUtf16` and
  `isUtf16Tagged_of_lt` for code-unit counts below `utf16_tag`.
* Worst-case sizes: `utf8Length_le_three_mul_utf16Length` (`store_utf16_to_utf8`),
  `utf8Length_le_two_mul_length` (`store_latin1_to_utf8`), `utf16Length_le_utf8Length`
  (`store_utf8_to_utf16`, `store_string_to_latin1_or_utf16`), and
  `length_le_utf16Length`/`length_le_utf8Length` (initial `allocate` sizes).
* `loadStringFromRange?_consistent`: loaded values satisfy the code-unit
  assertions of the store functions.
* `storeStringIntoRange_inBounds`: for consistent values, every write and every
  inflate/deflate loop of a store plan stays inside both the most recent realloc
  result and the most recent bounds check.
* `storeStringIntoRange_requestSize_le`: each realloc request is at most
  `3 * src_code_units`; `storeStringIntoRange_requestSize_le_reallocI32Max`: hence,
  for consistent values of at most `MAX_STRING_BYTE_LENGTH` code units, at most
  `REALLOC_I32_MAX`, discharging the Python `assert`s.

Not proved here: that the byte image left in memory by `StorePlan.run` decodes back to
the stored string. For the UTF-8 destination this is proved in
`ABI/String/RoundTrip/Utf8.lean` (`store_load_utf8`, under the `ReallocContract` of
`ABI/String/Contract.lean`); the other destinations are covered by their own round-trip
files or remain differentially tested against the Python (see `String/Examples.lean`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.ABI

/-! ## Characters -/

private theorem char_toNat_valid (c : Char) :
    c.toNat < 0xD800 ∨ (0xDFFF < c.toNat ∧ c.toNat < 0x110000) := c.valid

private theorem char_toNat_ofNat_of_valid {n : Nat} (h : n < 0xD800 ∨ (0xDFFF < n ∧ n < 0x110000)) :
    (Char.ofNat n).toNat = n := by
  have hv : n.isValidChar := h
  simp only [Char.ofNat, hv, dite_true, Char.ofNatAux, Char.toNat]
  rfl

private theorem char_utf8Size_eq_of_toNat (c : Char) :
    c.utf8Size = if c.toNat < 0x80 then 1 else if c.toNat < 0x800 then 2
      else if c.toNat < 0x10000 then 3 else 4 := by
  have h1 := @Char.utf8Size_eq_one_iff c
  have h2 := @Char.utf8Size_eq_two_iff c
  have h3 := @Char.utf8Size_eq_three_iff c
  have h4 := @Char.utf8Size_eq_four_iff c
  have := Char.utf8Size_eq c
  simp only [UInt32.le_iff_toNat_le, UInt32.lt_iff_toNat_lt, UInt32.reduceToNat] at h1 h2 h3 h4
  change _ = if c.val.toNat < 0x80 then 1 else if c.val.toNat < 0x800 then 2
      else if c.val.toNat < 0x10000 then 3 else 4
  split_ifs <;> omega

/-! ## Tagged code-unit counts -/

private theorem and_two_pow_of_lt {n k : Nat} (h : n < 2 ^ k) : n &&& 2 ^ k = 0 :=
  Nat.eq_of_testBit_eq fun i => by
    by_cases hi : k = i
    · subst hi; simp [Nat.testBit_lt_two_pow h]
    · simp [hi]

private theorem or_two_pow_and (n k : Nat) : (n ||| 2 ^ k) &&& 2 ^ k = 2 ^ k :=
  Nat.eq_of_testBit_eq fun i => by
    by_cases hi : k = i
    · subst hi; simp
    · simp [hi]

private theorem or_two_pow_xor {n k : Nat} (h : n < 2 ^ k) : (n ||| 2 ^ k) ^^^ 2 ^ k = n :=
  Nat.eq_of_testBit_eq fun i => by
    by_cases hi : k = i
    · subst hi; simp [Nat.testBit_lt_two_pow h]
    · simp [hi]

theorem utf16Tag_eq_two_pow (a : AddrType) : ∃ k, utf16Tag a = 2 ^ k := by
  cases a
  · exact ⟨31, rfl⟩
  · exact ⟨63, rfl⟩

theorem tagUtf16_eq_add {a : AddrType} {n : Nat} (h : n < utf16Tag a) :
    tagUtf16 a n = n + utf16Tag a := by
  obtain ⟨k, hk⟩ := utf16Tag_eq_two_pow a
  rw [hk] at h
  simp only [tagUtf16, hk, Nat.or_two_pow_eq_add_of_lt h]

theorem isUtf16Tagged_of_lt {a : AddrType} {n : Nat} (h : n < utf16Tag a) :
    isUtf16Tagged a n = false := by
  obtain ⟨k, hk⟩ := utf16Tag_eq_two_pow a
  rw [hk] at h
  simp only [isUtf16Tagged, hk, and_two_pow_of_lt h, bne_self_eq_false]

theorem isUtf16Tagged_tagUtf16 (a : AddrType) (n : Nat) :
    isUtf16Tagged a (tagUtf16 a n) = true := by
  obtain ⟨k, hk⟩ := utf16Tag_eq_two_pow a
  simp [isUtf16Tagged, tagUtf16, hk, or_two_pow_and]

theorem untagUtf16_tagUtf16 {a : AddrType} {n : Nat} (h : n < utf16Tag a) :
    untagUtf16 a (tagUtf16 a n) = n := by
  obtain ⟨k, hk⟩ := utf16Tag_eq_two_pow a
  rw [hk] at h
  simp only [untagUtf16, tagUtf16, hk, or_two_pow_xor h]

/-! ## UTF-8 -/

theorem utf8Encode_toByteArray (s : String) : (utf8Encode s).toByteArray = s.toByteArray := by
  rw [← String.utf8Encode_toList, List.utf8Encode_eq_toByteArray]
  rfl

theorem utf8Decode?_utf8Encode (s : String) : utf8Decode? (utf8Encode s) = some s := by
  simp only [utf8Decode?, utf8Encode_toByteArray, String.fromUTF8?, s.isValidUTF8, dite_true]
  rfl

theorem utf8Decode?_eq_some_iff {bs : List UInt8} {s : String} :
    utf8Decode? bs = some s ↔ utf8Encode s = bs := by
  constructor
  · intro h
    simp only [utf8Decode?, String.fromUTF8?] at h
    split at h
    · cases h
      apply List.toByteArray_inj.mp
      rw [utf8Encode_toByteArray]
      rfl
    · cases h
  · rintro rfl; exact utf8Decode?_utf8Encode s

theorem utf8Encode_length (s : String) :
    (utf8Encode s).length = (s.toList.map Char.utf8Size).sum := by
  simp only [utf8Encode]
  induction s.toList with
  | nil => rfl
  | cons c cs ih => simp [List.flatMap_cons, ih]

/-! ## UTF-16 -/

theorem utf16DecodeUnits?_utf16EncodeChar_append (c : Char) (us : List UInt16) :
    utf16DecodeUnits? (utf16EncodeChar c ++ us) = (c :: ·) <$> utf16DecodeUnits? us := by
  have hc := char_toNat_valid c
  by_cases h : c.toNat < 0x10000
  · have hu : (c.toNat.toUInt16).toNat = c.toNat := by
      simp only [Nat.toUInt16_eq, UInt16.toNat_ofNat']; omega
    have hbmp : c.toNat < 0xD800 ∨ 0xE000 ≤ c.toNat := by omega
    simp only [utf16EncodeChar, h, ↓reduceIte, List.cons_append, List.nil_append]
    rw [utf16DecodeUnits?.eq_def]
    simp only [hu, hbmp, ↓reduceIte, Char.ofNat_toNat]
  · obtain ⟨hi, lo, hhi, hlo, henc⟩ : ∃ hi lo : UInt16,
        hi.toNat = 0xD800 + (c.toNat - 0x10000) / 0x400 ∧
        lo.toNat = 0xDC00 + (c.toNat - 0x10000) % 0x400 ∧ utf16EncodeChar c = [hi, lo] :=
      ⟨(0xD800 + (c.toNat - 0x10000) / 0x400).toUInt16,
        (0xDC00 + (c.toNat - 0x10000) % 0x400).toUInt16,
        by simp only [Nat.toUInt16_eq, UInt16.toNat_ofNat']; omega,
        by simp only [Nat.toUInt16_eq, UInt16.toNat_ofNat']; omega,
        by simp only [utf16EncodeChar, h, ↓reduceIte]⟩
    have hv : 0x10000 + (hi.toNat - 0xD800) * 0x400 + (lo.toNat - 0xDC00) = c.toNat := by
      omega
    have h1 : ¬(hi.toNat < 0xD800 ∨ 0xE000 ≤ hi.toNat) := by omega
    have h2 : hi.toNat < 0xDC00 := by omega
    have h3 : 0xDC00 ≤ lo.toNat ∧ lo.toNat < 0xE000 := by omega
    rw [henc, List.cons_append, List.cons_append, List.nil_append, utf16DecodeUnits?]
    simp only [h1, h2, h3, and_self, ↓reduceIte, hv, Char.ofNat_toNat]

theorem utf16DecodeUnits?_flatMap (cs : List Char) :
    utf16DecodeUnits? (cs.flatMap utf16EncodeChar) = some cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatMap_cons, utf16DecodeUnits?_utf16EncodeChar_append, ih]
    rfl

theorem flatMap_of_utf16DecodeUnits? {us : List UInt16} {cs : List Char}
    (h : utf16DecodeUnits? us = some cs) : cs.flatMap utf16EncodeChar = us := by
  fun_induction utf16DecodeUnits? us generalizing cs with
  | case1 => cases h; rfl
  | case2 u us hu ih =>
    simp only [Option.map_eq_map, Option.map_eq_some_iff] at h
    obtain ⟨cs', h', rfl⟩ := h
    have hlt : u.toNat < 65536 := u.toNat_lt
    have hn : (Char.ofNat u.toNat).toNat = u.toNat := char_toNat_ofNat_of_valid (by omega)
    rw [List.flatMap_cons, ih h']
    simp only [utf16EncodeChar, hn, hlt, ↓reduceIte, List.cons_append, List.nil_append,
      Nat.toUInt16_eq, UInt16.ofNat_toNat]
  | case3 u hu hsu l us' hl ih =>
    simp only [Option.map_eq_map, Option.map_eq_some_iff] at h
    obtain ⟨cs', h', rfl⟩ := h
    have hlt : u.toNat < 65536 := u.toNat_lt
    have hn : (Char.ofNat (0x10000 + (u.toNat - 0xD800) * 0x400 + (l.toNat - 0xDC00))).toNat =
        0x10000 + (u.toNat - 0xD800) * 0x400 + (l.toNat - 0xDC00) :=
      char_toNat_ofNat_of_valid (by omega)
    have hge : ¬ 0x10000 + (u.toNat - 0xD800) * 0x400 + (l.toNat - 0xDC00) < 0x10000 := by
      omega
    rw [List.flatMap_cons, ih h']
    simp only [utf16EncodeChar, hn, hge, ↓reduceIte, List.cons_append, List.nil_append,
      List.cons.injEq, and_true]
    constructor <;> apply UInt16.toNat_inj.mp <;>
      simp only [Nat.toUInt16_eq, UInt16.toNat_ofNat'] <;> omega
  | case4 => cases h
  | case5 => cases h
  | case6 => cases h

theorem bytesToUnitsLE?_unitsToBytesLE (us : List UInt16) :
    bytesToUnitsLE? (unitsToBytesLE us) = some us := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    have hlt : u.toNat < 65536 := u.toNat_lt
    have hu : ((u.toNat % 256).toUInt8.toNat + 256 * (u.toNat / 256).toUInt8.toNat).toUInt16 = u := by
      apply UInt16.toNat_inj.mp
      simp only [Nat.toUInt16_eq, Nat.toUInt8_eq, UInt16.toNat_ofNat', UInt8.toNat_ofNat']
      omega
    simp only [unitsToBytesLE, bytesToUnitsLE?, ih, hu, Option.map_eq_map, Option.map_some]

theorem unitsToBytesLE_of_bytesToUnitsLE? {bs : List UInt8} {us : List UInt16}
    (h : bytesToUnitsLE? bs = some us) : unitsToBytesLE us = bs := by
  fun_induction bytesToUnitsLE? bs generalizing us with
  | case1 => cases h; rfl
  | case2 => cases h
  | case3 lo hi bs ih =>
    simp only [Option.map_eq_map, Option.map_eq_some_iff] at h
    obtain ⟨us', h', rfl⟩ := h
    have hl : lo.toNat < 256 := lo.toNat_lt
    have hh : hi.toNat < 256 := hi.toNat_lt
    have hv : ((lo.toNat + 256 * hi.toNat).toUInt16).toNat = lo.toNat + 256 * hi.toNat := by
      simp only [Nat.toUInt16_eq, UInt16.toNat_ofNat']; omega
    have h1 : (((lo.toNat + 256 * hi.toNat).toUInt16).toNat % 256).toUInt8 = lo := by
      apply UInt8.toNat_inj.mp
      simp only [hv, Nat.toUInt8_eq, UInt8.toNat_ofNat']; omega
    have h2 : (((lo.toNat + 256 * hi.toNat).toUInt16).toNat / 256).toUInt8 = hi := by
      apply UInt8.toNat_inj.mp
      simp only [hv, Nat.toUInt8_eq, UInt8.toNat_ofNat']; omega
    simp only [unitsToBytesLE, h1, h2, ih h']

theorem utf16Units_length (s : String) : (utf16Units s).length = utf16Length s := by
  simp only [utf16Units, utf16Length]
  induction s.toList with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, ih, List.map_cons, List.sum_cons]
    unfold utf16EncodeChar utf16CharLength
    split <;> simp

theorem unitsToBytesLE_length (us : List UInt16) : (unitsToBytesLE us).length = 2 * us.length := by
  induction us with
  | nil => rfl
  | cons u us ih => simp only [unitsToBytesLE, List.length_cons, ih]; omega

theorem utf16Encode_length (s : String) : (utf16Encode s).length = 2 * utf16Length s := by
  simp only [utf16Encode, unitsToBytesLE_length, utf16Units_length]

theorem utf16Decode?_utf16Encode (s : String) : utf16Decode? (utf16Encode s) = some s := by
  simp [utf16Decode?, utf16Encode, bytesToUnitsLE?_unitsToBytesLE, utf16Units,
    utf16DecodeUnits?_flatMap]

theorem utf16Decode?_eq_some_iff {bs : List UInt8} {s : String} :
    utf16Decode? bs = some s ↔ utf16Encode s = bs := by
  constructor
  · intro h
    simp only [utf16Decode?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨us, hus, cs, hcs, rfl⟩ := h
    simp only [utf16Encode, utf16Units, String.toList_ofList, flatMap_of_utf16DecodeUnits? hcs,
      unitsToBytesLE_of_bytesToUnitsLE? hus]
  · rintro rfl; exact utf16Decode?_utf16Encode s

/-! ## Latin-1 -/

theorem latin1Decode_latin1Encode {s : String} (h : isLatin1 s = true) :
    latin1Decode (latin1Encode s) = s := by
  simp only [isLatin1, List.all_eq_true, decide_eq_true_eq] at h
  simp only [latin1Decode, latin1Encode, List.map_map]
  conv => rhs; rw [← String.ofList_toList (s := s)]
  congr 1
  refine (List.map_congr_left (g := id) fun c hc => ?_).trans (List.map_id _)
  have := h c hc
  simp only [Function.comp_apply, Nat.toUInt8_eq, UInt8.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (by omega), Char.ofNat_toNat, id]

theorem latin1Decode_toList (bs : List UInt8) :
    (latin1Decode bs).toList = bs.map (Char.ofNat ·.toNat) := String.toList_ofList

private theorem toNat_ofNat_uint8 (b : UInt8) : (Char.ofNat b.toNat).toNat = b.toNat := by
  have : b.toNat < 256 := b.toNat_lt
  exact char_toNat_ofNat_of_valid (by omega)

theorem latin1Encode_latin1Decode (bs : List UInt8) : latin1Encode (latin1Decode bs) = bs := by
  simp only [latin1Encode, latin1Decode_toList, List.map_map]
  refine (List.map_congr_left (g := id) fun b _ => ?_).trans (List.map_id _)
  simp only [Function.comp_apply, id, toNat_ofNat_uint8, Nat.toUInt8_eq, UInt8.ofNat_toNat]

theorem isLatin1_latin1Decode (bs : List UInt8) : isLatin1 (latin1Decode bs) = true := by
  simp only [isLatin1, latin1Decode_toList, List.all_map, List.all_eq_true, Function.comp_apply,
    toNat_ofNat_uint8, decide_eq_true_eq]
  intro b _; exact b.toNat_lt

theorem latin1Decode_length (bs : List UInt8) : (latin1Decode bs).length = bs.length := by
  rw [← String.length_toList, latin1Decode_toList, List.length_map]

theorem latin1Encode_length (s : String) : (latin1Encode s).length = s.length := by
  simp only [latin1Encode, List.length_map, String.length_toList]

/-! ## Lengths and worst-case sizes -/

private theorem sum_map_le {l : List Char} {f g : Char → Nat} (h : ∀ c ∈ l, f c ≤ g c) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h c (by simp)
    have := ih fun d hd => h d (by simp [hd])
    omega

private theorem sum_map_mul (l : List Char) (f : Char → Nat) (k : Nat) :
    (l.map fun c => k * f c).sum = k * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons c cs ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

private theorem length_eq_sum (s : String) : s.length = (s.toList.map fun _ => 1).sum := by
  rw [← String.length_toList]
  induction s.toList with
  | nil => rfl
  | cons c cs ih => simp only [List.length_cons, ih, List.map_cons, List.sum_cons]; omega

theorem utf16CharLength_le_utf8Size (c : Char) : utf16CharLength c ≤ c.utf8Size := by
  rw [char_utf8Size_eq_of_toNat, utf16CharLength]; split_ifs <;> omega

theorem utf8Size_le_three_mul_utf16CharLength (c : Char) : c.utf8Size ≤ 3 * utf16CharLength c := by
  rw [char_utf8Size_eq_of_toNat, utf16CharLength]; split_ifs <;> omega

theorem length_le_utf16Length (s : String) : s.length ≤ utf16Length s := by
  rw [length_eq_sum, utf16Length]
  exact sum_map_le fun c _ => by unfold utf16CharLength; split <;> omega

/-- `store_utf8_to_utf16` allocates `2 * src_code_units` bytes, and
`store_string_to_latin1_or_utf16` inflates to `2 * src_code_units` bytes, for a
UTF-8 source. -/
theorem utf16Length_le_utf8Length (s : String) : utf16Length s ≤ (utf8Encode s).length := by
  rw [utf8Encode_length, utf16Length]
  exact sum_map_le fun c _ => utf16CharLength_le_utf8Size c

theorem length_le_utf8Length (s : String) : s.length ≤ (utf8Encode s).length :=
  Nat.le_trans (length_le_utf16Length s) (utf16Length_le_utf8Length s)

/-- `store_utf16_to_utf8` reallocates to `src_code_units * 3` bytes. -/
theorem utf8Length_le_three_mul_utf16Length (s : String) :
    (utf8Encode s).length ≤ 3 * utf16Length s := by
  rw [utf8Encode_length, utf16Length, ← sum_map_mul]
  exact sum_map_le fun c _ => utf8Size_le_three_mul_utf16CharLength c

/-- `store_latin1_to_utf8` reallocates to `src_code_units * 2` bytes. -/
theorem utf8Length_le_two_mul_length {s : String} (h : isLatin1 s = true) :
    (utf8Encode s).length ≤ 2 * s.length := by
  simp only [isLatin1, List.all_eq_true, decide_eq_true_eq] at h
  rw [utf8Encode_length, length_eq_sum, ← sum_map_mul]
  refine sum_map_le fun c hc => ?_
  have := h c hc
  rw [char_utf8Size_eq_of_toNat]; split_ifs <;> omega

theorem utf16Length_eq_length {s : String} (h : isLatin1 s = true) : utf16Length s = s.length := by
  simp only [isLatin1, List.all_eq_true, decide_eq_true_eq] at h
  rw [utf16Length, length_eq_sum]
  congr 1
  apply List.map_congr_left
  intro c hc
  have := h c hc
  simp only [utf16CharLength]; split <;> omega

theorem prefixBelow_le_length (b : Nat) (s : String) : prefixBelow b s ≤ s.length := by
  rw [prefixBelow, ← String.length_toList]
  exact (List.takeWhile_sublist _).length_le

/-! ## Loading -/

/-- Values produced by `load_string_from_range` satisfy the code-unit assertions
of the store functions. -/
theorem loadStringFromRange?_consistent {enc : StringEncoding} {a : AddrType} {mem : List UInt8}
    {ptr tagged : Nat} {v : StringValue} (h : loadStringFromRange? enc a mem ptr tagged = some v) :
    v.Consistent a := by
  simp only [loadStringFromRange?] at h
  split_ifs at h with h1 h2 h3
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨s, hs, rfl⟩ := h
  have hlen : ((mem.drop ptr).take (loadRange enc a tagged).byteLength).length =
      (loadRange enc a tagged).byteLength := by
    simp only [List.length_take, List.length_drop]; omega
  revert hs hlen
  generalize (mem.drop ptr).take (loadRange enc a tagged).byteLength = bs
  intro hs hlen
  cases enc with
  | utf8 =>
    simp only [loadRange, Codec.decode?] at hs hlen
    simp only [StringValue.Consistent, (utf8Decode?_eq_some_iff.mp hs), hlen]
  | utf16 =>
    simp only [loadRange, Codec.decode?] at hs hlen
    have := utf16Encode_length s
    rw [utf16Decode?_eq_some_iff.mp hs] at this
    simp only [StringValue.Consistent]; omega
  | latin1Utf16 =>
    simp only [StringValue.Consistent]
    by_cases ht : isUtf16Tagged a tagged = true
    · simp only [loadRange, ht, ↓reduceIte, Codec.decode?] at hs hlen ⊢
      have := utf16Encode_length s
      rw [utf16Decode?_eq_some_iff.mp hs] at this
      omega
    · simp only [loadRange, ht, Bool.false_eq_true, ↓reduceIte, Codec.decode?,
        Option.some.injEq] at hs hlen ⊢
      subst hs
      exact ⟨by rw [latin1Decode_length, hlen], isLatin1_latin1Decode bs⟩

/-! ## Store plans stay within their buffers -/

theorem storeStringCopy_inBounds {bs : List UInt8} {n u : Nat} {al : Alignment}
    (h : bs.length ≤ u * n) : (storeStringCopy bs n u al).InBounds := by
  simp [StorePlan.InBounds, storeStringCopy, stepsInBounds, h]

theorem storeStringToUtf8_inBounds {s : String} {n worst : Nat} (hn : s.length ≤ n)
    (hnw : n ≤ worst) (hw : (utf8Encode s).length ≤ worst) :
    (storeStringToUtf8 s n worst).InBounds := by
  have hi := prefixBelow_le_length 0x80 s
  simp only [StorePlan.InBounds, storeStringToUtf8]
  split
  · simp [stepsInBounds]; omega
  · split <;> simp [stepsInBounds] <;> omega

theorem storeUtf8ToUtf16_inBounds {s : String} {n : Nat} (h : utf16Length s ≤ n) :
    (storeUtf8ToUtf16 s n).InBounds := by
  have := utf16Encode_length s
  simp only [StorePlan.InBounds, storeUtf8ToUtf16]
  split <;> simp [stepsInBounds] <;> omega

theorem storeStringToLatin1OrUtf16_inBounds {a : AddrType} {s : String} {n : Nat}
    (hn : s.length ≤ n) (h : utf16Length s ≤ n) :
    (storeStringToLatin1OrUtf16 a s n).InBounds := by
  have := utf16Encode_length s
  have := latin1Encode_length s
  have hi := prefixBelow_le_length 0x100 s
  simp only [StorePlan.InBounds, storeStringToLatin1OrUtf16]
  split
  · split <;> simp [stepsInBounds] <;> omega
  · split <;> simp [stepsInBounds] <;> omega

theorem storeProbablyUtf16ToLatin1OrUtf16_inBounds {a : AddrType} {s : String} {n : Nat}
    (h : utf16Length s ≤ n) : (storeProbablyUtf16ToLatin1OrUtf16 a s n).InBounds := by
  have := utf16Encode_length s
  simp only [StorePlan.InBounds, storeProbablyUtf16ToLatin1OrUtf16]
  split <;> simp [stepsInBounds] <;> omega

/-- For values whose code-unit hint agrees with their text, each write and each
inflation/deflation of `store_string_into_range` stays within the most recent
realloc result and the most recent bounds check: the Python worst-case sizes
are sound. -/
theorem storeStringIntoRange_inBounds (dst : StringEncoding) {a : AddrType} {v : StringValue}
    (h : v.Consistent a) : (storeStringIntoRange dst a v).InBounds := by
  rcases v with ⟨s, enc, n⟩
  have := length_le_utf16Length s
  have := utf16Length_le_utf8Length s
  have := utf8Length_le_three_mul_utf16Length s
  have := utf16Encode_length s
  have := latin1Encode_length s
  cases enc <;> simp only [StringValue.Consistent] at h
  · cases dst <;> simp only [storeStringIntoRange, StringValue.simpleCodec, StringValue.codeUnits]
    · exact storeStringCopy_inBounds (by omega)
    · exact storeUtf8ToUtf16_inBounds (by omega)
    · exact storeStringToLatin1OrUtf16_inBounds (by omega) (by omega)
  · cases dst <;> simp only [storeStringIntoRange, StringValue.simpleCodec, StringValue.codeUnits]
    · exact storeStringToUtf8_inBounds (by omega) (by omega) (by omega)
    · exact storeStringCopy_inBounds (by omega)
    · exact storeStringToLatin1OrUtf16_inBounds (by omega) (by omega)
  · by_cases ht : isUtf16Tagged a n = true
    · simp only [ht, ↓reduceIte] at h
      cases dst <;> simp only [storeStringIntoRange, StringValue.simpleCodec,
        StringValue.codeUnits, ht, ↓reduceIte]
      · exact storeStringToUtf8_inBounds (by omega) (by omega) (by omega)
      · exact storeStringCopy_inBounds (by omega)
      · exact storeProbablyUtf16ToLatin1OrUtf16_inBounds (by omega)
    · simp only [ht, Bool.false_eq_true, ↓reduceIte] at h
      have := utf8Length_le_two_mul_length h.2
      have := utf16Length_eq_length h.2
      cases dst <;> simp only [storeStringIntoRange, StringValue.simpleCodec,
        StringValue.codeUnits, ht, Bool.false_eq_true, ↓reduceIte]
      · exact storeStringToUtf8_inBounds (by omega) (by omega) (by omega)
      · exact storeStringCopy_inBounds (by omega)
      · exact storeStringCopy_inBounds (by omega)

/-! ## Realloc sizes -/

theorem storeStringCopy_requestSizes (bs : List UInt8) (n u : Nat) (al : Alignment) :
    (storeStringCopy bs n u al).requestSizes = [u * n] := rfl

theorem storeStringToUtf8_requestSize_le {s : String} {n worst : Nat} (hnw : n ≤ worst)
    (hw : (utf8Encode s).length ≤ worst) :
    ∀ m ∈ (storeStringToUtf8 s n worst).requestSizes, m ≤ worst := by
  intro m hm
  simp only [StorePlan.requestSizes, storeStringToUtf8] at hm
  split at hm
  · simp at hm; omega
  · split at hm <;> simp at hm <;> omega

theorem storeUtf8ToUtf16_requestSize_le (s : String) (n : Nat) :
    ∀ m ∈ (storeUtf8ToUtf16 s n).requestSizes, m ≤ 2 * n := by
  intro m hm
  simp only [StorePlan.requestSizes, storeUtf8ToUtf16] at hm
  split at hm <;> simp at hm <;> omega

theorem storeStringToLatin1OrUtf16_requestSize_le (a : AddrType) (s : String) (n : Nat) :
    ∀ m ∈ (storeStringToLatin1OrUtf16 a s n).requestSizes, m ≤ 2 * n := by
  have := utf16Encode_length s
  have := prefixBelow_le_length 0x100 s
  intro m hm
  simp only [StorePlan.requestSizes, storeStringToLatin1OrUtf16] at hm
  split at hm
  · split at hm <;> simp at hm <;> omega
  · split at hm <;> simp at hm <;> omega

theorem storeProbablyUtf16ToLatin1OrUtf16_requestSize_le {a : AddrType} {s : String} {n : Nat}
    (h : utf16Length s ≤ n) :
    ∀ m ∈ (storeProbablyUtf16ToLatin1OrUtf16 a s n).requestSizes, m ≤ 2 * n := by
  have := utf16Encode_length s
  intro m hm
  simp only [StorePlan.requestSizes, storeProbablyUtf16ToLatin1OrUtf16] at hm
  split at hm <;> simp at hm <;> omega

/-- Every realloc of `store_string_into_range` on a consistent value requests at
most three bytes per source code unit. -/
theorem storeStringIntoRange_requestSize_le (dst : StringEncoding) {a : AddrType}
    {v : StringValue} (h : v.Consistent a) :
    ∀ m ∈ (storeStringIntoRange dst a v).requestSizes, m ≤ 3 * v.codeUnits a := by
  intro m hm
  rcases v with ⟨s, enc, n⟩
  have := length_le_utf16Length s
  have := utf16Length_le_utf8Length s
  have := utf8Length_le_three_mul_utf16Length s
  cases enc <;> simp only [StringValue.Consistent] at h
  · cases dst <;> simp only [storeStringIntoRange, StringValue.simpleCodec,
      StringValue.codeUnits] at hm ⊢
    · simp only [storeStringCopy_requestSizes, List.mem_singleton] at hm; omega
    · have := storeUtf8ToUtf16_requestSize_le s n m hm; omega
    · have := storeStringToLatin1OrUtf16_requestSize_le a s n m hm; omega
  · cases dst <;> simp only [storeStringIntoRange, StringValue.simpleCodec,
      StringValue.codeUnits] at hm ⊢
    · rw [storeUtf16ToUtf8] at hm
      have := storeStringToUtf8_requestSize_le (s := s) (worst := _ * 3) (by omega) (by omega) m hm
      omega
    · simp only [storeStringCopy_requestSizes, List.mem_singleton] at hm; omega
    · have := storeStringToLatin1OrUtf16_requestSize_le a s n m hm; omega
  · by_cases ht : isUtf16Tagged a n = true
    · simp only [ht, ↓reduceIte] at h
      cases dst <;> simp only [storeStringIntoRange, StringValue.simpleCodec,
        StringValue.codeUnits, ht, ↓reduceIte] at hm ⊢
      · rw [storeUtf16ToUtf8] at hm
        have := storeStringToUtf8_requestSize_le (s := s) (worst := _ * 3) (by omega) (by omega) m hm
        omega
      · simp only [storeStringCopy_requestSizes, List.mem_singleton] at hm; omega
      · have := storeProbablyUtf16ToLatin1OrUtf16_requestSize_le (a := a) (by omega) m hm
        omega
    · simp only [ht, Bool.false_eq_true, ↓reduceIte] at h
      have := utf8Length_le_two_mul_length h.2
      cases dst <;> simp only [storeStringIntoRange, StringValue.simpleCodec,
        StringValue.codeUnits, ht, Bool.false_eq_true, ↓reduceIte] at hm ⊢
      · rw [storeLatin1ToUtf8] at hm
        have := storeStringToUtf8_requestSize_le (s := s) (worst := _ * 2) (by omega) (by omega) m hm
        omega
      · simp only [storeStringCopy_requestSizes, List.mem_singleton] at hm; omega
      · simp only [storeStringCopy_requestSizes, List.mem_singleton] at hm; omega

/-- The Python `assert(... <= REALLOC_I32_MAX)` checks of the store functions hold
for consistent values within `MAX_STRING_BYTE_LENGTH` code units (as every loaded
value is, by the load-side trap). -/
theorem storeStringIntoRange_requestSize_le_reallocI32Max (dst : StringEncoding)
    {a : AddrType} {v : StringValue} (h : v.Consistent a)
    (hmax : v.codeUnits a ≤ maxStringByteLength) :
    ∀ m ∈ (storeStringIntoRange dst a v).requestSizes, m ≤ reallocI32Max := by
  intro m hm
  have := storeStringIntoRange_requestSize_le dst h m hm
  simp only [maxStringByteLength, reallocI32Max] at hmax ⊢
  omega

end Silmaril.Wasm.Component.ABI
