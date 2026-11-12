module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.SExp.Escape

/-!
# `escape` and `unescape?` are mutually inverse

`spectec --ast` prints every text and identifier as
`Atom ("\"" ^ String.escaped t ^ "\"")` (`spectec/src/backend-ast/print.ml:12`).
`Silmaril.SpecTec.Escape.escape` transcribes `String.escaped` and
`unescape?` is meant to be its exact inverse: it accepts a `\DDD` escape only
for the bytes that `escapeByte` renders that way.

This file proves that intent.  The two headline results are

* `unescape?_escape`, `unquote?_quote` — every escaped text decodes back, and
* `escape_of_unescape?`, `quote_of_unquote?` — everything that decodes is an
  escaped text,

so `escape` (resp. `quote`) is a bijection onto the image of `unescape?`
(resp. `unquote?`), which is what an encoding relation needs.  `escape_eq`
and `escapeChar_eq` additionally relate the kernel-friendly, per-scalar
`escapeChar` to the byte-level `escapeBytes ∘ Silmaril.Unicode.utf8`.

The decoder lemmas are proved by functional induction on `unescapeBytes?`,
whose cases line up one-for-one with the branches of `escapeByte`.
-/

@[expose] public section

namespace Silmaril.SpecTec.Escape

/-! ## Decimal digits -/

/-- `Char.ofNat` round-trips on the ASCII range. -/
theorem toNat_ofNat_of_le {n : Nat} (h : n ≤ 127) : (Char.ofNat n).toNat = n := by
  have hv : n.isValidChar := Or.inl (by omega)
  unfold Char.ofNat
  rw [dite_eq_left_of_eq_true (by simpa using hv)]
  simp [Char.ofNatAux]

/-- `digitChar k` is the ASCII digit with code point `k + 48`. -/
theorem toNat_digitChar {k : Nat} (h : k < 10) : (digitChar k).toNat = k + 48 := by
  rw [digitChar, toNat_ofNat_of_le (by omega)]

/-- `digitVal?` inverts `digitChar` on `k < 10`. -/
theorem digitVal?_digitChar {k : Nat} (h : k < 10) : digitVal? (digitChar k) = some k := by
  rw [digitVal?, toNat_digitChar h]
  split
  · congr 1
  · omega

/-- `digitChar` inverts `digitVal?`: anything `digitVal?` accepts is a digit. -/
theorem digitChar_eq_of_digitVal? {c : Char} {k : Nat} (h : digitVal? c = some k) :
    digitChar k = c ∧ k < 10 := by
  rw [digitVal?] at h
  split at h
  · rename_i hc
    obtain rfl := Option.some.inj h
    exact ⟨by rw [digitChar, show c.toNat - 48 + 48 = c.toNat by omega, Char.ofNat_toNat],
      by omega⟩
  · exact absurd h (by simp)

/-- A digit is distinct from any character outside the ASCII digit range; this
is what rules out confusing the first digit of a `\DDD` escape with one of the
two-character escapes `\"`, `\\`, `\n`, `\t`, `\r`, `\b`. -/
theorem digitChar_ne {k : Nat} (hk : k < 10) {c : Char} (hc : c.toNat < 48 ∨ 57 < c.toNat) :
    digitChar k ≠ c := by
  intro h
  have h' := toNat_digitChar hk
  rw [h] at h'
  omega

/-- `IsNamed` is exactly the six listed code points. -/
theorem not_isNamed {n : Nat} (h1 : n ≠ 34) (h2 : n ≠ 92) (h3 : n ≠ 10) (h4 : n ≠ 9)
    (h5 : n ≠ 13) (h6 : n ≠ 8) : ¬ IsNamed n := by
  rintro (h | h | h | h | h | h) <;> omega

/-! ## `unescapeBytes?` inverts `escapeBytes` -/

/-- The key local lemma: `unescapeBytes?` consumes exactly the characters that
`escapeByte b` produced, and yields `b`. -/
theorem unescapeBytes?_escapeByte (b : UInt8) (rest : List Char) :
    unescapeBytes? (escapeByte b ++ rest) = (b :: ·) <$> unescapeBytes? rest := by
  have hb : b.toNat < 256 := UInt8.toNat_lt_size b
  simp only [escapeByte]
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  · obtain rfl : b = 34 := UInt8.toNat_inj.mp h1
    rw [List.cons_append, List.cons_append, List.nil_append, unescapeBytes?.eq_def]; simp
  · obtain rfl : b = 92 := UInt8.toNat_inj.mp h2
    rw [List.cons_append, List.cons_append, List.nil_append, unescapeBytes?.eq_def]; simp
  · obtain rfl : b = 10 := UInt8.toNat_inj.mp h3
    rw [List.cons_append, List.cons_append, List.nil_append, unescapeBytes?.eq_def]; simp
  · obtain rfl : b = 9 := UInt8.toNat_inj.mp h4
    rw [List.cons_append, List.cons_append, List.nil_append, unescapeBytes?.eq_def]; simp
  · obtain rfl : b = 13 := UInt8.toNat_inj.mp h5
    rw [List.cons_append, List.cons_append, List.nil_append, unescapeBytes?.eq_def]; simp
  · obtain rfl : b = 8 := UInt8.toNat_inj.mp h6
    rw [List.cons_append, List.cons_append, List.nil_append, unescapeBytes?.eq_def]; simp
  · have hnm : ¬ IsNamed b.toNat := not_isNamed h1 h2 h3 h4 h5 h6
    have hcn : (Char.ofNat b.toNat).toNat = b.toNat := toNat_ofNat_of_le (by omega)
    have hne : Char.ofNat b.toNat ≠ '\\' := by
      intro hh
      have h92 : ('\\' : Char).toNat = 92 := by decide
      have hc := congrArg Char.toNat hh
      rw [hcn, h92] at hc
      exact h2 hc
    have hlit : IsLiteral b.toNat := ⟨h7.1, h7.2, hnm⟩
    rw [List.cons_append, List.nil_append, unescapeBytes?.eq_def]
    simp [hne, hcn, hlit]
  · have hnm : ¬ IsNamed b.toNat := not_isNamed h1 h2 h3 h4 h5 h6
    have hd : IsDecimal b.toNat := ⟨hb, hnm, fun hl => h7 ⟨hl.1, hl.2.1⟩⟩
    have k1 : b.toNat / 100 < 10 := by omega
    have k2 : b.toNat / 10 % 10 < 10 := by omega
    have k3 : b.toNat % 10 < 10 := by omega
    rw [List.cons_append, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
      unescapeBytes?.eq_def]
    simp only [digitChar_ne k1 (by decide : ('"'.toNat < 48 ∨ 57 < '"'.toNat)),
      digitChar_ne k1 (by decide : ('\\'.toNat < 48 ∨ 57 < '\\'.toNat)),
      digitChar_ne k1 (by decide : ('n'.toNat < 48 ∨ 57 < 'n'.toNat)),
      digitChar_ne k1 (by decide : ('t'.toNat < 48 ∨ 57 < 't'.toNat)),
      digitChar_ne k1 (by decide : ('r'.toNat < 48 ∨ 57 < 'r'.toNat)),
      digitChar_ne k1 (by decide : ('b'.toNat < 48 ∨ 57 < 'b'.toNat)),
      digitVal?_digitChar k1, digitVal?_digitChar k2, digitVal?_digitChar k3,
      show b.toNat / 100 * 100 + b.toNat / 10 % 10 * 10 + b.toNat % 10 = b.toNat by omega,
      hd, UInt8.ofNat_toNat]
    simp

/-- `unescapeBytes?` decodes every escaped byte string. -/
theorem unescapeBytes?_escapeBytes (bs : List UInt8) :
    unescapeBytes? (escapeBytes bs) = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => rw [escapeBytes, unescapeBytes?_escapeByte, ih]; rfl

/-- `String.escaped` is injective on byte strings. -/
theorem escapeBytes_injective : Function.Injective escapeBytes := by
  intro bs cs h
  have h1 := unescapeBytes?_escapeBytes bs
  rw [h, unescapeBytes?_escapeBytes] at h1
  exact (Option.some.inj h1).symm

/-! ## `escapeChar` is `escapeBytes` on the UTF-8 encoding -/

/-- `escapeBytes` is the per-byte `escapeByte` lifted to lists. -/
theorem escapeBytes_eq_flatMap (bs : List UInt8) : escapeBytes bs = bs.flatMap escapeByte := by
  induction bs with
  | nil => rfl
  | cons b bs ih => rw [escapeBytes, ih, List.flatMap_cons]

/-- The kernel-friendly `escapeChar` agrees with escaping the UTF-8 bytes.

For a scalar below `U+0080` the UTF-8 encoding is the single byte
`String.utf8EncodeChar c = [c.val.toUInt8]`, so the seven leading branches of
`escapeChar` line up with those of `escapeByte`; above `U+007F` both sides take
the `\DDD` path byte by byte. -/
theorem escapeChar_eq (c : Char) : escapeChar c = escapeBytes (String.utf8EncodeChar c) := by
  rw [escapeBytes_eq_flatMap]
  by_cases hs : c.toNat ≤ 127
  · have hsize : c.utf8Size = 1 := by
      rw [Char.utf8Size_eq_one_iff, UInt32.le_iff_toNat_le]
      simpa using hs
    have henc := String.utf8EncodeChar_eq_singleton hsize
    have hn : (c.val.toUInt8).toNat = c.toNat := by
      rw [UInt32.toNat_toUInt8, Char.toNat_val]
      omega
    simp only [escapeChar]
    rw [henc]
    simp only [List.flatMap_singleton, escapeByte, hn, Char.ofNat_toNat]
    split_ifs <;> rfl
  · simp only [escapeChar]
    split_ifs with h1 h2 h3 h4 h5 h6 h7
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · rfl

/-- Escaping the UTF-8 bytes of a string is escaping its scalars one by one. -/
theorem escapeBytes_utf8 (s : String) :
    escapeBytes (Silmaril.Unicode.utf8 s) = s.toList.flatMap escapeChar := by
  rw [Silmaril.Unicode.utf8, String.toUTF8_eq_toByteArray, ← String.utf8Encode_toList,
    List.utf8Encode_eq_toByteArray, List.toList_data_toByteArray, escapeBytes_eq_flatMap, List.flatMap_assoc]
  simp only [← escapeBytes_eq_flatMap, ← escapeChar_eq]

/-- `escape` is `String.escaped` on the UTF-8 encoding, as the OCaml source
(which works on byte strings) intends. -/
theorem escape_eq (s : String) :
    escape s = String.ofList (escapeBytes (Silmaril.Unicode.utf8 s)) := by
  rw [escape, escapeBytes_utf8]

/-! ## `escape` / `unescape?` -/

/-- `unescape?` decodes every escaped string. -/
@[simp] theorem unescape?_escape (s : String) : unescape? (escape s) = some s := by
  rw [unescape?, escape_eq, String.toList_ofList, unescapeBytes?_escapeBytes]
  simp

/-- `String.escaped` is injective. -/
theorem escape_injective : Function.Injective escape := by
  intro s t h
  have h1 := unescape?_escape s
  rw [h, unescape?_escape] at h1
  exact (Option.some.inj h1).symm

/-! ## Soundness: `unescape?` accepts only escaped strings -/

/-- One step of the soundness induction: if the input starts with the escape of
`b` and the tail decodes soundly, so does the whole input. -/
theorem escapeBytes_of_step {cs rest : List Char} {bs : List UInt8} {b : UInt8}
    (hcs : cs = escapeByte b ++ rest)
    (ih : ∀ bs', unescapeBytes? rest = some bs' → escapeBytes bs' = rest)
    (h : unescapeBytes? cs = some bs) : escapeBytes bs = cs := by
  subst hcs
  rw [unescapeBytes?_escapeByte] at h
  cases hr : unescapeBytes? rest with
  | none => rw [hr] at h; simp at h
  | some bs' =>
    rw [hr] at h
    obtain rfl : bs = b :: bs' := (Option.some.inj h).symm
    rw [escapeBytes, ih bs' hr]

/-- `escapeByte` on a literal byte reproduces the character. -/
theorem escapeByte_ofNat_of_isLiteral {c : Char} (hl : IsLiteral c.toNat) :
    escapeByte (UInt8.ofNat c.toNat) = [c] := by
  have hle : c.toNat ≤ 126 := hl.2.1
  have hn : (UInt8.ofNat c.toNat).toNat = c.toNat := by
    simp only [UInt8.toNat_ofNat']; omega
  have hnm : ¬ IsNamed c.toNat := hl.2.2
  simp only [escapeByte, hn]
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  · exact absurd (Or.inl h1) hnm
  · exact absurd (Or.inr (Or.inl h2)) hnm
  · exact absurd (Or.inr (Or.inr (Or.inl h3))) hnm
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl h4)))) hnm
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))) hnm
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h6))))) hnm
  · rw [Char.ofNat_toNat]
  · exact absurd ⟨hl.1, hl.2.1⟩ h7

/-- `escapeByte` on a `\DDD` byte produces the three-digit escape. -/
theorem escapeByte_ofNat_of_isDecimal {n : Nat} (hd : IsDecimal n) :
    escapeByte (UInt8.ofNat n) =
      ['\\', digitChar (n / 100), digitChar (n / 10 % 10), digitChar (n % 10)] := by
  have hlt : n < 256 := hd.1
  have hn : (UInt8.ofNat n).toNat = n := by
    simp only [UInt8.toNat_ofNat']; omega
  have hnm : ¬ IsNamed n := hd.2.1
  simp only [escapeByte, hn]
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  · exact absurd (Or.inl h1) hnm
  · exact absurd (Or.inr (Or.inl h2)) hnm
  · exact absurd (Or.inr (Or.inr (Or.inl h3))) hnm
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl h4)))) hnm
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))) hnm
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h6))))) hnm
  · exact absurd ⟨h7.1, h7.2, hnm⟩ hd.2.2
  · rfl

/-- `unescapeBytes?` accepts exactly the image of `escapeBytes`: whatever it
decodes re-escapes to the original character list. -/
theorem escapeBytes_of_unescapeBytes? (cs : List Char) :
    ∀ bs, unescapeBytes? cs = some bs → escapeBytes bs = cs := by
  induction cs using unescapeBytes?.induct with
  | case1 =>
    intro bs h
    rw [unescapeBytes?.eq_1] at h
    obtain rfl := (Option.some.inj h).symm
    rfl
  | case2 => intro bs h; rw [unescapeBytes?.eq_def] at h; simp at h
  | case3 rest ih => exact fun bs h => escapeBytes_of_step (b := 34) rfl ih h
  | case4 rest _ ih => exact fun bs h => escapeBytes_of_step (b := 92) rfl ih h
  | case5 rest _ _ ih => exact fun bs h => escapeBytes_of_step (b := 10) rfl ih h
  | case6 rest _ _ _ ih => exact fun bs h => escapeBytes_of_step (b := 9) rfl ih h
  | case7 rest _ _ _ _ ih => exact fun bs h => escapeBytes_of_step (b := 13) rfl ih h
  | case8 rest _ _ _ _ _ ih => exact fun bs h => escapeBytes_of_step (b := 8) rfl ih h
  | case9 e _ _ _ _ _ _ d₂ d₃ rest a₁ a₂ a₃ hv₃ hv₂ hv₁ n hd ih =>
    intro bs h
    obtain ⟨he₁, hk₁⟩ := digitChar_eq_of_digitVal? hv₁
    obtain ⟨he₂, hk₂⟩ := digitChar_eq_of_digitVal? hv₂
    obtain ⟨he₃, hk₃⟩ := digitChar_eq_of_digitVal? hv₃
    refine escapeBytes_of_step (b := UInt8.ofNat n) ?_ ih h
    rw [escapeByte_ofNat_of_isDecimal hd]
    rw [show n / 100 = a₁ by omega, show n / 10 % 10 = a₂ by omega,
      show n % 10 = a₃ by omega, he₁, he₂, he₃]
    rfl
  | case10 e h₁ h₂ h₃ h₄ h₅ h₆ d₂ d₃ rest a₁ a₂ a₃ hv₃ hv₂ hv₁ n hd =>
    intro bs h
    have hd' : ¬ IsDecimal (a₁ * 100 + a₂ * 10 + a₃) := hd
    rw [unescapeBytes?.eq_def] at h
    simp only [h₁, h₂, h₃, h₄, h₅, h₆, hv₁, hv₂, hv₃, hd', reduceIte, reduceCtorEq] at h
  | case11 e h₁ h₂ h₃ h₄ h₅ h₆ d₂ d₃ rest hv =>
    intro bs h
    rw [unescapeBytes?.eq_def] at h
    cases hv₁ : digitVal? e <;> cases hv₂ : digitVal? d₂ <;> cases hv₃ : digitVal? d₃ <;>
      simp only [h₁, h₂, h₃, h₄, h₅, h₆, hv₁, hv₂, hv₃, reduceIte, reduceCtorEq] at h
    exact absurd h (fun _ => hv _ _ _ hv₁ hv₂ hv₃)
  | case12 e rest h₁ h₂ h₃ h₄ h₅ h₆ hv =>
    intro bs h
    rw [unescapeBytes?.eq_def] at h
    match rest, hv with
    | [], _ => simp only [h₁, h₂, h₃, h₄, h₅, h₆, reduceIte, reduceCtorEq] at h
    | [_], _ => simp only [h₁, h₂, h₃, h₄, h₅, h₆, reduceIte, reduceCtorEq] at h
    | _ :: _ :: _, hv => exact absurd rfl (fun hh => hv _ _ _ hh)
  | case13 e rest _ hl ih =>
    intro bs h
    refine escapeBytes_of_step (b := UInt8.ofNat e.toNat) ?_ ih h
    rw [escapeByte_ofNat_of_isLiteral hl]
    rfl
  | case14 e rest h₁ hl =>
    intro bs h
    rw [unescapeBytes?.eq_def] at h
    simp only [h₁, hl, reduceIte, reduceCtorEq] at h

/-- Soundness of `unescape?`: anything it accepts is an escaped string. -/
theorem escape_of_unescape? {s t : String} (h : unescape? s = some t) : escape t = s := by
  rw [unescape?, Option.bind_eq_some_iff] at h
  obtain ⟨bs, hbs, ht⟩ := h
  have h1 : escapeBytes bs = s.toList := escapeBytes_of_unescapeBytes? _ _ hbs
  have h2 : Silmaril.Unicode.utf8 t = bs := Silmaril.Unicode.utf8?_eq_some_iff.mp ht
  rw [escape_eq, h2, h1, String.ofList_toList]

/-! ## `quote` / `unquote?` -/

/-- `quote s` is the escaped text between two `"` characters
(`spectec/src/backend-ast/print.ml:12`). -/
theorem toList_quote (s : String) : (quote s).toList = '"' :: ((escape s).toList ++ ['"']) := by
  rw [quote]
  simp

/-- A quoted atom always starts with `"`; the IL decoder uses this to tell
quoted atoms from bare ones. -/
theorem quote_head (s : String) : (quote s).toList.head? = some '"' := by
  rw [toList_quote]; rfl

/-- Conversely, anything not starting with `"` is rejected by `unquote?`. -/
theorem unquote?_eq_none_of_head_ne {s : String} (h : s.toList.head? ≠ some '"') :
    unquote? s = none := by
  rw [unquote?.eq_def]
  split
  · rename_i rest heq
    exact absurd (by rw [heq]; rfl) h
  · rfl

/-- `unquote?` decodes every quoted atom. -/
@[simp] theorem unquote?_quote (s : String) : unquote? (quote s) = some s := by
  rw [unquote?.eq_def, toList_quote]
  simp

/-- `quote` is injective. -/
theorem quote_injective : Function.Injective quote := by
  intro s t h
  have h1 := unquote?_quote s
  rw [h, unquote?_quote] at h1
  exact (Option.some.inj h1).symm

/-- Soundness of `unquote?`: anything it accepts is a quoted atom. -/
theorem quote_of_unquote? {s t : String} (h : unquote? s = some t) : quote t = s := by
  rw [unquote?.eq_def] at h
  split at h
  · rename_i rest heq
    split at h
    · rename_i body hrev
      have he := escape_of_unescape? h
      have hr : rest = body.reverse ++ ['"'] := by
        rw [← List.reverse_reverse rest, hrev]; simp
      apply String.toList_injective
      rw [toList_quote, he, String.toList_ofList, heq, hr]
    · exact absurd h (by simp)
  · exact absurd h (by simp)

end Silmaril.SpecTec.Escape
