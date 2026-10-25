module

public import Silmaril.Encoding.Base64Facts

/-!
# Base64 carrier maps

RFC 4648 base64 relates byte strings to text through a pair of carrier maps:

| map | direction | totality |
|-----|-----------|----------|
| `encode A padded` | `bytes ⇒ String` | total, injective |
| `decode? A padded` | `String ⇒ bytes` | exact partial inverse |

for an alphabet `A` (`Alphabet.std`, RFC 4648 §4, or `Alphabet.url`, §5) and a
choice of `'='` padding.  The decoder is strict: it rejects bad lengths,
characters outside the alphabet, misplaced padding, and non-zero pad bits
(the canonical requirement of RFC 4648 §3.5), so it is exact
(`decode?_eq_some_iff`) and `base64Rel` is a partial bijection.

Byte encodings become text encodings along `base64Functor`; the base64
spellings of a byte format are the strings whose strict decoding is a byte
spelling (`push_base64_eq`).  The group arithmetic lives in
`Silmaril.Encoding.Base64Facts`.
-/

@[expose] public section

open CategoryTheory

namespace Silmaril

namespace Base64

open Alphabet

variable (A : Alphabet)

/-! ## Encoder and decoder on characters -/

/-- Base64 digits of a byte string: 3-byte groups to 4 digits, a 1- or 2-byte
tail to 2 or 3 digits, plus `'='` padding when `padded`. -/
def encodeChars (padded : Bool) : List UInt8 → List Char
  | [] => []
  | [b0] => A.enc1 b0 ++ (if padded then ['=', '='] else [])
  | [b0, b1] => A.enc2 b0 b1 ++ (if padded then ['='] else [])
  | b0 :: b1 :: b2 :: rest => A.enc3 b0 b1 b2 ++ encodeChars padded rest

/-- Strict base64 decoding of a digit sequence. -/
def decodeChars (padded : Bool) : List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | [c0, c1] => if padded then none else A.dec2 c0 c1
  | [c0, c1, c2] => if padded then none else A.dec3 c0 c1 c2
  | [c0, c1, c2, c3] => if padded then A.decLast c0 c1 c2 c3 else A.dec4 c0 c1 c2 c3
  | c0 :: c1 :: c2 :: c3 :: c4 :: rest =>
    (A.dec4 c0 c1 c2 c3).bind fun g => (decodeChars padded (c4 :: rest)).map (g ++ ·)

theorem encodeChars_eq_nil_iff (padded : Bool) {bs : List UInt8} :
    encodeChars A padded bs = [] ↔ bs = [] := by
  match bs with
  | [] => simp [encodeChars]
  | [_] => simp [encodeChars, enc1]
  | [_, _] => simp [encodeChars, enc2]
  | _ :: _ :: _ :: _ => simp [encodeChars, enc3]

theorem decodeChars_sound (padded : Bool) :
    ∀ (cs : List Char) (bs : List UInt8),
      decodeChars A padded cs = some bs → encodeChars A padded bs = cs
  | [], bs, h => by
    simp only [decodeChars, Option.some.injEq] at h
    subst h
    rfl
  | [_], _, h => by simp [decodeChars] at h
  | [c0, c1], bs, h => by
    cases padded
    · simp only [decodeChars, Bool.false_eq_true, ite_false] at h
      obtain ⟨b0, rfl, he⟩ := (A.dec2_eq_some_iff).mp h
      simp [encodeChars, he]
    · simp [decodeChars] at h
  | [c0, c1, c2], bs, h => by
    cases padded
    · simp only [decodeChars, Bool.false_eq_true, ite_false] at h
      obtain ⟨b0, b1, rfl, he⟩ := (A.dec3_eq_some_iff).mp h
      simp [encodeChars, he]
    · simp [decodeChars] at h
  | [c0, c1, c2, c3], bs, h => by
    cases padded
    · simp only [decodeChars, Bool.false_eq_true, ite_false] at h
      obtain ⟨b0, b1, b2, rfl, he⟩ := (A.dec4_eq_some_iff).mp h
      simp [encodeChars, he]
    · simp only [decodeChars, ite_true, decLast] at h
      split_ifs at h with h3 h2
      · subst h3 h2
        obtain ⟨b0, rfl, he⟩ := (A.dec2_eq_some_iff).mp h
        simp [encodeChars, he]
      · subst h3
        obtain ⟨b0, b1, rfl, he⟩ := (A.dec3_eq_some_iff).mp h
        simp [encodeChars, he]
      · obtain ⟨b0, b1, b2, rfl, he⟩ := (A.dec4_eq_some_iff).mp h
        simp [encodeChars, he]
  | c0 :: c1 :: c2 :: c3 :: c4 :: rest, bs, h => by
    simp only [decodeChars, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨g, hg, r, hr, rfl⟩ := h
    obtain ⟨b0, b1, b2, rfl, he⟩ := (A.dec4_eq_some_iff).mp hg
    have ih := decodeChars_sound padded (c4 :: rest) r hr
    simp [encodeChars, he, ih]

@[simp] theorem decodeChars_encodeChars (padded : Bool) :
    ∀ bs : List UInt8, decodeChars A padded (encodeChars A padded bs) = some bs
  | [] => rfl
  | [b0] => by
    obtain ⟨c0, c1, he⟩ : ∃ c0 c1, A.enc1 b0 = [c0, c1] := ⟨_, _, rfl⟩
    have hd := (A.dec2_eq_some_iff).mpr ⟨b0, rfl, he⟩
    cases padded <;> simp [encodeChars, decodeChars, decLast, he, hd]
  | [b0, b1] => by
    obtain ⟨c0, c1, c2, he⟩ : ∃ c0 c1 c2, A.enc2 b0 b1 = [c0, c1, c2] := ⟨_, _, _, rfl⟩
    have hd := (A.dec3_eq_some_iff).mpr ⟨b0, b1, rfl, he⟩
    have h2 := A.enc2_ne_pad he
    cases padded <;> simp [encodeChars, decodeChars, decLast, he, hd, h2]
  | b0 :: b1 :: b2 :: rest => by
    obtain ⟨c0, c1, c2, c3, he⟩ : ∃ c0 c1 c2 c3, A.enc3 b0 b1 b2 = [c0, c1, c2, c3] :=
      ⟨_, _, _, _, rfl⟩
    have hd := (A.dec4_eq_some_iff).mpr ⟨b0, b1, b2, rfl, he⟩
    obtain ⟨h2, h3⟩ := A.enc3_ne_pad he
    have ih := decodeChars_encodeChars padded rest
    rcases hr : encodeChars A padded rest with _ | ⟨c4, r⟩
    · obtain rfl := (encodeChars_eq_nil_iff A padded).mp hr
      cases padded <;> simp [encodeChars, decodeChars, decLast, he, hd, h3]
    · rw [hr] at ih
      simp [encodeChars, decodeChars, he, hd, hr, ih]

theorem decodeChars_eq_some_iff (padded : Bool) {cs : List Char} {bs : List UInt8} :
    decodeChars A padded cs = some bs ↔ encodeChars A padded bs = cs :=
  ⟨decodeChars_sound A padded cs bs, fun h => h ▸ decodeChars_encodeChars A padded bs⟩

theorem length_encodeChars (padded : Bool) :
    ∀ bs : List UInt8, (encodeChars A padded bs).length =
      if padded then 4 * ((bs.length + 2) / 3)
      else 4 * (bs.length / 3) + (if bs.length % 3 = 0 then 0 else bs.length % 3 + 1)
  | [] => by cases padded <;> simp [encodeChars]
  | [_] => by cases padded <;> simp [encodeChars, enc1]
  | [_, _] => by cases padded <;> simp [encodeChars, enc2]
  | _ :: _ :: _ :: rest => by
    have ih := length_encodeChars padded rest
    simp only [encodeChars, enc3, List.length_append, List.length_cons, List.length_nil,
      ih]
    cases padded <;> simp <;> (try split_ifs) <;> omega

/-! ## Encoder and decoder on strings -/

/-- RFC 4648 base64 encoding of a byte string, in alphabet `A`, with `'='`
padding when `padded`. -/
def encode (padded : Bool) (bs : List UInt8) : String :=
  String.ofList (encodeChars A padded bs)

/-- Strict RFC 4648 base64 decoding: rejects bad lengths, characters outside
the alphabet, misplaced padding and non-zero pad bits. -/
def decode? (padded : Bool) (s : String) : Option (List UInt8) :=
  decodeChars A padded s.toList

/-- Exactness: the strict decoder is defined exactly on the encoder's image. -/
theorem decode?_eq_some_iff {padded : Bool} {s : String} {bs : List UInt8} :
    decode? A padded s = some bs ↔ encode A padded bs = s := by
  rw [decode?, decodeChars_eq_some_iff, encode]
  constructor
  · rintro h; rw [h, String.ofList_toList]
  · rintro rfl; rw [String.toList_ofList]

@[simp] theorem decode?_encode (padded : Bool) (bs : List UInt8) :
    decode? A padded (encode A padded bs) = some bs :=
  (decode?_eq_some_iff A).mpr rfl

theorem encode_injective (padded : Bool) : Function.Injective (encode A padded) := by
  intro b b' h
  have hb := decode?_encode A padded b
  rw [h, decode?_encode] at hb
  exact (Option.some.inj hb).symm

/-- Length: `4⌈n/3⌉` padded; `4⌊n/3⌋ + 0, 2, 3` (by `n % 3`) unpadded. -/
theorem length_encode (padded : Bool) (bs : List UInt8) :
    (encode A padded bs).length =
      if padded then 4 * ((bs.length + 2) / 3)
      else 4 * (bs.length / 3) + (if bs.length % 3 = 0 then 0 else bs.length % 3 + 1) := by
  rw [encode, String.length_ofList, length_encodeChars]

/-! ## RFC 4648 §10 test vectors -/

example : encode std true [] = "" := by decide
example : encode std true [0x66] = "Zg==" := by decide
example : encode std true [0x66, 0x6f] = "Zm8=" := by decide
example : encode std true [0x66, 0x6f, 0x6f] = "Zm9v" := by decide
example : encode std true [0x66, 0x6f, 0x6f, 0x62] = "Zm9vYg==" := by decide
example : encode std true [0x66, 0x6f, 0x6f, 0x62, 0x61] = "Zm9vYmE=" := by decide
example : encode std true [0x66, 0x6f, 0x6f, 0x62, 0x61, 0x72] = "Zm9vYmFy" := by decide

example : encode std false [] = "" := by decide
example : encode std false [0x66] = "Zg" := by decide
example : encode std false [0x66, 0x6f] = "Zm8" := by decide
example : encode std false [0x66, 0x6f, 0x6f] = "Zm9v" := by decide
example : encode std false [0x66, 0x6f, 0x6f, 0x62] = "Zm9vYg" := by decide
example : encode std false [0x66, 0x6f, 0x6f, 0x62, 0x61] = "Zm9vYmE" := by decide
example : encode std false [0x66, 0x6f, 0x6f, 0x62, 0x61, 0x72] = "Zm9vYmFy" := by decide

example : decode? std true "Zm9vYmE=" = some [0x66, 0x6f, 0x6f, 0x62, 0x61] := by decide
example : decode? std false "Zm9vYg" = some [0x66, 0x6f, 0x6f, 0x62] := by decide

/-- Non-zero pad bits are rejected: `"Zh=="` would also spell `"f"` (`'h'` is
`0b100001`, leaving pad bits `0001`). -/
example : decode? std true "Zh==" = none := by decide
example : decode? std true "Zm9=" = none := by decide
/-- Misplaced padding, wrong padding mode, and bad characters. -/
example : decode? std true "Zg=a" = none := by decide
example : decode? std true "Zg" = none := by decide
example : decode? std false "Zg==" = none := by decide
example : decode? std true "Zg==Zg==" = none := by decide
example : decode? std true "Z-8=" = none := by decide
example : decode? url true "_-8=" = some [0xff, 0xef] := by decide

/-! ## Encoding-theory glue -/

/-- Base64 as an encoding of byte strings by strings. -/
def base64Rel (padded : Bool) : EncRel String (List UInt8) :=
  EncRel.ofFun (encode A padded)

theorem base64Rel_bijective (padded : Bool) : (base64Rel A padded).Bijective :=
  ⟨fun _ _ _ h h' => encode_injective A padded (h.trans h'.symm),
    EncRel.ofFun_deterministic _⟩

/-- The base64 spellings of a byte format are the strings whose strict
decoding is a byte spelling. -/
theorem push_base64_eq {α : Type} (padded : Bool) (E : EncRel (List UInt8) α) :
    E.push (encode A padded) = E.pullPartial (decode? A padded) :=
  EncRel.push_eq_pullPartial (fun _ _ => decode?_eq_some_iff A) E

/-- Base64 preserves functionality of byte encodings. -/
theorem functional_push_base64 {α : Type} (padded : Bool) {E : EncRel (List UInt8) α}
    (hE : E.Functional) : (E.push (encode A padded)).Functional :=
  hE.push (encode_injective A padded)

/-- Byte encodings to text encodings, by base64. -/
abbrev base64Functor (padded : Bool) : EncCat (List UInt8) ⥤ EncCat String :=
  EncCat.pushFunctor (encode A padded)

/-- Text encodings to byte encodings, by strict base64 decoding. -/
abbrev base64DecodeFunctor (padded : Bool) : EncCat String ⥤ EncCat (List UInt8) :=
  EncCat.pushPartialFunctor (decode? A padded)

/-- Decoding after encoding base64 is the identity on encodings. -/
theorem base64Decode_base64 (padded : Bool) (X : EncCat (List UInt8)) :
    (base64DecodeFunctor A padded).obj ((base64Functor A padded).obj X) = X :=
  EncCat.pushPartialFunctor_obj_pushFunctor_obj (decode?_encode A padded) X

end Base64

end Silmaril
