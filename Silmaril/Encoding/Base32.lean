module

public import Silmaril.Encoding.Base32Facts
public import Silmaril.Encoding.Carriers

/-!
# Base32 carrier maps

RFC 4648 base32 (§6) and base32hex (§7) relate byte strings to text through a
pair of carrier maps:

| map | direction | totality |
|-----|-----------|----------|
| `encode A padded` | `bytes ⇒ String` | total, injective |
| `decode? A padded` | `String ⇒ bytes` | exact partial inverse |

for an alphabet `A` (`Alphabet.std`, §6, or `Alphabet.hex`, §7) and a choice of
`'='` padding.  The input is cut into 5-byte groups, each spelled by 8 digits;
a final group of 1–4 bytes is spelled by 2, 4, 5 or 7 digits, padded with
`'='` to 8 characters when `padded`.  The decoder is strict: it rejects bad
lengths, characters outside the alphabet, misplaced padding and non-zero pad
bits (the canonical requirement of RFC 4648 §3.5), so it is exact
(`decode?_eq_some_iff`) and `base32Rel` is a partial bijection.

The group arithmetic lives in `Silmaril.Encoding.RadixFacts` and the final
block in `Silmaril.Encoding.Base32Facts`.
-/

@[expose] public section

open CategoryTheory

namespace Silmaril

namespace Base32

open Radix Radix.Alphabet Alphabet

variable (A : Alphabet)

/-! ## Encoder and decoder on characters -/

/-- Base32 digits of a byte string: 5-byte groups to 8 digits, then the final
block (`encLast`). -/
def encodeChars (padded : Bool) : List UInt8 → List Char
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest =>
    A.encGroup [b0, b1, b2, b3, b4] ++ encodeChars padded rest
  | bs => encLast A padded bs

/-- Strict base32 decoding of a digit sequence: 8-digit groups while more than
8 characters remain, then the final block (`decLast`). -/
def decodeChars (padded : Bool) : List Char → Option (List UInt8)
  | c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: rest =>
    (A.decGroup [c0, c1, c2, c3, c4, c5, c6, c7]).bind fun g =>
      (decodeChars padded (c8 :: rest)).map (g ++ ·)
  | cs => decLast A padded cs

theorem encodeChars_of_length_le (padded : Bool) :
    ∀ {bs : List UInt8}, bs.length ≤ 5 → encodeChars A padded bs = encLast A padded bs
  | [], _ | [_], _ | [_, _], _ | [_, _, _], _ | [_, _, _, _], _ => rfl
  | [b0, b1, b2, b3, b4], _ => by
    simp only [encodeChars, encLast, padding, length_encGroup]
    cases padded <;> simp [digitCount, encGroup, toDigits]
  | _ :: _ :: _ :: _ :: _ :: _ :: _, h => by simp at h

theorem decodeChars_of_length_le (padded : Bool) :
    ∀ {cs : List Char}, cs.length ≤ 8 → decodeChars A padded cs = decLast A padded cs
  | [], _ | [_], _ | [_, _], _ | [_, _, _], _ | [_, _, _, _], _ | [_, _, _, _, _], _
  | [_, _, _, _, _, _], _ | [_, _, _, _, _, _, _], _ | [_, _, _, _, _, _, _, _], _ => rfl
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h => by simp at h

theorem length_encodeChars (padded : Bool) :
    ∀ bs : List UInt8, (encodeChars A padded bs).length =
      if padded then 8 * ((bs.length + 4) / 5) else (8 * bs.length + 4) / 5
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => by
    have ih := length_encodeChars padded rest
    simp only [encodeChars, List.length_append, length_encGroup, ih]
    cases padded <;> simp [digitCount] <;> omega
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] => by
    rw [encodeChars_of_length_le A padded (by simp), length_encLast A]

theorem decodeChars_sound (padded : Bool) :
    ∀ (cs : List Char) (bs : List UInt8),
      decodeChars A padded cs = some bs → encodeChars A padded bs = cs
  | c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: rest, bs, h => by
    simp only [decodeChars, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨g, hg, r, hr, rfl⟩ := h
    have he := (A.decGroup_eq_some_iff (by decide) (by decide)).mp hg
    have ih := decodeChars_sound padded (c8 :: rest) r hr
    match g, length_encGroup_eq_eight A (bs := g) (by rw [he]; rfl) with
    | [b0, b1, b2, b3, b4], _ => simp [encodeChars, he, ih]
  | [], bs, h | [_], bs, h | [_, _], bs, h | [_, _, _], bs, h | [_, _, _, _], bs, h
  | [_, _, _, _, _], bs, h | [_, _, _, _, _, _], bs, h | [_, _, _, _, _, _, _], bs, h
  | [_, _, _, _, _, _, _, _], bs, h => by
    have he := (decLast_eq_some_iff A).mp h
    have hle := length_le_of_length_encLast A (padded := padded) (bs := bs) (by simp [he])
    rw [encodeChars_of_length_le A padded hle, he]

@[simp] theorem decodeChars_encodeChars (padded : Bool) :
    ∀ bs : List UInt8, decodeChars A padded (encodeChars A padded bs) = some bs
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: rest => by
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, he⟩ : ∃ c0 c1 c2 c3 c4 c5 c6 c7,
        A.encGroup [b0, b1, b2, b3, b4] = [c0, c1, c2, c3, c4, c5, c6, c7] := by
      have h8 : digitCount 5 [b0, b1, b2, b3, b4].length = 8 := by simp [digitCount]
      unfold encGroup
      rw [h8]
      exact ⟨_, _, _, _, _, _, _, _, rfl⟩
    have hd := (A.decGroup_eq_some_iff (by decide) (by decide)).mpr he
    have ih := decodeChars_encodeChars padded (b5 :: rest)
    have hlen := length_encodeChars A padded (b5 :: rest)
    rcases hr : encodeChars A padded (b5 :: rest) with _ | ⟨c8, r⟩
    · rw [hr] at hlen
      simp at hlen
      split at hlen <;> omega
    · rw [hr] at ih
      simp only [encodeChars, he, hr, List.cons_append, List.nil_append, decodeChars, hd,
        Option.bind_some, ih, Option.map_some]
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] => by
    rw [encodeChars_of_length_le A padded (by simp),
      decodeChars_of_length_le A padded (by rw [length_encLast]; cases padded <;> simp),
      (decLast_eq_some_iff A).mpr rfl]

theorem decodeChars_eq_some_iff (padded : Bool) {cs : List Char} {bs : List UInt8} :
    decodeChars A padded cs = some bs ↔ encodeChars A padded bs = cs :=
  ⟨decodeChars_sound A padded cs bs, fun h => h ▸ decodeChars_encodeChars A padded bs⟩

/-! ## Encoder and decoder on strings -/

/-- RFC 4648 base32 encoding of a byte string, in alphabet `A`, with `'='`
padding when `padded`. -/
def encode (padded : Bool) (bs : List UInt8) : String :=
  String.ofList (encodeChars A padded bs)

/-- Strict RFC 4648 base32 decoding: rejects bad lengths, characters outside
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

/-- Length: `8⌈n/5⌉` padded; `⌈8n/5⌉` unpadded. -/
theorem length_encode (padded : Bool) (bs : List UInt8) :
    (encode A padded bs).length =
      if padded then 8 * ((bs.length + 4) / 5) else (8 * bs.length + 4) / 5 := by
  rw [encode, String.length_ofList, length_encodeChars]

/-! ## RFC 4648 §10 test vectors -/

example : encode std true [] = "" := by decide
example : encode std true [0x66] = "MY======" := by decide +kernel
example : encode std true [0x66, 0x6f] = "MZXQ====" := by decide +kernel
example : encode std true [0x66, 0x6f, 0x6f] = "MZXW6===" := by decide +kernel
example : encode std true [0x66, 0x6f, 0x6f, 0x62] = "MZXW6YQ=" := by decide +kernel
example : encode std true [0x66, 0x6f, 0x6f, 0x62, 0x61] = "MZXW6YTB" := by decide +kernel
example : encode std true [0x66, 0x6f, 0x6f, 0x62, 0x61, 0x72] = "MZXW6YTBOI======" := by
  decide +kernel

example : encode hex true [] = "" := by decide
example : encode hex true [0x66] = "CO======" := by decide +kernel
example : encode hex true [0x66, 0x6f] = "CPNG====" := by decide +kernel
example : encode hex true [0x66, 0x6f, 0x6f] = "CPNMU===" := by decide +kernel
example : encode hex true [0x66, 0x6f, 0x6f, 0x62] = "CPNMUOG=" := by decide +kernel
example : encode hex true [0x66, 0x6f, 0x6f, 0x62, 0x61] = "CPNMUOJ1" := by decide +kernel
example : encode hex true [0x66, 0x6f, 0x6f, 0x62, 0x61, 0x72] = "CPNMUOJ1E8======" := by
  decide +kernel

example : decode? std true "MZXW6YTBOI======" = some [0x66, 0x6f, 0x6f, 0x62, 0x61, 0x72] := by
  decide +kernel
example : decode? hex true "CPNMUOG=" = some [0x66, 0x6f, 0x6f, 0x62] := by decide +kernel

/-- Unpadded spellings drop the `'='`s. -/
example : encode std false [0x66, 0x6f, 0x6f, 0x62, 0x61, 0x72] = "MZXW6YTBOI" := by
  decide +kernel
example : decode? std false "MZXW6YQ" = some [0x66, 0x6f, 0x6f, 0x62] := by decide +kernel

/-- Non-zero pad bits are rejected: `"MZ======"` would also spell `"f"` (`'Z'`
is `0b11001`, leaving pad bits `01`). -/
example : decode? std true "MZ======" = none := by decide +kernel
/-- Bad digit counts (1, 3 and 6 digits spell no byte count). -/
example : decode? std true "MZX=====" = none := by decide +kernel
example : decode? std false "MZXW6Y" = none := by decide +kernel
/-- Misplaced or missing padding, wrong padding mode, and bad characters. -/
example : decode? std true "MY=====A" = none := by decide +kernel
example : decode? std true "MY" = none := by decide +kernel
example : decode? std false "MY======" = none := by decide +kernel
example : decode? std true "MY======MY======" = none := by decide +kernel
example : decode? std true "my======" = none := by decide +kernel
example : decode? hex true "MY======" = none := by decide +kernel

/-! ## Encoding-theory glue -/

/-- Base32 as an encoding of byte strings by strings. -/
def base32Rel (padded : Bool) : EncRel String (List UInt8) :=
  EncRel.ofFun (encode A padded)

theorem base32Rel_bijective (padded : Bool) : (base32Rel A padded).Bijective :=
  ⟨fun _ _ _ h h' => encode_injective A padded (h.trans h'.symm),
    EncRel.ofFun_deterministic _⟩

/-- The base32 spellings of a byte format are the strings whose strict
decoding is a byte spelling. -/
theorem push_base32_eq {α : Type} (padded : Bool) (E : EncRel (List UInt8) α) :
    E.push (encode A padded) = E.pullPartial (decode? A padded) :=
  EncRel.push_eq_pullPartial (fun _ _ => decode?_eq_some_iff A) E

/-- Base32 preserves functionality of byte encodings. -/
theorem functional_push_base32 {α : Type} (padded : Bool) {E : EncRel (List UInt8) α}
    (hE : E.Functional) : (E.push (encode A padded)).Functional :=
  hE.push (encode_injective A padded)

/-- Byte encodings to text encodings, by base32. -/
abbrev base32Functor (padded : Bool) : EncCat (List UInt8) ⥤ EncCat String :=
  EncCat.pushFunctor (encode A padded)

/-- Text encodings to byte encodings, by strict base32 decoding. -/
abbrev base32DecodeFunctor (padded : Bool) : EncCat String ⥤ EncCat (List UInt8) :=
  EncCat.pushPartialFunctor (decode? A padded)

/-- Decoding after encoding base32 is the identity on encodings. -/
theorem base32Decode_base32 (padded : Bool) (X : EncCat (List UInt8)) :
    (base32DecodeFunctor A padded).obj ((base32Functor A padded).obj X) = X :=
  EncCat.pushPartialFunctor_obj_pushFunctor_obj (decode?_encode A padded) X

end Base32

end Silmaril
