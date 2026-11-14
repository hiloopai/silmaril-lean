module

public import Silmaril.Encoding.RadixFacts
public import Silmaril.Encoding.Carriers

/-!
# Base16 carrier maps

RFC 4648 base16 (§8, "hex") relates byte strings to text through a pair of
carrier maps:

| map | direction | totality |
|-----|-----------|----------|
| `encode A` | `bytes ⇒ String` | total, injective |
| `decode? A` | `String ⇒ bytes` | exact partial inverse |
| `decodeAnyCase?` | `String ⇒ bytes` | partial inverse of both cases |

Each byte is spelled by two digits of a radix-16 alphabet (`Alphabet.upper`,
RFC 4648 Table 5, or `Alphabet.lower`); no padding is needed.  The strict
decoder `decode? A` accepts exactly the spellings in `A` (`decode?_eq_some_iff`,
so `base16Rel` is a partial bijection), rejecting odd lengths and characters
outside `A`.  RFC 4648 §8 calls base16 case-insensitive: that reading is the
separate `decodeAnyCase?`, which accepts upper- and lower-case digits
(`decodeAnyCase?_eq_some_iff`) and so is not injective on strings.

The digit arithmetic is the radix group codec of
`Silmaril.Encoding.RadixFacts`, on one-byte groups.
-/

@[expose] public section

open CategoryTheory

namespace Silmaril

namespace Base16

open Radix Radix.Alphabet

/-- A base16 alphabet: 16 digit characters with an exact partial inverse, not
containing `'='`. -/
abbrev Alphabet := Radix.Alphabet 4

namespace Alphabet

/-- The base16 alphabet (RFC 4648 §8, Table 5): `0–9 A–F`. -/
def upper : Alphabet :=
  ofTable (fun i => if i.val < 10 then Char.ofNat (48 + i.val) else Char.ofNat (55 + i.val))
    (by decide) (by decide)

/-- The lower-case hex alphabet `0–9 a–f` (not RFC 4648 canonical). -/
def lower : Alphabet :=
  ofTable (fun i => if i.val < 10 then Char.ofNat (48 + i.val) else Char.ofNat (87 + i.val))
    (by decide) (by decide)

example : upper.digit 0 = '0' ∧ upper.digit 9 = '9' ∧ upper.digit 10 = 'A' ∧
    upper.digit 15 = 'F' ∧ upper.value? 'a' = none ∧ upper.value? 'G' = none := by decide

example : lower.digit 10 = 'a' ∧ lower.digit 15 = 'f' ∧ lower.value? 'A' = none := by decide

theorem toUpper_upper (i : Fin 16) : (upper.digit i).toUpper = upper.digit i := by
  revert i; decide

theorem toUpper_lower (i : Fin 16) : (lower.digit i).toUpper = upper.digit i := by
  revert i; decide

end Alphabet

variable (A : Alphabet)

/-! ## Encoder and decoder on characters -/

/-- Base16 digits of a byte string: two digits per byte. -/
def encodeChars : List UInt8 → List Char
  | [] => []
  | b :: bs => A.encGroup [b] ++ encodeChars bs

/-- Strict base16 decoding of a digit sequence. -/
def decodeChars : List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | c0 :: c1 :: rest =>
    (A.decGroup [c0, c1]).bind fun g => (decodeChars rest).map (g ++ ·)

theorem encGroup_singleton (b : UInt8) : ∃ c0 c1, A.encGroup [b] = [c0, c1] := by
  have h2 : digitCount 4 [b].length = 2 := by simp [digitCount]
  unfold encGroup
  rw [h2]
  exact ⟨_, _, rfl⟩

theorem decodeChars_sound : ∀ (cs : List Char) (bs : List UInt8),
    decodeChars A cs = some bs → encodeChars A bs = cs
  | [], bs, h => by
    simp only [decodeChars, Option.some.injEq] at h
    subst h
    rfl
  | [_], _, h => by simp [decodeChars] at h
  | c0 :: c1 :: rest, bs, h => by
    simp only [decodeChars, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨g, hg, r, hr, rfl⟩ := h
    have he := (A.decGroup_eq_some_iff (by decide) (by decide)).mp hg
    have hlen := congrArg List.length he
    rw [length_encGroup] at hlen
    simp only [digitCount, List.length_cons, List.length_nil] at hlen
    match g, (by omega : g.length = 1) with
    | [b], _ => simp [encodeChars, he, decodeChars_sound rest r hr]

@[simp] theorem decodeChars_encodeChars :
    ∀ bs : List UInt8, decodeChars A (encodeChars A bs) = some bs
  | [] => rfl
  | b :: bs => by
    obtain ⟨c0, c1, he⟩ := encGroup_singleton A b
    have hd := (A.decGroup_eq_some_iff (by decide) (by decide)).mpr he
    simp [encodeChars, decodeChars, he, hd, decodeChars_encodeChars bs]

theorem decodeChars_eq_some_iff {cs : List Char} {bs : List UInt8} :
    decodeChars A cs = some bs ↔ encodeChars A bs = cs :=
  ⟨decodeChars_sound A cs bs, fun h => h ▸ decodeChars_encodeChars A bs⟩

theorem length_encodeChars : ∀ bs : List UInt8, (encodeChars A bs).length = 2 * bs.length
  | [] => rfl
  | b :: bs => by
    obtain ⟨c0, c1, he⟩ := encGroup_singleton A b
    simp only [encodeChars, he, List.length_append, length_encodeChars bs, List.length_cons,
      List.length_nil]
    omega

theorem map_encodeChars {B : Alphabet} {f : Char → Char} (hf : ∀ i, f (A.digit i) = B.digit i) :
    ∀ bs : List UInt8, (encodeChars A bs).map f = encodeChars B bs
  | [] => rfl
  | b :: bs => by
    rw [encodeChars, List.map_append, map_encGroup A hf, map_encodeChars hf bs, encodeChars]

/-! ## Encoder and decoders on strings -/

/-- RFC 4648 base16 encoding of a byte string in alphabet `A`. -/
def encode (bs : List UInt8) : String :=
  String.ofList (encodeChars A bs)

/-- Strict base16 decoding: rejects odd lengths and characters outside `A`. -/
def decode? (s : String) : Option (List UInt8) :=
  decodeChars A s.toList

/-- Exactness: the strict decoder is defined exactly on the encoder's image. -/
theorem decode?_eq_some_iff {s : String} {bs : List UInt8} :
    decode? A s = some bs ↔ encode A bs = s := by
  rw [decode?, decodeChars_eq_some_iff, encode]
  constructor
  · rintro h; rw [h, String.ofList_toList]
  · rintro rfl; rw [String.toList_ofList]

@[simp] theorem decode?_encode (bs : List UInt8) : decode? A (encode A bs) = some bs :=
  (decode?_eq_some_iff A).mpr rfl

theorem encode_injective : Function.Injective (encode A) := by
  intro b b' h
  have hb := decode?_encode A b
  rw [h, decode?_encode] at hb
  exact (Option.some.inj hb).symm

theorem length_encode (bs : List UInt8) : (encode A bs).length = 2 * bs.length := by
  rw [encode, String.length_ofList, length_encodeChars]

/-- Case-insensitive base16 decoding (RFC 4648 §8): ASCII letters are
upper-cased, then decoded strictly in `Alphabet.upper`. -/
def decodeAnyCase? (s : String) : Option (List UInt8) :=
  decodeChars Alphabet.upper (s.toList.map Char.toUpper)

/-- The case-insensitive decoder accepts exactly the strings whose upper-casing
is a canonical spelling. -/
theorem decodeAnyCase?_eq_some_iff {s : String} {bs : List UInt8} :
    decodeAnyCase? s = some bs ↔ s.toList.map Char.toUpper = encodeChars Alphabet.upper bs := by
  rw [decodeAnyCase?, decodeChars_eq_some_iff, eq_comm]

@[simp] theorem decodeAnyCase?_encode_upper (bs : List UInt8) :
    decodeAnyCase? (encode Alphabet.upper bs) = some bs := by
  rw [decodeAnyCase?_eq_some_iff, encode, String.toList_ofList,
    map_encodeChars _ Alphabet.toUpper_upper]

@[simp] theorem decodeAnyCase?_encode_lower (bs : List UInt8) :
    decodeAnyCase? (encode Alphabet.lower bs) = some bs := by
  rw [decodeAnyCase?_eq_some_iff, encode, String.toList_ofList,
    map_encodeChars _ Alphabet.toUpper_lower]

/-! ## RFC 4648 §10 test vectors -/

open Alphabet

example : encode upper [] = "" := by decide
example : encode upper [0x66] = "66" := by decide +kernel
example : encode upper [0x66, 0x6f] = "666F" := by decide +kernel
example : encode upper [0x66, 0x6f, 0x6f] = "666F6F" := by decide +kernel
example : encode upper [0x66, 0x6f, 0x6f, 0x62] = "666F6F62" := by decide +kernel
example : encode upper [0x66, 0x6f, 0x6f, 0x62, 0x61] = "666F6F6261" := by decide +kernel
example : encode upper [0x66, 0x6f, 0x6f, 0x62, 0x61, 0x72] = "666F6F626172" := by
  decide +kernel

example : decode? upper "666F6F626172" = some [0x66, 0x6f, 0x6f, 0x62, 0x61, 0x72] := by
  decide +kernel
example : encode lower [0x66, 0x6f, 0x6f, 0x62, 0x61, 0x72] = "666f6f626172" := by
  decide +kernel

/-- The strict decoder rejects lower case, odd lengths and non-digits; the
case-insensitive one accepts any case. -/
example : decode? upper "666f" = none := by decide +kernel
example : decode? upper "666" = none := by decide +kernel
example : decode? upper "6G" = none := by decide +kernel
example : decodeAnyCase? "666f6F" = some [0x66, 0x6f, 0x6f] := by decide +kernel
example : decodeAnyCase? "6g" = none := by decide +kernel

/-! ## Encoding-theory glue -/

/-- Base16 as an encoding of byte strings by strings. -/
def base16Rel : EncRel String (List UInt8) :=
  EncRel.ofFun (encode A)

theorem base16Rel_bijective : (base16Rel A).Bijective :=
  ⟨fun _ _ _ h h' => encode_injective A (h.trans h'.symm), EncRel.ofFun_deterministic _⟩

/-- The base16 spellings of a byte format are the strings whose strict
decoding is a byte spelling. -/
theorem push_base16_eq {α : Type} (E : EncRel (List UInt8) α) :
    E.push (encode A) = E.pullPartial (decode? A) :=
  EncRel.push_eq_pullPartial (fun _ _ => decode?_eq_some_iff A) E

/-- Base16 preserves functionality of byte encodings. -/
theorem functional_push_base16 {α : Type} {E : EncRel (List UInt8) α}
    (hE : E.Functional) : (E.push (encode A)).Functional :=
  hE.push (encode_injective A)

/-- Byte encodings to text encodings, by base16. -/
abbrev base16Functor : EncCat (List UInt8) ⥤ EncCat String :=
  EncCat.pushFunctor (encode A)

/-- Text encodings to byte encodings, by strict base16 decoding. -/
abbrev base16DecodeFunctor : EncCat String ⥤ EncCat (List UInt8) :=
  EncCat.pushPartialFunctor (decode? A)

/-- Decoding after encoding base16 is the identity on encodings. -/
theorem base16Decode_base16 (X : EncCat (List UInt8)) :
    (base16DecodeFunctor A).obj ((base16Functor A).obj X) = X :=
  EncCat.pushPartialFunctor_obj_pushFunctor_obj (decode?_encode A) X

end Base16

end Silmaril
