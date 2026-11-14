module

public import Silmaril.Encoding.PunycodeFacts

/-!
# Punycode

RFC 3492 Bootstring with the Punycode parameters (§5: base 36, tmin 1,
tmax 26, skew 38, damp 700, initial_bias 72, initial_n 128, delimiter `'-'`),
as a pair of maps between sequences of code points and sequences of basic code
points (ASCII characters):

| map | direction | totality |
|-----|-----------|----------|
| `encode` | `List Nat ⇒ List Char` | total (§6.3) |
| `decode` | `List Char ⇒ List Nat` | partial (§6.2) |

with the round trip `decode_encode : decode (encode cs) = some cs` for every
input.  The building blocks — `adapt`, the digits, generalized
variable-length integers and insertion unsort coding — and their round trips
live in `Silmaril.Encoding.PunycodeFacts`.

**Overflow (§6.4).**  Code points and all state variables are unbounded `Nat`,
so overflow cannot occur and the encoder is total; the decoder fails only on
the other error conditions of §6.2 (a non-basic code point before the last
delimiter, a non-digit after it, a truncated integer).  An implementation with
bounded integers must add the §6.4 checks; `decode` is the specification they
refine.  Code points are not required to be Unicode scalar values: Bootstring
only requires nonnegative integers.

**Case.**  The encoder writes lower-case digits; the decoder accepts digits
in either case (§5).  Mixed-case annotation (Appendix A) is not implemented:
the case of the basic code points is preserved literally, and the case of
digit letters is ignored.

**Scope.**  IDNA (RFC 3490 ToASCII/ToUnicode, nameprep, UTS #46) is planned
but not covered here; `aceLabel` only prepends the ACE prefix `xn--` to the
Punycode encoding of a label containing non-ASCII code points.

**Samples.**  All of RFC 3492 §7.1 (A)–(S) are checked by `decide` in both
directions (`encode_sampleA`, `decode_sampleA`, …), with code points copied from the RFC's `u+XXXX` lists.
For (I) the RFC's encoding uses mixed-case annotation (`…baDot…`); `encode`
writes it in lower case and `decode` accepts the RFC's spelling.
-/

@[expose] public section

namespace Silmaril

namespace Punycode

/-- The delimiter `'-'` (U+002D). -/
def delimiter : Char := '-'

/-- Split at the last delimiter: `(some pre, post)` if there is one (`pre`
before it, `post` after it), `(none, input)` otherwise. -/
def splitLast : List Char → Option (List Char) × List Char
  | [] => (none, [])
  | c :: cs =>
    match splitLast cs with
    | (some pre, post) => (some (c :: pre), post)
    | (none, post) => if c = delimiter then (some [], post) else (none, c :: post)

/-- Punycode encoding (§6.3): the basic code points in order, a delimiter if
there are any, then the deltas as generalized variable-length integers. -/
def encode (input : List Nat) : List Char :=
  let b := basicPart input
  b.map Char.ofNat ++ (if b = [] then [] else [delimiter]) ++
    encodeDeltas initialBias b.length true (deltas input)

/-- Punycode decoding (§6.2): copy the code points before the last delimiter
(failing on a non-basic one), read the deltas after it, and run the insertion
state machine.  A delimiter at position 0 is not consumed (§6.2: only "if more
than zero code points were consumed"), so it then fails as a non-digit. -/
def decode (input : List Char) : Option (List Nat) :=
  match splitLast input with
  | (some [], _) => none
  | (some pre, post) =>
    if pre.all (·.toNat < initialN) then
      (decodeDigits initialBias pre.length true base 1 0 post).map
        (insertAll (pre.map Char.toNat))
    else none
  | (none, post) => (decodeDigits initialBias 0 true base 1 0 post).map (insertAll [])

/-! ## Round trip -/

theorem splitLast_of_not_mem : ∀ {X : List Char}, delimiter ∉ X → splitLast X = (none, X)
  | [], _ => rfl
  | c :: X, h => by
    simp only [List.mem_cons, not_or] at h
    simp [splitLast, splitLast_of_not_mem h.2, Ne.symm h.1]

theorem splitLast_append : ∀ (A : List Char) {X : List Char}, delimiter ∉ X →
    splitLast (A ++ delimiter :: X) = (some A, X)
  | [], X, h => by simp [splitLast, splitLast_of_not_mem h]
  | c :: A, X, h => by simp [splitLast, splitLast_append A h]

theorem delimiter_not_mem_encodeDeltas (bias h : Nat) (firsttime : Bool) (qs : List Nat) :
    delimiter ∉ encodeDeltas bias h firsttime qs := fun hm => by
  obtain ⟨d, hd, he⟩ := mem_encodeDeltas hm
  exact digitChar_ne_delimiter d hd he.symm

/-- **Round trip**: Punycode decoding inverts encoding, for every sequence of
code points (no overflow can occur on `Nat`). -/
theorem decode_encode (cs : List Nat) : decode (encode cs) = some cs := by
  have hD := delimiter_not_mem_encodeDeltas initialBias (basicPart cs).length true (deltas cs)
  have hround := insertAll_deltas cs
  unfold encode
  generalize hB : basicPart cs = B at *
  cases B with
  | nil =>
    simp only [List.length_nil] at hD
    simp only [List.map_nil, List.nil_append, List.length_nil, ite_true, decode,
      splitLast_of_not_mem hD, decodeDigits_encodeDeltas, Option.map_some, hround]
  | cons b bs =>
    have hbasic : ∀ x ∈ b :: bs, x < initialN := fun x hx => by
      rw [← hB] at hx
      exact (List.mem_filter.mp hx).2 |> of_decide_eq_true
    have hmap : (b :: bs).map (Char.toNat ∘ Char.ofNat) = b :: bs := by
      conv => rhs; rw [← List.map_id (b :: bs)]
      exact List.map_congr_left fun x hx => toNat_charOfNat (by
        have := hbasic x hx; simp only [initialN] at this; omega)
    show decode ((List.map Char.ofNat (b :: bs) ++ if b :: bs = [] then [] else [delimiter]) ++
      encodeDeltas initialBias (b :: bs).length true (deltas cs)) = some cs
    rw [ite_eq_right_of_eq_false _ _ (by simp), List.append_assoc, List.singleton_append]
    unfold decode
    rw [splitLast_append _ hD]
    have hmap' : (Char.ofNat b).toNat :: List.map (Char.toNat ∘ Char.ofNat) bs = b :: bs := hmap
    simp only [List.map_cons, List.length_cons, List.length_map] at hD ⊢
    rw [List.map_map, hmap']
    have hall : ((Char.ofNat b :: List.map Char.ofNat bs).all
        fun x => decide (x.toNat < initialN)) = true := by
      rw [← List.map_cons, List.all_map, List.all_eq_true]
      intro x hx
      have := hbasic x hx
      simp only [Function.comp_apply, decide_eq_true_eq]
      rw [toNat_charOfNat (by simp only [initialN] at this; omega)]
      exact this
    rw [ite_eq_left hall, decodeDigits_encodeDeltas, Option.map_some, hround]

/-- The encoding consists of basic code points (ASCII). -/
theorem toNat_lt_of_mem_encode {cs : List Nat} {c : Char} (h : c ∈ encode cs) :
    c.toNat < initialN := by
  simp only [encode, List.mem_append, List.mem_map] at h
  rcases h with (⟨x, hx, rfl⟩ | h) | h
  · have := (List.mem_filter.mp hx).2 |> of_decide_eq_true
    rw [toNat_charOfNat (by simp only [initialN] at this; omega)]
    exact this
  · split at h
    · cases h
    · simp only [List.mem_singleton] at h; subst h; decide
  · obtain ⟨d, hd, rfl⟩ := mem_encodeDeltas h
    exact toNat_digitChar_lt d hd

/-- Punycode encoding is injective. -/
theorem encode_injective : Function.Injective encode := fun a b h => by
  have := decode_encode a
  rw [h, decode_encode] at this
  exact (Option.some.inj this).symm

/-! ## Strings and the ACE prefix -/

/-- Punycode encoding of a string's code points. -/
def encodeString (s : String) : String := String.ofList (encode (s.toList.map Char.toNat))

/-- Punycode decoding to a string: fails if a decoded code point is not a
Unicode scalar value. -/
def decodeString (s : String) : Option String :=
  (decode s.toList).bind fun ns =>
    if ns.all fun n => decide (n < 0xD800 ∨ (0xDFFF < n ∧ n < 0x110000)) then
      some (String.ofList (ns.map Char.ofNat))
    else none

theorem decodeString_encodeString (s : String) : decodeString (encodeString s) = some s := by
  have hall : (s.toList.map Char.toNat).all
      (fun n => decide (n < 0xD800 ∨ (0xDFFF < n ∧ n < 0x110000))) = true := by
    simp only [List.all_map, List.all_eq_true, Function.comp_apply, decide_eq_true_eq]
    intro c _
    have h := c.valid
    simp only [UInt32.isValidChar] at h
    exact h
  simp only [decodeString, encodeString, String.toList_ofList, decode_encode,
    Option.bind_some, hall, ite_true, List.map_map]
  conv => rhs; rw [← String.ofList_toList (s := s)]
  congr 2
  conv => rhs; rw [← List.map_id s.toList]
  exact List.map_congr_left fun c _ => Char.ofNat_toNat c

/-- The ACE label of an IDNA label (RFC 3490 §5 prefix `xn--`), *without*
nameprep or any IDNA check: ASCII labels are returned unchanged, others are
`xn--` followed by their Punycode encoding.  A convenience, not ToASCII. -/
def aceLabel (s : String) : String :=
  if s.toList.all (·.toNat < initialN) then s else "xn--" ++ encodeString s

/-! ## RFC 3492 §7.1 samples

Each sample is checked in both directions by `decide`: `encode` produces the
RFC's encoding (lower-cased for (I), whose RFC spelling uses mixed-case
annotation) and `decode` of the RFC's spelling returns the code points. -/

/-- RFC 3492 §7.1 (A) Arabic (Egyptian). -/
def sampleA : List Nat :=
  [0x0644, 0x064A, 0x0647, 0x0645, 0x0627, 0x0628, 0x062A, 0x0643, 0x0644, 0x0645, 0x0648, 0x0634,
   0x0639, 0x0631, 0x0628, 0x064A, 0x061F]

theorem encode_sampleA :
    encode sampleA = "egbpdaj6bu4bxfgehfvwxn".toList := by decide

theorem decode_sampleA :
    decode "egbpdaj6bu4bxfgehfvwxn".toList = some sampleA := by decide

/-- RFC 3492 §7.1 (B) Chinese (simplified). -/
def sampleB : List Nat :=
  [0x4ED6, 0x4EEC, 0x4E3A, 0x4EC0, 0x4E48, 0x4E0D, 0x8BF4, 0x4E2D, 0x6587]

theorem encode_sampleB :
    encode sampleB = "ihqwcrb4cv8a8dqg056pqjye".toList := by decide

theorem decode_sampleB :
    decode "ihqwcrb4cv8a8dqg056pqjye".toList = some sampleB := by decide

/-- RFC 3492 §7.1 (C) Chinese (traditional). -/
def sampleC : List Nat :=
  [0x4ED6, 0x5011, 0x7232, 0x4EC0, 0x9EBD, 0x4E0D, 0x8AAA, 0x4E2D, 0x6587]

theorem encode_sampleC :
    encode sampleC = "ihqwctvzc91f659drss3x8bo0yb".toList := by decide

theorem decode_sampleC :
    decode "ihqwctvzc91f659drss3x8bo0yb".toList = some sampleC := by decide

/-- RFC 3492 §7.1 (D) Czech. -/
def sampleD : List Nat :=
  [0x0050, 0x0072, 0x006F, 0x010D, 0x0070, 0x0072, 0x006F, 0x0073, 0x0074, 0x011B, 0x006E, 0x0065,
   0x006D, 0x006C, 0x0075, 0x0076, 0x00ED, 0x010D, 0x0065, 0x0073, 0x006B, 0x0079]

theorem encode_sampleD :
    encode sampleD = "Proprostnemluvesky-uyb24dma41a".toList := by decide

theorem decode_sampleD :
    decode "Proprostnemluvesky-uyb24dma41a".toList = some sampleD := by decide

/-- RFC 3492 §7.1 (E) Hebrew. -/
def sampleE : List Nat :=
  [0x05DC, 0x05DE, 0x05D4, 0x05D4, 0x05DD, 0x05E4, 0x05E9, 0x05D5, 0x05D8, 0x05DC, 0x05D0, 0x05DE,
   0x05D3, 0x05D1, 0x05E8, 0x05D9, 0x05DD, 0x05E2, 0x05D1, 0x05E8, 0x05D9, 0x05EA]

theorem encode_sampleE :
    encode sampleE = "4dbcagdahymbxekheh6e0a7fei0b".toList := by decide

theorem decode_sampleE :
    decode "4dbcagdahymbxekheh6e0a7fei0b".toList = some sampleE := by decide

/-- RFC 3492 §7.1 (F) Hindi (Devanagari). -/
def sampleF : List Nat :=
  [0x092F, 0x0939, 0x0932, 0x094B, 0x0917, 0x0939, 0x093F, 0x0928, 0x094D, 0x0926, 0x0940, 0x0915,
   0x094D, 0x092F, 0x094B, 0x0902, 0x0928, 0x0939, 0x0940, 0x0902, 0x092C, 0x094B, 0x0932, 0x0938,
   0x0915, 0x0924, 0x0947, 0x0939, 0x0948, 0x0902]

theorem encode_sampleF :
    encode sampleF = "i1baa7eci9glrd9b2ae1bj0hfcgg6iyaf8o0a1dig0cd".toList := by decide

theorem decode_sampleF :
    decode "i1baa7eci9glrd9b2ae1bj0hfcgg6iyaf8o0a1dig0cd".toList = some sampleF := by decide

/-- RFC 3492 §7.1 (G) Japanese (kanji and hiragana). -/
def sampleG : List Nat :=
  [0x306A, 0x305C, 0x307F, 0x3093, 0x306A, 0x65E5, 0x672C, 0x8A9E, 0x3092, 0x8A71, 0x3057, 0x3066,
   0x304F, 0x308C, 0x306A, 0x3044, 0x306E, 0x304B]

theorem encode_sampleG :
    encode sampleG = "n8jok5ay5dzabd5bym9f0cm5685rrjetr6pdxa".toList := by decide

theorem decode_sampleG :
    decode "n8jok5ay5dzabd5bym9f0cm5685rrjetr6pdxa".toList = some sampleG := by decide

/-- RFC 3492 §7.1 (H) Korean (Hangul syllables). -/
def sampleH : List Nat :=
  [0xC138, 0xACC4, 0xC758, 0xBAA8, 0xB4E0, 0xC0AC, 0xB78C, 0xB4E4, 0xC774, 0xD55C, 0xAD6D, 0xC5B4,
   0xB97C, 0xC774, 0xD574, 0xD55C, 0xB2E4, 0xBA74, 0xC5BC, 0xB9C8, 0xB098, 0xC88B, 0xC744, 0xAE4C]

theorem encode_sampleH :
    encode sampleH =
      "989aomsvi5e83db1d2a355cv1e0vak1dwrv93d5x".toList ++
        "bh15a0dt30a5jpsd879ccm6fea98c".toList := by
  decide

theorem decode_sampleH :
    decode ("989aomsvi5e83db1d2a355cv1e0vak1dwrv93d5x".toList ++
        "bh15a0dt30a5jpsd879ccm6fea98c".toList) = some sampleH := by
  decide

/-- RFC 3492 §7.1 (I) Russian (Cyrillic). -/
def sampleI : List Nat :=
  [0x043F, 0x043E, 0x0447, 0x0435, 0x043C, 0x0443, 0x0436, 0x0435, 0x043E, 0x043D, 0x0438, 0x043D,
   0x0435, 0x0433, 0x043E, 0x0432, 0x043E, 0x0440, 0x044F, 0x0442, 0x043F, 0x043E, 0x0440, 0x0443,
   0x0441, 0x0441, 0x043A, 0x0438]

theorem encode_sampleI :
    encode sampleI = "b1abfaaepdrnnbgefbadotcwatmq2g4l".toList := by decide

theorem decode_sampleI :
    decode "b1abfaaepdrnnbgefbaDotcwatmq2g4l".toList = some sampleI := by decide

/-- RFC 3492 §7.1 (J) Spanish. -/
def sampleJ : List Nat :=
  [0x0050, 0x006F, 0x0072, 0x0071, 0x0075, 0x00E9, 0x006E, 0x006F, 0x0070, 0x0075, 0x0065, 0x0064,
   0x0065, 0x006E, 0x0073, 0x0069, 0x006D, 0x0070, 0x006C, 0x0065, 0x006D, 0x0065, 0x006E, 0x0074,
   0x0065, 0x0068, 0x0061, 0x0062, 0x006C, 0x0061, 0x0072, 0x0065, 0x006E, 0x0045, 0x0073, 0x0070,
   0x0061, 0x00F1, 0x006F, 0x006C]

theorem encode_sampleJ :
    encode sampleJ = "PorqunopuedensimplementehablarenEspaol-fmd56a".toList := by decide

theorem decode_sampleJ :
    decode "PorqunopuedensimplementehablarenEspaol-fmd56a".toList = some sampleJ := by decide

/-- RFC 3492 §7.1 (K) Vietnamese. -/
def sampleK : List Nat :=
  [0x0054, 0x1EA1, 0x0069, 0x0073, 0x0061, 0x006F, 0x0068, 0x1ECD, 0x006B, 0x0068, 0x00F4, 0x006E,
   0x0067, 0x0074, 0x0068, 0x1EC3, 0x0063, 0x0068, 0x1EC9, 0x006E, 0x00F3, 0x0069, 0x0074, 0x0069,
   0x1EBF, 0x006E, 0x0067, 0x0056, 0x0069, 0x1EC7, 0x0074]

theorem encode_sampleK :
    encode sampleK = "TisaohkhngthchnitingVit-kjcr8268qyxafd2f1b9g".toList := by decide

theorem decode_sampleK :
    decode "TisaohkhngthchnitingVit-kjcr8268qyxafd2f1b9g".toList = some sampleK := by decide

/-- RFC 3492 §7.1 (L) 3<nen>B<gumi><kinpachi><sensei>. -/
def sampleL : List Nat :=
  [0x0033, 0x5E74, 0x0042, 0x7D44, 0x91D1, 0x516B, 0x5148, 0x751F]

theorem encode_sampleL :
    encode sampleL = "3B-ww4c5e180e575a65lsy2b".toList := by decide

theorem decode_sampleL :
    decode "3B-ww4c5e180e575a65lsy2b".toList = some sampleL := by decide

/-- RFC 3492 §7.1 (M) <amuro><namie>-with-SUPER-MONKEYS. -/
def sampleM : List Nat :=
  [0x5B89, 0x5BA4, 0x5948, 0x7F8E, 0x6075, 0x002D, 0x0077, 0x0069, 0x0074, 0x0068, 0x002D, 0x0053,
   0x0055, 0x0050, 0x0045, 0x0052, 0x002D, 0x004D, 0x004F, 0x004E, 0x004B, 0x0045, 0x0059, 0x0053]

theorem encode_sampleM :
    encode sampleM = "-with-SUPER-MONKEYS-pc58ag80a8qai00g7n9n".toList := by decide

theorem decode_sampleM :
    decode "-with-SUPER-MONKEYS-pc58ag80a8qai00g7n9n".toList = some sampleM := by decide

/-- RFC 3492 §7.1 (N) Hello-Another-Way-<sorezore><no><basho>. -/
def sampleN : List Nat :=
  [0x0048, 0x0065, 0x006C, 0x006C, 0x006F, 0x002D, 0x0041, 0x006E, 0x006F, 0x0074, 0x0068, 0x0065,
   0x0072, 0x002D, 0x0057, 0x0061, 0x0079, 0x002D, 0x305D, 0x308C, 0x305E, 0x308C, 0x306E, 0x5834,
   0x6240]

theorem encode_sampleN :
    encode sampleN = "Hello-Another-Way--fc4qua05auwb3674vfr0b".toList := by decide

theorem decode_sampleN :
    decode "Hello-Another-Way--fc4qua05auwb3674vfr0b".toList = some sampleN := by decide

/-- RFC 3492 §7.1 (O) <hitotsu><yane><no><shita>2. -/
def sampleO : List Nat :=
  [0x3072, 0x3068, 0x3064, 0x5C4B, 0x6839, 0x306E, 0x4E0B, 0x0032]

theorem encode_sampleO :
    encode sampleO = "2-u9tlzr9756bt3uc0v".toList := by decide

theorem decode_sampleO :
    decode "2-u9tlzr9756bt3uc0v".toList = some sampleO := by decide

/-- RFC 3492 §7.1 (P) Maji<de>Koi<suru>5<byou><mae>. -/
def sampleP : List Nat :=
  [0x004D, 0x0061, 0x006A, 0x0069, 0x3067, 0x004B, 0x006F, 0x0069, 0x3059, 0x308B, 0x0035, 0x79D2,
   0x524D]

theorem encode_sampleP :
    encode sampleP = "MajiKoi5-783gue6qz075azm5e".toList := by decide

theorem decode_sampleP :
    decode "MajiKoi5-783gue6qz075azm5e".toList = some sampleP := by decide

/-- RFC 3492 §7.1 (Q) <pafii>de<runba>. -/
def sampleQ : List Nat :=
  [0x30D1, 0x30D5, 0x30A3, 0x30FC, 0x0064, 0x0065, 0x30EB, 0x30F3, 0x30D0]

theorem encode_sampleQ :
    encode sampleQ = "de-jg4avhby1noc0d".toList := by decide

theorem decode_sampleQ :
    decode "de-jg4avhby1noc0d".toList = some sampleQ := by decide

/-- RFC 3492 §7.1 (R) <sono><supiido><de>. -/
def sampleR : List Nat :=
  [0x305D, 0x306E, 0x30B9, 0x30D4, 0x30FC, 0x30C9, 0x3067]

theorem encode_sampleR :
    encode sampleR = "d9juau41awczczp".toList := by decide

theorem decode_sampleR :
    decode "d9juau41awczczp".toList = some sampleR := by decide

/-- RFC 3492 §7.1 (S) -> $1.00 <-. -/
def sampleS : List Nat :=
  [0x002D, 0x003E, 0x0020, 0x0024, 0x0031, 0x002E, 0x0030, 0x0030, 0x0020, 0x003C, 0x002D]

theorem encode_sampleS :
    encode sampleS = "-> $1.00 <--".toList := by decide

theorem decode_sampleS :
    decode "-> $1.00 <--".toList = some sampleS := by decide

/-! ## Further checks -/

example : encode [] = [] := by decide
/-- A leading delimiter with nothing before it is not consumed (§6.2). -/
example : decode "-a".toList = none := by decide
/-- A non-basic code point before the last delimiter fails. -/
example : decode "ü-a".toList = none := by decide
/-- A truncated variable-length integer fails. -/
example : decode "b".toList = none := by decide
/-- Digits are read case-insensitively. -/
example : decode "EGBPDAJ6BU4BXFGEHFVWXN".toList = some sampleA := by decide
example : aceLabel "bücher" = "xn--bcher-kva" := by decide +kernel
example : aceLabel "example" = "example" := by decide +kernel

end Punycode

end Silmaril
