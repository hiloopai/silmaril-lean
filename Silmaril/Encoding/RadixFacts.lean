module

/-!
# Radix-2^k alphabets and bit-group arithmetic

The shared building blocks of the RFC 4648 base-N carriers
(`Silmaril.Encoding.Base32`, `Silmaril.Encoding.Base16`):

* `toDigits b n v` / `ofDigits b ds` — fixed-width big-endian base-`b`
  digits, with `ofDigits_toDigits` and `toDigits_ofDigits`;
* `Alphabet bits` — `2 ^ bits` digit characters with an exact partial inverse
  `value?`, excluding the pad character `'='`;
* the group codec: `encGroup` spells a byte string as one bit stream, padded
  on the right with zero bits to a whole number of `bits`-bit digits
  (`digitCount bits m = ⌈8m / bits⌉` digits, `padBits bits m` zero bits), and
  the strict `decGroup` rejects digit counts that no byte count produces and
  non-zero pad bits (RFC 4648 §3.5); `decGroup_eq_some_iff` is exactness.

A base-N carrier cuts its input into fixed groups (5 bytes for base32, 1 for
base16) and spells each with `encGroup`; any group size works, since
`encGroup` is exact for every byte count.
-/

@[expose] public section

namespace Silmaril

namespace Radix

/-! ## Fixed-width digits -/

/-- The low `n` base-`b` digits of `v`, most significant first. -/
def toDigits (b : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, v => v / b ^ n % b :: toDigits b n v

/-- The value of a big-endian base-`b` digit list. -/
def ofDigits (b : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d * b ^ ds.length + ofDigits b ds

@[simp] theorem length_toDigits (b : Nat) : ∀ n v, (toDigits b n v).length = n
  | 0, _ => rfl
  | n + 1, v => by simp [toDigits, length_toDigits b n]

theorem lt_of_mem_toDigits {b : Nat} (hb : 0 < b) :
    ∀ {n v d}, d ∈ toDigits b n v → d < b
  | 0, _, _, h => by simp [toDigits] at h
  | n + 1, v, d, h => by
    simp only [toDigits, List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.mod_lt _ hb
    · exact lt_of_mem_toDigits hb h

theorem ofDigits_toDigits (b : Nat) : ∀ n v, ofDigits b (toDigits b n v) = v % b ^ n
  | 0, v => by simp [toDigits, ofDigits, Nat.mod_one]
  | n + 1, v => by
    rw [toDigits, ofDigits, length_toDigits, ofDigits_toDigits b n, Nat.mod_pow_succ,
      Nat.mul_comm, Nat.add_comm]

theorem ofDigits_lt {b : Nat} : ∀ {ds : List Nat}, (∀ d ∈ ds, d < b) →
    ofDigits b ds < b ^ ds.length
  | [], _ => by simp [ofDigits]
  | d :: ds, hd => by
    have h1 := ofDigits_lt (b := b) (ds := ds) (fun x hx => hd x (List.mem_cons_of_mem _ hx))
    have h2 := hd d List.mem_cons_self
    rw [ofDigits, List.length_cons, Nat.pow_succ, Nat.mul_comm (b ^ _) b]
    calc d * b ^ ds.length + ofDigits b ds < d * b ^ ds.length + b ^ ds.length :=
          Nat.add_lt_add_left h1 _
      _ = (d + 1) * b ^ ds.length := by rw [Nat.succ_mul]
      _ ≤ b * b ^ ds.length := Nat.mul_le_mul_right _ h2

/-- Digits only see the value modulo `b ^ n`. -/
theorem toDigits_add_mul {b : Nat} (hb : 0 < b) :
    ∀ n v k, toDigits b n (v + k * b ^ n) = toDigits b n v
  | 0, _, _ => rfl
  | n + 1, v, k => by
    have hpow : k * b ^ (n + 1) = k * b * b ^ n := by
      rw [Nat.pow_succ, Nat.mul_comm (b ^ n) b, Nat.mul_assoc]
    rw [toDigits, toDigits, hpow, toDigits_add_mul hb n v (k * b),
      Nat.add_mul_div_right _ _ (Nat.pow_pos hb), Nat.add_mul_mod_self_right]

theorem toDigits_ofDigits {b : Nat} : ∀ {ds : List Nat}, (∀ d ∈ ds, d < b) →
    toDigits b ds.length (ofDigits b ds) = ds
  | [], _ => rfl
  | d :: ds, hd => by
    have h1 := ofDigits_lt (b := b) (ds := ds) (fun x hx => hd x (List.mem_cons_of_mem _ hx))
    have h2 := hd d List.mem_cons_self
    have hb : 0 < b := Nat.lt_of_le_of_lt (Nat.zero_le _) h2
    rw [List.length_cons, toDigits, ofDigits, Nat.add_comm, toDigits_add_mul hb,
      toDigits_ofDigits (fun x hx => hd x (List.mem_cons_of_mem _ hx)),
      Nat.add_mul_div_right _ _ (Nat.pow_pos hb), Nat.div_eq_of_lt h1, Nat.zero_add,
      Nat.mod_eq_of_lt h2]

/-! ## Alphabets -/

/-- A radix-`2 ^ bits` alphabet: `2 ^ bits` digit characters with an exact
partial inverse, not containing the pad character `'='`. -/
structure Alphabet (bits : Nat) where
  /-- The digit for each `bits`-bit value. -/
  digit : Fin (2 ^ bits) → Char
  /-- The value of a digit character (partial inverse of `digit`). -/
  value? : Char → Option (Fin (2 ^ bits))
  value?_digit : ∀ i, value? (digit i) = some i
  digit_of_value? : ∀ {c : Char} {i : Fin (2 ^ bits)}, value? c = some i → digit i = c
  value?_pad : value? '=' = none

namespace Alphabet

variable {bits : Nat} (A : Alphabet bits)

theorem value?_eq_some_iff {c : Char} {i : Fin (2 ^ bits)} :
    A.value? c = some i ↔ A.digit i = c :=
  ⟨A.digit_of_value?, fun h => h ▸ A.value?_digit i⟩

theorem digit_injective : Function.Injective A.digit := fun i j hij => by
  have hi := A.value?_digit i
  rw [hij, A.value?_digit j] at hi
  exact (Option.some.inj hi).symm

theorem digit_ne_pad (i : Fin (2 ^ bits)) : A.digit i ≠ '=' := fun h => by
  have hi := A.value?_digit i
  rw [h, A.value?_pad] at hi
  cases hi

/-- The alphabet of a digit table, with `value?` by search; the side
conditions are decidable facts about the table. -/
def ofTable (digit : Fin (2 ^ bits) → Char)
    (h : ∀ i, (List.finRange (2 ^ bits)).find? (fun j => digit j == digit i) = some i)
    (hpad : (List.finRange (2 ^ bits)).find? (fun j => digit j == '=') = none) :
    Alphabet bits where
  digit := digit
  value? c := (List.finRange (2 ^ bits)).find? (fun j => digit j == c)
  value?_digit := h
  digit_of_value? {c i} hc := by
    have := List.find?_some hc
    simpa using this
  value?_pad := hpad

/-- The digit of a natural number, modulo `2 ^ bits`. -/
def dig (n : Nat) : Char := A.digit ⟨n % 2 ^ bits, Nat.mod_lt _ (Nat.two_pow_pos bits)⟩

theorem dig_ne_pad (n : Nat) : A.dig n ≠ '=' := A.digit_ne_pad _

theorem dig_of_lt {n : Nat} (h : n < 2 ^ bits) : A.dig n = A.digit ⟨n, h⟩ :=
  congrArg A.digit (Fin.ext (Nat.mod_eq_of_lt h))

/-- The values of a digit sequence; `none` if some character is not a digit. -/
def values? : List Char → Option (List Nat)
  | [] => some []
  | c :: cs => (A.value? c).bind fun v => (values? cs).map (v.val :: ·)

theorem values?_eq_some_iff {cs : List Char} {vs : List Nat} :
    A.values? cs = some vs ↔ (∀ v ∈ vs, v < 2 ^ bits) ∧ vs.map A.dig = cs := by
  induction cs generalizing vs with
  | nil =>
    cases vs <;> simp [values?]
  | cons c cs ih =>
    simp only [values?, Option.bind_eq_some_iff, Option.map_eq_some_iff, ih]
    constructor
    · rintro ⟨i, hi, vs', ⟨hlt, rfl⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · intro v hv
        simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact i.isLt
        · exact hlt v hv
      · simp only [List.map_cons, List.cons.injEq, and_true]
        rw [← A.digit_of_value? hi, A.dig_of_lt i.isLt]
    · intro ⟨hlt, hmap⟩
      match vs, hmap with
      | v :: vs', hmap =>
        simp only [List.map_cons, List.cons.injEq] at hmap
        obtain ⟨rfl, rfl⟩ := hmap
        have hv := hlt v (by simp)
        refine ⟨⟨v, hv⟩, ?_, vs',
          ⟨fun x hx => hlt x (List.mem_cons_of_mem _ hx), rfl⟩, rfl⟩
        rw [A.dig_of_lt hv]
        exact A.value?_digit _

/-! ## Bit groups -/

/-- The number of `bits`-bit digits spelling `m` bytes: `⌈8m / bits⌉`. -/
def digitCount (bits m : Nat) : Nat := (8 * m + bits - 1) / bits

/-- The number of zero bits padding `m` bytes to `digitCount bits m` digits. -/
def padBits (bits m : Nat) : Nat := bits * digitCount bits m - 8 * m

/-- A byte string as one big-endian number. -/
def bytesVal (bs : List UInt8) : Nat := ofDigits 256 (bs.map UInt8.toNat)

/-- The `m`-byte string of a number below `256 ^ m`. -/
def valBytes (m v : Nat) : List UInt8 := (toDigits 256 m v).map UInt8.ofNat

/-- A byte string as `digitCount bits bs.length` digits: its bits followed by
`padBits` zero bits. -/
def encGroup (bs : List UInt8) : List Char :=
  (toDigits (2 ^ bits) (digitCount bits bs.length)
    (bytesVal bs * 2 ^ padBits bits bs.length)).map A.dig

/-- Strict decoding of a digit group: the digit count must be
`digitCount bits m` for some byte count `m`, and the pad bits must be zero. -/
def decGroup (cs : List Char) : Option (List UInt8) :=
  if digitCount bits (bits * cs.length / 8) = cs.length then
    (A.values? cs).bind fun vs =>
      if ofDigits (2 ^ bits) vs % 2 ^ padBits bits (bits * cs.length / 8) = 0 then
        some (valBytes (bits * cs.length / 8)
          (ofDigits (2 ^ bits) vs / 2 ^ padBits bits (bits * cs.length / 8)))
      else none
  else none

theorem length_encGroup (bs : List UInt8) :
    (A.encGroup bs).length = digitCount bits bs.length := by
  simp [encGroup]

theorem pad_not_mem_encGroup (bs : List UInt8) : '=' ∉ A.encGroup bs := by
  simp only [encGroup, List.mem_map, not_exists, not_and]
  exact fun _ _ => A.dig_ne_pad _

/-- Spellings in two alphabets correspond along any digit translation. -/
theorem map_encGroup {B : Alphabet bits} {f : Char → Char} (hf : ∀ i, f (A.digit i) = B.digit i)
    (bs : List UInt8) : (A.encGroup bs).map f = B.encGroup bs := by
  simp only [encGroup, List.map_map]
  exact List.map_congr_left fun _ _ => hf _

/-! ## Group arithmetic -/

theorem bits_mul_digitCount (hbits : 0 < bits) (m : Nat) :
    8 * m ≤ bits * digitCount bits m ∧ bits * digitCount bits m < 8 * m + bits := by
  have := Nat.div_add_mod (8 * m + bits - 1) bits
  have := Nat.mod_lt (8 * m + bits - 1) hbits
  unfold digitCount
  omega

theorem bits_mul_digitCount_eq (hbits : 0 < bits) (m : Nat) :
    bits * digitCount bits m = 8 * m + padBits bits m := by
  have := bits_mul_digitCount hbits m
  unfold padBits
  omega

/-- The digit count determines the byte count when digits are at most a byte. -/
theorem bits_mul_digitCount_div (hbits : 0 < bits) (h8 : bits ≤ 8) (m : Nat) :
    bits * digitCount bits m / 8 = m := by
  have := bits_mul_digitCount hbits m
  omega

theorem pow_digitCount (hbits : 0 < bits) (m : Nat) :
    (2 ^ bits) ^ digitCount bits m = 256 ^ m * 2 ^ padBits bits m := by
  rw [← Nat.pow_mul, bits_mul_digitCount_eq hbits, Nat.pow_add, Nat.pow_mul]

theorem lt_of_mem_map_toNat {bs : List UInt8} : ∀ d ∈ bs.map UInt8.toNat, d < 256 := by
  intro d hd
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hd
  exact a.toNat_lt

theorem bytesVal_lt (bs : List UInt8) : bytesVal bs < 256 ^ bs.length := by
  have := ofDigits_lt (b := 256) (ds := bs.map UInt8.toNat) lt_of_mem_map_toNat
  simpa [bytesVal] using this

theorem valBytes_bytesVal (bs : List UInt8) : valBytes bs.length (bytesVal bs) = bs := by
  have := toDigits_ofDigits (b := 256) (ds := bs.map UInt8.toNat) lt_of_mem_map_toNat
  rw [List.length_map] at this
  rw [valBytes, bytesVal, this, List.map_map]
  exact (List.map_congr_left fun a _ => UInt8.ofNat_toNat).trans (List.map_id bs)

theorem length_valBytes (m v : Nat) : (valBytes m v).length = m := by
  simp [valBytes]

theorem bytesVal_valBytes (m v : Nat) : bytesVal (valBytes m v) = v % 256 ^ m := by
  have hmap : (valBytes m v).map UInt8.toNat = toDigits 256 m v := by
    rw [valBytes, List.map_map]
    conv => rhs; rw [← List.map_id (toDigits 256 m v)]
    refine List.map_congr_left fun d hd => ?_
    simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (lt_of_mem_toDigits (by decide) hd)]
  rw [bytesVal, hmap, ofDigits_toDigits]

/-! ## Exactness of the group codec -/

theorem decGroup_encGroup (hbits : 0 < bits) (h8 : bits ≤ 8) (bs : List UInt8) :
    A.decGroup (A.encGroup bs) = some bs := by
  have hx := bytesVal_lt bs
  have hpos : 0 < 2 ^ padBits bits bs.length := Nat.two_pow_pos _
  have hlt : bytesVal bs * 2 ^ padBits bits bs.length <
      (2 ^ bits) ^ digitCount bits bs.length := by
    rw [pow_digitCount hbits]
    exact Nat.mul_lt_mul_of_pos_right hx hpos
  have hvals : A.values? (A.encGroup bs) = some (toDigits (2 ^ bits)
      (digitCount bits bs.length) (bytesVal bs * 2 ^ padBits bits bs.length)) :=
    (A.values?_eq_some_iff).mpr
      ⟨fun _ hd => lt_of_mem_toDigits (Nat.two_pow_pos _) hd, rfl⟩
  rw [decGroup, length_encGroup, bits_mul_digitCount_div hbits h8, hvals]
  simp only [↓reduceIte, Option.bind_some, ofDigits_toDigits, Nat.mod_eq_of_lt hlt,
    Nat.mul_mod_left, Nat.mul_div_cancel _ hpos, valBytes_bytesVal]

theorem encGroup_of_decGroup (hbits : 0 < bits) {cs : List Char} {bs : List UInt8}
    (h : A.decGroup cs = some bs) : A.encGroup bs = cs := by
  unfold decGroup at h
  split at h
  case isFalse => cases h
  case isTrue hlen =>
    obtain ⟨vs, hvs, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    case isFalse => cases h
    case isTrue hmod =>
      cases h
      obtain ⟨hlt, rfl⟩ := (A.values?_eq_some_iff).mp hvs
      generalize hm : bits * (vs.map A.dig).length / 8 = m at hlen hmod
      rw [List.length_map] at hlen hm
      have hv := ofDigits_lt hlt
      rw [← hlen, pow_digitCount hbits] at hv
      have hpos : 0 < 2 ^ padBits bits m := Nat.two_pow_pos _
      have hq : ofDigits (2 ^ bits) vs / 2 ^ padBits bits m < 256 ^ m :=
        Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      rw [encGroup, length_valBytes, bytesVal_valBytes, Nat.mod_eq_of_lt hq,
        Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod), hlen, toDigits_ofDigits hlt]

/-- Exactness: the strict group decoder is defined exactly on the image of the
group encoder. -/
theorem decGroup_eq_some_iff (hbits : 0 < bits) (h8 : bits ≤ 8) {cs : List Char}
    {bs : List UInt8} : A.decGroup cs = some bs ↔ A.encGroup bs = cs :=
  ⟨A.encGroup_of_decGroup hbits, fun h => h ▸ A.decGroup_encGroup hbits h8 bs⟩

theorem encGroup_injective (hbits : 0 < bits) (h8 : bits ≤ 8) :
    Function.Injective A.encGroup := fun b b' h => by
  have hb := A.decGroup_encGroup hbits h8 b
  rw [h, A.decGroup_encGroup hbits h8] at hb
  exact (Option.some.inj hb).symm

end Alphabet

end Radix

end Silmaril
