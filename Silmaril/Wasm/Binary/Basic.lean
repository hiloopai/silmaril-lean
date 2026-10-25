module

public import Silmaril.Wasm.Types

/-! # Shared WebAssembly binary grammar

Productions common to the Wasm 1.0 Recommendation (2019, chapter 5) and the
Core 3.0 SpecTec grammar (`5.1-binary.values.spectec`, `5.4-binary.modules.spectec`):
bytes, LEB128 integers with a bit-width bound, IEEE floats, vectors, names,
indices, sections and custom sections.

Every production is a relation `G : Bytes → α → Prop` on the *exact* byte string
it generates; sequencing is list concatenation, as in the attribute grammars of
both specifications. Citations `5.1:n` refer to line `n` of
`5.1-binary.values.spectec`, and `REC 5.x.y` to the 2019 Recommendation.

## Deviations from the pinned SpecTec source (errata)

* `$cont(b)` is defined for `0x80 ≤ b < 0xC0`. SpecTec (5.1:49) writes
  `0x80 < b < 0xC0`, which would make e.g. `U+0080` (`C2 80`) unencodable; the
  Recommendation (REC 5.2.4: `b₂,b₃,b₄ < 0xC0` with `bᵢ - 0x80`) and Unicode agree
  with the inclusive bound.
* The four-byte UTF-8 range is `U+10000 ≤ c < U+110000`. SpecTec (5.1:63) writes
  `U+11000`, an evident typo (REC 5.2.4 has `U+110000`).
* `Bi32`/`Bi64` (uninterpreted integers) are `BiN`, i.e. *signed* LEB128 (`IN`
  below). The pinned SpecTec (5.1:31–32) writes `Bi32 = BuN(32)`, leaving `BiN`
  unused; this contradicts REC 5.2.2 ("uninterpreted integers are encoded as
  signed integers") and every implementation (`i32.const -1` is `41 7F`).

All three were independently re-verified against the pinned file (SHA-256 matches
`specs/wasm/core-3.0.json`), SpecTec's elaboration, the reference interpreter and the
test suite. These checks describe the pinned source revision.

## Agreement with the reference interpreter

The integer and name productions accept exactly the bytes that the official reference
interpreter (`WebAssembly/spec@6087111…`, `interpreter/binary/decode.ml` and `utf8.ml`)
accepts, with the same values. `Silmaril.Wasm.Binary.RefInterp` transcribes those
decoders line by line and proves, for every width `N > 0`:

* `RefInterp.utf8_iff : Utf8 cs b ↔ refUtf8Decode b = some cs`;
* `RefInterp.name_iff : Name b s ↔ refName b = some (s.toList, [])`;
* `RefInterp.un_iff : UN N b n ↔ refUN N b = some (n, [])`, likewise `sn_iff` and `in_iff`
  (with `u32_iff`, `u64_iff`, `s32_iff`, `s33_iff`, `s64_iff`, `i32_iff`, `i64_iff`), and
  the consumed-prefix forms `refUN_eq_some_iff`, `refSN_eq_some_iff`, `refIN_eq_some_iff`,
  `refName_eq_some_iff`.

The UTF-8 leading-byte bounds (`0xC0 ≤ b₁`, `0xE0 ≤ b₁`, `0xF0 ≤ b₁`) are SpecTec's
partial subtraction `b₁ - 0xC0` made explicit, and are needed for `utf8_iff`: without
`0xE0 ≤ b₁`, truncated subtraction would accept `00 A0 80` as `U+0800`.
-/

@[expose] public section

namespace Silmaril.Wasm.Binary

/-- Byte strings, the terminals of the grammar. -/
abbrev Bytes := List UInt8

/-! ## Unambiguity -/

/-- No encoding is a proper prefix of another, and equal encodings agree on the
syntax: the parse of a production is determined by any byte string it begins. -/
def PrefixFree {α : Type} (G : Bytes → α → Prop) : Prop :=
  ∀ ⦃b b' r r' : Bytes⦄ ⦃a a' : α⦄, G b a → G b' a' → b ++ r = b' ++ r' → b = b' ∧ a = a'

/-- A byte string encodes at most one value. -/
def Functional {α : Type} (G : Bytes → α → Prop) : Prop :=
  ∀ ⦃b : Bytes⦄ ⦃a a' : α⦄, G b a → G b a' → a = a'

theorem PrefixFree.functional {α : Type} {G : Bytes → α → Prop} (h : PrefixFree G) :
    Functional G :=
  fun _ _ _ ha ha' => (h (r := []) (r' := []) ha ha' rfl).2

/-! ## Bytes (5.1:7, REC 5.2.1) -/

/-- `Bbyte : byte = 0x00 | … | 0xFF`. -/
inductive Byte : Bytes → UInt8 → Prop where
  | mk (b : UInt8) : Byte [b] b

theorem Byte.prefixFree : PrefixFree Byte := by
  rintro _ _ r r' _ _ ⟨b⟩ ⟨b'⟩ h
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
  exact ⟨by rw [h.1], h.1⟩

/-! ## Integers (5.1:9–21, REC 5.2.2) -/

/-- `BuN(N)`, unsigned LEB128 bounded to `N` bits (5.1:9–11):

* `n:Bbyte => n` if `n < 2^7 ∧ n < 2^N`;
* `n:Bbyte m:BuN(N-7) => 2^7 * m + (n - 2^7)` if `n ≥ 2^7 ∧ N > 7`.

Non-minimal encodings are allowed up to `⌈N/7⌉` bytes; the bound on the final
byte forces its unused high bits to be zero. -/
inductive UN : Nat → Bytes → Nat → Prop where
  | byte {N : Nat} (n : UInt8) (h₁ : n.toNat < 2 ^ 7) (h₂ : n.toNat < 2 ^ N) :
      UN N [n] n.toNat
  | cont {N : Nat} (n : UInt8) {b : Bytes} {m : Nat} (h₁ : 2 ^ 7 ≤ n.toNat) (h₂ : 7 < N)
      (rest : UN (N - 7) b m) : UN N (n :: b) (2 ^ 7 * m + (n.toNat - 2 ^ 7))

/-- `Bu32 = BuN(32)` (5.1:26). -/
abbrev U32 := UN 32
/-- `Bu64 = BuN(64)` (5.1:27). -/
abbrev U64 := UN 64

/-- `BsN(N)`, signed LEB128 bounded to `N` bits (5.1:13–16):

* `n:Bbyte => n` if `n < 2^6 ∧ n < 2^(N-1)`;
* `n:Bbyte => n - 2^7` if `2^6 ≤ n < 2^7 ∧ n ≥ 2^7 - 2^(N-1)`;
* `n:Bbyte i:BsN(N-7) => 2^7 * i + (n - 2^7)` if `n ≥ 2^7 ∧ N > 7`. -/
inductive SN : Nat → Bytes → Int → Prop where
  | pos {N : Nat} (n : UInt8) (h₁ : n.toNat < 2 ^ 6) (h₂ : n.toNat < 2 ^ (N - 1)) :
      SN N [n] n.toNat
  | neg {N : Nat} (n : UInt8) (h₁ : 2 ^ 6 ≤ n.toNat) (h₂ : n.toNat < 2 ^ 7)
      (h₃ : (2 : Int) ^ 7 - 2 ^ (N - 1) ≤ n.toNat) : SN N [n] ((n.toNat : Int) - 2 ^ 7)
  | cont {N : Nat} (n : UInt8) {b : Bytes} {i : Int} (h₁ : 2 ^ 7 ≤ n.toNat) (h₂ : 7 < N)
      (rest : SN (N - 7) b i) : SN N (n :: b) (2 ^ 7 * i + ((n.toNat : Int) - 2 ^ 7))

/-- `Bs33 = BsN(33)` (5.1:29), used by block types and heap types. -/
abbrev S33 := SN 33

/-- `BiN(N) : iN(N) = i:BsN(N) => $inv_signed_(N, i)` (5.1:18–19): uninterpreted
integers are signed LEB128, stored as their two's-complement bit pattern. -/
inductive IN (N : Nat) : Bytes → BitVec N → Prop where
  | mk {b : Bytes} {i : Int} (h : SN N b i) : IN N b (BitVec.ofInt N i)

/-! ## Floating point (5.1:22–23, REC 5.2.3) -/

/-- The little-endian value of a byte string. -/
def littleEndian : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 ^ 8 * littleEndian bs

/-- `BfN(N) : fN(N) = b*:Bbyte^(N/8) => $inv_fbytes_(N, b*)`: the IEEE 754 bit
pattern in little-endian byte order. -/
inductive FN (N : Nat) : Bytes → BitVec N → Prop where
  | mk (b : Bytes) (h : b.length = N / 8) : FN N b (BitVec.ofNat N (littleEndian b))

/-! ## Sequences and vectors (5.1:39–41, REC 5.1.3) -/

/-- `(x:B)*`: a concatenation of encodings, one per element. -/
inductive Seq {α : Type} (G : Bytes → α → Prop) : Bytes → List α → Prop where
  | nil : Seq G [] []
  | cons {b bs : Bytes} {a : α} {as : List α} : G b a → Seq G bs as → Seq G (b ++ bs) (a :: as)

/-- `Blist(BX) : el* = n:Bu32 (el:BX)^n => el^n` (REC: `vec(B)`). -/
inductive Vec {α : Type} (G : Bytes → α → Prop) : Bytes → List α → Prop where
  | mk {n b : Bytes} {xs : List α} : U32 n xs.length → Seq G b xs → Vec G (n ++ b) xs

/-- A byte vector `Blist(Bbyte)`. -/
abbrev ByteVec := Vec Byte

/-! ## Names (5.1:44–67, REC 5.2.4) -/

/-- A UTF-8 continuation byte, the domain of `$cont` (see the errata above). -/
def IsCont (b : UInt8) : Prop := 0x80 ≤ b.toNat ∧ b.toNat < 0xC0

/-- `$utf8(ch)` as a relation between a scalar value and its bytes (5.1:53–64). -/
inductive Utf8Char : Char → Bytes → Prop where
  | one {c : Char} (b : UInt8) (h : c.toNat < 0x80) (e : c.toNat = b.toNat) : Utf8Char c [b]
  | two {c : Char} (b₁ b₂ : UInt8) (lo : 0x80 ≤ c.toNat) (hi : c.toNat < 0x800)
      (h₁ : 0xC0 ≤ b₁.toNat) (h₂ : IsCont b₂)
      (e : c.toNat = 2 ^ 6 * (b₁.toNat - 0xC0) + (b₂.toNat - 0x80)) : Utf8Char c [b₁, b₂]
  | three {c : Char} (b₁ b₂ b₃ : UInt8)
      (range : 0x800 ≤ c.toNat ∧ c.toNat < 0xD800 ∨ 0xE000 ≤ c.toNat ∧ c.toNat < 0x10000)
      (h₁ : 0xE0 ≤ b₁.toNat) (h₂ : IsCont b₂) (h₃ : IsCont b₃)
      (e : c.toNat = 2 ^ 12 * (b₁.toNat - 0xE0) + 2 ^ 6 * (b₂.toNat - 0x80) + (b₃.toNat - 0x80)) :
      Utf8Char c [b₁, b₂, b₃]
  | four {c : Char} (b₁ b₂ b₃ b₄ : UInt8) (lo : 0x10000 ≤ c.toNat) (hi : c.toNat < 0x110000)
      (h₁ : 0xF0 ≤ b₁.toNat) (h₂ : IsCont b₂) (h₃ : IsCont b₃) (h₄ : IsCont b₄)
      (e : c.toNat = 2 ^ 18 * (b₁.toNat - 0xF0) + 2 ^ 12 * (b₂.toNat - 0x80) +
        2 ^ 6 * (b₃.toNat - 0x80) + (b₄.toNat - 0x80)) :
      Utf8Char c [b₁, b₂, b₃, b₄]

/-- `$utf8(ch*) = $concat_(byte, $utf8(ch)*)` (5.1:52). -/
def Utf8 (cs : List Char) (b : Bytes) : Prop := Seq (fun b c => Utf8Char c b) b cs

/-- `Bname : name = b*:Blist(Bbyte) => name -- if $utf8(name) = b*` (5.1:66–67). -/
inductive Name : Bytes → String → Prop where
  | mk {b : Bytes} {bs : List UInt8} {s : String} (v : ByteVec b bs) (u : Utf8 s.toList bs) :
      Name b s

/-! ## Indices (5.1:72–82, REC 5.5.1) -/

/-- Every index production is `x:Bu32 => x`. -/
def Index {k : IndexKind} (b : Bytes) (x : Idx k) : Prop := U32 b x.toNat

/-! ## Sections (5.4:9–11, REC 5.5.2) -/

/-- `Bsection_(N, BX) : en* = N:Bbyte len:Bu32 en*:BX => en* -- if len = ||BX|| | eps => eps`. -/
inductive Section {α : Type} (N : UInt8) (G : Bytes → List α → Prop) : Bytes → List α → Prop where
  | mk {lb c : Bytes} {len : Nat} {xs : List α} (hl : U32 lb len) (hlen : len = c.length)
      (hc : G c xs) : Section N G ([N] ++ lb ++ c) xs
  | empty : Section N G [] []

/-- `Bcustom : ()* = Bname Bbyte* => ()` (5.4:16–17; REC 5.5.3 `custom ::= name byte*`). -/
inductive Custom : Bytes → List Unit → Prop where
  | mk {bn : Bytes} {nm : String} (rest : Bytes) (h : Name bn nm) : Custom (bn ++ rest) [()]

/-- `Bcustomsec : () = Bsection_(0, Bcustom) => ()` (5.4:19–20). -/
def CustomSec (b : Bytes) : Prop := ∃ xs, Section 0 Custom b xs

/-- `Bcustomsec*`: any number of custom sections, ignored by the abstract syntax. -/
inductive Customs : Bytes → Prop where
  | nil : Customs []
  | cons {b bs : Bytes} : CustomSec b → Customs bs → Customs (b ++ bs)

/-- `Bstart : start* = x:Bfuncidx => (START x)` (5.4:86–87; REC 5.5.11 `start ::= x:funcidx`). -/
inductive Start : Bytes → List FuncIdx → Prop where
  | mk {b : Bytes} {x : FuncIdx} (h : Index b x) : Start b [x]

/-- `Bstartsec : start? = startopt:Bsection_(8, Bstart) => $opt_(start, startopt)` (5.4:91–92). -/
inductive StartSec : Bytes → Option FuncIdx → Prop where
  | mk {b : Bytes} {xs : List FuncIdx} (h : Section 8 Start b xs) : StartSec b xs.head?

/-- The magic number `\0asm` (5.4:173, REC 5.5.15). -/
def magic : Bytes := [0x00, 0x61, 0x73, 0x6D]

/-- The version field `1` (5.4:174, REC 5.5.15). -/
def version : Bytes := [0x01, 0x00, 0x00, 0x00]

/-! ## Properties -/

namespace UN

/-- No `UN` encoding is empty. -/
theorem ne_nil {N : Nat} {v : Nat} (h : UN N [] v) : False := by
  cases h

/-- A byte below `2^7` ends an encoding. -/
theorem head_lt {N : Nat} {n : UInt8} {b : Bytes} {v : Nat} (h : UN N (n :: b) v)
    (hn : n.toNat < 2 ^ 7) : b = [] ∧ v = n.toNat := by
  cases h with
  | byte _ _ _ => exact ⟨rfl, rfl⟩
  | cont _ h₁ _ _ => omega

theorem lt_two_pow {N : Nat} {b : Bytes} {v : Nat} (h : UN N b v) : v < 2 ^ N := by
  induction h with
  | byte _ _ h₂ => exact h₂
  | @cont N n b m h₁ h₂ _ ih =>
    have hn := n.toNat_lt_size
    obtain ⟨k, rfl⟩ : ∃ k, N = k + 7 := ⟨N - 7, by omega⟩
    simp only [Nat.add_sub_cancel] at ih
    rw [Nat.pow_add]
    simp only [Nat.reducePow, UInt8.size] at hn h₁ ⊢
    omega

/-- At most `⌈N/7⌉` bytes. The hypothesis `0 < N` is needed: `UN 0 [0x00] 0` holds. -/
theorem length_le {N : Nat} (hN : 0 < N) {b : Bytes} {v : Nat} (h : UN N b v) :
    b.length ≤ (N + 6) / 7 := by
  induction h with
  | byte => simp only [List.length_singleton]; omega
  | cont _ _ h₂ _ ih =>
    have := ih (by omega)
    simp only [List.length_cons]
    omega

/-- A narrower encoding is also a wider one; e.g. every `u32` encoding is a `u64` encoding
of the same value. The converse fails (`u64` admits up to ten bytes). -/
theorem mono {N M : Nat} (hNM : N ≤ M) {b : Bytes} {v : Nat} (h : UN N b v) : UN M b v := by
  induction h generalizing M with
  | byte n h₁ h₂ => exact UN.byte n h₁ (Nat.lt_of_lt_of_le h₂ (Nat.pow_le_pow_right (by decide) hNM))
  | cont n h₁ h₂ _ ih => exact UN.cont n h₁ (by omega) (ih (by omega))

/-- Every in-range value has an encoding (the minimal one). -/
theorem exists_of_lt {N v : Nat} (hN : 0 < N) (hv : v < 2 ^ N) : ∃ b, UN N b v := by
  induction N using Nat.strong_induction_on generalizing v with
  | _ N ih =>
  by_cases hs : v < 2 ^ 7
  · refine ⟨[UInt8.ofNat v], ?_⟩
    have hv' : (UInt8.ofNat v).toNat = v := by
      simp only [UInt8.toNat_ofNat', Nat.reducePow] at hs ⊢
      omega
    have := UN.byte (N := N) (UInt8.ofNat v) (by rw [hv']; exact hs) (by rw [hv']; exact hv)
    rwa [hv'] at this
  · have hN7 : 7 < N := by
      apply Nat.lt_of_not_le
      intro hc
      have := Nat.pow_le_pow_right (by decide : 0 < 2) hc
      omega
    obtain ⟨b, hb⟩ := ih (N - 7) (by omega) (v := v / 2 ^ 7) (by omega) (by
      rw [Nat.div_lt_iff_lt_mul (by decide), ← Nat.pow_add, Nat.sub_add_cancel (by omega)]
      exact hv)
    have hn : (UInt8.ofNat (v % 2 ^ 7 + 2 ^ 7)).toNat = v % 2 ^ 7 + 2 ^ 7 := by
      simp only [UInt8.toNat_ofNat', Nat.reducePow]
      omega
    refine ⟨UInt8.ofNat (v % 2 ^ 7 + 2 ^ 7) :: b, ?_⟩
    have := UN.cont (UInt8.ofNat (v % 2 ^ 7 + 2 ^ 7)) (by rw [hn]; omega) hN7 hb
    rw [hn] at this
    convert this using 1
    simp only [Nat.reducePow]
    omega

theorem prefixFree (N : Nat) : PrefixFree (UN N) := by
  intro b b' r r' a a' h h' he
  induction h generalizing b' r r' a' with
  | byte n h₁ _ =>
    cases b' with
    | nil => exact (ne_nil h').elim
    | cons n' b'' =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      obtain ⟨rfl, rfl⟩ := head_lt h' h₁
      exact ⟨rfl, rfl⟩
  | cont n h₁ _ _ ih =>
    cases h' with
    | byte n' h₁' _ =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      omega
    | cont n' _ _ rest' =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      obtain ⟨rfl, rfl⟩ := ih rest' he
      exact ⟨rfl, rfl⟩

theorem functional (N : Nat) : Functional (UN N) := (prefixFree N).functional

private theorem zero_shape {N : Nat} {b : Bytes} {v : Nat} (h : UN N b v) (hv : v = 0) :
    ∃ k, b = List.replicate k 0x80 ++ [0x00] := by
  induction h with
  | byte n _ _ =>
    refine ⟨0, ?_⟩
    have : n = 0 := UInt8.toNat_inj.mp (by rw [hv]; rfl)
    simp [this]
  | cont n h₁ _ _ ih =>
    obtain ⟨k, rfl⟩ := ih (by omega)
    refine ⟨k + 1, ?_⟩
    have : n = 0x80 := UInt8.toNat_inj.mp (by
      have := n.toNat_lt_size
      simp only [Nat.reducePow, UInt8.size] at this h₁ hv
      show n.toNat = 128
      omega)
    simp [this, List.replicate_succ]

private theorem zero_enc {N : Nat} (k : Nat) (hk : 7 * k < N) :
    UN N (List.replicate k 0x80 ++ [0x00]) 0 := by
  induction k generalizing N with
  | zero => exact UN.byte (N := N) 0 (by decide) (Nat.two_pow_pos N)
  | succ k ih =>
    have := UN.cont (N := N) 0x80 (by decide) (by omega) (ih (N := N - 7) (by omega))
    simpa [List.replicate_succ] using this

/-- The `u32` encodings of zero are `0x80^k 0x00` with `k ≤ 4`. -/
theorem u32_zero_iff (b : Bytes) :
    U32 b 0 ↔ ∃ k, k ≤ 4 ∧ b = List.replicate k 0x80 ++ [0x00] := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := zero_shape h rfl
    have := length_le (by decide) h
    simp only [List.length_append, List.length_replicate, List.length_singleton] at this
    exact ⟨k, by omega, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact zero_enc k (by omega)

end UN

namespace SN

theorem bounds {N : Nat} {b : Bytes} {i : Int} (h : SN N b i) :
    -(2 : Int) ^ (N - 1) ≤ i ∧ i < 2 ^ (N - 1) := by
  induction h with
  | @pos N n _ h₂ =>
    have e : ((2 ^ (N - 1) : Nat) : Int) = (2 : Int) ^ (N - 1) := by simp
    have := Nat.two_pow_pos (N - 1)
    rw [← e]
    omega
  | @neg N n h₁ _ h₃ =>
    have e : ((2 ^ (N - 1) : Nat) : Int) = (2 : Int) ^ (N - 1) := by simp
    have := Nat.two_pow_pos (N - 1)
    rw [← e] at h₃ ⊢
    simp only [Int.reducePow, Nat.reducePow] at h₁ h₃ ⊢
    omega
  | @cont N n b i h₁ h₂ _ ih =>
    have hn := n.toNat_lt_size
    have e : (2 : Int) ^ (N - 1) = 2 ^ 7 * 2 ^ (N - 7 - 1) := by
      rw [← Int.pow_add]
      congr 1
      omega
    rw [e]
    simp only [Int.reducePow, Nat.reducePow, UInt8.size] at h₁ hn ih ⊢
    omega

/-- At most `⌈N/7⌉` bytes. The hypothesis `0 < N` is needed: `SN 0 [0x00] 0` holds
(`2 ^ (0 - 1) = 1` in `Nat`). -/
theorem length_le {N : Nat} (hN : 0 < N) {b : Bytes} {i : Int} (h : SN N b i) :
    b.length ≤ (N + 6) / 7 := by
  induction h with
  | pos => simp only [List.length_singleton]; omega
  | neg => simp only [List.length_singleton]; omega
  | cont _ _ h₂ _ ih =>
    have := ih (by omega)
    simp only [List.length_cons]
    omega

theorem mono {N M : Nat} (hNM : N ≤ M) {b : Bytes} {i : Int} (h : SN N b i) : SN M b i := by
  induction h generalizing M with
  | pos n h₁ h₂ =>
    exact SN.pos n h₁ (Nat.lt_of_lt_of_le h₂ (Nat.pow_le_pow_right (by decide) (by omega)))
  | @neg N n h₁ h₂ h₃ =>
    have : (2 : Int) ^ (N - 1) ≤ 2 ^ (M - 1) := by
      exact_mod_cast Nat.pow_le_pow_right (by decide) (show N - 1 ≤ M - 1 by omega)
    exact SN.neg n h₁ h₂ (by omega)
  | cont n h₁ h₂ _ ih => exact SN.cont n h₁ (by omega) (ih (by omega))

private theorem head_lt {N : Nat} {n : UInt8} {b : Bytes} {i : Int} (h : SN N (n :: b) i)
    (hn : n.toNat < 2 ^ 7) :
    b = [] ∧ i = (if n.toNat < 2 ^ 6 then (n.toNat : Int) else (n.toNat : Int) - 2 ^ 7) := by
  cases h with
  | pos _ h₁ _ => exact ⟨rfl, (ite_eq_left h₁).symm⟩
  | neg _ h₁ _ _ => exact ⟨rfl, (ite_eq_right (by omega)).symm⟩
  | cont _ h₁ _ _ => omega

theorem prefixFree (N : Nat) : PrefixFree (SN N) := by
  intro b b' r r' a a' h h' he
  induction h generalizing b' r r' a' with
  | pos n h₁ _ =>
    cases b' with
    | nil => cases h'
    | cons n' b'' =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      obtain ⟨rfl, rfl⟩ := head_lt h' (by omega)
      exact ⟨rfl, (ite_eq_left h₁).symm⟩
  | neg n h₁ h₂ _ =>
    cases b' with
    | nil => cases h'
    | cons n' b'' =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      obtain ⟨rfl, rfl⟩ := head_lt h' h₂
      exact ⟨rfl, (ite_eq_right (by omega)).symm⟩
  | cont n h₁ _ _ ih =>
    cases h' with
    | pos n' h₁' _ =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      omega
    | neg n' _ h₂' _ =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      omega
    | cont n' _ _ rest' =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      obtain ⟨rfl, rfl⟩ := ih rest' he
      exact ⟨rfl, rfl⟩

theorem functional (N : Nat) : Functional (SN N) := (prefixFree N).functional

end SN

theorem IN.prefixFree (N : Nat) : PrefixFree (IN N) := by
  intro _ _ _ _ _ _ h h' he
  cases h with
  | mk hs =>
    cases h' with
    | mk hs' =>
      obtain ⟨rfl, rfl⟩ := SN.prefixFree N hs hs' he
      exact ⟨rfl, rfl⟩

theorem FN.prefixFree (N : Nat) : PrefixFree (FN N) := by
  intro _ _ r r' _ _ ha ha' h
  cases ha with
  | mk hb =>
    cases ha' with
    | mk hb' =>
      obtain ⟨rfl, -⟩ := List.append_inj h (hb.trans hb'.symm)
      exact ⟨rfl, rfl⟩

/-- A sequence of a prefix-free production with no empty encoding is functional.
The hypothesis `hne` is needed: for `G b () := b = []`, `Seq G [] []` and
`Seq G [] [()]` both hold. (`Vec.prefixFree` needs no such hypothesis, since the
count is fixed.) -/
theorem Seq.functional {α : Type} {G : Bytes → α → Prop} (h : PrefixFree G)
    (hne : ∀ a, ¬ G [] a) : Functional (Seq G) := by
  intro b xs ys hs hs'
  induction hs generalizing ys with
  | nil =>
    generalize hb : ([] : Bytes) = x at hs'
    cases hs' with
    | nil => rfl
    | @cons b0 bs0 _ _ hg _ =>
      rcases b0 with _ | ⟨y, b0⟩
      · exact (hne _ hg).elim
      · simp at hb
  | @cons b bs a as hg _ ih =>
    generalize hb : b ++ bs = x at hs'
    cases hs' with
    | nil =>
      rcases b with _ | ⟨y, b⟩
      · exact (hne _ hg).elim
      · simp at hb
    | cons hg' hs' =>
      obtain ⟨rfl, rfl⟩ := h hg hg' hb
      obtain rfl := List.append_cancel_left hb
      rw [ih hs']

private theorem Seq.prefixFree_len {α : Type} {G : Bytes → α → Prop} (h : PrefixFree G) :
    ∀ {b b' r r' : Bytes} {xs xs' : List α}, Seq G b xs → Seq G b' xs' →
      xs.length = xs'.length → b ++ r = b' ++ r' → b = b' ∧ xs = xs' := by
  intro b b' r r' xs xs' hs hs' hl he
  induction hs generalizing b' r r' xs' with
  | nil =>
    cases hs' with
    | nil => exact ⟨rfl, rfl⟩
    | cons => simp at hl
  | cons hg _ ih =>
    cases hs' with
    | nil => simp at hl
    | cons hg' hs' =>
      simp only [List.append_assoc] at he
      obtain ⟨rfl, rfl⟩ := h hg hg' he
      obtain ⟨rfl, rfl⟩ := ih hs' (by simpa using hl) (List.append_cancel_left he)
      exact ⟨rfl, rfl⟩

theorem Vec.prefixFree {α : Type} {G : Bytes → α → Prop} (h : PrefixFree G) :
    PrefixFree (Vec G) := by
  intro _ _ _ _ _ _ h1 h2 he
  cases h1 with
  | mk hn hc =>
    cases h2 with
    | mk hn' hc' =>
      simp only [List.append_assoc] at he
      obtain ⟨rfl, hl⟩ := UN.prefixFree 32 hn hn' he
      obtain ⟨rfl, rfl⟩ := Seq.prefixFree_len h hc hc' hl (List.append_cancel_left he)
      exact ⟨rfl, rfl⟩

/-- The number of continuation bytes announced by a UTF-8 leading byte. -/
private def utf8Len (b : UInt8) : Nat :=
  if b.toNat < 0x80 then 0 else if b.toNat < 0xE0 then 1 else if b.toNat < 0xF0 then 2 else 3

private theorem Utf8Char.shape {c : Char} {b : Bytes} (h : Utf8Char c b) :
    ∃ b₀ t, b = b₀ :: t ∧ t.length = utf8Len b₀ := by
  cases h with
  | one b h e =>
    refine ⟨b, [], rfl, ?_⟩
    unfold utf8Len
    rw [ite_eq_left (by omega)]
    rfl
  | two b₁ b₂ lo hi h₁ h₂ e =>
    refine ⟨b₁, [b₂], rfl, ?_⟩
    unfold utf8Len
    simp only [Nat.reducePow] at e
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    rfl
  | three b₁ b₂ b₃ range h₁ h₂ h₃ e =>
    refine ⟨b₁, [b₂, b₃], rfl, ?_⟩
    unfold utf8Len
    simp only [Nat.reducePow] at e
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
    rfl
  | four b₁ b₂ b₃ b₄ lo hi h₁ h₂ h₃ h₄ e =>
    refine ⟨b₁, [b₂, b₃, b₄], rfl, ?_⟩
    unfold utf8Len
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    rfl

private theorem char_eq_of_toNat_eq {c c' : Char} (h : c.toNat = c'.toNat) : c = c' :=
  Char.ext (UInt32.toNat_inj.mp h)

private theorem Utf8Char.prefixFree : PrefixFree (fun b c => Utf8Char c b) := by
  intro b b' r r' c c' h h' he
  obtain ⟨b₀, t, rfl, ht⟩ := Utf8Char.shape h
  obtain ⟨b₀', t', rfl, ht'⟩ := Utf8Char.shape h'
  simp only [List.cons_append, List.cons.injEq] at he
  obtain ⟨rfl, he⟩ := he
  obtain ⟨rfl, -⟩ := List.append_inj he (ht.trans ht'.symm)
  refine ⟨rfl, char_eq_of_toNat_eq ?_⟩
  cases h <;> cases h' <;> omega

theorem Utf8.functional : Functional (fun b (s : List Char) => Utf8 s b) :=
  fun _ _ _ h h' => Seq.functional Utf8Char.prefixFree (fun _ h => by cases h) h h'

private theorem utf8Char_encode (c : Char) : Utf8Char c (String.utf8EncodeChar c) := by
  have hv : c.toNat < 0xd800 ∨ (0xdfff < c.toNat ∧ c.toNat < 0x110000) := c.valid
  have hn : c.toNat = c.val.toNat := rfl
  unfold String.utf8EncodeChar
  dsimp only
  split
  · exact Utf8Char.one _ (by omega) (by simp only [UInt8.toNat_ofNat']; omega)
  · split
    · exact Utf8Char.two _ _ (by omega) (by omega) (by simp only [UInt8.toNat_ofNat']; omega)
        ⟨by simp only [UInt8.toNat_ofNat']; omega, by simp only [UInt8.toNat_ofNat']; omega⟩
        (by simp only [UInt8.toNat_ofNat', Nat.reducePow]; omega)
    · split
      · exact Utf8Char.three _ _ _ (by omega) (by simp only [UInt8.toNat_ofNat']; omega)
          ⟨by simp only [UInt8.toNat_ofNat']; omega, by simp only [UInt8.toNat_ofNat']; omega⟩
          ⟨by simp only [UInt8.toNat_ofNat']; omega, by simp only [UInt8.toNat_ofNat']; omega⟩
          (by simp only [UInt8.toNat_ofNat', Nat.reducePow]; omega)
      · exact Utf8Char.four _ _ _ _ (by omega) (by omega)
          (by simp only [UInt8.toNat_ofNat']; omega)
          ⟨by simp only [UInt8.toNat_ofNat']; omega, by simp only [UInt8.toNat_ofNat']; omega⟩
          ⟨by simp only [UInt8.toNat_ofNat']; omega, by simp only [UInt8.toNat_ofNat']; omega⟩
          ⟨by simp only [UInt8.toNat_ofNat']; omega, by simp only [UInt8.toNat_ofNat']; omega⟩
          (by simp only [UInt8.toNat_ofNat', Nat.reducePow]; omega)

/-- The specification's UTF-8 relation agrees with Lean's encoder. -/
theorem Utf8.toUTF8 (s : String) : Utf8 s.toList s.toUTF8.data.toList := by
  rw [String.toUTF8_eq_toByteArray, ← String.utf8Encode_toList, List.utf8Encode,
    List.toList_data_toByteArray]
  generalize s.toList = l
  induction l with
  | nil => exact Seq.nil
  | cons c l ih =>
    rw [List.flatMap_cons]
    exact Seq.cons (utf8Char_encode c) ih

theorem Name.prefixFree : PrefixFree Name := by
  intro _ _ _ _ _ _ h h' he
  cases h with
  | mk v u =>
    cases h' with
    | mk v' u' =>
      obtain ⟨rfl, rfl⟩ := Vec.prefixFree Byte.prefixFree v v' he
      exact ⟨rfl, String.toList_injective (Utf8.functional u u')⟩

theorem Index.prefixFree {k : IndexKind} : PrefixFree (Index (k := k)) := by
  intro _ _ _ _ x x' h h' he
  obtain ⟨rfl, hx⟩ := UN.prefixFree 32 h h' he
  refine ⟨rfl, ?_⟩
  cases x
  cases x'
  simp only [Idx.toNat] at hx
  exact congrArg Idx.mk (Fin.ext hx)

end Silmaril.Wasm.Binary
