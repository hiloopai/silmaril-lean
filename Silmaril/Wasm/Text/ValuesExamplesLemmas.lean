module

public import Silmaril.Wasm.Text.Values

/-!
# Computation lemmas for the literal relations of `Values.lean`

Executable characterisations of the character-level relations of
`Silmaril/Wasm/Text/Values.lean`, used by `ValuesExamples.lean` to discharge
concrete literal examples by `decide` (kernel reduction):

* `numVal?` / `hexNumVal?` — `Num` / `HexNum` as partial functions
  (`num_iff`, `hexNum_iff`), via a generic snoc-inductive `Digits` and a
  forward scanner `digitsGo`;
* `splits` — all ways of cutting a list in two, turning the `cs = a ++ b`
  existentials of the grammar into a finite search;
* candidate lists `signCands`, `unCands`, `snCands`, `inCands`, `mantCands`,
  `expCands`, `fmagCands`, `fnCands` with membership characterisations
  (`signChars_iff`, `un_iff`, `sn_iff`, `in_iff`, `mant_iff`, `expPart_iff`,
  `fmag_iff`, `fn_iff`).

These are *completeness and soundness* statements (every derivation is
enumerated), not functionality statements: the candidate lists may a priori
contain several values.
-/

@[expose] public section

namespace Silmaril.Wasm.Text.ValuesExamples

open Silmaril Silmaril.Formats.SExpEncoding Silmaril.Formats.SExpEncoding.Wat
open Silmaril.Wasm.Text

/-! ## Generic digit strings -/

/-- Digit strings in radix `rad` with single `_` separators (the common shape
of `Num` and `HexNum`). -/
inductive Digits (rad : Nat) (isD : Char → Bool) (val : Char → Nat) : Chars → Nat → Prop where
  | one {d : Char} : isD d = true → Digits rad isD val [d] (val d)
  | snoc {ds : Chars} {n : Nat} {d : Char} : Digits rad isD val ds n → isD d = true →
      Digits rad isD val (ds ++ [d]) (rad * n + val d)
  | snocSep {ds : Chars} {n : Nat} {d : Char} : Digits rad isD val ds n → isD d = true →
      Digits rad isD val (ds ++ ['_', d]) (rad * n + val d)

/-- Forward scanner after at least one digit, with accumulated value `acc`. -/
def digitsGo (rad : Nat) (isD : Char → Bool) (val : Char → Nat) (acc : Nat) : Chars → Option Nat
  | [] => some acc
  | c :: r =>
    if c = '_' then
      match r with
      | [] => none
      | d :: r' => if isD d then digitsGo rad isD val (rad * acc + val d) r' else none
    else if isD c then digitsGo rad isD val (rad * acc + val c) r else none

/-- The value of a digit string, if it is one. -/
def digitsVal? (rad : Nat) (isD : Char → Bool) (val : Char → Nat) : Chars → Option Nat
  | [] => none
  | d :: r => if isD d then digitsGo rad isD val (val d) r else none

section Digits

variable {rad : Nat} {isD : Char → Bool} {val : Char → Nat}

theorem digitsGo_sound (hs : isD '_' = false) :
    ∀ (r : Chars) {ds : Chars} {acc n : Nat}, Digits rad isD val ds acc →
      digitsGo rad isD val acc r = some n → Digits rad isD val (ds ++ r) n
  | [], _, _, _, h, e => by
    simp only [digitsGo, Option.some.injEq] at e; subst e; simpa using h
  | [c], ds, acc, n, h, e => by
    by_cases hc : c = '_'
    · simp [digitsGo, hc] at e
    · simp only [digitsGo, hc, ite_false] at e
      split at e
      · simp only [Option.some.injEq] at e; subst e; exact .snoc h (by assumption)
      · cases e
  | c :: d :: r, ds, acc, n, h, e => by
    by_cases hc : c = '_'
    · subst hc
      simp only [digitsGo, ite_true] at e
      split at e
      · have := digitsGo_sound hs r (Digits.snocSep h (by assumption)) e
        simpa using this
      · cases e
    · simp only [digitsGo, hc, ite_false] at e
      split at e
      · have := digitsGo_sound hs (d :: r) (Digits.snoc h (by assumption)) e
        simpa using this
      · cases e

theorem digitsGo_ne_under {c : Char} (hs : isD '_' = false) (hc : isD c = true) : c ≠ '_' := by
  rintro rfl; rw [hs] at hc; cases hc

theorem digitsGo_snoc (hs : isD '_' = false) {d : Char} (hd : isD d = true) :
    ∀ (r : Chars) {acc k : Nat}, digitsGo rad isD val acc r = some k →
      digitsGo rad isD val acc (r ++ [d]) = some (rad * k + val d) ∧
      digitsGo rad isD val acc (r ++ ['_', d]) = some (rad * k + val d)
  | [], acc, k, e => by
    simp only [digitsGo, Option.some.injEq] at e; subst e
    simp [digitsGo, digitsGo_ne_under hs hd, hd]
  | [c], acc, k, e => by
    by_cases hc : c = '_'
    · simp [digitsGo, hc] at e
    · simp only [digitsGo, hc, ite_false] at e
      split at e
      · rename_i hc'
        simp only [Option.some.injEq] at e; subst e
        simp [digitsGo, hc, hc', digitsGo_ne_under hs hd, hd]
      · cases e
  | c :: d' :: r, acc, k, e => by
    by_cases hc : c = '_'
    · subst hc
      simp only [digitsGo, ite_true] at e
      split at e
      · rename_i hd'
        have := digitsGo_snoc hs hd r e
        simpa [digitsGo, hd'] using this
      · cases e
    · simp only [digitsGo, hc, ite_false] at e
      split at e
      · rename_i hc'
        have := digitsGo_snoc hs hd (d' :: r) e
        simpa [digitsGo, hc, hc'] using this
      · cases e

theorem Digits.ne_nil {cs : Chars} {n : Nat} (h : Digits rad isD val cs n) : cs ≠ [] := by
  cases h <;> simp

theorem digitsVal?_iff (hs : isD '_' = false) {cs : Chars} {n : Nat} :
    Digits rad isD val cs n ↔ digitsVal? rad isD val cs = some n := by
  constructor
  · intro h
    induction h with
    | @one d hd => simp [digitsVal?, digitsGo, hd]
    | @snoc ds n d h hd ih =>
      cases ds with
      | nil => exact absurd rfl h.ne_nil
      | cons d0 ds =>
        simp only [digitsVal?] at ih
        split at ih
        · rename_i h0
          simp [digitsVal?, h0, (digitsGo_snoc hs hd ds ih).1]
        · cases ih
    | @snocSep ds n d h hd ih =>
      cases ds with
      | nil => exact absurd rfl h.ne_nil
      | cons d0 ds =>
        simp only [digitsVal?] at ih
        split at ih
        · rename_i h0
          simp [digitsVal?, h0, (digitsGo_snoc hs hd ds ih).2]
        · cases ih
  · intro h
    cases cs with
    | nil => cases h
    | cons d r =>
      simp only [digitsVal?] at h
      split at h
      · exact digitsGo_sound hs r (Digits.one (by assumption)) h
      · cases h

end Digits

/-! ## `Num` and `HexNum` -/

/-- Decimal digit test. -/
def isDec (d : Char) : Bool := decide ('0' ≤ d ∧ d ≤ '9')

/-- Decimal digit value. -/
def decVal (d : Char) : Nat := d.toNat - '0'.toNat

/-- Hexadecimal digit test. -/
def isHex (d : Char) : Bool := decide (IsHexDigit d)

/-- `Tnum` as a partial function. -/
def numVal? : Chars → Option Nat := digitsVal? 10 isDec decVal

/-- `Thexnum` as a partial function. -/
def hexNumVal? : Chars → Option Nat := digitsVal? 16 isHex hexVal

theorem num_digits {cs : Chars} {n : Nat} : Num cs n ↔ Digits 10 isDec decVal cs n := by
  constructor
  · intro h
    induction h with
    | one hd => exact .one (by simpa [isDec] using hd)
    | snoc _ hd ih => exact .snoc ih (by simpa [isDec] using hd)
    | snocSep _ hd ih => exact .snocSep ih (by simpa [isDec] using hd)
  · intro h
    induction h with
    | one hd => exact .one (by simpa [isDec] using hd)
    | snoc _ hd ih => exact .snoc ih (by simpa [isDec] using hd)
    | snocSep _ hd ih => exact .snocSep ih (by simpa [isDec] using hd)

theorem hexNum_digits {cs : Chars} {n : Nat} : HexNum cs n ↔ Digits 16 isHex hexVal cs n := by
  constructor
  · intro h
    induction h with
    | one hd => exact .one (by simpa [isHex] using hd)
    | snoc _ hd ih => exact .snoc ih (by simpa [isHex] using hd)
    | snocSep _ hd ih => exact .snocSep ih (by simpa [isHex] using hd)
  · intro h
    induction h with
    | one hd => exact .one (by simpa [isHex] using hd)
    | snoc _ hd ih => exact .snoc ih (by simpa [isHex] using hd)
    | snocSep _ hd ih => exact .snocSep ih (by simpa [isHex] using hd)

theorem num_iff {cs : Chars} {n : Nat} : Num cs n ↔ numVal? cs = some n :=
  num_digits.trans (digitsVal?_iff (by decide))

theorem hexNum_iff {cs : Chars} {n : Nat} : HexNum cs n ↔ hexNumVal? cs = some n :=
  hexNum_digits.trans (digitsVal?_iff (by decide))

/-- `Num` or `HexNum` according to `hex` (as in `Mant`). -/
def radixVal? (hex : Bool) : Chars → Option Nat := if hex then hexNumVal? else numVal?

theorem radix_iff {hex : Bool} {cs : Chars} {n : Nat} :
    (if hex then HexNum else Num) cs n ↔ radixVal? hex cs = some n := by
  cases hex <;> simp [radixVal?, num_iff, hexNum_iff]

/-! ## Splitting lists -/

/-- All ways of cutting a list into a prefix and a suffix. -/
def splits {α : Type} (l : List α) : List (List α × List α) :=
  (List.range (l.length + 1)).map fun i => (l.take i, l.drop i)

theorem mem_splits {α : Type} {l : List α} {p : List α × List α} :
    p ∈ splits l ↔ l = p.1 ++ p.2 := by
  obtain ⟨a, b⟩ := p
  simp only [splits, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨i, -, rfl, rfl⟩; simp
  · rintro rfl; exact ⟨a.length, by simp; omega, by simp, by simp⟩

theorem prefix_iff {α : Type} {cs pre : List α} {P : List α → Prop} :
    (∃ ds, cs = pre ++ ds ∧ P ds) ↔ cs.take pre.length = pre ∧ P (cs.drop pre.length) := by
  constructor
  · rintro ⟨ds, rfl, h⟩; simp [h]
  · rintro ⟨h1, h2⟩
    exact ⟨_, by rw [← List.take_append_drop pre.length cs, h1]; simp, h2⟩

theorem cons_iff {α : Type} {q : List α} {c : α} {P : List α → Prop} :
    (∃ f, q = c :: f ∧ P f) ↔ q.head? = some c ∧ P q.tail := by
  cases q <;> simp [eq_comm]

/-! ## Integers -/

/-- `Tsign` candidates. -/
def signCands (cs : Chars) : List Int :=
  if cs = [] then [1] else if cs = ['+'] then [1] else if cs = ['-'] then [-1] else []

theorem signChars_iff {cs : Chars} {s : Int} : SignChars cs s ↔ s ∈ signCands cs := by
  unfold SignChars signCands
  by_cases h1 : cs = [] <;> by_cases h2 : cs = ['+'] <;> by_cases h3 : cs = ['-'] <;>
    simp_all

/-- `TuN(N)` candidates. -/
def unCands (N : Nat) (cs : Chars) : List Nat :=
  ((numVal? cs).toList ++
    (if cs.take 2 = ['0', 'x'] then (hexNumVal? (cs.drop 2)).toList else [])).filter
    (fun n => decide (n < 2 ^ N))

theorem un_iff {N : Nat} {cs : Chars} {n : Nat} : UN N cs n ↔ n ∈ unCands N cs := by
  have hp := prefix_iff (cs := cs) (pre := ['0', 'x']) (P := fun ds => HexNum ds n)
  simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil] at hp
  unfold UN unCands
  rw [hp]
  by_cases h : cs.take 2 = ['0', 'x'] <;> simp [h, num_iff, hexNum_iff, eq_comm, or_and_right]

/-- `TsN(N)` candidates. -/
def snCands (N : Nat) (cs : Chars) : List Int :=
  (splits cs).flatMap fun p => (signCands p.1).flatMap fun s => (unCands N p.2).filterMap
    fun (n : Nat) => if -(2 ^ (N - 1) : Int) ≤ s * (n : Int) ∧ s * (n : Int) < 2 ^ (N - 1) then
      some (s * (n : Int)) else none

theorem sn_iff {N : Nat} {cs : Chars} {i : Int} : SN N cs i ↔ i ∈ snCands N cs := by
  unfold SN snCands
  simp only [List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨sc, rest, s, n, rfl, hs, hu, rfl, h1, h2⟩
    exact ⟨(sc, rest), mem_splits.2 rfl, s, signChars_iff.1 hs, n, un_iff.1 hu, by simp [h1, h2]⟩
  · rintro ⟨⟨sc, rest⟩, hp, s, hs, n, hn, he⟩
    split at he
    · rename_i hr
      simp only [Option.some.injEq] at he; subst he
      exact ⟨sc, rest, s, n, mem_splits.1 hp, signChars_iff.2 hs, un_iff.2 hn, rfl, hr.1, hr.2⟩
    · cases he

/-- `TiN(N)` candidates. -/
def inCands (N : Nat) (cs : Chars) : List (BitVec N) :=
  (unCands N cs).map (BitVec.ofNat N) ++ (snCands N cs).map (BitVec.ofInt N)

theorem in_iff {N : Nat} {cs : Chars} {b : BitVec N} : IN N cs b ↔ b ∈ inCands N cs := by
  unfold IN inCands
  simp only [un_iff, sn_iff, List.mem_append, List.mem_map]
  constructor
  · rintro (⟨n, h, rfl⟩ | ⟨i, h, rfl⟩)
    · exact Or.inl ⟨n, h, rfl⟩
    · exact Or.inr ⟨i, h, rfl⟩
  · rintro (⟨n, h, rfl⟩ | ⟨i, h, rfl⟩)
    · exact Or.inl ⟨n, h, rfl⟩
    · exact Or.inr ⟨i, h, rfl⟩

/-! ## Floats -/

/-- `Tmant`/`Thexmant` candidates `(m, k)`. -/
def mantCands (hex : Bool) (cs : Chars) : List (Nat × Nat) :=
  (radixVal? hex cs).toList.map (·, 0) ++
  ((splits cs).flatMap fun p =>
    if p.2 = ['.'] then (radixVal? hex p.1).toList.map (·, 0) else []) ++
  ((splits cs).flatMap fun p =>
    if p.2.head? = some '.' then
      (radixVal? hex p.1).toList.flatMap fun n => (radixVal? hex p.2.tail).toList.map fun v =>
        (n * (if hex then 16 else 10) ^ digitCount p.2.tail + v, digitCount p.2.tail)
    else [])

theorem mant_iff {hex : Bool} {cs : Chars} {m k : Nat} :
    Mant hex cs m k ↔ (m, k) ∈ mantCands hex cs := by
  unfold Mant mantCands
  simp only [radix_iff, List.mem_append, List.mem_map, List.mem_flatMap, Option.mem_toList,
    Prod.mk.injEq]
  constructor
  · rintro (⟨h, rfl⟩ | ⟨p, rfl, h, rfl⟩ | ⟨p, f, n, v, rfl, hn, hv, rfl, rfl⟩)
    · exact Or.inl (Or.inl ⟨m, h, rfl, rfl⟩)
    · exact Or.inl (Or.inr ⟨(p, ['.']), mem_splits.2 rfl, by simp [h]⟩)
    · refine Or.inr ⟨(p, '.' :: f), mem_splits.2 rfl, ?_⟩
      simp [hn, hv]
  · rintro ((⟨m', h, rfl, rfl⟩ | ⟨pq, hp, hq⟩) | ⟨pq, hp, hq⟩)
    · exact Or.inl ⟨h, rfl⟩
    · obtain ⟨p, q⟩ := pq
      have hp := mem_splits.1 hp
      simp only at hp hq
      split at hq
      · rename_i hq'
        subst hq' hp
        simp only [List.mem_map, Option.mem_toList, Prod.mk.injEq] at hq
        obtain ⟨m', h, rfl, rfl⟩ := hq
        exact Or.inr (Or.inl ⟨p, rfl, h, rfl⟩)
      · simp at hq
    · obtain ⟨p, q⟩ := pq
      have hp := mem_splits.1 hp
      simp only at hp hq
      split at hq
      · rename_i hq'
        subst hp
        simp only [List.mem_flatMap, List.mem_map, Option.mem_toList, Prod.mk.injEq] at hq
        obtain ⟨n, hn, v, hv, rfl, rfl⟩ := hq
        cases q with
        | nil => simp at hq'
        | cons c f =>
          simp only [List.head?_cons, Option.some.injEq] at hq'
          subst hq'
          exact Or.inr (Or.inr ⟨p, f, n, v, rfl, hn, hv, rfl, rfl⟩)
      · simp at hq

/-- The exponent mark condition of `ExpPart`. -/
def MarkOk (hex : Bool) (c : Char) : Prop :=
  (hex = true ∧ (c = 'p' ∨ c = 'P')) ∨ (hex = false ∧ (c = 'e' ∨ c = 'E'))

instance (hex : Bool) (c : Char) : Decidable (MarkOk hex c) := by
  unfold MarkOk; infer_instance

/-- Exponent-part candidates. -/
def expCands (hex : Bool) : Chars → List Int
  | [] => [0]
  | mark :: rest =>
    if MarkOk hex mark then
      (splits rest).flatMap fun p => (signCands p.1).flatMap fun s =>
        (numVal? p.2).toList.map fun (n : Nat) => s * (n : Int)
    else []

theorem expPart_iff {hex : Bool} {cs : Chars} {e : Int} :
    ExpPart hex cs e ↔ e ∈ expCands hex cs := by
  unfold ExpPart
  cases cs with
  | nil => simp [expCands]
  | cons mark rest =>
    have hm : (if hex then mark = 'p' ∨ mark = 'P' else mark = 'e' ∨ mark = 'E') ↔
        MarkOk hex mark := by
      cases hex <;> simp [MarkOk]
    simp only [reduceCtorEq, false_and, false_or, List.cons.injEq, expCands]
    constructor
    · rintro ⟨_, sc, ds, s, n, ⟨rfl, rfl⟩, hk, hs, hn, rfl⟩
      simp only [hm.1 hk, ↓reduceIte, List.mem_flatMap, List.mem_map, Option.mem_toList]
      exact ⟨(sc, ds), mem_splits.2 rfl, s, signChars_iff.1 hs, n, num_iff.1 hn, rfl⟩
    · intro h
      split at h
      · rename_i hk
        simp only [List.mem_flatMap, List.mem_map, Option.mem_toList] at h
        obtain ⟨⟨sc, ds⟩, hp, s, hs, n, hn, rfl⟩ := h
        exact ⟨mark, sc, ds, s, n, ⟨rfl, mem_splits.1 hp⟩, hm.2 hk, signChars_iff.2 hs,
          num_iff.2 hn, rfl⟩
      · simp at h

theorem mem_ite_nil {α : Type} {c : Prop} [Decidable c] {l : List α} {a : α} :
    a ∈ (if c then l else []) ↔ c ∧ a ∈ l := by
  by_cases h : c <;> simp [h]

/-- `TfNmag` candidates. -/
def fmagCands (cs : Chars) : List FloatMag :=
  ((splits cs).flatMap fun p => (mantCands false p.1).flatMap fun mk =>
    (expCands false p.2).map fun e => .dec mk.1 (e - mk.2)) ++
  (if cs.take 2 = ['0', 'x'] then
    (splits (cs.drop 2)).flatMap fun p => (mantCands true p.1).flatMap fun mk =>
      (expCands true p.2).map fun e => .hex mk.1 (e - 4 * mk.2)
   else []) ++
  (if cs = "inf".toList then [.inf] else []) ++
  (if cs = "nan".toList then [.nan] else []) ++
  (if cs.take "nan:0x".toList.length = "nan:0x".toList then
    (hexNumVal? (cs.drop "nan:0x".toList.length)).toList.map .nanPayload else [])

theorem fmag_iff {cs : Chars} {v : FloatMag} : FMag cs v ↔ v ∈ fmagCands cs := by
  have hx := prefix_iff (cs := cs) (pre := ['0', 'x'])
    (P := fun ds => ∃ mc ec m k e, ds = mc ++ ec ∧ Mant true mc m k ∧ ExpPart true ec e ∧
      v = .hex m (e - 4 * k))
  have hn := prefix_iff (cs := cs) (pre := "nan:0x".toList)
    (P := fun ds => ∃ n, HexNum ds n ∧ v = .nanPayload n)
  simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil] at hx
  have hx' : (∃ mc ec m k e, cs = '0' :: 'x' :: (mc ++ ec) ∧ Mant true mc m k ∧
      ExpPart true ec e ∧ v = .hex m (e - 4 * k)) ↔ ∃ ds, cs = '0' :: 'x' :: ds ∧
      ∃ mc ec m k e, ds = mc ++ ec ∧ Mant true mc m k ∧ ExpPart true ec e ∧
        v = .hex m (e - 4 * k) := by
    constructor
    · rintro ⟨mc, ec, m, k, e, rfl, h⟩; exact ⟨_, rfl, mc, ec, m, k, e, rfl, h⟩
    · rintro ⟨_, rfl, mc, ec, m, k, e, rfl, h⟩; exact ⟨mc, ec, m, k, e, rfl, h⟩
  have hn' : (∃ ds n, cs = "nan:0x".toList ++ ds ∧ HexNum ds n ∧ v = .nanPayload n) ↔
      ∃ ds, cs = "nan:0x".toList ++ ds ∧ ∃ n, HexNum ds n ∧ v = .nanPayload n := by
    constructor
    · rintro ⟨ds, n, rfl, h⟩; exact ⟨ds, rfl, n, h⟩
    · rintro ⟨ds, rfl, n, h⟩; exact ⟨ds, n, rfl, h⟩
  have hdec : (∃ mc ec m k e, cs = mc ++ ec ∧ Mant false mc m k ∧ ExpPart false ec e ∧
      v = .dec m (e - k)) ↔ v ∈ (splits cs).flatMap fun p => (mantCands false p.1).flatMap
        fun mk => (expCands false p.2).map fun e => FloatMag.dec mk.1 (e - mk.2) := by
    simp only [List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨mc, ec, m, k, e, rfl, hm, he, rfl⟩
      exact ⟨(mc, ec), mem_splits.2 rfl, (m, k), mant_iff.1 hm, e, expPart_iff.1 he, rfl⟩
    · rintro ⟨⟨mc, ec⟩, hp, ⟨m, k⟩, hm, e, he, rfl⟩
      exact ⟨mc, ec, m, k, e, mem_splits.1 hp, mant_iff.2 hm, expPart_iff.2 he, rfl⟩
  have hhex : ∀ ds : Chars, (∃ mc ec m k e, ds = mc ++ ec ∧ Mant true mc m k ∧
      ExpPart true ec e ∧ v = .hex m (e - 4 * k)) ↔ v ∈ (splits ds).flatMap fun p =>
        (mantCands true p.1).flatMap fun mk =>
          (expCands true p.2).map fun e => FloatMag.hex mk.1 (e - 4 * mk.2) := by
    intro ds
    simp only [List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨mc, ec, m, k, e, rfl, hm, he, rfl⟩
      exact ⟨(mc, ec), mem_splits.2 rfl, (m, k), mant_iff.1 hm, e, expPart_iff.1 he, rfl⟩
    · rintro ⟨⟨mc, ec⟩, hp, ⟨m, k⟩, hm, e, he, rfl⟩
      exact ⟨mc, ec, m, k, e, mem_splits.1 hp, mant_iff.2 hm, expPart_iff.2 he, rfl⟩
  unfold FMag fmagCands
  rw [hx', hx, hn', hn, hdec, hhex]
  simp only [List.mem_append, hexNum_iff, mem_ite_nil, List.mem_singleton, List.mem_map,
    Option.mem_toList, Nat.zero_add, Nat.reduceAdd, or_assoc,
    eq_comm (a := FloatMag.nanPayload _)]

/-- `TfN(N)` candidates. -/
def fnCands (t : FloatType) (cs : Chars) : List (BitVec t.width) :=
  (splits cs).flatMap fun p => (signCands p.1).flatMap fun s => (fmagCands p.2).flatMap fun v =>
    (magBits t v).toList.map fun n =>
      BitVec.ofNat t.width (if s = -1 then n + 2 ^ (t.width - 1) else n)

theorem fn_iff {t : FloatType} {cs : Chars} {b : BitVec t.width} :
    FN t cs b ↔ b ∈ fnCands t cs := by
  unfold FN fnCands
  simp only [List.mem_flatMap, List.mem_map, Option.mem_toList]
  constructor
  · rintro ⟨sc, mc, s, v, n, rfl, hs, hv, hn, rfl⟩
    exact ⟨(sc, mc), mem_splits.2 rfl, s, signChars_iff.1 hs, v, fmag_iff.1 hv, n, hn, rfl⟩
  · rintro ⟨⟨sc, mc⟩, hp, s, hs, v, hv, n, hn, rfl⟩
    exact ⟨sc, mc, s, v, n, mem_splits.1 hp, signChars_iff.2 hs, fmag_iff.2 hv, hn, rfl⟩

/-! ## Negative examples from empty candidate lists -/

theorem not_un_of_nil {N : Nat} {cs : Chars} (h : unCands N cs = []) (n : Nat) : ¬ UN N cs n := by
  rw [un_iff, h]; simp

theorem not_sn_of_nil {N : Nat} {cs : Chars} (h : snCands N cs = []) (i : Int) : ¬ SN N cs i := by
  rw [sn_iff, h]; simp

theorem not_in_of_nil {N : Nat} {cs : Chars} (h : inCands N cs = []) (b : BitVec N) :
    ¬ IN N cs b := by
  rw [in_iff, h]; simp

theorem not_fmag_of_nil {cs : Chars} (h : fmagCands cs = []) (v : FloatMag) : ¬ FMag cs v := by
  rw [fmag_iff, h]; simp

theorem not_fn_of_nil {t : FloatType} {cs : Chars} (h : fnCands t cs = []) (b : BitVec t.width) :
    ¬ FN t cs b := by
  rw [fn_iff, h]; simp

/-! ## Atoms -/

theorem atomI_K_iff {N : Nat} {s : String} {b : BitVec N} : AtomI N (K s) b ↔ IN N s.toList b := by
  constructor
  · rintro ⟨t, ht, h⟩
    injection ht with ht; injection ht with ht
    subst ht; exact h
  · intro h; exact ⟨s, rfl, h⟩

theorem atomU_K_iff {N : Nat} {s : String} {n : Nat} : AtomU N (K s) n ↔ UN N s.toList n := by
  constructor
  · rintro ⟨t, ht, h⟩
    injection ht with ht; injection ht with ht
    subst ht; exact h
  · intro h; exact ⟨s, rfl, h⟩

theorem atomF_K_iff {t : FloatType} {s : String} {b : BitVec t.width} :
    AtomF t (K s) b ↔ FN t s.toList b := by
  constructor
  · rintro ⟨u, hu, h⟩
    injection hu with hu; injection hu with hu
    subst hu; exact h
  · intro h; exact ⟨s, rfl, h⟩

end Silmaril.Wasm.Text.ValuesExamples
