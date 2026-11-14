module

/-!
# Punycode building blocks

The layers of RFC 3492 Bootstring with the Punycode parameters (§5), used by
`Silmaril.Encoding.Punycode`:

* the bias adaptation function `adapt` (§6.1) and the digit thresholds
  `threshold` (§6.2/§6.3, "`t = tmin` if `k ≤ bias`, `tmax` if `k ≥ bias + tmax`,
  `k - bias` otherwise");
* the base-36 digits (§5): `digitChar` (`a–z` = 0–25, `0–9` = 26–35, the
  encoder writes lower case) and `digitValue?` (case-insensitive);
* generalized variable-length integers (§3.3): `encodeVLI`, and the digit
  layer `encodeDeltas` / `decodeDigits` that threads the adapted bias through
  a sequence of deltas, with the round trip `decodeDigits_encodeDeltas`;
* insertion unsort coding (§3.2): the decoder state machine `insertStep` /
  `insertAll`, the encoder's delta computation `deltas` (the inner and outer
  loops of §6.3), and the round trip `insertAll_deltas`.

All arithmetic is on unbounded `Nat`, so the overflow checks of §6.2–§6.4 never
fire and are omitted; the integer layer is total.  Structural recursion with
explicit fuel (`adaptLoop`, `encodeVLIAux`) keeps every function reducible by
the kernel, so the RFC 3492 §7.1 samples are checked by `decide`.
-/

@[expose] public section

namespace Silmaril

namespace Punycode

/-! ## Parameters (RFC 3492 §5) -/

/-- `base = 36`. -/
abbrev base : Nat := 36
/-- `tmin = 1`. -/
abbrev tmin : Nat := 1
/-- `tmax = 26`. -/
abbrev tmax : Nat := 26
/-- `skew = 38`. -/
abbrev skew : Nat := 38
/-- `damp = 700`. -/
abbrev damp : Nat := 700
/-- `initial_bias = 72`. -/
abbrev initialBias : Nat := 72
/-- `initial_n = 128 = 0x80`. -/
abbrev initialN : Nat := 0x80

/-! ## Bias adaptation (§6.1) -/

/-- The `while delta > ((base - tmin) * tmax) div 2` loop of `adapt` and its
result `k + (((base - tmin + 1) * delta) div (delta + skew))`.  The fuel bounds
the iteration count; any fuel `≥ delta` is enough (`adaptLoop_fuel`). -/
def adaptLoop : (fuel delta k : Nat) → Nat
  | 0, delta, k => k + ((base - tmin + 1) * delta) / (delta + skew)
  | fuel + 1, delta, k =>
    if delta > ((base - tmin) * tmax) / 2 then adaptLoop fuel (delta / (base - tmin)) (k + base)
    else k + ((base - tmin + 1) * delta) / (delta + skew)

/-- `adapt(delta, numpoints, firsttime)` (§6.1). -/
def adapt (delta numpoints : Nat) (firsttime : Bool) : Nat :=
  let delta := if firsttime then delta / damp else delta / 2
  let delta := delta + delta / numpoints
  adaptLoop delta delta 0

/-- The digit threshold for position `k` (a multiple of `base`) under `bias`.
The "`+ tmin`" of the RFC's clamp is omitted, as §6.2 allows; on `Nat` with
`tmin = 1` the clamp is exact. -/
def threshold (bias k : Nat) : Nat :=
  if k ≤ bias then tmin else if bias + tmax ≤ k then tmax else k - bias

/-! ## Digits (§5) -/

/-- The (lower-case) basic code point of a digit value `d < 36`. -/
def digitChar (d : Nat) : Char :=
  if d < 26 then Char.ofNat (0x61 + d) else Char.ofNat (0x30 + (d - 26))

/-- The digit value of a basic code point: `A–Z` and `a–z` are 0–25, `0–9`
are 26–35 (case-insensitive, as decoders MUST be). -/
def digitValue? (c : Char) : Option Nat :=
  if 0x61 ≤ c.toNat ∧ c.toNat ≤ 0x7A then some (c.toNat - 0x61)
  else if 0x41 ≤ c.toNat ∧ c.toNat ≤ 0x5A then some (c.toNat - 0x41)
  else if 0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39 then some (c.toNat - 0x30 + 26)
  else none

/-! ## Generalized variable-length integers (§3.3) -/

/-- The digits of `q` starting at position `k` under `bias`: the inner
`for k = base to infinity` loop of §6.3.  The fuel bounds the digit count; any
fuel `≥ q` is enough. -/
def encodeVLIAux (bias : Nat) : (fuel k q : Nat) → List Char
  | 0, _, q => [digitChar q]
  | fuel + 1, k, q =>
    let t := threshold bias k
    if q < t then [digitChar q]
    else digitChar (t + (q - t) % (base - t)) ::
      encodeVLIAux bias fuel (k + base) ((q - t) / (base - t))

/-- The generalized variable-length integer spelling of `q` under `bias`. -/
def encodeVLI (bias q : Nat) : List Char := encodeVLIAux bias q base q

/-- The digit spelling of a sequence of deltas, adapting the bias after each
(§6.3): `h` is the number of code points handled so far and `firsttime` is
"`h` equals `b`". -/
def encodeDeltas : (bias h : Nat) → (firsttime : Bool) → List Nat → List Char
  | _, _, _, [] => []
  | bias, h, firsttime, q :: qs =>
    encodeVLI bias q ++ encodeDeltas (adapt q (h + 1) firsttime) (h + 1) false qs

/-- The digit-reading part of the §6.2 decoder: read generalized
variable-length integers, adapting the bias after each, and return the deltas
`i - oldi`.  The state is the bias, the output length `h`, whether this is the
first delta (`oldi = 0`), and, within an integer, the position `k`, the weight
`w` and the value read so far.  Fails on a non-digit or a truncated integer. -/
def decodeDigits (bias h : Nat) (firsttime : Bool) (k w acc : Nat) :
    List Char → Option (List Nat)
  | [] => if k = base then some [] else none
  | c :: cs =>
    match digitValue? c with
    | none => none
    | some d =>
      let acc := acc + d * w
      let t := threshold bias k
      if d < t then
        (decodeDigits (adapt acc (h + 1) firsttime) (h + 1) false base 1 0 cs).map (acc :: ·)
      else decodeDigits bias h firsttime (k + base) (w * (base - t)) acc cs

/-! ## Insertion unsort coding (§3.2) -/

/-- Insert `x` at position `p` (at the end if `p` is past it). -/
def insertAt (x : Nat) : Nat → List Nat → List Nat
  | 0, l => x :: l
  | _ + 1, [] => [x]
  | p + 1, y :: l => y :: insertAt x p l

/-- One decoder step for a delta (§6.2): from state `⟨n, i⟩` with the current
output, advance `delta` states, insert `n` at `i`, and advance once more. -/
def insertStep (st : Nat × Nat × List Nat) (delta : Nat) : Nat × Nat × List Nat :=
  let (n, i, out) := st
  let i := i + delta
  let n := n + i / (out.length + 1)
  let i := i % (out.length + 1)
  (n, i + 1, insertAt n i out)

/-- The decoder state machine: insert one code point per delta into the basic
code points, starting from `⟨initial_n, 0⟩`. -/
def insertAll (basic deltas : List Nat) : List Nat :=
  (deltas.foldl insertStep (initialN, 0, basic)).2.2

/-- The inner loop of §6.3 for the code point `n = m`: scan the input,
counting code points `< m` into `delta`, emitting `delta` (and resetting it)
at each occurrence of `m`.  Returns the emitted deltas, the final `delta` and
the final `h`. -/
def pass (m : Nat) : List Nat → (delta h : Nat) → List Nat × Nat × Nat
  | [], delta, h => ([], delta, h)
  | c :: cs, delta, h =>
    if c < m then pass m cs (delta + 1) h
    else if c = m then
      let r := pass m cs 0 (h + 1)
      (delta :: r.1, r.2.1, r.2.2)
    else pass m cs delta h

/-- The outer loop of §6.3 over the successive code points `m` (the sorted
non-basic code points of the input): `delta += (m - n) * (h + 1)`, the inner
loop, then `delta += 1`, `n := m + 1`. -/
def deltasLoop (input : List Nat) : (ms : List Nat) → (n delta h : Nat) → List Nat
  | [], _, _, _ => []
  | m :: ms, n, delta, h =>
    let r := pass m input (delta + (m - n) * (h + 1)) h
    r.1 ++ deltasLoop input ms (m + 1) (r.2.1 + 1) r.2.2

/-- Insert into a strictly increasing list, dropping duplicates. -/
def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x < y then x :: y :: ys else if x = y then y :: ys else y :: insertSorted x ys

/-- The distinct values of a list in increasing order. -/
def sortDedup (l : List Nat) : List Nat := l.foldr insertSorted []

/-- The basic code points of an input, in order. -/
def basicPart (input : List Nat) : List Nat := input.filter (· < initialN)

/-- The deltas the §6.3 encoder emits for an input.  The successive minima
"`m` = the minimum code point `≥ n` in the input" are exactly the distinct
non-basic code points in increasing order, and the loop "while `h <
length(input)`" ends exactly when they are exhausted. -/
def deltas (input : List Nat) : List Nat :=
  deltasLoop input (sortDedup (input.filter (initialN ≤ ·))) initialN 0 (basicPart input).length


/-- Unfold the Punycode parameters to numerals everywhere. -/
local macro "params" : tactic => `(tactic| (try simp only [base, tmin, tmax, skew, damp,
  initialBias, initialN, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv] at *))

/-! ## Facts: `adapt` and thresholds -/

/-- The fuel of `adaptLoop` is irrelevant once it covers `delta`: `adaptLoop`
is the `while` loop of §6.1. -/
theorem adaptLoop_fuel : ∀ {f f' : Nat} {delta : Nat} (k : Nat), delta ≤ f → delta ≤ f' →
    adaptLoop f delta k = adaptLoop f' delta k
  | 0, 0, _, _, _, _ => rfl
  | 0, _ + 1, delta, k, h, _ => by
    obtain rfl : delta = 0 := by omega
    simp [adaptLoop]
  | _ + 1, 0, delta, k, _, h => by
    obtain rfl : delta = 0 := by omega
    simp [adaptLoop]
  | f + 1, f' + 1, delta, k, h, h' => by
    simp only [adaptLoop]
    split
    · exact adaptLoop_fuel _ (by params; omega) (by params; omega)
    · rfl

theorem adaptLoop_le : ∀ (f delta k : Nat), adaptLoop f delta k ≤ k + delta
  | 0, delta, k => by
    simp only [adaptLoop]
    have : (base - tmin + 1) * delta / (delta + skew) ≤ delta :=
      Nat.div_le_of_le_mul (by simp only [base, tmin, skew]; grind)
    omega
  | f + 1, delta, k => by
    simp only [adaptLoop]
    split
    · have := adaptLoop_le f (delta / (base - tmin)) (k + base)
      simp only [base, tmin, tmax] at *
      omega
    · have : (base - tmin + 1) * delta / (delta + skew) ≤ delta :=
        Nat.div_le_of_le_mul (by simp only [base, tmin, skew]; grind)
      omega

/-- With enough fuel, the final term of `adapt` is at most 33, so the bias
is `33` or less modulo `base`. -/
theorem adaptLoop_mod : ∀ {f delta : Nat} (j : Nat), delta ≤ f →
    adaptLoop f delta (base * j) % base ≤ 33
  | 0, delta, j, h => by
    obtain rfl : delta = 0 := by omega
    simp [adaptLoop]
  | f + 1, delta, j, h => by
    simp only [adaptLoop]
    split
    · rw [show base * j + base = base * (j + 1) by simp only [base]; omega]
      exact adaptLoop_mod _ (by simp only [base, tmin] at *; omega)
    · next hd =>
      params
      have : 36 * delta / (delta + 38) ≤ 33 :=
        Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega))
      generalize 36 * delta / (delta + 38) = x at *
      omega

/-- `adapt` never exceeds its `delta`. -/
theorem adapt_le (delta numpoints : Nat) (firsttime : Bool) :
    adapt delta numpoints firsttime ≤ delta := by
  unfold adapt
  refine Nat.le_trans (adaptLoop_le _ _ 0) ?_
  have h1 : (if firsttime then delta / damp else delta / 2) ≤ delta / 2 := by
    split
    · exact Nat.div_le_div_left (by decide) (by decide)
    · exact Nat.le_refl _
  have h2 := Nat.div_le_self (if firsttime then delta / damp else delta / 2) numpoints
  omega

/-- The adapted bias is at most `33` modulo `base`. -/
theorem adapt_mod_base (delta numpoints : Nat) (firsttime : Bool) :
    adapt delta numpoints firsttime % base ≤ 33 := by
  have := adaptLoop_mod (f := (if firsttime then delta / damp else delta / 2) +
    (if firsttime then delta / damp else delta / 2) / numpoints) 0 (Nat.le_refl _)
  simpa [adapt] using this

theorem tmin_le_threshold (bias k : Nat) : tmin ≤ threshold bias k := by
  unfold threshold; params; split <;> (try split) <;> omega

theorem threshold_le_tmax (bias k : Nat) : threshold bias k ≤ tmax := by
  unfold threshold; params; split <;> (try split) <;> omega

/-! ## Facts: digits -/

theorem digitValue?_digitChar : ∀ d, d < base → digitValue? (digitChar d) = some d := by
  decide

theorem digitChar_ne_delimiter : ∀ d, d < base → digitChar d ≠ '-' := by
  decide

theorem toNat_digitChar_lt : ∀ d, d < base → (digitChar d).toNat < initialN := by
  decide

theorem toNat_charOfNat {n : Nat} (h : n < 0xD800) : (Char.ofNat n).toNat = n := by
  have hv : n.isValidChar := .inl h
  simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat]

theorem digitValue?_lt {c : Char} {d : Nat} (h : digitValue? c = some d) : d < base := by
  unfold digitValue? at h
  params
  repeat' split at h
  all_goals first | (cases h; omega) | cases h

/-! ## Facts: generalized variable-length integers -/

private theorem vli_arith (q t w acc : Nat) (ht : t ≤ q) :
    acc + (t + (q - t) % (base - t)) * w + (q - t) / (base - t) * (w * (base - t)) =
      acc + q * w := by
  have h := Nat.mod_add_div (q - t) (base - t)
  generalize (q - t) % (base - t) = r at *
  generalize (q - t) / (base - t) = s at *
  generalize base - t = u at *
  obtain ⟨q, rfl⟩ : ∃ e, q = t + e := ⟨q - t, by omega⟩
  simp only [Nat.add_sub_cancel_left] at h
  subst h
  grind

/-- Every digit of a variable-length integer is a digit character. -/
theorem mem_encodeVLIAux {bias : Nat} :
    ∀ {fuel k q : Nat} {c : Char}, c ∈ encodeVLIAux bias fuel k q → q ≤ fuel →
      ∃ d, d < base ∧ c = digitChar d
  | 0, k, q, c, h, hq => by
    simp only [encodeVLIAux, List.mem_singleton] at h
    exact ⟨q, by simp only [base]; omega, h⟩
  | fuel + 1, k, q, c, h, hq => by
    have ht1 := tmin_le_threshold bias k
    have ht2 := threshold_le_tmax bias k
    simp only [encodeVLIAux] at h
    split at h
    · simp only [List.mem_singleton] at h
      exact ⟨q, by simp only [base, tmin, tmax] at *; omega, h⟩
    · simp only [List.mem_cons] at h
      rcases h with h | h
      · exact ⟨_, by
          have := Nat.mod_lt (q - threshold bias k) (show base - threshold bias k > 0 by
            simp only [base, tmax] at *; omega)
          simp only [base, tmax] at *; omega, h⟩
      · refine mem_encodeVLIAux h ?_
        have := Nat.div_le_self (q - threshold bias k) (base - threshold bias k)
        simp only [tmin] at *
        omega

/-- Reading the digits of `q` adds `q * w` to the integer being read, then
continues with the next delta. -/
theorem decodeDigits_encodeVLIAux {bias h : Nat} {firsttime : Bool} :
    ∀ {fuel k q : Nat} (w acc : Nat) (rest : List Char), q ≤ fuel →
      decodeDigits bias h firsttime k w acc (encodeVLIAux bias fuel k q ++ rest) =
        (decodeDigits (adapt (acc + q * w) (h + 1) firsttime) (h + 1) false base 1 0 rest).map
          ((acc + q * w) :: ·)
  | 0, k, q, w, acc, rest, hq => by
    obtain rfl : q = 0 := by omega
    have ht := tmin_le_threshold bias k
    simp only [encodeVLIAux, List.cons_append, List.nil_append, decodeDigits,
      digitValue?_digitChar 0 (by decide)]
    rw [ite_eq_left (by simp only [tmin] at ht; omega)]
  | fuel + 1, k, q, w, acc, rest, hq => by
    have ht1 := tmin_le_threshold bias k
    have ht2 := threshold_le_tmax bias k
    simp only [encodeVLIAux]
    split
    · next hlt =>
      simp only [List.cons_append, List.nil_append, decodeDigits,
        digitValue?_digitChar q (by simp only [base, tmax] at *; omega)]
      rw [ite_eq_left hlt]
    · next hge =>
      have hmod := Nat.mod_lt (q - threshold bias k) (show base - threshold bias k > 0 by
        simp only [base, tmax] at *; omega)
      simp only [List.cons_append, decodeDigits,
        digitValue?_digitChar _ (show threshold bias k + (q - threshold bias k) %
          (base - threshold bias k) < base by simp only [base, tmax] at *; omega)]
      rw [ite_eq_right (by omega)]
      rw [decodeDigits_encodeVLIAux _ _ _ (by
        have := Nat.div_le_self (q - threshold bias k) (base - threshold bias k)
        simp only [tmin] at *; omega)]
      rw [vli_arith _ _ _ _ (by omega)]

/-- The variable-length integer round trip (§3.3): reading the digits of `q`
under `bias` yields the delta `q`, then reading continues under the adapted
bias. -/
theorem decodeDigits_encodeVLI (bias h : Nat) (firsttime : Bool) (q : Nat) (rest : List Char) :
    decodeDigits bias h firsttime base 1 0 (encodeVLI bias q ++ rest) =
      (decodeDigits (adapt q (h + 1) firsttime) (h + 1) false base 1 0 rest).map (q :: ·) := by
  rw [encodeVLI, decodeDigits_encodeVLIAux _ _ _ (Nat.le_refl _), Nat.zero_add, Nat.mul_one]

/-- Every character of the digit spelling of deltas is a digit character. -/
theorem mem_encodeDeltas : ∀ {bias h : Nat} {firsttime : Bool} {qs : List Nat} {c : Char},
    c ∈ encodeDeltas bias h firsttime qs → ∃ d, d < base ∧ c = digitChar d
  | _, _, _, [], c, hc => by simp [encodeDeltas] at hc
  | bias, h, firsttime, q :: qs, c, hc => by
    simp only [encodeDeltas, List.mem_append] at hc
    rcases hc with hc | hc
    · exact mem_encodeVLIAux hc (Nat.le_refl _)
    · exact mem_encodeDeltas hc

/-- The digit layer round trip: reading the digit spelling of a sequence of
deltas returns it. -/
theorem decodeDigits_encodeDeltas : ∀ (bias h : Nat) (firsttime : Bool) (qs : List Nat),
    decodeDigits bias h firsttime base 1 0 (encodeDeltas bias h firsttime qs) = some qs
  | _, _, _, [] => by simp [encodeDeltas, decodeDigits]
  | bias, h, firsttime, q :: qs => by
    rw [encodeDeltas, decodeDigits_encodeVLI, decodeDigits_encodeDeltas]
    rfl

/-! ## Facts: insertion unsort coding -/

theorem insertAt_append (x : Nat) : ∀ (A B : List Nat), insertAt x A.length (A ++ B) = A ++ x :: B
  | [], B => rfl
  | a :: A, B => by simp [insertAt, insertAt_append x A B]

theorem mem_insertSorted {x y : Nat} :
    ∀ {l : List Nat}, y ∈ insertSorted x l ↔ y = x ∨ y ∈ l
  | [] => by simp [insertSorted]
  | z :: l => by
    unfold insertSorted
    split
    · simp
    · split
      · next h => subst h; simp
      · simp only [List.mem_cons, mem_insertSorted (l := l), or_left_comm]

theorem pairwise_insertSorted (x : Nat) :
    ∀ {l : List Nat}, l.Pairwise (· < ·) → (insertSorted x l).Pairwise (· < ·)
  | [], _ => by simp [insertSorted]
  | z :: l, hl => by
    have hl' := List.pairwise_cons.mp hl
    unfold insertSorted
    split
    · next h =>
      refine List.Pairwise.cons (fun a ha => ?_) hl
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact h
      · exact Nat.lt_trans h (hl'.1 a ha)
    · split
      · exact hl
      · next h₁ h₂ =>
        refine List.Pairwise.cons (fun a ha => ?_) (pairwise_insertSorted x hl'.2)
        rcases mem_insertSorted.mp ha with rfl | ha
        · omega
        · exact hl'.1 a ha

theorem mem_sortDedup {x : Nat} : ∀ {l : List Nat}, x ∈ sortDedup l ↔ x ∈ l
  | [] => by simp [sortDedup]
  | y :: l => by
    simp only [sortDedup, List.foldr_cons, List.mem_cons] at *
    rw [mem_insertSorted, ← sortDedup, mem_sortDedup]

theorem pairwise_sortDedup : ∀ (l : List Nat), (sortDedup l).Pairwise (· < ·)
  | [] => by simp [sortDedup]
  | y :: l => by
    simp only [sortDedup, List.foldr_cons]
    exact pairwise_insertSorted y (pairwise_sortDedup l)

/-- The inner loop of §6.3 against the decoder: if the decoder's output holds
the code points `≤ m` of the scanned prefix `pre` and `< m` of the rest, and
the decoder position plus the encoder's `delta` is the number of states to the
next insertion, then the emitted deltas make the decoder insert the
occurrences of `m` exactly where they belong. -/
theorem pass_spec (m : Nat) : ∀ (rest pre : List Nat) (delta h n i : Nat) (out : List Nat),
    out = pre.filter (· ≤ m) ++ rest.filter (· < m) → h = out.length → n ≤ m →
    i + delta = (m - n) * (h + 1) + (pre.filter (· ≤ m)).length →
    let r := pass m rest delta h
    let st := r.1.foldl insertStep (n, i, out)
    st.2.2 = (pre ++ rest).filter (· ≤ m) ∧ r.2.2 = st.2.2.length ∧ st.1 ≤ m ∧
      st.2.1 + r.2.1 = (m - st.1) * (r.2.2 + 1) + st.2.2.length
  | [], pre, delta, h, n, i, out, hout, hh, hn, hi => by
    subst hout
    simp_all [pass]
  | c :: rest, pre, delta, h, n, i, out, hout, hh, hn, hi => by
    simp only [pass]
    split
    · next hc =>
      have := pass_spec m rest (pre ++ [c]) (delta + 1) h n i out
        (by rw [hout]; simp [hc, Nat.le_of_lt hc])
        hh hn (by simp [Nat.le_of_lt hc]; omega)
      simpa using this
    · split
      · next hc₁ hc₂ =>
        subst hc₂
        simp only [List.foldl_cons]
        -- the decoder step for this occurrence of `m`
        have hP : (pre.filter (· ≤ c)).length ≤ h := by
          rw [hh, hout, List.length_append]; omega
        have hj : i + delta = (h + 1) * (c - n) + (pre.filter (· ≤ c)).length := by
          rw [hi, Nat.mul_comm]
        have hstep : insertStep (n, i, out) delta =
            (c, (pre.filter (· ≤ c)).length + 1, (pre ++ [c]).filter (· ≤ c) ++
              rest.filter (· < c)) := by
          simp only [insertStep, ← hh, hj, Nat.mul_add_div (Nat.succ_pos h),
            Nat.mul_add_mod, Nat.div_eq_of_lt (Nat.lt_succ_of_le hP),
            Nat.mod_eq_of_lt (Nat.lt_succ_of_le hP), Nat.add_zero, Nat.add_sub_of_le hn]
          refine Prod.ext rfl (Prod.ext rfl ?_)
          simp only [hout, List.filter_cons, Nat.lt_irrefl, decide_false]
          rw [insertAt_append]
          simp
        rw [hstep]
        have := pass_spec c rest (pre ++ [c]) 0 (h + 1) c
          ((pre.filter (· ≤ c)).length + 1) _ rfl
          (by simp [hh, hout]; omega) (Nat.le_refl _) (by simp)
        simpa using this
      · next hc₁ hc₂ =>
        have hc : c > m := by omega
        have := pass_spec m rest (pre ++ [c]) delta h n i out
          (by rw [hout]; simp [hc₁, show ¬ c ≤ m by omega])
          hh hn (by simp [show ¬ c ≤ m by omega]; omega)
        simpa using this

/-- The outer loop of §6.3 against the decoder: if the decoder holds the code
points `< n`, the remaining `ms` are the larger code points in increasing
order, and the decoder position plus `delta` counts the states up to `n`, the
remaining deltas rebuild the input. -/
theorem deltasLoop_spec (s : List Nat) : ∀ (ms : List Nat) (n delta h nd i : Nat)
    (out : List Nat),
    out = s.filter (· < n) → h = out.length → nd ≤ n → i + delta = (n - nd) * (h + 1) →
    ms.Pairwise (· < ·) → (∀ v ∈ ms, n ≤ v) → (∀ x ∈ s, n ≤ x → x ∈ ms) →
    ((deltasLoop s ms n delta h).foldl insertStep (nd, i, out)).2.2 = s
  | [], n, delta, h, nd, i, out, hout, _, _, _, _, _, hcov => by
    simp only [deltasLoop, List.foldl_nil, hout]
    refine List.filter_eq_self.mpr fun x hx => ?_
    have := hcov x hx
    simp only [List.not_mem_nil, imp_false, Nat.not_le] at this
    simpa using this
  | m :: ms, n, delta, h, nd, i, out, hout, hh, hnd, hi, hpw, hge, hcov => by
    have hpw' := List.pairwise_cons.mp hpw
    have hnm : n ≤ m := hge m (by simp)
    simp only [deltasLoop, List.foldl_append]
    have hout' : out = ([] : List Nat).filter (· ≤ m) ++ s.filter (· < m) := by
      rw [hout, List.filter_nil, List.nil_append]
      refine List.filter_congr fun x hx => ?_
      by_cases hx' : n ≤ x
      · have := hcov x hx hx'
        simp only [List.mem_cons] at this
        rcases this with rfl | hms
        · simpa using hnm
        · have := hpw'.1 x hms; simp; omega
      · simp; omega
    have hi' : i + (delta + (m - n) * (h + 1)) =
        (m - nd) * (h + 1) + (([] : List Nat).filter (· ≤ m)).length := by
      rw [← Nat.add_assoc, hi, List.filter_nil, List.length_nil, Nat.add_zero, ← Nat.add_mul]
      congr 1; omega
    obtain ⟨h1, h2, h3, h4⟩ := pass_spec m s [] _ h nd i out hout' hh (by omega) hi'
    simp only [List.nil_append] at h1
    generalize hp : pass m s (delta + (m - n) * (h + 1)) h = r at *
    generalize hst : r.1.foldl insertStep (nd, i, out) = st at *
    obtain ⟨n', i', out'⟩ := st
    simp only at h1 h2 h3 h4 ⊢
    refine deltasLoop_spec s ms (m + 1) (r.2.1 + 1) r.2.2 n' i' out' ?_ h2 (by omega) ?_ hpw'.2
      (fun v hv => hpw'.1 v hv) ?_
    · rw [h1]; exact List.filter_congr fun x _ => by simp; omega
    · rw [← Nat.add_assoc, h4, ← h2, show m + 1 - n' = (m - n') + 1 by omega, Nat.add_mul,
        Nat.one_mul]
      omega
    · intro x hx hx'
      have := hcov x hx (by omega)
      simp only [List.mem_cons] at this
      rcases this with rfl | h
      · omega
      · exact h

/-- The insertion layer round trip: the decoder state machine, started on the
basic code points, rebuilds the input from the encoder's deltas. -/
theorem insertAll_deltas (s : List Nat) : insertAll (basicPart s) (deltas s) = s := by
  unfold insertAll deltas basicPart
  refine deltasLoop_spec s _ initialN 0 _ initialN 0 _ rfl rfl (Nat.le_refl _) (by simp)
    (pairwise_sortDedup _) (fun v hv => ?_) (fun x hx hx' => ?_)
  · have := mem_sortDedup.mp hv
    simp only [List.mem_filter, decide_eq_true_eq] at this
    exact this.2
  · exact mem_sortDedup.mpr (by simp [hx, hx'])

end Punycode

end Silmaril
