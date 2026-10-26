module

public import Silmaril.Crypto.SHA256.Kernel
public import Mathlib.Data.List.GetD

/-!
# The SHA-256 message schedule as an indexed function (FIPS 180-4 §6.2.2 step 1)

`Silmaril.Crypto.SHA256.Kernel` builds the message schedule as a *reversed accumulator*:
`expandSchedule` pushes each new word onto the front of a list and `messageSchedule`
reverses the result at the end.  That shape is good for computing and useless for
reasoning: a machine-code loop invariant says "slot `t` holds `W t`", so it needs the
schedule as an indexed function `W : Nat → Word` satisfying

`W t = σ₁ (W (t-2)) + W (t-7) + σ₀ (W (t-15)) + W (t-16)`  for `16 ≤ t < 64`.

This module is the bridge.  The load-bearing step is `schedulePrefix_getD_reverse`,
which turns the prose claim in `nextScheduleWord`'s doc comment — "`acc[i]` is
`W (t-1-i)`" — into a theorem; everything else is bookkeeping on top of it.

Indices are kept as `getD _ 0` on the schedule list rather than being wrapped in a new
`scheduleWord M t` definition: `messageSchedule` is already the list every consumer
holds (`rounds` zips it against `Ks`), so an extra definition would only add an
unfolding step between the loop invariant and the compression proof.  The recurrence is
stated both in the additive form `messageSchedule_succ` (`W (t+16)` from `W (t+14)`,
`W (t+9)`, `W (t+1)`, `W t` — what a loop invariant stepping `t ↦ t+1` consumes) and in
the FIPS subtraction form `messageSchedule_getD`, the latter derived from the former.

## Theorems
- `expandSchedule_length`, `messageSchedule_length`: the schedule is 64 words.
- `schedulePrefix_getD_reverse`: the accumulator invariant — entry `i` of the reversed
  accumulator is the forward word at index `length - 1 - i`.
- `schedulePrefix_getD_of_le`: longer expansions extend shorter ones, so the schedule
  may be read at any index that is already in range of a shorter expansion.
- `messageSchedule_succ`, `messageSchedule_getD`: the §6.2.2 recurrence in indexed form.
- `messageSchedule_getD_of_lt`: below 16 the schedule is the parsed block (§5.2.1).
- `messageSchedule_getD_of_ge`: outside `0 … 63` the indexed reading is `0`.
- `messageSchedule_abc_getD`: cross-check of the indexed reading against the schedule of
  the FIPS 180-4 §B.1 `"abc"` block computed from the recurrence outside Lean.

## References
* FIPS PUB 180-4, August 2015, §6.2.2.
-/

@[expose] public section

namespace Silmaril.Crypto.SHA256.Kernel

/-! ### Block parsing (§5.2.1) -/

/-- A parsed block is always sixteen words, whatever the input length. -/
theorem blockWords_length (M : List Word) : (blockWords M).length = 16 := by
  simp [blockWords]

/-- On a well-formed sixteen-word block, parsing is the identity: this is what lets a
caller that already holds `M₀ … M₁₅` read the schedule's first sixteen words off `M`
directly. -/
theorem blockWords_eq_self {M : List Word} (h : M.length = 16) : blockWords M = M := by
  simp [blockWords, ← h]

/-! ### The expansion loop -/

/-- Each expansion step adds exactly one word, so the accumulator length is known
statically.  Needed by every `getD`/`getD_reverse` side condition below. -/
theorem expandSchedule_length (n : Nat) (acc : List Word) :
    (expandSchedule n acc).length = acc.length + n := by
  induction n generalizing acc with
  | zero => simp [expandSchedule]
  | succ n ih =>
    rw [show expandSchedule (n + 1) acc = expandSchedule n (nextScheduleWord acc :: acc) from rfl,
      ih, List.length_cons]
    omega

/-- `expandSchedule` is tail recursive, so its unfolding exposes the *first* step; this
is the matching unfolding of the *last* step, which is the one an induction on the
number of words produced needs. -/
theorem expandSchedule_succ (n : Nat) (acc : List Word) :
    expandSchedule (n + 1) acc
      = nextScheduleWord (expandSchedule n acc) :: expandSchedule n acc := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
    show expandSchedule (n + 1) (nextScheduleWord acc :: acc) = _
    rw [ih]
    rfl

/-! ### The schedule truncated to its first `16 + n` words -/

/-- The message schedule after `n` expansion steps, in forward order: `W 0 … W (15 + n)`.
`messageSchedule M` is the case `n = 48`.  Reasoning runs through this family because
the recurrence relates the word produced at step `n` to words that are already present
after `n - 1` steps. -/
def schedulePrefix (M : List Word) (n : Nat) : List Word :=
  (expandSchedule n (blockWords M).reverse).reverse

/-- The full schedule is the expansion run to its end. -/
theorem messageSchedule_eq_schedulePrefix (M : List Word) :
    messageSchedule M = schedulePrefix M 48 := rfl

/-- Sixteen parsed words plus one per expansion step. -/
theorem schedulePrefix_length (M : List Word) (n : Nat) :
    (schedulePrefix M n).length = 16 + n := by
  rw [schedulePrefix, List.length_reverse, expandSchedule_length, List.length_reverse,
    blockWords_length]

/-- The schedule is exactly the sixty-four words §6.2.2 asks for. -/
theorem messageSchedule_length (M : List Word) : (messageSchedule M).length = 64 := by
  rw [messageSchedule_eq_schedulePrefix, schedulePrefix_length]

/-- Before any expansion the schedule is the parsed block (§5.2.1). -/
theorem schedulePrefix_zero (M : List Word) : schedulePrefix M 0 = blockWords M := by
  simp [schedulePrefix, expandSchedule]

/-- One expansion step appends one word at the *end* of the forward schedule.  This is
`expandSchedule_succ` read forwards, and it is what makes the schedule a growing prefix
rather than a list that is rebuilt at every step. -/
theorem schedulePrefix_succ (M : List Word) (n : Nat) :
    schedulePrefix M (n + 1)
      = schedulePrefix M n ++ [nextScheduleWord (schedulePrefix M n).reverse] := by
  rw [schedulePrefix, schedulePrefix, expandSchedule_succ, List.reverse_cons,
    List.reverse_reverse]

/-- **The accumulator invariant.**  `nextScheduleWord` reads its argument — the reversed
accumulator — at small indices, and documents that "`acc[i]` is `W (t-1-i)`".  Here that
claim is proved: reading the reversed schedule at `i` is reading the forward schedule at
`15 + n - i`, the `i`-th word back from the most recently produced one. -/
theorem schedulePrefix_getD_reverse (M : List Word) {n i : Nat} (h : i < 16 + n) :
    (schedulePrefix M n).reverse.getD i 0 = (schedulePrefix M n).getD (15 + n - i) 0 := by
  have hlen : i < (schedulePrefix M n).length := by rw [schedulePrefix_length]; omega
  rw [List.getD_reverse i hlen, schedulePrefix_length]
  congr 1
  omega

/-- Expanding further never disturbs a word already produced, so any index in range of a
shorter expansion may be read off a longer one.  Every step of the recurrence below is
an instance of this: the four operands live in the `n`-step prefix, the result in the
`(n+1)`-step one, and both are read off the full 48-step schedule. -/
theorem schedulePrefix_getD_of_le (M : List Word) {m n i : Nat} (hmn : m ≤ n)
    (hi : i < 16 + m) : (schedulePrefix M n).getD i 0 = (schedulePrefix M m).getD i 0 := by
  induction n with
  | zero =>
    obtain rfl : m = 0 := Nat.le_zero.mp hmn
    rfl
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with h | h
    · have hm : m ≤ n := Nat.lt_succ_iff.mp h
      have hlt : i < (schedulePrefix M n).length := by rw [schedulePrefix_length]; omega
      rw [schedulePrefix_succ, List.getD_append _ _ _ _ hlt, ih hm]
    · obtain rfl : m = n + 1 := Nat.le_antisymm hmn h
      rfl

/-- The word produced by expansion step `n + 1` sits at index `16 + n`, and is the
§6.2.2 recurrence applied to four words of the `n`-step prefix.  This is where the
accumulator offsets `1, 6, 14, 15` of `nextScheduleWord` become the schedule offsets
`-2, -7, -15, -16`. -/
theorem schedulePrefix_getD_sixteen_add (M : List Word) (n : Nat) :
    (schedulePrefix M (n + 1)).getD (16 + n) 0
      = sigma1 ((schedulePrefix M n).getD (14 + n) 0) + (schedulePrefix M n).getD (9 + n) 0
        + sigma0 ((schedulePrefix M n).getD (1 + n) 0) + (schedulePrefix M n).getD n 0 := by
  have hlen : (schedulePrefix M n).length ≤ 16 + n := by rw [schedulePrefix_length]
  rw [schedulePrefix_succ, List.getD_append_right _ _ _ _ hlen, schedulePrefix_length]
  have h16 : 16 + n - (16 + n) = 0 := by omega
  rw [h16]
  show nextScheduleWord (schedulePrefix M n).reverse = _
  rw [nextScheduleWord, schedulePrefix_getD_reverse M (by omega),
    schedulePrefix_getD_reverse M (by omega), schedulePrefix_getD_reverse M (by omega),
    schedulePrefix_getD_reverse M (by omega)]
  have e1 : 15 + n - 1 = 14 + n := by omega
  have e6 : 15 + n - 6 = 9 + n := by omega
  have e14 : 15 + n - 14 = 1 + n := by omega
  have e15 : 15 + n - 15 = n := by omega
  rw [e1, e6, e14, e15]

/-! ### The schedule as an indexed function -/

/-- Below sixteen the schedule is the parsed block: `W t = M t` (§6.2.2 step 1, first
case). -/
theorem messageSchedule_getD_of_lt (M : List Word) {t : Nat} (h : t < 16) :
    (messageSchedule M).getD t 0 = (blockWords M).getD t 0 := by
  rw [messageSchedule_eq_schedulePrefix,
    schedulePrefix_getD_of_le M (Nat.zero_le 48) (by omega), schedulePrefix_zero]

/-- **The §6.2.2 recurrence, in the form a loop invariant steps with.**  An invariant
that already holds `W 0 … W (t+15)` extends to `W (t+16)` by one application of this. -/
theorem messageSchedule_succ (M : List Word) {t : Nat} (ht : t < 48) :
    (messageSchedule M).getD (t + 16) 0
      = sigma1 ((messageSchedule M).getD (t + 14) 0) + (messageSchedule M).getD (t + 9) 0
        + sigma0 ((messageSchedule M).getD (t + 1) 0) + (messageSchedule M).getD t 0 := by
  have hres : (messageSchedule M).getD (t + 16) 0 = (schedulePrefix M (t + 1)).getD (16 + t) 0 := by
    rw [messageSchedule_eq_schedulePrefix, show t + 16 = 16 + t from by omega]
    exact schedulePrefix_getD_of_le M (m := t + 1) (n := 48) (i := 16 + t) (by omega) (by omega)
  have h14 : (messageSchedule M).getD (t + 14) 0 = (schedulePrefix M t).getD (14 + t) 0 := by
    rw [messageSchedule_eq_schedulePrefix, show t + 14 = 14 + t from by omega]
    exact schedulePrefix_getD_of_le M (m := t) (n := 48) (i := 14 + t) (by omega) (by omega)
  have h9 : (messageSchedule M).getD (t + 9) 0 = (schedulePrefix M t).getD (9 + t) 0 := by
    rw [messageSchedule_eq_schedulePrefix, show t + 9 = 9 + t from by omega]
    exact schedulePrefix_getD_of_le M (m := t) (n := 48) (i := 9 + t) (by omega) (by omega)
  have h1 : (messageSchedule M).getD (t + 1) 0 = (schedulePrefix M t).getD (1 + t) 0 := by
    rw [messageSchedule_eq_schedulePrefix, show t + 1 = 1 + t from by omega]
    exact schedulePrefix_getD_of_le M (m := t) (n := 48) (i := 1 + t) (by omega) (by omega)
  have h0 : (messageSchedule M).getD t 0 = (schedulePrefix M t).getD t 0 := by
    rw [messageSchedule_eq_schedulePrefix]
    exact schedulePrefix_getD_of_le M (m := t) (n := 48) (i := t) (by omega) (by omega)
  rw [hres, h14, h9, h1, h0, schedulePrefix_getD_sixteen_add]

/-- **The §6.2.2 recurrence, in FIPS subtraction form.**  Derived from
`messageSchedule_succ`; cite whichever reads better at the use site. -/
theorem messageSchedule_getD (M : List Word) {t : Nat} (h16 : 16 ≤ t) (h64 : t < 64) :
    (messageSchedule M).getD t 0 =
      sigma1 ((messageSchedule M).getD (t - 2) 0) + (messageSchedule M).getD (t - 7) 0
        + sigma0 ((messageSchedule M).getD (t - 15) 0) + (messageSchedule M).getD (t - 16) 0 := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 16 := ⟨t - 16, by omega⟩
  have e2 : s + 16 - 2 = s + 14 := by omega
  have e7 : s + 16 - 7 = s + 9 := by omega
  have e15 : s + 16 - 15 = s + 1 := by omega
  have e16 : s + 16 - 16 = s := by omega
  rw [e2, e7, e15, e16, messageSchedule_succ M (by omega)]

/-- Outside `0 … 63` the indexed reading is the default `0`, so a loop invariant need
not carry a separate bound on `t`. -/
theorem messageSchedule_getD_of_ge (M : List Word) {t : Nat} (h : 64 ≤ t) :
    (messageSchedule M).getD t 0 = 0 :=
  List.getD_eq_default _ _ (by rw [messageSchedule_length]; exact h)

/-! ### Cross-check against the §B.1 test vector

The theorems above are proved from the definition, so they cannot disagree with the list
form; what they *can* get wrong is the direction of the reversal, which would show up as
an off-by-one between index `t` and the word FIPS calls `W t`.  The schedule of the
`"abc"` block below was computed from the §6.2.2 recurrence outside Lean, so this pins
the indexing to the standard's. -/

/-- The padded `"abc"` block of §B.1: the sixteen words `compress_abc` compresses. -/
def abc_block : List Word :=
  [abc_msg0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, abc_msg15]

/-- Selected words of the schedule of the padded `"abc"` block (§B.1), against values
computed from the §6.2.2 recurrence outside Lean. -/
theorem messageSchedule_abc_getD :
    (messageSchedule abc_block).getD 0 0 = 0x61626380#32
      ∧ (messageSchedule abc_block).getD 15 0 = 0x00000018#32
      ∧ (messageSchedule abc_block).getD 16 0 = 0x61626380#32
      ∧ (messageSchedule abc_block).getD 17 0 = 0x000f0000#32
      ∧ (messageSchedule abc_block).getD 18 0 = 0x7da86405#32
      ∧ (messageSchedule abc_block).getD 19 0 = 0x600003c6#32
      ∧ (messageSchedule abc_block).getD 32 0 = 0x93f5997f#32
      ∧ (messageSchedule abc_block).getD 62 0 = 0xeeaba2cc#32
      ∧ (messageSchedule abc_block).getD 63 0 = 0x12b1edeb#32 := by
  decide +kernel

end Silmaril.Crypto.SHA256.Kernel
