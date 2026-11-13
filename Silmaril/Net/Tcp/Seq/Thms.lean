module

public import Silmaril.Net.Tcp.Seq.Defs
public import Silmaril.Net.Wire.Thms

/-!
# TCP sequence numbers: theorems

PROVED (standard axioms):

* Offsets and advancing: `off_self`, `off_adv` (advancing by `n` lies `n mod 2^32` ahead),
  `adv_off` (advancing by the offset reaches the target), `off_trans` (offsets add modulo
  2^32), `adv_adv`, **`adv_inj`** (below 2^32, advancing is injective: distinct offsets give
  distinct sequence numbers; the fact the TCP data-transfer proof rests on).
* Comparison: `lt_irrefl`, `lt_asymm`, `le_refl`, `lt_adv` (advancing by `0 < n < 2^31` moves
  forward), and **`lt_not_trans`**: modular `<` is not transitive (a concrete triple).
* **`inWindow_iff`**: `x` is in the window `[lo, lo + wnd)` iff it is `lo` advanced by some
  `k < wnd` (for windows up to 2^32).
* **`acceptableAck_iff`**: with less than half the space outstanding, the offset reading of
  "SND.UNA < SEG.ACK =< SND.NXT" is `lt una ack ∧ le ack nxt`.
* Table 5 cases: `segAcceptable_zero_zero`, `segAcceptable_zero_pos`,
  `segAcceptable_pos_zero`, `segAcceptable_pos_pos`.
-/

@[expose] public section

namespace Silmaril.Net.Tcp.SeqNum

open Silmaril.Net.Wire

theorem off_toNat (a b : SeqNum) : off a b = (4294967296 - a.toNat + b.toNat) % 4294967296 := by
  simp only [off, UInt32.toNat_sub, Nat.reducePow]

theorem adv_toNat (a : SeqNum) (n : Nat) : (adv a n).toNat = (a.toNat + n % 4294967296) % 4294967296 := by
  simp only [adv, UInt32.toNat_add, Nat.reducePow, u32_toNat_ofNat]

theorem off_lt (a b : SeqNum) : off a b < 4294967296 := by
  rw [off_toNat]; omega

@[simp] theorem off_self (a : SeqNum) : off a a = 0 := by
  rw [off_toNat]; have := a.toNat_lt; simp only [Nat.reducePow] at this; omega

/-- Advancing by `n` lies `n mod 2^32` ahead. -/
theorem off_adv (a : SeqNum) (n : Nat) : off a (adv a n) = n % 4294967296 := by
  have ha : a.toNat < 4294967296 := a.toNat_lt
  rw [off_toNat, adv_toNat]
  omega

theorem eq_of_toNat {a b : SeqNum} (h : a.toNat = b.toNat) : a = b := UInt32.toNat_inj.mp h

/-- Advancing by the offset reaches the target. -/
theorem adv_off (a b : SeqNum) : adv a (off a b) = b := by
  have ha : a.toNat < 4294967296 := a.toNat_lt
  have hb : b.toNat < 4294967296 := b.toNat_lt
  apply eq_of_toNat
  rw [adv_toNat, off_toNat]
  omega

/-- Offsets add modulo 2^32. -/
theorem off_trans (a b c : SeqNum) : off a c = (off a b + off b c) % 4294967296 := by
  have ha : a.toNat < 4294967296 := a.toNat_lt
  have hb : b.toNat < 4294967296 := b.toNat_lt
  have hc : c.toNat < 4294967296 := c.toNat_lt
  rw [off_toNat, off_toNat, off_toNat]
  omega

theorem adv_adv (a : SeqNum) (m n : Nat) : adv (adv a m) n = adv a (m + n) := by
  have ha : a.toNat < 4294967296 := a.toNat_lt
  apply eq_of_toNat
  rw [adv_toNat, adv_toNat, adv_toNat]
  omega

@[simp] theorem adv_zero (a : SeqNum) : adv a 0 = a := by
  apply eq_of_toNat
  have ha : a.toNat < 4294967296 := a.toNat_lt
  rw [adv_toNat]; omega

/-- **Below 2^32, advancing is injective.** -/
theorem adv_inj (a : SeqNum) {i j : Nat} (hi : i < 4294967296) (hj : j < 4294967296)
    (h : adv a i = adv a j) : i = j := by
  have h1 : off a (adv a i) = i % 4294967296 := off_adv a i
  have h2 : off a (adv a j) = j % 4294967296 := off_adv a j
  rw [h] at h1
  omega

theorem lt_irrefl (a : SeqNum) : ¬ lt a a := by
  simp [lt]

theorem lt_asymm {a b : SeqNum} (h : lt a b) : ¬ lt b a := by
  have ha : a.toNat < 4294967296 := a.toNat_lt
  have hb : b.toNat < 4294967296 := b.toNat_lt
  unfold lt at h ⊢
  rw [off_toNat] at h ⊢
  omega

theorem le_refl (a : SeqNum) : le a a := by
  simp [le]

/-- Advancing by `0 < n < 2^31` moves forward. -/
theorem lt_adv (a : SeqNum) {n : Nat} (h0 : 0 < n) (h1 : n < 2 ^ 31) : lt a (adv a n) := by
  unfold lt
  rw [off_adv]
  omega

/-- **Modular `<` is not transitive**: `0 < 2^30 < 3·2^30 - 1`, but not `0 < 3·2^30 - 1`. -/
theorem lt_not_trans :
    lt 0 1073741824 ∧ lt 1073741824 3221225471 ∧ ¬ lt 0 3221225471 := by
  decide

/-- **The window `[lo, lo + wnd)`**: the sequence numbers `lo` advanced by less than `wnd`. -/
theorem inWindow_iff (lo : SeqNum) {wnd : Nat} (hw : wnd ≤ 4294967296) (x : SeqNum) :
    inWindow lo wnd x = true ↔ ∃ k < wnd, x = adv lo k := by
  constructor
  · intro h
    have h' : off lo x < wnd := by simpa [inWindow] using h
    exact ⟨off lo x, h', (adv_off lo x).symm⟩
  · rintro ⟨k, hk, rfl⟩
    have hk' : off lo (adv lo k) = k := by rw [off_adv]; omega
    simp [inWindow, hk', hk]

/-- **Acceptable acks**: with less than half the space outstanding, the offset reading is
"SND.UNA < SEG.ACK =< SND.NXT" with modular `<` and `=<`. -/
theorem acceptableAck_iff (una nxt ack : SeqNum) (h : off una nxt < 2 ^ 31) :
    acceptableAck una nxt ack = true ↔ lt una ack ∧ le ack nxt := by
  have htr : off una nxt = (off una ack + off ack nxt) % 4294967296 := off_trans una ack nxt
  have h1 : off una ack < 4294967296 := off_lt _ _
  have h2 : off ack nxt < 4294967296 := off_lt _ _
  simp only [acceptableAck, decide_eq_true_eq, lt, le]
  omega

theorem segAcceptable_zero_zero (n s : SeqNum) : segAcceptable n 0 s 0 = (s == n) := rfl

theorem segAcceptable_zero_pos (n s : SeqNum) {w : Nat} (hw : 0 < w) :
    segAcceptable n w s 0 = inWindow n w s := by
  simp [segAcceptable, Nat.pos_iff_ne_zero.mp hw]

theorem segAcceptable_pos_zero (n s : SeqNum) {l : Nat} (hl : 0 < l) :
    segAcceptable n 0 s l = false := by
  simp [segAcceptable, Nat.pos_iff_ne_zero.mp hl]

theorem segAcceptable_pos_pos (n s : SeqNum) {w l : Nat} (hw : 0 < w) (hl : 0 < l) :
    segAcceptable n w s l = (inWindow n w s || inWindow n w (adv s (l - 1))) := by
  simp [segAcceptable, Nat.pos_iff_ne_zero.mp hw, Nat.pos_iff_ne_zero.mp hl]

end Silmaril.Net.Tcp.SeqNum
