module

public import Silmaril.Machine.RiscV.Lir.Arith.Defs
/-!
# Bit counting without Zbb

`clz`, `ctz`, `popcnt` and their 32-bit forms have no RV64 instruction in the
modeled subset (no Zbb). They are selected as branch-free unrolled sums of one
bit-sized term per bit position, accumulated in `t1`:

* `popcnt x = Σ_{i<64} ((x >>> i) & 1)` (`SRLI`, `ANDI`, `ADD`);
* `clz x = #{i < 64 | x >>> i = 0}` (`SRLI`, `SLTIU 1`, `ADD`);
* `ctz x = #{j < 64 | x <<< j = 0}` (`SLLI`, `SLTIU 1`, `ADD`).

The 32-bit forms sum 32 terms: `popcnt32` over the low bits of `x`, `clz32`
over the zero extension of the low half, and `ctz32` over `x <<< (32 + j)`.
Each sequence has 3 instructions per bit, about 195 for the 64-bit forms: the
code is verified, not fast. `clz_count` and `ctz_count` relate the counts to
`BitVec.clz` and `BitVec.ctz`, and `cpopNatRec_eq_sum` to `BitVec.cpop`.
-/

@[expose] public section

namespace Silmaril.RiscV.Backend

open Silmaril.RiscV.Ext (Compute)
open Machine.Lir (Unop)

/-! ## Counting identities -/

/-- `Σ_{i<n} g i`. -/
def sumNat (g : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumNat g n + g n

/-- `1` if the proposition holds. -/
def ind (p : Prop) [Decidable p] : Nat := if p then 1 else 0

theorem ushiftRight_eq_zero_iff {w : Nat} (x : BitVec w) (i : Nat) :
    x >>> i = 0#w ↔ ∀ j, i ≤ j → x.getLsbD j = false := by
  constructor
  · intro h j hj
    have := congrArg (fun y => y.getLsbD (j - i)) h
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero] at this
    rwa [Nat.add_sub_cancel' hj] at this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro k _
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
    exact h _ (by omega)

theorem shiftLeft_eq_zero_iff {w : Nat} (x : BitVec w) (j : Nat) :
    x <<< j = 0#w ↔ ∀ i, i + j < w → x.getLsbD i = false := by
  constructor
  · intro h i hi
    have := congrArg (fun y => y.getLsbD (i + j)) h
    simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero] at this
    simpa [hi, show ¬ (i + j < j) by omega] using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
    by_cases hkj : k < j
    · simp [hkj]
    · simp only [hk, decide_true, hkj, decide_false, Bool.not_false, Bool.and_self, Bool.true_and]
      exact h _ (by omega)

theorem sumNat_zero_of {g : Nat → Nat} : ∀ {m}, (∀ i < m, g i = 0) → sumNat g m = 0
  | 0, _ => rfl
  | m + 1, h => by rw [sumNat, sumNat_zero_of fun i hi => h i (by omega), h m (by omega)]

theorem clzAuxRec_count {w : Nat} (x : BitVec w) (hw : 0 < w) :
    ∀ n, n < w → (∀ i, n < i → x.getLsbD i = false) →
      (x.clzAuxRec n).toNat = (w - 1 - n) + sumNat (fun i => ind (x >>> i = 0#w)) (n + 1)
  | 0, _, h => by
    rw [BitVec.clzAuxRec_zero]
    by_cases h0 : x.getLsbD 0
    · have hx : ¬ x >>> 0 = 0#w := by
        rw [ushiftRight_eq_zero_iff]; intro hh; rw [hh 0 (le_refl _)] at h0; cases h0
      simp only [h0, ↓reduceIte, sumNat, ind, hx, Nat.zero_add]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.lt_two_pow_self (n := w); omega)]
      omega
    · have hx : x >>> 0 = 0#w := by
        rw [ushiftRight_eq_zero_iff]; intro j _
        by_cases hj : j = 0
        · subst hj; simpa using h0
        · exact h j (by omega)
      simp only [h0, Bool.false_eq_true, ↓reduceIte, sumNat, ind, hx, Nat.zero_add]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_two_pow_self)]
      omega
  | n + 1, hn, h => by
    rw [BitVec.clzAuxRec_succ]
    by_cases hb : x.getLsbD (n + 1)
    · simp only [hb, ↓reduceIte]
      rw [sumNat_zero_of fun i hi => by
        simp only [ind]
        rw [ite_false_of]
        rw [ushiftRight_eq_zero_iff]
        intro hh
        rw [hh (n + 1) (by omega)] at hb
        cases hb]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.lt_two_pow_self (n := w); omega)]
      omega
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      have h' : ∀ i, n < i → x.getLsbD i = false := by
        intro i hi
        by_cases e : i = n + 1
        · subst e; simpa using hb
        · exact h i (by omega)
      rw [clzAuxRec_count x hw n (by omega) h']
      have hz : x >>> (n + 1) = 0#w := by
        rw [ushiftRight_eq_zero_iff]; intro j hj
        by_cases e : j = n + 1
        · subst e; simpa using hb
        · exact h j (by omega)
      simp only [sumNat, ind, hz, ↓reduceIte]
      omega

/-- `clz x` is the number of shifts `x >>> i`, `i < w`, that are zero. -/
theorem clz_count {w : Nat} (x : BitVec w) (hw : 0 < w) :
    x.clz.toNat = sumNat (fun i => ind (x >>> i = 0#w)) w := by
  have := clzAuxRec_count x hw (w - 1) (by omega) (fun i hi => BitVec.getLsbD_of_ge x i (by omega))
  rw [BitVec.clz_eq_clzAuxRec, this, show w - 1 + 1 = w by omega]
  omega

theorem reverse_ushiftRight_eq_zero_iff {w : Nat} (x : BitVec w) (j : Nat) :
    x.reverse >>> j = 0#w ↔ x <<< j = 0#w := by
  rw [ushiftRight_eq_zero_iff, shiftLeft_eq_zero_iff]
  constructor
  · intro h i hi
    have := h (w - 1 - i) (by omega)
    rw [BitVec.getLsbD_reverse, BitVec.getMsbD] at this
    simpa [show w - 1 - i < w by omega, show w - 1 - (w - 1 - i) = i by omega] using this
  · intro h k hk
    rw [BitVec.getLsbD_reverse, BitVec.getMsbD]
    by_cases hkw : k < w
    · simp only [hkw, decide_true, Bool.true_and]
      exact h _ (by omega)
    · simp [hkw]

theorem sumNat_congr {g g' : Nat → Nat} : ∀ {n}, (∀ i < n, g i = g' i) → sumNat g n = sumNat g' n
  | 0, _ => rfl
  | n + 1, h => by rw [sumNat, sumNat, sumNat_congr fun i hi => h i (by omega), h n (by omega)]

/-- `ctz x` is the number of shifts `x <<< j`, `j < w`, that are zero. -/
theorem ctz_count {w : Nat} (x : BitVec w) (hw : 0 < w) :
    x.ctz.toNat = sumNat (fun j => ind (x <<< j = 0#w)) w := by
  rw [BitVec.ctz_eq_reverse_clz, clz_count _ hw]
  apply sumNat_congr
  intro i _
  simp only [ind, reverse_ushiftRight_eq_zero_iff]

theorem cpopNatRec_eq_sum {w : Nat} (x : BitVec w) :
    ∀ n, x.cpopNatRec n 0 = sumNat (fun i => (x.getLsbD i).toNat) n
  | 0 => rfl
  | n + 1 => by
    rw [BitVec.cpopNatRec_succ, BitVec.cpopNatRec_eq, Nat.zero_add, cpopNatRec_eq_sum x n, sumNat]

theorem sumNat_le {g : Nat → Nat} (h : ∀ i, g i ≤ 1) : ∀ n, sumNat g n ≤ n
  | 0 => le_rfl
  | n + 1 => by have := sumNat_le h n; have := h n; rw [sumNat]; omega

theorem ind_le (p : Prop) [Decidable p] : ind p ≤ 1 := by unfold ind; split <;> omega

theorem toNat_le_one (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide

/-! ## Unrolled sums -/

/-- Accumulate `n` terms into `t1`, term `n - 1` first; `term i` leaves its
value in `t0`. -/
def sumTerms (term : Nat → List Compute) : Nat → List Compute
  | 0 => []
  | n + 1 => term n ++ .base (.reg .add t1 t1 t0) :: sumTerms term n

theorem sumTerms_spec (term : Nat → List Compute) (g : Nat → Nat) (src : Reg) (V : Word)
    (hsrc : src ≠ t0 ∧ src ≠ t1) (N : Nat)
    (hterm : ∀ i, i < N → ∀ (s : State), s.read src = V →
      (Machine.Block.run Compute.step (term i) s).read t0 = BitVec.ofNat 64 (g i) ∧
      ∀ r, r ≠ t0 → (Machine.Block.run Compute.step (term i) s).read r = s.read r) :
    ∀ n, n ≤ N → ∀ (s : State) (A : Nat), s.read src = V → s.read t1 = BitVec.ofNat 64 A →
      (Machine.Block.run Compute.step (sumTerms term n) s).read t1 =
        BitVec.ofNat 64 (A + sumNat g n) ∧
      ∀ r, r ≠ t0 → r ≠ t1 →
        (Machine.Block.run Compute.step (sumTerms term n) s).read r = s.read r
  | 0, _, s, A, _, h1 => ⟨by simpa [sumTerms, sumNat] using h1, fun _ _ _ => rfl⟩
  | n + 1, hn, s, A, hs, h1 => by
    obtain ⟨v₀, fr₀⟩ := hterm n (by omega) s hs
    set s₁ := Machine.Block.run Compute.step (term n) s
    set c : Compute := .base (.reg .add t1 t1 t0)
    have hs₂ : (Compute.step c s₁).read src = V := by
      simp only [c, read_compute_step, Compute.dest, RiscV.Instr.dest, hsrc.2, false_and,
        ↓reduceIte]
      rw [fr₀ src hsrc.1]; exact hs
    have h1₂ : (Compute.step c s₁).read t1 = BitVec.ofNat 64 (A + g n) := by
      simp only [c, read_compute_step, Compute.dest, RiscV.Instr.dest, ne_eq, t1_ne_zero,
        not_false_eq_true, and_self, ↓reduceIte, Compute.value, RiscV.Instr.value, RiscV.RegOp.eval]
      rw [fr₀ t1 t1_ne_t0, h1, v₀, BitVec.ofNat_add]
    obtain ⟨vt, fr⟩ := sumTerms_spec term g src V hsrc N hterm n (by omega) (Compute.step c s₁)
      (A + g n) hs₂ h1₂
    refine ⟨?_, fun r h0 h1' => ?_⟩
    · simp only [sumTerms, Machine.Block.run_append, Machine.Block.run_cons]
      rw [vt, sumNat]; congr 1; omega
    · simp only [sumTerms, Machine.Block.run_append, Machine.Block.run_cons]
      rw [fr r h0 h1']
      simp only [c, read_compute_step, Compute.dest, RiscV.Instr.dest, h1', false_and, ↓reduceIte]
      exact fr₀ r h0

theorem sumTerms_dests {term : Nat → List Compute} (h : ∀ i, ∀ c ∈ term i, c.dest = t0) :
    ∀ n, ∀ c ∈ sumTerms term n, c.dest = t0 ∨ c.dest = t1
  | 0 => by simp [sumTerms]
  | n + 1 => by
    intro c hc
    simp only [sumTerms, List.mem_append, List.mem_cons] at hc
    rcases hc with hc | rfl | hc
    · exact .inl (h n c hc)
    · exact .inr rfl
    · exact sumTerms_dests h n c hc

/-! ## Terms -/

theorem ofNat6_toNat {i : Nat} (h : i < 64) : (BitVec.ofNat 6 i).toNat = i := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- Bit `i` of `x` into `t0`. -/
def popTerm (x : Reg) (i : Nat) : List Compute :=
  [.base (.shift .srl t0 x (BitVec.ofNat 6 i)), .base (.imm .and t0 t0 1#12)]

/-- Whether `x >>> i` is zero, into `t0`. -/
def shrTerm (x : Reg) (i : Nat) : List Compute :=
  [.base (.shift .srl t0 x (BitVec.ofNat 6 i)), .base (.imm .sltu t0 t0 1#12)]

/-- Whether `x <<< (k + i)` is zero, into `t0`. -/
def shlTerm (x : Reg) (k i : Nat) : List Compute :=
  [.base (.shift .sll t0 x (BitVec.ofNat 6 (k + i))), .base (.imm .sltu t0 t0 1#12)]

theorem and_one_bit (v : Word) (i : Nat) :
    (v >>> i) &&& 1#64 = BitVec.ofNat 64 (v.getLsbD i).toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, show (1#64).toNat = 1 from rfl, Nat.and_one_is_mod]
  rw [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
  have h2 : v.toNat >>> i % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [Nat.shiftRight_eq_div_pow] at *
  by_cases h : v.toNat / 2 ^ i % 2 = 1
  · simp [h]
  · have : v.toNat / 2 ^ i % 2 = 0 := by omega
    simp [this]

theorem sltiu_ind (v : Word) :
    boolWord (v.ult ((1#12).signExtend 64)) = BitVec.ofNat 64 (ind (v = 0#64)) := by
  rw [ult_one, boolWord_eq]
  by_cases h : v = 0#64
  · simp [h, ind, Machine.Lir.ofBool]
  · simp [h, ind, Machine.Lir.ofBool]

theorem term_frame {cs : List Compute} (h : ∀ c ∈ cs, c.dest = t0) (s : State) (r : Reg)
    (hr : r ≠ t0) : (Machine.Block.run Compute.step cs s).read r = s.read r :=
  Ext.run_read_frame cs s r fun c hc e => hr (e.trans (h c hc))

theorem popTerm_spec {x : Reg} {V : Word} (i : Nat) (hi : i < 64) (s : State)
    (hs : s.read x = V) :
    (Machine.Block.run Compute.step (popTerm x i) s).read t0 = BitVec.ofNat 64 (V.getLsbD i).toNat ∧
      ∀ r, r ≠ t0 → (Machine.Block.run Compute.step (popTerm x i) s).read r = s.read r := by
  refine ⟨?_, term_frame (by simp [popTerm, Compute.dest, RiscV.Instr.dest]) s⟩
  simp [popTerm, RiscV.Instr.dest, RiscV.Instr.value, RiscV.ShiftOp.eval, RiscV.ImmOp.eval,
    ofNat6_toNat hi, hs, and_one_bit]

theorem shrTerm_spec {x : Reg} {V : Word} (i : Nat) (hi : i < 64) (s : State)
    (hs : s.read x = V) :
    (Machine.Block.run Compute.step (shrTerm x i) s).read t0 = BitVec.ofNat 64 (ind (V >>> i = 0#64)) ∧
      ∀ r, r ≠ t0 → (Machine.Block.run Compute.step (shrTerm x i) s).read r = s.read r := by
  refine ⟨?_, term_frame (by simp [shrTerm, Compute.dest, RiscV.Instr.dest]) s⟩
  simp only [shrTerm, Machine.Block.run_cons, Machine.Block.run_nil, Ext.Compute.step_base,
    read_base_step, RiscV.Instr.dest, ne_eq, t0_ne_zero, not_false_eq_true, and_self, ↓reduceIte,
    RiscV.Instr.value, RiscV.ImmOp.eval, RiscV.ShiftOp.eval, ofNat6_toNat hi, hs]
  exact sltiu_ind _

theorem shlTerm_spec {x : Reg} {V : Word} (k i : Nat) (hi : k + i < 64) (s : State)
    (hs : s.read x = V) :
    (Machine.Block.run Compute.step (shlTerm x k i) s).read t0 =
        BitVec.ofNat 64 (ind (V <<< (k + i) = 0#64)) ∧
      ∀ r, r ≠ t0 → (Machine.Block.run Compute.step (shlTerm x k i) s).read r = s.read r := by
  refine ⟨?_, term_frame (by simp [shlTerm, Compute.dest, RiscV.Instr.dest]) s⟩
  simp only [shlTerm, Machine.Block.run_cons, Machine.Block.run_nil, Ext.Compute.step_base,
    read_base_step, RiscV.Instr.dest, ne_eq, t0_ne_zero, not_false_eq_true, and_self, ↓reduceIte,
    RiscV.Instr.value, RiscV.ImmOp.eval, RiscV.ShiftOp.eval, ofNat6_toNat hi, hs]
  exact sltiu_ind _

/-! ## Selection -/

/-- `t1 := 0`, the `n` terms summed into `t1` (after `pre`), then `d := t1`. -/
def countSeq (pre : List Compute) (term : Nat → List Compute) (n : Nat) (d : Reg) : List Compute :=
  pre ++ .base (.imm .add t1 0#5 0#12) :: (sumTerms term n ++ [.base (.imm .add d t1 0#12)])

theorem countSeq_value (pre : List Compute) (term : Nat → List Compute) (g : Nat → Nat)
    (n : Nat) {d src : Reg} {V : Word} (hd : d ≠ 0#5) (hsrc : src ≠ t0 ∧ src ≠ t1)
    (hterm : ∀ i, i < n → ∀ (s : State), s.read src = V →
      (Machine.Block.run Compute.step (term i) s).read t0 = BitVec.ofNat 64 (g i) ∧
      ∀ r, r ≠ t0 → (Machine.Block.run Compute.step (term i) s).read r = s.read r)
    (s : State) (hpre : (Machine.Block.run Compute.step pre s).read src = V) :
    (Machine.Block.run Compute.step (countSeq pre term n d) s).read d =
      BitVec.ofNat 64 (sumNat g n) := by
  set s₁ := Machine.Block.run Compute.step pre s
  set c : Compute := .base (.imm .add t1 0#5 0#12)
  have hs₂ : (Compute.step c s₁).read src = V := by
    simp only [c, read_compute_step, Compute.dest, RiscV.Instr.dest, hsrc.2, false_and, ↓reduceIte]
    exact hpre
  have h1₂ : (Compute.step c s₁).read t1 = BitVec.ofNat 64 0 := by
    simp [c, RiscV.Instr.dest, RiscV.Instr.value, RiscV.ImmOp.eval]
  obtain ⟨vt, _⟩ := sumTerms_spec term g src V hsrc n hterm n le_rfl _ 0 hs₂ h1₂
  simp only [countSeq, Machine.Block.run_append, Machine.Block.run_cons, Machine.Block.run_nil]
  rw [read_compute_step]
  simp only [Compute.dest, RiscV.Instr.dest, ne_eq, hd, not_false_eq_true, and_self, ↓reduceIte,
    Compute.value, RiscV.Instr.value, RiscV.ImmOp.eval, zero_signExtend64, BitVec.add_zero]
  rw [vt, Nat.zero_add]

theorem countSeq_dests {pre : List Compute} {term : Nat → List Compute} {n : Nat} {d : Reg}
    (hpre : ∀ c ∈ pre, Scratch c.dest) (hterm : ∀ i, ∀ c ∈ term i, c.dest = t0) :
    DestsIn (countSeq pre term n d) d := by
  intro c hc
  simp only [countSeq, List.mem_append, List.mem_cons] at hc
  rcases hc with hc | rfl | hc | rfl | hc
  · exact .inr (hpre c hc)
  · exact .inr (.inr (.inl rfl))
  · rcases sumTerms_dests hterm n c hc with h | h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
  · exact .inl rfl
  · cases hc

/-- All unary operators: the bit-counting operators as unrolled sums, the rest
by `selUnopBasic`. -/
def selUnop (op : Unop) (d x : Reg) : Option (List Compute) :=
  match op with
  | .popcnt => some (countSeq [] (popTerm x) 64 d)
  | .popcnt32 => some (countSeq [] (popTerm x) 32 d)
  | .clz => some (countSeq [] (shrTerm x) 64 d)
  | .clz32 =>
    some (countSeq [.base (.shift .sll t2 x 32#6), .base (.shift .srl t2 t2 32#6)] (shrTerm t2) 32 d)
  | .ctz => some (countSeq [] (shlTerm x 0) 64 d)
  | .ctz32 => some (countSeq [] (shlTerm x 32) 32 d)
  | _ => selUnopBasic op d x

theorem selUnop_isSome (op : Unop) (d x : Reg) : (selUnop op d x).isSome = true := by
  cases op <;> rfl

theorem selUnop_dests {op : Unop} {d x : Reg} {cs : List Compute} (h : selUnop op d x = some cs) :
    DestsIn cs d := by
  cases op <;> simp only [selUnop, Option.some.injEq] at h
  case clz | clz32 =>
    subst h
    exact countSeq_dests (by simp [Compute.dest, RiscV.Instr.dest, Scratch])
      (fun i => by simp [shrTerm, Compute.dest, RiscV.Instr.dest])
  case ctz | ctz32 =>
    subst h
    exact countSeq_dests (by simp) (fun i => by simp [shlTerm, Compute.dest, RiscV.Instr.dest])
  case popcnt | popcnt32 =>
    subst h
    exact countSeq_dests (by simp) (fun i => by simp [popTerm, Compute.dest, RiscV.Instr.dest])
  all_goals exact selUnopBasic_dests h

theorem selUnop_ne_nil {op : Unop} {d x : Reg} {cs : List Compute} (h : selUnop op d x = some cs) :
    cs ≠ [] := by
  cases op <;> simp only [selUnop, Option.some.injEq] at h
  case clz | clz32 | ctz | ctz32 | popcnt | popcnt32 => subst h; simp [countSeq]
  all_goals exact selUnopBasic_ne_nil h

theorem ofNat_count {S n : Nat} (hS : S ≤ n) (hn : n ≤ 64) {v : Word} (hv : v.toNat = S) :
    BitVec.ofNat 64 S = v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (hS.trans hn) (by decide)), hv]

theorem getLsbD_lo32 (x : Word) {i : Nat} (hi : i < 32) :
    (Machine.Lir.lo32 x).getLsbD i = x.getLsbD i := by
  simp [Machine.Lir.lo32, hi]

theorem selUnop_value {op : Unop} {d x : Reg} {cs : List Compute} (hsel : selUnop op d x = some cs)
    (hx : ¬ Scratch x) (hd : d ≠ 0#5) (s : State) :
    (Machine.Block.run Compute.step cs s).read d = op.eval (s.read x) := by
  obtain ⟨hx0, hx1, -⟩ := ne_scratch hx
  cases op <;> simp only [selUnop, Option.some.injEq] at hsel
  case popcnt =>
    subst hsel
    rw [countSeq_value [] _ (fun i => ((s.read x).getLsbD i).toNat) 64 hd ⟨hx0, hx1⟩
      (fun i hi s' hs' => popTerm_spec i (by omega) s' hs') s rfl]
    apply ofNat_count (sumNat_le (fun i => toNat_le_one _) 64) le_rfl
    simp only [Machine.Lir.Unop.eval, BitVec.toNat_cpop, cpopNatRec_eq_sum]
  case popcnt32 =>
    subst hsel
    rw [countSeq_value [] _ (fun i => ((s.read x).getLsbD i).toNat) 32 hd ⟨hx0, hx1⟩
      (fun i hi s' hs' => popTerm_spec i (by omega) s' hs') s rfl]
    apply ofNat_count (sumNat_le (fun i => toNat_le_one _) 32) (by decide)
    simp only [Machine.Lir.Unop.eval, of32_toNat, BitVec.toNat_cpop, cpopNatRec_eq_sum]
    exact sumNat_congr fun i hi => by rw [getLsbD_lo32 _ hi]
  case clz =>
    subst hsel
    rw [countSeq_value [] _ (fun i => ind (s.read x >>> i = 0#64)) 64 hd ⟨hx0, hx1⟩
      (fun i hi s' hs' => shrTerm_spec i (by omega) s' hs') s rfl]
    apply ofNat_count (sumNat_le (fun i => ind_le _) 64) le_rfl
    rw [Machine.Lir.Unop.eval, clz_count _ (by decide)]
  case ctz =>
    subst hsel
    rw [countSeq_value [] _ (fun i => ind (s.read x <<< (0 + i) = 0#64)) 64 hd ⟨hx0, hx1⟩
      (fun i hi s' hs' => shlTerm_spec 0 i (by omega) s' hs') s rfl]
    apply ofNat_count (sumNat_le (fun i => ind_le _) 64) le_rfl
    rw [Machine.Lir.Unop.eval, ctz_count _ (by decide)]
    exact sumNat_congr fun i _ => by rw [Nat.zero_add]
  case clz32 =>
    subst hsel
    set z : Word := Machine.Lir.of32 (Machine.Lir.lo32 (s.read x))
    have hpre : (Machine.Block.run Compute.step
        [.base (.shift .sll t2 x 32#6), .base (.shift .srl t2 t2 32#6)] s).read t2 = z := by
      simp [RiscV.Instr.dest, RiscV.Instr.value, RiscV.ShiftOp.eval, z, zext32_eq, lo32_eq]
    rw [countSeq_value _ _ (fun i => ind (z >>> i = 0#64)) 32 hd ⟨by decide, by decide⟩
      (fun i hi s' hs' => shrTerm_spec i (by omega) s' hs') s hpre]
    apply ofNat_count (sumNat_le (fun i => ind_le _) 32) (by decide)
    rw [Machine.Lir.Unop.eval, of32_toNat, clz_count _ (by decide)]
    apply sumNat_congr
    intro i hi
    have key : z >>> i = 0#64 ↔ Machine.Lir.lo32 (s.read x) >>> i = 0#32 := by
      rw [ushiftRight_eq_zero_iff, ushiftRight_eq_zero_iff]
      constructor
      · intro h j hj
        by_cases hj32 : j < 32
        · have := h j hj
          simpa [z, Machine.Lir.of32, BitVec.getLsbD_setWidth, hj32, show j < 64 by omega] using this
        · exact BitVec.getLsbD_of_ge _ _ (by omega)
      · intro h j hj
        by_cases hj32 : j < 32
        · have := h j hj
          simpa [z, Machine.Lir.of32, BitVec.getLsbD_setWidth, hj32, show j < 64 by omega] using this
        · simp only [z, Machine.Lir.of32, BitVec.getLsbD_setWidth]
          rw [BitVec.getLsbD_of_ge _ _ (by omega : 32 ≤ j), Bool.and_false]
    simp only [ind, key]
  case ctz32 =>
    subst hsel
    rw [countSeq_value [] _ (fun i => ind (s.read x <<< (32 + i) = 0#64)) 32 hd ⟨hx0, hx1⟩
      (fun i hi s' hs' => shlTerm_spec 32 i (by omega) s' hs') s rfl]
    apply ofNat_count (sumNat_le (fun i => ind_le _) 32) (by decide)
    rw [Machine.Lir.Unop.eval, of32_toNat, ctz_count _ (by decide)]
    apply sumNat_congr
    intro i hi
    have key : s.read x <<< (32 + i) = 0#64 ↔ Machine.Lir.lo32 (s.read x) <<< i = 0#32 := by
      rw [shiftLeft_eq_zero_iff, shiftLeft_eq_zero_iff]
      constructor
      · intro h k hk
        rw [getLsbD_lo32 _ (by omega)]
        exact h k (by omega)
      · intro h k hk
        have := h k (by omega)
        rwa [getLsbD_lo32 _ (by omega)] at this
    simp only [ind, key]
  all_goals exact selUnopBasic_value hsel hd s

end Silmaril.RiscV.Backend
