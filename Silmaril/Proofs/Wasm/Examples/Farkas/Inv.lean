module

public import Silmaril.Proofs.Wasm.Examples.Farkas.Exec
public import Silmaril.Logic.LinArith.Thms
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# The Farkas checker: the invariant

`Inv m rs`: the memory is one page and, unless the sticky flag is set, the machine state
represents the weighted rows `rs` exactly (`Exact`): nonnegative multipliers at most `2³⁰`,
the current row's multiplier in `y`, `accB = combB rs`, `acc[j] = comb rs j` for `j < nVars`,
all within `2⁶²`, and no coefficient for `j ≥ nVars`.

* `inv_row`, `inv_entry`: `row`/`entry` preserve it, for the rows extended by `Cmd.apply`;
* `cert_of_check`: if `check` answers `1`, the rows carry a valid Farkas certificate;
* `inv_check`: after `check` (all slots zeroed, globals reset) it holds for no rows;
* `inv_init`: it holds initially;
* `check_complete`: from a valid certificate with no failed check, the answer is `1`.
-/

namespace Silmaril.Wasm.Examples.Farkas

open Silmaril.Wasm Silmaril.Wasm.Numerics
open Silmaril.Logic.LinArith (WRows Cmd Ineq)

/-- The exact representation of the weighted rows. -/
structure Exact (m : Mach) (rs : WRows) : Prop where
  mults : ∀ p ∈ rs, 0 ≤ p.1 ∧ p.1 ≤ cB
  cur : m.hr ≠ 0 → ∃ r rs', rs = (m.y.toInt, r) :: rs'
  accB : m.vb.toInt = WRows.combB rs
  accB_le : -aB ≤ WRows.combB rs ∧ WRows.combB rs ≤ aB
  acc : ∀ j < nVars, (slot m.mem j).toInt = WRows.comb rs j
  acc_le : ∀ j, -aB ≤ WRows.comb rs j ∧ WRows.comb rs j ≤ aB
  high : ∀ j, nVars ≤ j → WRows.comb rs j = 0

/-- **The invariant of the checker.** -/
def Inv (m : Mach) (rs : WRows) : Prop := m.mem.size = 65536 ∧ (m.bad = 0 → Exact m rs)

/-! ## Reading the flags -/

theorem ltS_eq_zero {x : BitVec 64} {v : Int} (h₁ : -2 ^ 63 ≤ v) (h₂ : v < 2 ^ 63) :
    ltS x v = 0 ↔ v ≤ x.toInt := by
  simp only [ltS]
  rw [ltS_ofInt h₁ h₂, bool32_eq_zero, decide_eq_false_iff_not, not_lt]

theorem gtS_eq_zero {x : BitVec 64} {v : Int} (h₁ : -2 ^ 63 ≤ v) (h₂ : v < 2 ^ 63) :
    gtS x v = 0 ↔ x.toInt ≤ v := by
  simp only [gtS]
  rw [gtS_ofInt h₁ h₂, bool32_eq_zero, decide_eq_false_iff_not, gt_iff_lt, not_lt]

theorem eqz_eq_zero {x : BitVec 32} : intTestOp .i32 .eqz x = 0 ↔ x ≠ 0 := by
  show bool32 (x == 0) = 0 ↔ x ≠ 0
  rw [bool32_eq_zero]
  cases hx : x == 0 <;> simp_all

theorem geU_eq_zero {j : BitVec 32} :
    intRelOp .i32 (.ge .unsigned) j (BitVec.ofNat 32 nVars) = 0 ↔ j.toNat < nVars := by
  have hn : (BitVec.ofNat 32 nVars).toNat = nVars := rfl
  simp only [intRelOp, bool32_eq_zero, decide_eq_false_iff_not, ge_iff_le, not_le]
  exact iff_of_eq (congrArg (j.toNat < ·) hn)

theorem ne_eq_zero {x : BitVec 64} : intRelOp .i64 .ne x (BitVec.ofInt 64 0) = 0 ↔ x = 0 := by
  show bool32 (x != 0) = 0 ↔ x = 0
  rw [bool32_eq_zero]
  cases hx : x != 0 <;> simp_all

/-! ## `row` -/

/-- What a passing `row` checked. -/
theorem row_checks {m : Mach} {y b : BitVec 64} (h : (rowM m y b).bad = 0) :
    m.bad = 0 ∧ (0 ≤ y.toInt ∧ y.toInt ≤ cB) ∧ (-cB ≤ b.toInt ∧ b.toInt ≤ cB) ∧
      (-aB ≤ (m.vb + y * b).toInt ∧ (m.vb + y * b).toInt ≤ aB) := by
  simp only [rowM, or_eq_zero] at h
  obtain ⟨⟨⟨⟨⟨⟨h₀, h₁⟩, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩ := h
  refine ⟨h₀, ⟨(ltS_eq_zero ?_ ?_).1 h₁, (gtS_eq_zero ?_ ?_).1 h₂⟩,
    ⟨(ltS_eq_zero ?_ ?_).1 h₃, (gtS_eq_zero ?_ ?_).1 h₄⟩,
    ⟨(ltS_eq_zero ?_ ?_).1 h₅, (gtS_eq_zero ?_ ?_).1 h₆⟩⟩ <;> norm_num [cB, aB]

/-- **`row` preserves the invariant.** -/
theorem inv_row {m : Mach} {rs : WRows} (h : Inv m rs) (y b : BitVec 64) :
    Inv (rowM m y b) ((Cmd.row y.toInt b.toInt).apply rs) := by
  refine ⟨h.1, fun hbad => ?_⟩
  obtain ⟨hm, hy, hb, ht⟩ := row_checks hbad
  have hE : Exact m rs := h.2 hm
  have hv : -aB ≤ m.vb.toInt ∧ m.vb.toInt ≤ aB := hE.accB ▸ hE.accB_le
  have hy' : -cB ≤ y.toInt ∧ y.toInt ≤ cB := ⟨by simp only [cB] at hy ⊢; omega, hy.2⟩
  have hsum : (m.vb + y * b).toInt = y.toInt * b.toInt + WRows.combB rs := by
    rw [macc_toInt hv hy' hb, hE.accB]
    ring
  have hcomb := Cmd.comb_row rs y.toInt b.toInt
  have hcombB := Cmd.combB_row rs y.toInt b.toInt
  refine ⟨fun p hp => ?_, fun _ => ⟨⟨[], b.toInt⟩, rs, rfl⟩, hsum.trans hcombB.symm, ?_, fun j hj => ?_,
    fun j => hcomb j ▸ hE.acc_le j, fun j hj => (hcomb j).trans (hE.high j hj)⟩
  · rcases Cmd.mults_row rs y.toInt b.toInt p hp with rfl | hp'
    · exact hy
    · exact hE.mults p hp'
  · rw [hcombB, ← hsum]
    exact ht
  · exact (hE.acc j hj).trans (hcomb j).symm

/-! ## `entry` -/

/-- What a passing `entry` checked. -/
theorem entry_checks {m : Mach} {j : BitVec 32} {a : BitVec 64} (h : (entryM m j a).bad = 0) :
    m.bad = 0 ∧ m.hr ≠ 0 ∧ j.toNat < nVars ∧ (-cB ≤ a.toInt ∧ a.toInt ≤ cB) ∧
      (-aB ≤ (slot m.mem (j.toNat % nVars) + m.y * a).toInt ∧
        (slot m.mem (j.toNat % nVars) + m.y * a).toInt ≤ aB) := by
  simp only [entryM, or_eq_zero] at h
  obtain ⟨⟨⟨⟨⟨⟨h₀, h₁⟩, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩ := h
  refine ⟨h₀, eqz_eq_zero.1 h₁, geU_eq_zero.1 h₂, ⟨(ltS_eq_zero ?_ ?_).1 h₃, (gtS_eq_zero ?_ ?_).1 h₄⟩,
    ⟨(ltS_eq_zero ?_ ?_).1 h₅, (gtS_eq_zero ?_ ?_).1 h₆⟩⟩ <;> norm_num [cB, aB]

/-- The accumulators after an `entry` that passed. -/
theorem entry_acc {m : Mach} {r : Ineq} {rs : WRows} {j : BitVec 32} {a : BitVec 64}
    (hB : m.mem.size = 65536) (hE : Exact m ((m.y.toInt, r) :: rs)) (hj : j.toNat < nVars)
    (hy : -cB ≤ m.y.toInt ∧ m.y.toInt ≤ cB) (ha : -cB ≤ a.toInt ∧ a.toInt ≤ cB) (k : Nat)
    (hk : k < nVars) :
    (slot (setSlot m.mem j.toNat (slot m.mem j.toNat + m.y * a)) k).toInt =
      WRows.comb ((Cmd.entry j.toNat a.toInt).apply ((m.y.toInt, r) :: rs)) k := by
  rw [Cmd.comb_entry]
  by_cases hjk : j.toNat = k
  · subst hjk
    have hv : -aB ≤ (slot m.mem j.toNat).toInt ∧ (slot m.mem j.toNat).toInt ≤ aB :=
      hE.acc j.toNat hj ▸ hE.acc_le j.toNat
    rw [slot_setSlot_same hB hj, macc_toInt hv hy ha, hE.acc j.toNat hj]
    simp only [↓reduceIte]
    ring
  · rw [slot_setSlot_ne hB hj hjk]
    simp only [hjk, ↓reduceIte, zero_add]
    exact hE.acc k hk

/-- **`entry` preserves the invariant.** -/
theorem inv_entry {m : Mach} {rs : WRows} (h : Inv m rs) (j : BitVec 32) (a : BitVec 64) :
    Inv (entryM m j a) ((Cmd.entry j.toNat a.toInt).apply rs) := by
  have hj' : j.toNat % nVars < nVars := Nat.mod_lt _ (by decide)
  refine ⟨size_setSlot h.1 hj' _, fun hbad => ?_⟩
  obtain ⟨hm, hhr, hj, ha, ht⟩ := entry_checks hbad
  have hE : Exact m rs := h.2 hm
  obtain ⟨r, rs', hrs⟩ := hE.cur hhr
  subst hrs
  have hmod : j.toNat % nVars = j.toNat := Nat.mod_eq_of_lt hj
  have hy₀ := hE.mults _ List.mem_cons_self
  have hy : -cB ≤ m.y.toInt ∧ m.y.toInt ≤ cB := ⟨by simp only [cB] at hy₀ ⊢; omega, hy₀.2⟩
  have hcomb := Cmd.comb_entry m.y.toInt r rs' j.toNat a.toInt
  have hacc := entry_acc h.1 hE hj hy ha
  have hslot : ∀ k < nVars, (slot (entryM m j a).mem k).toInt =
      WRows.comb ((Cmd.entry j.toNat a.toInt).apply ((m.y.toInt, r) :: rs')) k := by
    intro k hk
    simpa only [entryM, hmod] using hacc k hk
  refine ⟨fun p hp => ?_, fun _ => ⟨_, rs', rfl⟩, ?_, ?_, hslot, fun k => ?_, fun k hk => ?_⟩
  · rcases Cmd.mults_entry m.y.toInt r rs' j.toNat a.toInt p hp with hp' | hp'
    · exact hp' ▸ hy₀
    · exact hE.mults p (List.mem_cons_of_mem _ hp')
  · rw [Cmd.combB_entry]
    exact hE.accB
  · rw [Cmd.combB_entry]
    exact hE.accB_le
  · show -aB ≤ WRows.comb _ k ∧ WRows.comb _ k ≤ aB
    by_cases hk : k < nVars
    · rw [← hslot k hk]
      by_cases hjk : j.toNat = k
      · subst hjk
        have ht' := ht
        simp only [hmod] at ht'
        simpa only [entryM, hmod, slot_setSlot_same h.1 hj] using ht'
      · simpa only [entryM, hmod, slot_setSlot_ne h.1 hj hjk, hE.acc k hk] using hE.acc_le k
    · have hne : j.toNat ≠ k := fun he => hk (he ▸ hj)
      rw [hcomb k]
      simp only [hne, ↓reduceIte, zero_add]
      exact hE.acc_le k
  · have hne : j.toNat ≠ k := fun he => absurd (he ▸ hj) (Nat.not_lt.2 hk)
    rw [hcomb k]
    simp only [hne, ↓reduceIte, zero_add]
    exact hE.high k hk

/-! ## `check` -/

/-- What the scan loop of `check` establishes: every slot is zero afterwards, and if no
nonzero slot was seen, every slot was zero before. -/
structure ScanDone (B₀ B : ByteArray) (nz : BitVec 32) : Prop where
  size : B.size = 65536
  zero : ∀ k < nVars, slot B k = 0
  nz_zero : nz = 0 → ∀ k < nVars, slot B₀ k = 0
  nz_of : (∀ k < nVars, slot B₀ k = 0) → nz = 0

theorem bool32_and (a b : Bool) : bool32 a &&& bool32 b = bool32 (a && b) := by
  cases a <;> cases b <;> decide

theorem bool32_eq_one {b : Bool} : bool32 b = 1 ↔ b = true := by
  cases b <;> decide

/-- `check` answers `1` only if no check failed, no slot was nonzero and `accB < 0`. -/
theorem checkRes_eq_one {m : Mach} {nz : BitVec 32} (h : checkRes m nz = 1) :
    m.bad = 0 ∧ nz = 0 ∧ m.vb.toInt < 0 := by
  have hlt : ltS m.vb 0 = bool32 (decide (m.vb.toInt < 0)) := ltS_ofInt (by norm_num) (by norm_num)
  have he : checkRes m nz = bool32 ((m.bad == 0) && (nz == 0) && decide (m.vb.toInt < 0)) := by
    rw [checkRes, hlt]
    exact (congrArg (· &&& _) (bool32_and _ _)).trans (bool32_and _ _)
  rw [he, bool32_eq_one] at h
  simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] using h

/-- `check` answers `1` when no check failed, no slot was nonzero and `accB < 0`. -/
theorem checkRes_of {m : Mach} {nz : BitVec 32} (hb : m.bad = 0) (hnz : nz = 0)
    (hv : m.vb.toInt < 0) : checkRes m nz = 1 := by
  have hlt : ltS m.vb 0 = bool32 (decide (m.vb.toInt < 0)) := ltS_ofInt (by norm_num) (by norm_num)
  rw [checkRes, hlt, hb, hnz]
  simp only [decide_eq_true hv]
  decide

/-- **Completeness of `check`**: from a state representing a valid certificate with no failed
check, the scan's answer is `1`. -/
theorem check_complete {m : Mach} {rs : WRows} {B : ByteArray} {nz : BitVec 32} (h : Inv m rs)
    (hb : m.bad = 0) (hc : WRows.IsCert rs) (hd : ScanDone m.mem B nz) : checkRes m nz = 1 := by
  have hE : Exact m rs := h.2 hb
  have hz : ∀ k < nVars, slot m.mem k = 0 := fun k hk =>
    BitVec.eq_of_toInt_eq ((hE.acc k hk).trans (hc.comb_zero k))
  exact checkRes_of hb (hd.nz_of hz) (hE.accB ▸ hc.combB_neg)

/-- **`check` answering `1` certifies the loaded rows.** -/
theorem cert_of_check {m : Mach} {rs : WRows} {B : ByteArray} {nz : BitVec 32} (h : Inv m rs)
    (hd : ScanDone m.mem B nz) (hr : checkRes m nz = 1) : WRows.IsCert rs := by
  obtain ⟨hm, hnz, hvb⟩ := checkRes_eq_one hr
  have hE : Exact m rs := h.2 hm
  refine ⟨fun p hp => (hE.mults p hp).1, fun j => ?_, hE.accB ▸ hvb⟩
  by_cases hj : j < nVars
  · rw [← hE.acc j hj, hd.nz_zero hnz j hj]
    rfl
  · exact hE.high j (Nat.not_lt.1 hj)

/-- **After `check`** the invariant holds for no rows. -/
theorem inv_check {B₀ B : ByteArray} {nz : BitVec 32} (hd : ScanDone B₀ B nz) :
    Inv (checkEnd B) [] :=
  ⟨hd.size, fun _ => ⟨fun _ hp => absurd hp List.not_mem_nil, fun h => absurd rfl h, rfl,
    by norm_num [aB, WRows.combB], fun j hj => by rw [show (checkEnd B).mem = B from rfl, hd.zero j hj]; rfl,
    fun _ => by norm_num [aB, WRows.comb], fun _ _ => rfl⟩⟩

/-- The invariant holds initially. -/
theorem inv_init : Inv Mach.init [] :=
  inv_check (B₀ := zeroBytes) (nz := 0)
    ⟨size_zeroBytes, fun _ hk => slot_zeroBytes hk, fun _ _ hk => slot_zeroBytes hk, fun _ => rfl⟩

end Silmaril.Wasm.Examples.Farkas
