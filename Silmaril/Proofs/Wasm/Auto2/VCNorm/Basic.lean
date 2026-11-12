module

public import Silmaril.Wasm.Auto2.VCNorm.Defs
public import Silmaril.Wasm.Auto2.VCGen.Thms

/-!
# Soundness of the normaliser and of renaming (the VC generator)

* `Tm.den_norm`, `Fm.den_norm`: normalisation preserves the meaning of terms and formulas;
* `Tm.den_rn`, `Fm.den_rn`: renaming the variables is a change of environment (`Env.comp`);
* `valid_rn`, `valid_norm`: validity is preserved by both;
* `valid_of_accepts`, `allValid_of_coveredN`: the conditions the check accepts are valid.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCGen

open Silmaril.Wasm
open Silmaril.Wasm.Auto.VCGen (binW relW relB unW litT unT binT relP relV eqzV nz32 iteT wrapW
  extSW extUW)

variable {F : Fns}

/-! ## Normalisation -/

theorem binW_comm {n : Nat} {op : IntBinOp} (h : IntBinOp.comm op = true) (x y : BitVec n) :
    binW n op x y = binW n op y x := by
  cases op <;> simp [IntBinOp.comm] at h <;> simp only [binW]
  · exact BitVec.add_comm x y
  · exact BitVec.mul_comm x y
  · exact BitVec.and_comm x y
  · exact BitVec.or_comm x y
  · exact BitVec.xor_comm x y

theorem binT_comm {t : IntType} {op : IntBinOp} (h : IntBinOp.comm op = true)
    (x y : BitVec t.width) : binT t op x y = binT t op y x := by
  cases t <;> exact binW_comm h x y

theorem den_binN (ρ ξ : Env) {t : IntType} (op : IntBinOp) (a b : Tm t) :
    (binN op a b).den F ρ ξ = binT t op (a.den F ρ ξ) (b.den F ρ ξ) := by
  unfold binN
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    simp only [Tm.den]
    exact binT_comm h.1 _ _
  · rfl

theorem relB_eq_comm {n : Nat} (x y : BitVec n) : relB n .eq y x = relB n .eq x y := by
  simp only [relB]
  by_cases h : x = y
  · rw [h]
  · rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (Ne.symm h)]

theorem relB_eq_comm' {n : Nat} (x y : BitVec n) : (y == x) = (x == y) :=
  relB_eq_comm x y

theorem relB_ne_comm {n : Nat} (x y : BitVec n) : relB n .ne y x = relB n .ne x y := by
  simp only [relB, bne]
  rw [relB_eq_comm' x y]

theorem relV_eq_comm {t : IntType} (x y : BitVec t.width) : relV t .eq y x = relV t .eq x y := by
  cases t
  · exact congrArg Silmaril.Wasm.Numerics.bool32 (relB_eq_comm (n := 32) x y)
  · exact congrArg Silmaril.Wasm.Numerics.bool32 (relB_eq_comm (n := 64) x y)

theorem relV_ne_comm {t : IntType} (x y : BitVec t.width) : relV t .ne y x = relV t .ne x y := by
  cases t
  · exact congrArg Silmaril.Wasm.Numerics.bool32 (relB_ne_comm (n := 32) x y)
  · exact congrArg Silmaril.Wasm.Numerics.bool32 (relB_ne_comm (n := 64) x y)

theorem den_relTN (ρ ξ : Env) {t : IntType} (op : IntRelOp) (a b : Tm t) :
    (relTN op a b).den F ρ ξ = relV t op (a.den F ρ ξ) (b.den F ρ ξ) := by
  unfold relTN
  split
  · rename_i s; cases t <;> cases s <;> rfl
  · rename_i s; cases t <;> cases s <;> rfl
  · split
    · exact relV_eq_comm _ _
    · rfl
  · split
    · exact relV_ne_comm _ _
    · rfl
  · rfl

theorem iteT_self {t : IntType} (c : Bool) (x : BitVec t.width) : iteT t c x x = x := by
  cases t <;> cases c <;> rfl

theorem den_iteN (ρ ξ : Env) {t : IntType} (c : Tm .i32) (a b : Tm t) :
    (iteN c a b).den F ρ ξ = iteT t (nz32 (c.den F ρ ξ)) (a.den F ρ ξ) (b.den F ρ ξ) := by
  unfold iteN
  split
  · rename_i h
    subst h
    exact (iteT_self _ _).symm
  · rfl

/-! ## Linear arithmetic -/

/-- The meaning of the monomials of a linear form. -/
def linTerms (F : Fns) (ρ ξ : Env) {t : IntType} : List (Nat × Tm t) → BitVec t.width
  | [] => 0
  | (c, a) :: r => BitVec.ofNat t.width c * a.den F ρ ξ + linTerms F ρ ξ r

/-- The meaning of a linear form. -/
def Lin.den (F : Fns) (ρ ξ : Env) {t : IntType} (x : Lin t) : BitVec t.width :=
  linTerms F ρ ξ x.1 + BitVec.ofNat t.width x.2

theorem litT_eq (t : IntType) (n : Nat) : litT t n = BitVec.ofNat t.width n := by
  cases t <;> rfl

theorem bv_add_left_comm {w : Nat} (x y z : BitVec w) : x + (y + z) = y + (x + z) := by
  rw [← BitVec.add_assoc, BitVec.add_comm x y, BitVec.add_assoc]

theorem bv_add_add_add_comm {w : Nat} (a b c d : BitVec w) : a + b + (c + d) = a + c + (b + d) := by
  rw [BitVec.add_assoc, bv_add_left_comm b c d, ← BitVec.add_assoc]

theorem linTerms_ins (ρ ξ : Env) {t : IntType} (c : Nat) (a : Tm t) :
    ∀ l : List (Nat × Tm t), linTerms F ρ ξ (linIns c a l) =
      BitVec.ofNat t.width c * a.den F ρ ξ + linTerms F ρ ξ l
  | [] => rfl
  | (d, b) :: r => by
    unfold linIns
    split
    · rename_i h
      subst h
      simp only [linTerms, BitVec.ofNat_add, BitVec.add_mul, BitVec.add_assoc]
    · split
      · rfl
      · simp only [linTerms, linTerms_ins ρ ξ c a r, bv_add_left_comm]

theorem linTerms_foldr (ρ ξ : Env) {t : IntType} (l₂ : List (Nat × Tm t)) :
    ∀ l₁ : List (Nat × Tm t), linTerms F ρ ξ (l₁.foldr (fun p acc => linIns p.1 p.2 acc) l₂) =
      linTerms F ρ ξ l₁ + linTerms F ρ ξ l₂
  | [] => by simp [linTerms]
  | (c, a) :: r => by
    simp only [List.foldr_cons, linTerms_ins, linTerms_foldr ρ ξ l₂ r, linTerms, BitVec.add_assoc]

theorem den_linAdd (ρ ξ : Env) {t : IntType} (x y : Lin t) :
    Lin.den F ρ ξ (linAdd x y) = Lin.den F ρ ξ x + Lin.den F ρ ξ y := by
  simp only [Lin.den, linAdd, linTerms_foldr, BitVec.ofNat_add, bv_add_add_add_comm]

theorem linTerms_scale (ρ ξ : Env) {t : IntType} (c : Nat) :
    ∀ l : List (Nat × Tm t), linTerms F ρ ξ (l.map fun p => (c * p.1, p.2)) =
      BitVec.ofNat t.width c * linTerms F ρ ξ l
  | [] => by simp [linTerms]
  | (d, a) :: r => by
    simp only [List.map_cons, linTerms, linTerms_scale ρ ξ c r, BitVec.ofNat_mul, BitVec.mul_add,
      BitVec.mul_assoc]

theorem den_linScale (ρ ξ : Env) {t : IntType} (c : Nat) (x : Lin t) :
    Lin.den F ρ ξ (linScale c x) = BitVec.ofNat t.width c * Lin.den F ρ ξ x := by
  simp only [Lin.den, linScale, linTerms_scale, BitVec.ofNat_mul, BitVec.mul_add]

theorem den_atom (ρ ξ : Env) {t : IntType} (a : Tm t) :
    Lin.den F ρ ξ ([(1, a)], 0) = a.den F ρ ξ := by
  simp [Lin.den, linTerms]

theorem ofNat_allOnes_mul {w : Nat} (y : BitVec w) : BitVec.ofNat w (2 ^ w - 1) * y = -y := by
  have h : BitVec.ofNat w (2 ^ w - 1) = -1#w := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_neg, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rcases w with _ | w
    · simp
    · have h1 : 1 % 2 ^ (w + 1) = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
      have h2 : 0 < 2 ^ (w + 1) := Nat.two_pow_pos _
      rw [h1, Nat.mod_eq_of_lt (by omega)]
  rw [h, BitVec.neg_mul, BitVec.one_mul]

theorem shl_ofNat {w : Nat} (x : BitVec w) (n : Nat) :
    x <<< ((BitVec.ofNat w n).toNat % w) = BitVec.ofNat w (2 ^ (n % 2 ^ w % w)) * x := by
  rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.mul_comm, BitVec.toNat_ofNat]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_twoPow, BitVec.toNat_ofNat]

theorem binT_add {t : IntType} (x y : BitVec t.width) : binT t .add x y = x + y := by
  cases t <;> rfl

theorem binT_sub {t : IntType} (x y : BitVec t.width) : binT t .sub x y = x - y := by
  cases t <;> rfl

theorem binT_mul {t : IntType} (x y : BitVec t.width) : binT t .mul x y = x * y := by
  cases t <;> rfl

theorem binT_shl {t : IntType} (x y : BitVec t.width) :
    binT t .shl x y = x <<< (y.toNat % t.width) := by
  cases t <;> rfl

theorem litOf?_den (ρ ξ : Env) {t : IntType} {b : Tm t} {n : Nat} (h : b.litOf? = some n) :
    b.den F ρ ξ = BitVec.ofNat t.width n := by
  cases b <;> simp [Tm.litOf?] at h
  subst h
  exact litT_eq _ _

theorem den_linBin_mul (ρ ξ : Env) {t : IntType} (a b : Tm t) {la lb : Lin t}
    (ha : Lin.den F ρ ξ la = a.den F ρ ξ) (hb : Lin.den F ρ ξ lb = b.den F ρ ξ) :
    Lin.den F ρ ξ (linBin .mul a b la lb) = binT t .mul (a.den F ρ ξ) (b.den F ρ ξ) := by
  unfold linBin
  cases hB : b.litOf? with
  | some n =>
    simp only
    rw [den_linScale, ha, binT_mul, litOf?_den ρ ξ hB, BitVec.mul_comm]
  | none =>
    cases hA : a.litOf? with
    | some n =>
      simp only
      rw [den_linScale, hb, binT_mul, litOf?_den ρ ξ hA]
    | none => exact den_atom ρ ξ _

theorem den_linBin_shl (ρ ξ : Env) {t : IntType} (a b : Tm t) {la lb : Lin t}
    (ha : Lin.den F ρ ξ la = a.den F ρ ξ) :
    Lin.den F ρ ξ (linBin .shl a b la lb) = binT t .shl (a.den F ρ ξ) (b.den F ρ ξ) := by
  unfold linBin
  cases hB : b.litOf? with
  | some n =>
    simp only
    rw [den_linScale, ha, binT_shl, litOf?_den ρ ξ hB, shl_ofNat]
  | none => exact den_atom ρ ξ _

theorem den_linBin (ρ ξ : Env) {t : IntType} (op : IntBinOp) (a b : Tm t) {la lb : Lin t}
    (ha : Lin.den F ρ ξ la = a.den F ρ ξ) (hb : Lin.den F ρ ξ lb = b.den F ρ ξ) :
    Lin.den F ρ ξ (linBin op a b la lb) = binT t op (a.den F ρ ξ) (b.den F ρ ξ) := by
  cases op
  case add => rw [linBin, den_linAdd, ha, hb, binT_add]
  case sub =>
    rw [linBin, den_linAdd, den_linScale, ha, hb, binT_sub, ofNat_allOnes_mul,
      BitVec.sub_eq_add_neg]
  case mul => exact den_linBin_mul ρ ξ a b ha hb
  case shl => exact den_linBin_shl ρ ξ a b ha
  all_goals exact den_atom ρ ξ _

theorem Tm.den_lin (ρ ξ : Env) : ∀ {t : IntType} (a : Tm t), Lin.den F ρ ξ a.lin = a.den F ρ ξ
  | _, .lit t n => by simp [Tm.lin, Lin.den, linTerms, Tm.den, litT_eq]
  | _, .bin op a b => den_linBin ρ ξ op a b (Tm.den_lin ρ ξ a) (Tm.den_lin ρ ξ b)
  | _, .var .. => den_atom ρ ξ _
  | _, .loc .. => den_atom ρ ξ _
  | _, .un .. => den_atom ρ ξ _
  | _, .rel .. => den_atom ρ ξ _
  | _, .eqz .. => den_atom ρ ξ _
  | _, .ite .. => den_atom ρ ξ _
  | _, .wrap .. => den_atom ρ ξ _
  | _, .ext .. => den_atom ρ ξ _
  | _, .fn .. => den_atom ρ ξ _
  | _, .fn2 .. => den_atom ρ ξ _
  | _, .load .. => den_atom ρ ξ _
  | _, .mfn .. => den_atom ρ ξ _

theorem ofNat_mod_width {w : Nat} (c : Nat) : BitVec.ofNat w (c % 2 ^ w) = BitVec.ofNat w c := by
  apply BitVec.eq_of_toNat_eq
  simp

theorem den_linMono (ρ ξ : Env) {t : IntType} (c : Nat) (a : Tm t) :
    (linMono c a).den F ρ ξ = BitVec.ofNat t.width c * a.den F ρ ξ := by
  unfold linMono
  split
  · rename_i h
    subst h
    simp
  · simp only [Tm.den, binT_mul, litT_eq, BitVec.mul_comm]

theorem ofNat_eq_zero_of_mod {w c : Nat} (h : c % 2 ^ w = 0) : BitVec.ofNat w c = 0#w := by
  rw [← ofNat_mod_width, h]

theorem den_linSum (ρ ξ : Env) {t : IntType} :
    ∀ (acc : Tm t) (r : List (Nat × Tm t)),
      (linSum acc r).den F ρ ξ = acc.den F ρ ξ + linTerms F ρ ξ r
  | acc, [] => by simp [linSum, linTerms]
  | acc, (c, a) :: r => by
    unfold linSum
    split
    · rename_i h
      rw [den_linSum ρ ξ acc r, linTerms, ofNat_eq_zero_of_mod h, BitVec.zero_mul, BitVec.zero_add]
    · rw [den_linSum ρ ξ _ r, linTerms, Tm.den, binT_add, den_linMono, ofNat_mod_width,
        BitVec.add_assoc]

theorem den_linFirst (ρ ξ : Env) {t : IntType} :
    ∀ l : List (Nat × Tm t), (linFirst l = none → linTerms F ρ ξ l = 0) ∧
      ∀ e r, linFirst l = some (e, r) → e.den F ρ ξ + linTerms F ρ ξ r = linTerms F ρ ξ l
  | [] => ⟨fun _ => rfl, fun e r h => by simp [linFirst] at h⟩
  | (c, a) :: r => by
    unfold linFirst
    split
    · rename_i h
      obtain ⟨h₁, h₂⟩ := den_linFirst ρ ξ r
      refine ⟨fun hn => ?_, fun e r' he => ?_⟩
      · rw [linTerms, h₁ hn, ofNat_eq_zero_of_mod h, BitVec.zero_mul, BitVec.zero_add]
      · rw [h₂ e r' he, linTerms, ofNat_eq_zero_of_mod h, BitVec.zero_mul, BitVec.zero_add]
    · refine ⟨fun hn => by simp at hn, fun e r' he => ?_⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [den_linMono, ofNat_mod_width, linTerms]

theorem den_linBuild (ρ ξ : Env) {t : IntType} (x : Lin t) :
    (linBuild x).den F ρ ξ = Lin.den F ρ ξ x := by
  unfold linBuild Lin.den
  obtain ⟨h₁, h₂⟩ := den_linFirst (F := F) ρ ξ x.1
  split
  · rename_i hn
    rw [h₁ hn]
    simp [Tm.den, litT_eq, ofNat_mod_width]
  · rename_i e r he
    split
    · rename_i hk
      rw [den_linSum, h₂ e r he, ofNat_eq_zero_of_mod hk, BitVec.add_zero]
    · rw [Tm.den, binT_add, den_linSum, h₂ e r he, Tm.den, litT_eq, ofNat_mod_width]

theorem den_arithN (ρ ξ : Env) {t : IntType} (op : IntBinOp) (a b : Tm t) :
    (arithN op a b).den F ρ ξ = binT t op (a.den F ρ ξ) (b.den F ρ ξ) := by
  unfold arithN
  split
  · rw [den_linBuild, Tm.den_lin, den_binN]
  · exact den_binN ρ ξ op a b

theorem Tm.den_norm (ρ ξ : Env) : ∀ {t : IntType} (a : Tm t), a.norm.den F ρ ξ = a.den F ρ ξ
  | _, .var t i => rfl
  | _, .loc t j => rfl
  | _, .lit t n => rfl
  | _, .un op a => by simp only [Tm.norm, Tm.den, Tm.den_norm ρ ξ a]
  | _, .bin op a b => by
    simp only [Tm.norm, den_arithN, Tm.den, Tm.den_norm ρ ξ a, Tm.den_norm ρ ξ b]
  | _, .rel op a b => by
    simp only [Tm.norm, den_relTN, Tm.den, Tm.den_norm ρ ξ a, Tm.den_norm ρ ξ b]; rfl
  | _, .eqz a => by simp only [Tm.norm, Tm.den, Tm.den_norm ρ ξ a]; rfl
  | _, .ite c a b => by
    simp only [Tm.norm, den_iteN, Tm.den, Tm.den_norm ρ ξ c, Tm.den_norm ρ ξ a,
      Tm.den_norm ρ ξ b]
  | _, .wrap a => by simp only [Tm.norm, Tm.den, Tm.den_norm ρ ξ a]; rfl
  | _, .ext sx a => by cases sx <;> simp only [Tm.norm, Tm.den, Tm.den_norm ρ ξ a] <;> rfl
  | _, .fn k a => by simp only [Tm.norm, Tm.den, Tm.den_norm ρ ξ a]
  | _, .fn2 k a b => by simp only [Tm.norm, Tm.den, Tm.den_norm ρ ξ a, Tm.den_norm ρ ξ b]
  | _, .load t n sx m a off => by simp only [Tm.norm, Tm.den, Tm.den_norm ρ ξ a]
  | _, .mfn k m a b => by simp only [Tm.norm, Tm.den, Tm.den_norm ρ ξ a, Tm.den_norm ρ ξ b]; rfl

theorem relP_lt_gt {t : IntType} (s : Signedness) (x y : BitVec t.width) :
    relP t (.lt s) y x ↔ relP t (.gt s) x y := by
  cases t <;> cases s <;> exact Iff.rfl

theorem relP_le_ge {t : IntType} (s : Signedness) (x y : BitVec t.width) :
    relP t (.le s) y x ↔ relP t (.ge s) x y := by
  cases t <;> cases s <;> exact Iff.rfl

theorem relP_eq {t : IntType} (x y : BitVec t.width) : relP t .eq x y ↔ x = y := by
  cases t <;> exact Iff.rfl

theorem relP_ne {t : IntType} (x y : BitVec t.width) : relP t .ne x y ↔ x ≠ y := by
  cases t <;> exact Iff.rfl

theorem den_relFN_eq (ρ ξ : Env) {t : IntType} (a b : Tm t) :
    (relFN .eq a b).den F ρ ξ ↔ relP t .eq (a.den F ρ ξ) (b.den F ρ ξ) := by
  simp only [relFN]
  split
  · rename_i h
    subst h
    simp only [Fm.den, relP_eq]
  · split
    · simp only [Fm.den, relP_eq]
      exact eq_comm
    · exact Iff.rfl

theorem den_relFN_ne (ρ ξ : Env) {t : IntType} (a b : Tm t) :
    (relFN .ne a b).den F ρ ξ ↔ relP t .ne (a.den F ρ ξ) (b.den F ρ ξ) := by
  simp only [relFN]
  split
  · rename_i h
    subst h
    simp only [Fm.den, relP_ne, ne_eq, not_true_eq_false]
  · split
    · simp only [Fm.den, relP_ne]
      exact ne_comm
    · exact Iff.rfl

theorem den_relFN (ρ ξ : Env) {t : IntType} (op : IntRelOp) (a b : Tm t) :
    (relFN op a b).den F ρ ξ ↔ relP t op (a.den F ρ ξ) (b.den F ρ ξ) := by
  cases op with
  | eq => exact den_relFN_eq ρ ξ a b
  | ne => exact den_relFN_ne ρ ξ a b
  | gt s => exact relP_lt_gt s _ _
  | ge s => exact relP_le_ge s _ _
  | lt s => exact Iff.rfl
  | le s => exact Iff.rfl

theorem den_notN (ρ ξ : Env) (p : Fm) : (notN p).den F ρ ξ ↔ ¬ p.den F ρ ξ := by
  unfold notN
  split
  · subst p; simp [Fm.den]
  · split
    · subst p; simp [Fm.den]
    · exact Iff.rfl

theorem den_andN (ρ ξ : Env) (p q : Fm) : (andN p q).den F ρ ξ ↔ p.den F ρ ξ ∧ q.den F ρ ξ := by
  unfold andN
  split
  · subst p; simp [Fm.den]
  · split
    · subst q; simp [Fm.den]
    · split
      · rename_i h
        rcases h with rfl | rfl <;> simp [Fm.den]
      · exact Iff.rfl

theorem den_orN (ρ ξ : Env) (p q : Fm) : (orN p q).den F ρ ξ ↔ p.den F ρ ξ ∨ q.den F ρ ξ := by
  unfold orN
  split
  · subst p; simp [Fm.den]
  · split
    · subst q; simp [Fm.den]
    · split
      · rename_i h
        rcases h with rfl | rfl <;> simp [Fm.den]
      · exact Iff.rfl

theorem Fm.den_of_mem_conjs (ρ ξ : Env) :
    ∀ (p : Fm), p.den F ρ ξ → ∀ q ∈ p.conjs, q.den F ρ ξ
  | .and p₁ p₂, h, q, hq => by
    simp only [Fm.conjs, List.mem_append] at hq
    rcases hq with hq | hq
    · exact Fm.den_of_mem_conjs ρ ξ p₁ h.1 q hq
    · exact Fm.den_of_mem_conjs ρ ξ p₂ h.2 q hq
  | .tt, h, q, hq | .ff, h, q, hq | .rel _ _ _, h, q, hq | .nz _, h, q, hq | .not _, h, q, hq
  | .or _ _, h, q, hq | .imp _ _, h, q, hq | .inb _ _ _, h, q, hq | .pr _ _ _, h, q, hq
  | .meq _ _, h, q, hq | .st _ _ _ _ _ _, h, q, hq | .pr2 _ _ _ _, h, q, hq => by
    simp only [Fm.conjs, List.mem_singleton] at hq
    exact hq ▸ h

theorem den_impN (ρ ξ : Env) (p q : Fm) :
    (impN p q).den F ρ ξ ↔ (p.den F ρ ξ → q.den F ρ ξ) := by
  unfold impN
  split
  · rename_i h
    rcases h with rfl | rfl <;> simp [Fm.den]
  · split
    · subst p; simp [Fm.den]
    · split
      · rename_i h
        simp only [Fm.den, true_iff]
        exact fun hp => Fm.den_of_mem_conjs ρ ξ p hp q h
      · exact Iff.rfl

theorem den_meqN (ρ ξ : Env) (m₁ m₂ : MR) : (meqN m₁ m₂).den F ρ ξ ↔ m₁.den ρ ξ = m₂.den ρ ξ := by
  unfold meqN
  split
  · rename_i h; subst h; simp [Fm.den]
  · exact Iff.rfl

theorem Tm.dens32_norm (ρ ξ : Env) (as : List (Tm .i32)) :
    Tm.dens32 F ρ ξ (as.map Tm.norm) = Tm.dens32 F ρ ξ as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, Tm.dens32, Tm.den_norm, ih]

theorem Fm.den_norm (ρ ξ : Env) : ∀ φ : Fm, φ.norm.den F ρ ξ ↔ φ.den F ρ ξ
  | .tt => Iff.rfl
  | .ff => Iff.rfl
  | .rel op a b => by simp only [Fm.norm, den_relFN, Tm.den_norm, Fm.den]
  | .nz a => by simp only [Fm.norm, Fm.den, Tm.den_norm]
  | .not p => by simp only [Fm.norm, den_notN, Fm.den_norm ρ ξ p, Fm.den]
  | .and p q => by simp only [Fm.norm, den_andN, Fm.den_norm ρ ξ p, Fm.den_norm ρ ξ q, Fm.den]
  | .or p q => by simp only [Fm.norm, den_orN, Fm.den_norm ρ ξ p, Fm.den_norm ρ ξ q, Fm.den]
  | .imp p q => by simp only [Fm.norm, den_impN, Fm.den_norm ρ ξ p, Fm.den_norm ρ ξ q, Fm.den]
  | .inb m a n => by simp only [Fm.norm, Fm.den, Tm.den_norm]
  | .pr k m as => by simp only [Fm.norm, Fm.den, Tm.dens32_norm]
  | .pr2 k m₁ m₂ as => by simp only [Fm.norm, Fm.den, Tm.dens32_norm]
  | .meq m₁ m₂ => by simp only [Fm.norm, den_meqN, Fm.den]
  | .st k m n a off v => by simp only [Fm.norm, Fm.den, Tm.den_norm]

theorem valid_norm {φ : Fm} : Valid F φ.norm ↔ Valid F φ :=
  forall_congr' fun ρ => Fm.den_norm ρ ρ φ

/-! ## Renaming -/

/-- The environment `ρ` seen through the renaming `σ`. -/
def Env.comp (ρ : Env) (σ : Ren) : Env where
  e32 i := ρ.e32 (σ.ty .i32 i)
  e64 i := ρ.e64 (σ.ty .i64 i)
  mem k := ρ.mem (σ.mem k)

theorem Env.get_comp (ρ : Env) (σ : Ren) (t : IntType) (i : Nat) :
    (ρ.comp σ).get t i = ρ.get t (σ.ty t i) := by
  cases t <;> rfl

theorem MR.den_rn (ρ ξ : Env) (σ : Ren) : ∀ m : MR, (m.rn σ).den ρ ξ = m.den (ρ.comp σ) (ξ.comp σ)
  | .v k => rfl
  | .cur => by simp [MR.rn, MR.den, Env.comp, Ren.mem]

theorem Tm.den_rn (ρ ξ : Env) (σ : Ren) :
    ∀ {t : IntType} (a : Tm t), (a.rn σ).den F ρ ξ = a.den F (ρ.comp σ) (ξ.comp σ)
  | _, .var t i => by simp only [Tm.rn, Tm.den, Env.get_comp]
  | _, .loc t j => by simp only [Tm.rn, Tm.den, Env.get_comp]
  | _, .lit t n => rfl
  | _, .un op a => by simp only [Tm.rn, Tm.den, Tm.den_rn ρ ξ σ a]
  | _, .bin op a b => by simp only [Tm.rn, Tm.den, Tm.den_rn ρ ξ σ a, Tm.den_rn ρ ξ σ b]
  | _, .rel op a b => by simp only [Tm.rn, Tm.den, Tm.den_rn ρ ξ σ a, Tm.den_rn ρ ξ σ b]; rfl
  | _, .eqz a => by simp only [Tm.rn, Tm.den, Tm.den_rn ρ ξ σ a]; rfl
  | _, .ite c a b => by
    simp only [Tm.rn, Tm.den, Tm.den_rn ρ ξ σ c, Tm.den_rn ρ ξ σ a, Tm.den_rn ρ ξ σ b]
  | _, .wrap a => by simp only [Tm.rn, Tm.den, Tm.den_rn ρ ξ σ a]; rfl
  | _, .ext sx a => by cases sx <;> simp only [Tm.rn, Tm.den, Tm.den_rn ρ ξ σ a] <;> rfl
  | _, .fn k a => by simp only [Tm.rn, Tm.den, Tm.den_rn ρ ξ σ a]
  | _, .fn2 k a b => by simp only [Tm.rn, Tm.den, Tm.den_rn ρ ξ σ a, Tm.den_rn ρ ξ σ b]
  | _, .load t n sx m a off => by simp only [Tm.rn, Tm.den, Tm.den_rn ρ ξ σ a, MR.den_rn ρ ξ σ m]
  | _, .mfn k m a b => by
    simp only [Tm.rn, Tm.den, Tm.den_rn ρ ξ σ a, Tm.den_rn ρ ξ σ b, MR.den_rn ρ ξ σ m]; rfl

theorem Tm.dens32_rn (ρ ξ : Env) (σ : Ren) (as : List (Tm .i32)) :
    Tm.dens32 F ρ ξ (as.map (Tm.rn σ)) = Tm.dens32 F (ρ.comp σ) (ξ.comp σ) as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, Tm.dens32, Tm.den_rn, ih]

theorem Fm.den_rn (ρ ξ : Env) (σ : Ren) :
    ∀ φ : Fm, (φ.rn σ).den F ρ ξ ↔ φ.den F (ρ.comp σ) (ξ.comp σ)
  | .tt => Iff.rfl
  | .ff => Iff.rfl
  | .rel op a b => by simp only [Fm.rn, Fm.den, Tm.den_rn]
  | .nz a => by simp only [Fm.rn, Fm.den, Tm.den_rn]
  | .not p => by simp only [Fm.rn, Fm.den, Fm.den_rn ρ ξ σ p]
  | .and p q => by simp only [Fm.rn, Fm.den, Fm.den_rn ρ ξ σ p, Fm.den_rn ρ ξ σ q]
  | .or p q => by simp only [Fm.rn, Fm.den, Fm.den_rn ρ ξ σ p, Fm.den_rn ρ ξ σ q]
  | .imp p q => by simp only [Fm.rn, Fm.den, Fm.den_rn ρ ξ σ p, Fm.den_rn ρ ξ σ q]
  | .inb m a n => by simp only [Fm.rn, Fm.den, Tm.den_rn, MR.den_rn]
  | .pr k m as => by simp only [Fm.rn, Fm.den, Tm.dens32_rn, MR.den_rn]
  | .pr2 k m₁ m₂ as => by simp only [Fm.rn, Fm.den, Tm.dens32_rn, MR.den_rn]
  | .meq m₁ m₂ => by simp only [Fm.rn, Fm.den, MR.den_rn]
  | .st k m n a off v => by simp only [Fm.rn, Fm.den, Tm.den_rn, MR.den_rn]; rfl

theorem valid_rn {φ : Fm} (σ : Ren) (h : Valid F φ) : Valid F (φ.rn σ) :=
  fun ρ => (Fm.den_rn ρ ρ σ φ).mpr (h (ρ.comp σ))

/-! ## The check -/

theorem valid_of_accepts {conds : List Fm} (hv : ∀ ψ ∈ conds, Valid F ψ) {φ : Fm}
    (h : accepts conds φ = true) : Valid F φ := by
  unfold accepts at h
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  apply valid_norm.mp
  rcases h with h | ⟨ψ, hψ, he⟩
  · rw [h]
    exact fun _ => trivial
  · rw [← he]
    exact valid_rn _ (valid_norm.mpr (hv ψ hψ))

theorem allValid_of_coveredN {l conds : List Fm} (hc : coveredN l conds = true)
    (hv : AllValid F conds) : AllValid F l := by
  rw [allValid_iff] at hv ⊢
  intro φ hφ
  exact valid_of_accepts hv ((List.all_eq_true.mp hc) φ hφ)

end Silmaril.Wasm.Auto2.VCGen
