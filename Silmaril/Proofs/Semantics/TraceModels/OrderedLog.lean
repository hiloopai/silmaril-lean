module

public import Silmaril.Semantics.TraceModels.Defs
import Batteries.Tactic.Alias

/-!
# Ordered accumulation of logs: proofs

Proofs for `Silmaril.Semantics.TraceModels.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot

universe u v

namespace ContinuousLog

variable {W : Type u} [Monoid W] [CompleteLattice W] [ContinuousLog W]

private theorem one_le (w : W) : 1 ≤ w := by rw [one_eq_bot]; exact bot_le
alias _root_.Silmaril.Proofs.Semantics.Elgot.ContinuousLog.one_le := Silmaril.Elgot.ContinuousLog.one_le

private theorem mul_iSup {ι : Type v} [Nonempty ι] (w : W) (f : ι → W) :
    w * (⨆ i, f i) = ⨆ i, w * f i := by
  simpa only [← Set.range_comp, sSup_range, Function.comp_def] using
    mul_sSup w (Set.range f) (Set.range_nonempty f)
alias _root_.Silmaril.Proofs.Semantics.Elgot.ContinuousLog.mul_iSup := Silmaril.Elgot.ContinuousLog.mul_iSup

private theorem le_mul_right (a b : W) : a ≤ a * b := by
  simpa only [mul_one] using mul_mono (le_refl a) (one_le b)
alias _root_.Silmaril.Proofs.Semantics.Elgot.ContinuousLog.le_mul_right := Silmaril.Elgot.ContinuousLog.le_mul_right

end ContinuousLog

namespace ContinuousLog

variable {W : Type u} [Monoid W]

@[simp] private theorem prefixProd_zero (ws : ℕ → W) : prefixProd ws 0 = 1 := rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.ContinuousLog.prefixProd_zero := Silmaril.Elgot.ContinuousLog.prefixProd_zero

@[simp] private theorem prefixProd_succ (ws : ℕ → W) (n : ℕ) :
    prefixProd ws (n + 1) = prefixProd ws n * ws n := rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.ContinuousLog.prefixProd_succ := Silmaril.Elgot.ContinuousLog.prefixProd_succ

private theorem prefixProd_add (ws : ℕ → W) (n k : ℕ) :
    prefixProd ws (n + k) = prefixProd ws n * prefixProd (fun i => ws (n + i)) k := by
  induction k with
  | zero => simp
  | succ k ih => simp only [Nat.add_succ, prefixProd_succ, ih, mul_assoc]
alias _root_.Silmaril.Proofs.Semantics.Elgot.ContinuousLog.prefixProd_add := Silmaril.Elgot.ContinuousLog.prefixProd_add

private theorem prefixProd_blocks (ws : ℕ → W) (cuts : ℕ → ℕ)
    (hzero : cuts 0 = 0) (hmono : Monotone cuts) (n : ℕ) :
    prefixProd (blocks ws cuts) n = prefixProd ws (cuts n) := by
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
      rw [prefixProd_succ, ih, blocks, ← prefixProd_add]
      rw [Nat.add_sub_of_le (hmono (Nat.le_succ n))]
alias _root_.Silmaril.Proofs.Semantics.Elgot.ContinuousLog.prefixProd_blocks := Silmaril.Elgot.ContinuousLog.prefixProd_blocks

variable [CompleteLattice W]

private theorem prefixProd_le_omegaProduct (ws : ℕ → W) (n : ℕ) :
    prefixProd ws n ≤ omegaProduct ws := le_iSup _ n
alias _root_.Silmaril.Proofs.Semantics.Elgot.ContinuousLog.prefixProd_le_omegaProduct := Silmaril.Elgot.ContinuousLog.prefixProd_le_omegaProduct

variable [ContinuousLog W]

private theorem prefixProd_monotone (ws : ℕ → W) : Monotone (prefixProd ws) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_mul_right _ _
alias _root_.Silmaril.Proofs.Semantics.Elgot.ContinuousLog.prefixProd_monotone := Silmaril.Elgot.ContinuousLog.prefixProd_monotone

private theorem prefixProd_mono {ws vs : ℕ → W} (h : ∀ n, ws n ≤ vs n) (n : ℕ) :
    prefixProd ws n ≤ prefixProd vs n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact mul_mono ih (h n)
alias _root_.Silmaril.Proofs.Semantics.Elgot.ContinuousLog.prefixProd_mono := Silmaril.Elgot.ContinuousLog.prefixProd_mono

private theorem omegaProduct_eq_iSup_cofinal (ws : ℕ → W) (cuts : ℕ → ℕ)
    (hcofinal : ∀ n, ∃ k, n ≤ cuts k) :
    omegaProduct ws = ⨆ k, prefixProd ws (cuts k) := by
  apply le_antisymm
  · apply iSup_le
    intro n
    obtain ⟨k, hk⟩ := hcofinal n
    exact le_iSup_of_le k (prefixProd_monotone ws hk)
  · exact iSup_le fun k => prefixProd_le_omegaProduct ws (cuts k)
alias _root_.Silmaril.Proofs.Semantics.Elgot.ContinuousLog.omegaProduct_eq_iSup_cofinal := Silmaril.Elgot.ContinuousLog.omegaProduct_eq_iSup_cofinal

private theorem omegaProduct_split (ws : ℕ → W) (n : ℕ) :
    omegaProduct ws = prefixProd ws n * omegaProduct (fun i => ws (n + i)) := by
  simp only [omegaProduct, mul_iSup]
  simp_rw [← prefixProd_add]
  exact omegaProduct_eq_iSup_cofinal ws (n + ·) fun k => ⟨k, Nat.le_add_left k n⟩
alias _root_.Silmaril.Proofs.Semantics.Elgot.ContinuousLog.omegaProduct_split := Silmaril.Elgot.ContinuousLog.omegaProduct_split

private theorem omegaProduct_regroup (ws : ℕ → W) (cuts : ℕ → ℕ)
    (hzero : cuts 0 = 0) (hmono : Monotone cuts)
    (hcofinal : ∀ n, ∃ k, n ≤ cuts k) :
    omegaProduct (blocks ws cuts) = omegaProduct ws := by
  unfold omegaProduct
  simp_rw [prefixProd_blocks ws cuts hzero hmono]
  exact (omegaProduct_eq_iSup_cofinal ws cuts hcofinal).symm
alias _root_.Silmaril.Proofs.Semantics.Elgot.ContinuousLog.omegaProduct_regroup := Silmaril.Elgot.ContinuousLog.omegaProduct_regroup

end ContinuousLog

end Silmaril.Elgot
