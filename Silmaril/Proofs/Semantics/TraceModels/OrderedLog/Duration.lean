module

public import Silmaril.Semantics.TraceModels.Defs
public import Silmaril.Proofs.Semantics.TraceModels.OrderedLog
import all Silmaril.Proofs.Semantics.TraceModels.OrderedLog
import Batteries.Tactic.Alias

/-!
# Extended natural durations: proofs

Proofs for `Silmaril.Semantics.TraceModels.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot

namespace Duration

@[simp] private theorem toAdd_iSup {ι : Sort*} (f : ι → Duration) :
    (⨆ i, f i).toAdd = ⨆ i, (f i).toAdd := toENat.map_iSup f
alias _root_.Silmaril.Proofs.Semantics.Elgot.Duration.toAdd_iSup := Silmaril.Elgot.Duration.toAdd_iSup

private theorem toAdd_sSup (s : Set Duration) :
    (sSup s).toAdd = ⨆ a ∈ s, a.toAdd := toENat.map_sSup s
alias _root_.Silmaril.Proofs.Semantics.Elgot.Duration.toAdd_sSup := Silmaril.Elgot.Duration.toAdd_sSup

instance _root_.Silmaril.Proofs.Semantics.Elgot.Duration.instContinuousLog : ContinuousLog Duration where
  one_eq_bot := rfl
  mul_mono hab hcd := add_le_add (α := ℕ∞) hab hcd
  mul_sSup w s hs := by
    apply Multiplicative.toAdd.injective
    simp only [sSup_image, toAdd_mul, toAdd_sSup, toAdd_iSup]
    exact ENat.add_biSup hs _
  sSup_mul s hs w := by
    apply Multiplicative.toAdd.injective
    simp only [sSup_image, toAdd_mul, toAdd_sSup, toAdd_iSup]
    exact ENat.biSup_add hs _

@[simp] private theorem prefixProd_tick (n : ℕ) :
    ContinuousLog.prefixProd (fun _ => tick) n = Multiplicative.ofAdd (n : ℕ∞) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [ContinuousLog.prefixProd_succ, ih]
      change Multiplicative.ofAdd ((n : ℕ∞) + 1) = Multiplicative.ofAdd ((n + 1 : ℕ) : ℕ∞)
      rw [ENat.natCast_add, ENat.natCast_one]
alias _root_.Silmaril.Proofs.Semantics.Elgot.Duration.prefixProd_tick := Silmaril.Elgot.Duration.prefixProd_tick

private theorem omegaProduct_tick : ContinuousLog.omegaProduct (fun _ => tick) = ⊤ := by
  unfold ContinuousLog.omegaProduct
  simp only [prefixProd_tick]
  exact ENat.iSup_natCast
alias _root_.Silmaril.Proofs.Semantics.Elgot.Duration.omegaProduct_tick := Silmaril.Elgot.Duration.omegaProduct_tick

end Duration

end Silmaril.Elgot
