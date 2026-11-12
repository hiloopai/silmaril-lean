module

public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Machine.Agreement
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.OperationalDenotation

/-! # The small-step machine and the existing typed denotation -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LetIter.Semantics.Machine

open LocallyNameless Isotope.Semantics

variable {κ : Type u} (F : κ → Type u) {ν : Type v} [DecidableEq ν]
    {Φ : Type w} [HasTy Φ (Ty κ)] {σ : Type u}
    (M : InstructionModel (Ty.denote F) Φ (StateT σ SetM))
    (instr : Φ → Value (Sigma F) → σ → Value (Sigma F) → σ → Prop)

/-- Actual machine steps return a typed value and final state exactly when the
existing stateful powerset interpretation contains that outcome. -/
theorem steps_iff_denote (compatible : M.Compatible F instr)
    {Γ : Ctx ν (Ty κ)} {n : Nat} {β : BoundCtx (Ty κ) n}
    {t : Tm ν Φ n} {A : Ty κ} (d : Derivation Φ Γ β t A)
    (γ : Isotope.Semantics.FreeEnv (Ty.denote F) Γ)
    (ρ : Isotope.Semantics.BoundEnv (Ty.denote F) β)
    (free : ν → Value (Sigma F)) (bound : Fin n → Value (Sigma F))
    (hf : FreeEncodes F γ free) (hb : BoundEncodes F ρ bound)
    (s s' : σ) (a : Ty.denote F A) :
    Steps instr free (.eval bound t .halt s) (.ret (encodeValue F A a) .halt s') ↔
      (a, s') ∈ (d.denote (Ty.denote F) M γ ρ s).run :=
  eval_iff_steps.symm.trans
    (eval_encode_iff_denote F M instr compatible d γ ρ free bound hf hb s s' a)

end Silmaril.Isotope.LetIter.Semantics.Machine
