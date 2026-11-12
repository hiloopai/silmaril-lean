module

public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.OperationalDenotation
public import Silmaril.Raw.SSA.Isotope.Morphism.CaseIter.Operational
public import Silmaril.Raw.SSA.Isotope.Morphism.CaseIter.Monadic

/-!
# Operational and denotational agreement for let-case

Independent let-case evaluation and its existing typed monadic interpretation
agree through the already proved operational and denotational inclusion laws.
This theorem compares successful outcomes and complete threaded state; it does
not infer divergence from the absence of a powerset outcome.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LetCase.Semantics

open LocallyNameless Isotope.Semantics

variable {κ : Type u} (F : κ → Type u) {ν : Type v} [DecidableEq ν]
    {Φ : Type w} [HasTy Φ (Ty κ)] {σ : Type u}
    (M : InstructionModel (Ty.denote F) Φ (StateT σ SetM))
    (instr : Φ → Value (Sigma F) → σ → Value (Sigma F) → σ → Prop)
    (compatible : M.Compatible F instr)

include compatible

/-- Exact finite outcome agreement, with no primitive determinism or totality premise. -/
theorem eval_iff_denote {Γ : Ctx ν (Ty κ)} {n : Nat} {β : BoundCtx (Ty κ) n}
    {t : Tm ν Φ n} {A : Ty κ} (d : Derivation Φ Γ β t A)
    (γ : Isotope.Semantics.FreeEnv (Ty.denote F) Γ)
    (ρ : Isotope.Semantics.BoundEnv (Ty.denote F) β)
    (free : ν → Value (Sigma F)) (bound : Fin n → Value (Sigma F))
    (hf : LetIter.Semantics.FreeEncodes F γ free) (hb : LetIter.Semantics.BoundEncodes F ρ bound)
    (s : σ) (value : Value (Sigma F)) (s' : σ) :
    Eval instr free bound t s value s' ↔
      ∃ a, value = encodeValue F A a ∧ (a, s') ∈ (d.denote (Ty.denote F) M γ ρ s).run := by
  rw [← Morphism.CaseIter.embed_eval_iff]
  simpa only [Morphism.CaseIter.denote_derivation] using
    LetIter.Semantics.eval_iff_denote F M instr compatible (Morphism.CaseIter.derivation d)
      γ ρ free bound hf hb s value s'

/-- A particular typed output is obtained exactly when its denotation contains it. -/
theorem eval_encode_iff_denote {Γ : Ctx ν (Ty κ)} {n : Nat} {β : BoundCtx (Ty κ) n}
    {t : Tm ν Φ n} {A : Ty κ} (d : Derivation Φ Γ β t A)
    (γ : Isotope.Semantics.FreeEnv (Ty.denote F) Γ)
    (ρ : Isotope.Semantics.BoundEnv (Ty.denote F) β)
    (free : ν → Value (Sigma F)) (bound : Fin n → Value (Sigma F))
    (hf : LetIter.Semantics.FreeEncodes F γ free) (hb : LetIter.Semantics.BoundEncodes F ρ bound)
    (s s' : σ) (a : Ty.denote F A) :
    Eval instr free bound t s (encodeValue F A a) s' ↔
      (a, s') ∈ (d.denote (Ty.denote F) M γ ρ s).run := by
  rw [← Morphism.CaseIter.embed_eval_iff]
  simpa only [Morphism.CaseIter.denote_derivation] using
    LetIter.Semantics.eval_encode_iff_denote F M instr compatible (Morphism.CaseIter.derivation d)
      γ ρ free bound hf hb s s' a

end Silmaril.Isotope.LetCase.Semantics
