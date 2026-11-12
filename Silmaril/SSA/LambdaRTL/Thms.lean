module

public import Silmaril.SSA.LambdaRTL.Defs
import Silmaril.Proofs.SSA.LambdaRTL.Agreement
import Silmaril.Proofs.SSA.LambdaRTL.Counterexample

/-!
# λRTL and lexical λSSA (acyclic stage): checked results

* `evalSSA_congr`: the lexical semantics reads only free variables.
* `evalRTL_frame`: λRTL writes only registers it assigns (stated by bind-congruence, so it holds
  in every lawful monad without a support modality).
* `evalObs_eq_evalSSA`: under `NoClobber`, observable λRTL semantics = lexical λSSA semantics.
* `noClobber_of_isSSA`, `evalObs_eq_evalSSA_of_isSSA`: dominance-scoped SSA has no clobbering,
  so on SSA programs the overwriting reading and the lexical reading agree.
* `clobber_counterexample`: without `NoClobber` they differ, so the identity "read λRTL as
  λSSA" is **not** a semantics-preserving translation in general.
* `evalSSA_mapOp`, `evalRTL_mapOp`: both semantics commute with instruction renaming (the
  satisfaction condition of the institutions in `LambdaRTL.Institution`).
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL

universe v w

variable {V L : Type w} {F F' F'' : Type v} {M : Type w → Type w} {α : Type w}

section Syntax

theorem Region.noClobber_of_isSSA [DecidableEq V] {r : Region V L F} {Γ : Finset V}
    (h : r.IsSSA Γ) : r.NoClobber :=
  Silmaril.Proofs.SSA.LambdaRTL.Region.noClobber_of_isSSA r Γ h

theorem Region.fv_subset_of_isSSA [DecidableEq V] {r : Region V L F} {Γ : Finset V}
    (h : r.IsSSA Γ) : r.fv ⊆ Γ :=
  Silmaril.Proofs.SSA.LambdaRTL.Region.fv_subset_of_isSSA r Γ h

theorem Region.bound_disjoint_of_isSSA [DecidableEq V] {r : Region V L F} {Γ : Finset V}
    (h : r.IsSSA Γ) : Disjoint r.bound Γ :=
  Silmaril.Proofs.SSA.LambdaRTL.Region.bound_disjoint_of_isSSA r Γ h

theorem Region.isSSA_mapOp [DecidableEq V] (h : F → F') (r : Region V L F) (Γ : Finset V) :
    (r.mapOp h).IsSSA Γ ↔ r.IsSSA Γ :=
  Silmaril.Proofs.SSA.LambdaRTL.Region.isSSA_mapOp h r Γ

theorem Region.fv_mapOp [DecidableEq V] (h : F → F') (r : Region V L F) :
    (r.mapOp h).fv = r.fv :=
  Silmaril.Proofs.SSA.LambdaRTL.Region.fv_mapOp h r

theorem Region.mapOp_id (r : Region V L F) : r.mapOp id = r :=
  Silmaril.Proofs.SSA.LambdaRTL.Region.mapOp_id r

theorem Region.mapOp_comp (h : F → F') (k : F' → F'') (r : Region V L F) :
    r.mapOp (k ∘ h) = (r.mapOp h).mapOp k :=
  Silmaril.Proofs.SSA.LambdaRTL.Region.mapOp_comp h k r

end Syntax

variable [Monad M] [DecidableEq V] [DecidableEq L]

theorem Region.evalSSA_congr (m : Model F M α) (r : Region V L F) {ρ₁ ρ₂ : V → α}
    (h : ∀ y ∈ r.fv, ρ₁ y = ρ₂ y) : r.evalSSA m ρ₁ = r.evalSSA m ρ₂ :=
  Silmaril.Proofs.SSA.LambdaRTL.Region.evalSSA_congr m r h

theorem Region.evalSSA_mapOp (h : F → F') (m : Model F' M α) (r : Region V L F) (ρ : V → α) :
    (r.mapOp h).evalSSA m ρ = r.evalSSA (m.reduct h) ρ :=
  Silmaril.Proofs.SSA.LambdaRTL.Region.evalSSA_mapOp h m r ρ

theorem Region.evalRTL_mapOp (h : F → F') (m : Model F' M α) (r : Region V L F) (σ : V → α) :
    (r.mapOp h).evalRTL m σ = r.evalRTL (m.reduct h) σ :=
  Silmaril.Proofs.SSA.LambdaRTL.Region.evalRTL_mapOp h m r σ

theorem Region.evalObs_mapOp (h : F → F') (m : Model F' M α) (r : Region V L F) (σ : V → α) :
    (r.mapOp h).evalObs m σ = r.evalObs (m.reduct h) σ := by
  simp only [Region.evalObs, Region.evalRTL_mapOp]

variable [LawfulMonad M]

theorem Region.evalRTL_frame (m : Model F M α) {β : Type w} (r : Region V L F) (σ : V → α)
    (f g : L × α × (V → α) → M β)
    (h : ∀ l a σ', (∀ y, y ∉ r.bound → σ' y = σ y) → f (l, a, σ') = g (l, a, σ')) :
    (r.evalRTL m σ >>= f) = (r.evalRTL m σ >>= g) :=
  Silmaril.Proofs.SSA.LambdaRTL.Region.evalRTL_frame m r σ f g h

/-- **Agreement.** If no join point's live-ins are clobbered, the observable λRTL (overwriting
store) semantics equals the lexical λSSA semantics. -/
theorem Region.evalObs_eq_evalSSA (m : Model F M α) {r : Region V L F} (h : r.NoClobber)
    (σ : V → α) : r.evalObs m σ = r.evalSSA m σ :=
  Silmaril.Proofs.SSA.LambdaRTL.Region.evalObs_eq_evalSSA m r h σ

/-- **Agreement on SSA.** On dominance-scoped SSA programs, reading binders as register
overwrites does not change the observable semantics. -/
theorem Region.evalObs_eq_evalSSA_of_isSSA (m : Model F M α) {r : Region V L F}
    {Γ : Finset V} (h : r.IsSSA Γ) (σ : V → α) : r.evalObs m σ = r.evalSSA m σ :=
  Region.evalObs_eq_evalSSA m (Region.noClobber_of_isSSA h) σ

end Silmaril.SSA.LambdaRTL

namespace Silmaril.SSA.LambdaRTL.Counterexample

open Silmaril.Proofs.SSA.LambdaRTL.Counterexample in
/-- **No naive equivalence.** There is a λRTL program (necessarily violating `NoClobber`) on
which the overwriting and the lexical readings differ. -/
theorem clobber_counterexample :
    ∃ (r : Region Bool Bool Empty) (m : Model Empty Id Bool) (σ : Bool → Bool),
      ¬ r.NoClobber ∧ r.evalObs m σ ≠ r.evalSSA m σ :=
  ⟨clobber, model, σ₀, not_noClobber, evalObs_ne_evalSSA⟩

end Silmaril.SSA.LambdaRTL.Counterexample
