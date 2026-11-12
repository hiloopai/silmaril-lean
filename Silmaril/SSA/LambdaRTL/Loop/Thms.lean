module

public import Silmaril.SSA.LambdaRTL.Loop.Defs
public import Silmaril.SSA.LambdaRTL.Thms
public import Silmaril.Semantics.Elgot.Thms
import Silmaril.Proofs.SSA.LambdaRTL.Loop.Agreement
import Silmaril.Proofs.SSA.LambdaRTL.Loop.Counterexample

/-!
# λRTL with loops and lexical λSSA: checked results

For every monad `M` with a lawful Elgot iteration (`Silmaril.Elgot.LawfulElgotMonad`: fixpoint,
naturality, codiagonal, pure uniformity; only naturality and pure uniformity are used):

* `Loop.Region.evalSSA_congr`: the lexical semantics reads only free variables.
* `Loop.Region.evalRTL_frame`: λRTL with loops writes only registers it assigns
  (bind-congruence form). The loop case is proved by `iter_eq_of_retract`, uniformity on the
  image of a pure retraction of the `(argument, store)` state space.
* `Loop.Region.evalObs_eq_evalSSA`: under `NoClobber` (now also: no loop handler assigns its own
  live-ins), observable λRTL semantics = lexical λSSA semantics.
* `Loop.Region.noClobber_of_isSSA`, `Loop.Region.evalObs_eq_evalSSA_of_isSSA`: dominance-scoped
  SSA with loops has no clobbering, hence agreement.
* `Loop.Region.evalSSA_ofAcyclic`, `Loop.Region.evalRTL_ofAcyclic` (and `fv`, `bound`,
  `NoClobber`, `IsSSA`, `mapOp`): the acyclic stage embeds unchanged; these need no Elgot law.
* `Loop.Counterexample.selfClobber_counterexample`: a loop whose handler assigns its own live-in
  (body clean, so the join-style condition holds) separates the readings in `Part`; the loop
  clause of `NoClobber` cannot be dropped. The acyclic `Counterexample.clobber_counterexample`
  transfers along `ofAcyclic` by `evalSSA_ofAcyclic`/`evalObs_ofAcyclic`.
* `Loop.Region.evalObs_eq_evalSSA_part`: the hypotheses are inhabited — `Part` is a lawful
  Elgot monad (`Silmaril.Elgot.Part`).
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.Loop

open Silmaril.Elgot

universe v w

variable {V L : Type w} {F F' F'' : Type v} {M : Type w → Type w} {α : Type w}

section Syntax

theorem Region.noClobber_of_isSSA [DecidableEq V] {r : Region V L F} {Γ : Finset V}
    (h : r.IsSSA Γ) : r.NoClobber :=
  Silmaril.Proofs.SSA.LambdaRTL.Loop.Region.noClobber_of_isSSA r Γ h

theorem Region.fv_subset_of_isSSA [DecidableEq V] {r : Region V L F} {Γ : Finset V}
    (h : r.IsSSA Γ) : r.fv ⊆ Γ :=
  Silmaril.Proofs.SSA.LambdaRTL.Loop.Region.fv_subset_of_isSSA r Γ h

theorem Region.bound_disjoint_of_isSSA [DecidableEq V] {r : Region V L F} {Γ : Finset V}
    (h : r.IsSSA Γ) : Disjoint r.bound Γ :=
  Silmaril.Proofs.SSA.LambdaRTL.Loop.Region.bound_disjoint_of_isSSA r Γ h

theorem Region.isSSA_mapOp [DecidableEq V] (h : F → F') (r : Region V L F) (Γ : Finset V) :
    (r.mapOp h).IsSSA Γ ↔ r.IsSSA Γ :=
  Silmaril.Proofs.SSA.LambdaRTL.Loop.Region.isSSA_mapOp h r Γ

theorem Region.fv_mapOp [DecidableEq V] (h : F → F') (r : Region V L F) :
    (r.mapOp h).fv = r.fv :=
  Silmaril.Proofs.SSA.LambdaRTL.Loop.Region.fv_mapOp h r

theorem Region.mapOp_id (r : Region V L F) : r.mapOp id = r :=
  Silmaril.Proofs.SSA.LambdaRTL.Loop.Region.mapOp_id r

theorem Region.mapOp_comp (h : F → F') (k : F' → F'') (r : Region V L F) :
    r.mapOp (k ∘ h) = (r.mapOp h).mapOp k :=
  Silmaril.Proofs.SSA.LambdaRTL.Loop.Region.mapOp_comp h k r

theorem Region.mapOp_ofAcyclic (h : F → F') (r : LambdaRTL.Region V L F) :
    (Region.ofAcyclic r).mapOp h = Region.ofAcyclic (r.mapOp h) :=
  Silmaril.Proofs.SSA.LambdaRTL.Loop.Region.mapOp_ofAcyclic h r

theorem Region.fv_ofAcyclic [DecidableEq V] (r : LambdaRTL.Region V L F) :
    (Region.ofAcyclic r).fv = r.fv :=
  Silmaril.Proofs.SSA.LambdaRTL.Loop.Region.fv_ofAcyclic r

theorem Region.bound_ofAcyclic [DecidableEq V] (r : LambdaRTL.Region V L F) :
    (Region.ofAcyclic r).bound = r.bound :=
  Silmaril.Proofs.SSA.LambdaRTL.Loop.Region.bound_ofAcyclic r

theorem Region.noClobber_ofAcyclic [DecidableEq V] (r : LambdaRTL.Region V L F) :
    (Region.ofAcyclic r).NoClobber ↔ r.NoClobber :=
  Silmaril.Proofs.SSA.LambdaRTL.Loop.Region.noClobber_ofAcyclic r

theorem Region.isSSA_ofAcyclic [DecidableEq V] (r : LambdaRTL.Region V L F) (Γ : Finset V) :
    (Region.ofAcyclic r).IsSSA Γ ↔ r.IsSSA Γ :=
  Silmaril.Proofs.SSA.LambdaRTL.Loop.Region.isSSA_ofAcyclic r Γ

end Syntax

section Iterate

variable [Monad M] [Iterate M] [DecidableEq V] [DecidableEq L]

theorem Region.evalSSA_congr (m : Model F M α) (r : Region V L F) {ρ₁ ρ₂ : V → α}
    (h : ∀ y ∈ r.fv, ρ₁ y = ρ₂ y) : r.evalSSA m ρ₁ = r.evalSSA m ρ₂ :=
  Silmaril.Proofs.SSA.LambdaRTL.Loop.Region.evalSSA_congr m r h

theorem Region.evalSSA_mapOp (h : F → F') (m : Model F' M α) (r : Region V L F) (ρ : V → α) :
    (r.mapOp h).evalSSA m ρ = r.evalSSA (m.reduct h) ρ :=
  Silmaril.Proofs.SSA.LambdaRTL.Loop.Region.evalSSA_mapOp h m r ρ

theorem Region.evalRTL_mapOp (h : F → F') (m : Model F' M α) (r : Region V L F) (σ : V → α) :
    (r.mapOp h).evalRTL m σ = r.evalRTL (m.reduct h) σ :=
  Silmaril.Proofs.SSA.LambdaRTL.Loop.Region.evalRTL_mapOp h m r σ

theorem Region.evalObs_mapOp (h : F → F') (m : Model F' M α) (r : Region V L F) (σ : V → α) :
    (r.mapOp h).evalObs m σ = r.evalObs (m.reduct h) σ := by
  simp only [Region.evalObs, Region.evalRTL_mapOp]

/-- The lexical semantics of an embedded acyclic region is the acyclic lexical semantics. -/
theorem Region.evalSSA_ofAcyclic (m : Model F M α) (r : LambdaRTL.Region V L F) (ρ : V → α) :
    (Region.ofAcyclic r).evalSSA m ρ = r.evalSSA m ρ :=
  Silmaril.Proofs.SSA.LambdaRTL.Loop.Region.evalSSA_ofAcyclic m r ρ

/-- The store semantics of an embedded acyclic region is the acyclic store semantics. -/
theorem Region.evalRTL_ofAcyclic (m : Model F M α) (r : LambdaRTL.Region V L F) (σ : V → α) :
    (Region.ofAcyclic r).evalRTL m σ = r.evalRTL m σ :=
  Silmaril.Proofs.SSA.LambdaRTL.Loop.Region.evalRTL_ofAcyclic m r σ

theorem Region.evalObs_ofAcyclic (m : Model F M α) (r : LambdaRTL.Region V L F) (σ : V → α) :
    (Region.ofAcyclic r).evalObs m σ = r.evalObs m σ := by
  simp only [Region.evalObs, LambdaRTL.Region.evalObs, Region.evalRTL_ofAcyclic]

variable [LawfulMonad M] [LawfulElgotMonad M]

/-- **Uniformity on the image of a pure retraction** (a consequence of pure uniformity). -/
theorem iter_eq_of_retract {A B C : Type w} (f : A → M (B ⊕ A)) (g : C → M (B ⊕ C))
    (h : A → A) (k : A → C)
    (hf : ∀ a, (f (h a) >>= fun s => pure (Sum.map id h s)) = f (h a))
    (hfg : ∀ a, (f (h a) >>= fun s => pure (Sum.map id k s)) = g (k a)) (a : A) :
    iter f (h a) = iter g (k a) :=
  Silmaril.Proofs.SSA.LambdaRTL.Loop.iter_eq_of_retract f g h k hf hfg a

/-- **Frame lemma** with loops: two continuations that agree on every outcome whose store
agrees with the initial store outside `r.bound` give equal results. -/
theorem Region.evalRTL_frame (m : Model F M α) {β : Type w} (r : Region V L F) (σ : V → α)
    (f g : L × α × (V → α) → M β)
    (h : ∀ l a σ', (∀ y, y ∉ r.bound → σ' y = σ y) → f (l, a, σ') = g (l, a, σ')) :
    (r.evalRTL m σ >>= f) = (r.evalRTL m σ >>= g) :=
  Silmaril.Proofs.SSA.LambdaRTL.Loop.Region.evalRTL_frame m r σ f g h

/-- **Agreement with loops.** If no join point's and no loop's handler live-ins are clobbered,
the observable λRTL (overwriting store, jump-site store carried around the loop) semantics
equals the lexical λSSA semantics, in every lawful Elgot monad. -/
theorem Region.evalObs_eq_evalSSA (m : Model F M α) {r : Region V L F} (h : r.NoClobber)
    (σ : V → α) : r.evalObs m σ = r.evalSSA m σ :=
  Silmaril.Proofs.SSA.LambdaRTL.Loop.Region.evalObs_eq_evalSSA m r h σ

/-- **Agreement on SSA with loops.** -/
theorem Region.evalObs_eq_evalSSA_of_isSSA (m : Model F M α) {r : Region V L F}
    {Γ : Finset V} (h : r.IsSSA Γ) (σ : V → α) : r.evalObs m σ = r.evalSSA m σ :=
  Region.evalObs_eq_evalSSA m (Region.noClobber_of_isSSA h) σ

end Iterate

/-- **Instance check.** The agreement theorem applies to `Part`, a lawful Elgot monad
(`Silmaril.Elgot.Part`): partial, possibly divergent loops. -/
theorem Region.evalObs_eq_evalSSA_part {V L F α : Type} [DecidableEq V] [DecidableEq L]
    (m : Model F Part α) {r : Region V L F} (h : r.NoClobber) (σ : V → α) :
    r.evalObs m σ = r.evalSSA m σ :=
  Region.evalObs_eq_evalSSA m h σ

end Silmaril.SSA.LambdaRTL.Loop

namespace Silmaril.SSA.LambdaRTL.Loop.Counterexample

open Silmaril.Proofs.SSA.LambdaRTL.Loop.Counterexample in
/-- **The loop clause of `NoClobber` is needed.** There is a loop whose body assigns nothing
(so the join-style condition holds) but whose handler assigns its own live-in, on which the
overwriting and the lexical readings differ, in the lawful Elgot monad `Part`. -/
theorem selfClobber_counterexample :
    ∃ (r : Region Bool Bool Empty) (ℓ x : Bool) (t : Region Bool Bool Empty)
      (m : Model Empty Part Bool) (σ : Bool → Bool),
      Disjoint (t.fv.erase x) r.bound ∧ ¬ (Region.loop r ℓ x t).NoClobber ∧
      (Region.loop r ℓ x t).evalObs m σ ≠ (Region.loop r ℓ x t).evalSSA m σ :=
  ⟨_, _, _, _, model, σ₀, joinCondition, not_noClobber, evalObs_ne_evalSSA⟩

end Silmaril.SSA.LambdaRTL.Loop.Counterexample
