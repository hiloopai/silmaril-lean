module

public import Silmaril.SSA.LambdaRTL.CFG.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Correctness

/-!
# Flat three-address CFGs for acyclic λRTL: checked results

* `run_flatten`: the flattening of a dominator-tree region runs exactly as the region under the
  λRTL store semantics, with free labels embedded as exits.
* `run_eq_toRegion`: every forward CFG runs as its reading-back region `CFG.toRegion`.
* `run_relabel`: running is invariant under block relabellings injective on the block labels.
* `run_of_validate`: **validator soundness** — if `validate exit r g = true` then `g` runs as
  `r` (exits renamed by `exit`) in every model and every lawful monad.

Scope: acyclic (forward-only jumps; a backward jump is an exit). The validator is syntactic
(flattening up to relabelling), so it is complete only for CFGs of that shape.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG

universe v w

variable {V L K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w} [Monad M]
  [LawfulMonad M] [DecidableEq V] [DecidableEq L] [DecidableEq K]

theorem run_flatten (m : Model F M α) (r : Region V L F) (σ : V → α) :
    (flatten r).run m σ = (fun e => (Sum.inl e.1, e.2)) <$> r.evalRTL m σ :=
  Silmaril.Proofs.SSA.LambdaRTL.CFG.run_flatten m r σ

theorem run_eq_toRegion (m : Model F M α) (g : CFG V K F) (σ : V → α) :
    g.run m σ = g.toRegion.evalRTL m σ :=
  Silmaril.Proofs.SSA.LambdaRTL.CFG.run_eq_toRegion m g σ

theorem run_relabel {K' : Type w} [DecidableEq K'] (m : Model F M α) (π : K → K')
    (g : CFG V K F) (hinj : ∀ a ∈ g.labels, ∀ b ∈ g.labels, π a = π b → a = b) (σ : V → α) :
    (g.relabel π).run m σ = (fun e => (π e.1, e.2)) <$> g.run m σ :=
  Silmaril.Proofs.SSA.LambdaRTL.CFG.run_relabel m π g hinj σ

theorem run_of_validate [DecidableEq F] [Inhabited K] (m : Model F M α) (exit : L → K)
    (r : Region V L F) (g : CFG V K F) (h : validate exit r g = true) (σ : V → α) :
    g.run m σ = (fun e => (exit e.1, e.2)) <$> r.evalRTL m σ :=
  Silmaril.Proofs.SSA.LambdaRTL.CFG.run_of_validate m exit r g h σ

end Silmaril.SSA.LambdaRTL.CFG
