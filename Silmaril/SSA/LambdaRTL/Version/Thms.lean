module

public import Silmaril.SSA.LambdaRTL.Version.Defs
public import Silmaril.SSA.LambdaRTL.Thms
import Silmaril.Proofs.SSA.LambdaRTL.Version

/-!
# Versioning λRTL into λSSA: checked results

* `Version.version_isSSA`, `Version.versionTop_isSSA`: the translation of *any* acyclic λRTL
  region is dominance-scoped SSA (in `initCtx r`, version `0` of each free variable).
* `Version.version_evalSSA`: the invariant — the lexical semantics of the translation is the
  store semantics of the source, with jumps to in-scope join labels carrying packed live-ins.
  Assumes `Model.PairLawful`.
* `Version.versionTop_evalSSA`: `(versionTop r).evalSSA m ρ = r.evalObs m σ` whenever
  `ρ (y, 0) = σ y` for all `y`.
* `Version.versionTop_evalObs`: the same for the λRTL reading of the translation (via the
  agreement theorem on SSA programs).

Not claimed: that versioning an SSA program gives an α-equivalent program, or any round trip.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.Version

universe v w

variable {V L : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}
variable [DecidableEq V] [DecidableEq L]

theorem version_isSSA (r : Region V L F) (lenv : L → Option (List V)) (live : List V)
    (cur : V → ℕ) (d : ℕ) (Γ : Finset (V × ℕ))
    (hl : ∀ ℓ ys, lenv ℓ = some ys → ∀ y ∈ ys, y ∈ live) (hd : ∀ p ∈ Γ, p.2 ≤ d)
    (hΓ : ∀ y, y ∈ r.fvList ∨ y ∈ live → (y, cur y) ∈ Γ) :
    (version lenv live cur d r).IsSSA Γ :=
  Silmaril.Proofs.SSA.LambdaRTL.Version.version_isSSA r lenv live cur d Γ hl hd hΓ

theorem versionTop_isSSA (r : Region V L F) : (versionTop r).IsSSA (initCtx r) :=
  version_isSSA r _ [] _ 0 _ (fun _ _ h => by cases h)
    (fun p hp => by
      simp only [initCtx, List.mem_toFinset, List.mem_map] at hp
      obtain ⟨_, _, rfl⟩ := hp
      exact le_refl 0)
    (fun y hy => by
      rcases hy with hy | hy
      · simp only [initCtx, List.mem_toFinset, List.mem_map]
        exact ⟨y, hy, rfl⟩
      · cases hy)

/-- `versionTop r` is SSA in any context of version-`0` names containing `initCtx r`. -/
theorem versionTop_isSSA_of (r : Region V L F) (Γ : Finset (V × ℕ)) (hd : ∀ p ∈ Γ, p.2 = 0)
    (hΓ : ∀ y ∈ r.fvList, (y, 0) ∈ Γ) : (versionTop r).IsSSA Γ :=
  version_isSSA r _ [] _ 0 _ (fun _ _ h => by cases h) (fun p hp => (hd p hp).le)
    (fun y hy => by
      rcases hy with hy | hy
      · exact hΓ y hy
      · cases hy)

omit [DecidableEq L] in
theorem fvList_mapOp {F' : Type v} (h : F → F') (r : Region V L F) :
    (r.mapOp h).fvList = r.fvList :=
  Silmaril.Proofs.SSA.LambdaRTL.Version.Region.fvList_mapOp h r

omit [DecidableEq L] in
theorem initCtx_mapOp {F' : Type v} (h : F → F') (r : Region V L F) :
    initCtx (r.mapOp h) = initCtx r := by
  simp only [initCtx, fvList_mapOp]

theorem version_mapOp {F' : Type v} (h : F → F') (r : Region V L F) (lenv : L → Option (List V))
    (live : List V) (cur : V → ℕ) (d : ℕ) :
    version lenv live cur d (r.mapOp h) = (version lenv live cur d r).mapOp h :=
  Silmaril.Proofs.SSA.LambdaRTL.Version.version_mapOp h r lenv live cur d

theorem versionTop_mapOp {F' : Type v} (h : F → F') (r : Region V L F) :
    versionTop (r.mapOp h) = (versionTop r).mapOp h :=
  version_mapOp h r _ _ _ _

variable [Monad M] [LawfulMonad M]

theorem version_evalSSA (m : Model F M α) (hm : m.PairLawful) (r : Region V L F)
    (lenv : L → Option (List V)) (live : List V) (cur : V → ℕ) (d : ℕ) (σ : V → α)
    (ρ : V × ℕ → α) (hl : ∀ ℓ ys, lenv ℓ = some ys → ∀ y ∈ ys, y ∈ live)
    (hrel : ∀ y, y ∈ r.fvList ∨ y ∈ live → ρ (y, cur y) = σ y) :
    (version lenv live cur d r).evalSSA m ρ = r.evalRTL m σ >>= fun e => pure (enc m lenv e) :=
  Silmaril.Proofs.SSA.LambdaRTL.Version.version_evalSSA m hm r lenv live cur d σ ρ hl hrel

/-- **Versioning is sound.** The lexical λSSA semantics of the versioned program is the
observable λRTL semantics of the source, for every pair-lawful model and initial store. -/
theorem versionTop_evalSSA (m : Model F M α) (hm : m.PairLawful) (r : Region V L F)
    (σ : V → α) (ρ : V × ℕ → α) (h : ∀ y, ρ (y, 0) = σ y) :
    (versionTop r).evalSSA m ρ = r.evalObs m σ := by
  rw [versionTop, version_evalSSA m hm r _ [] _ 0 σ ρ (fun _ _ h => by cases h)
    (fun y _ => h y), Region.evalObs, ← bind_pure_comp]
  rfl

/-- Versioning is sound for the λRTL reading of the versioned program as well. -/
theorem versionTop_evalObs (m : Model F M α) (hm : m.PairLawful) (r : Region V L F)
    (σ : V → α) (ρ : V × ℕ → α) (h : ∀ y, ρ (y, 0) = σ y) :
    (versionTop r).evalObs m ρ = r.evalObs m σ := by
  rw [Region.evalObs_eq_evalSSA_of_isSSA m (versionTop_isSSA r) ρ,
    versionTop_evalSSA m hm r σ ρ h]

end Silmaril.SSA.LambdaRTL.Version
