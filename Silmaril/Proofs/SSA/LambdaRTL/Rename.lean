module

public import Silmaril.SSA.LambdaRTL.Nameless.Defs

/-!
# Register renaming invariance of λRTL (proofs)

Restated in `Silmaril.SSA.LambdaRTL.Nameless.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.Rename

open Silmaril.SSA.LambdaRTL

universe v w

variable {V W L : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}

theorem Val.eval_rename (m : Model F M α) (f : V → W) {σ : V → α} {σ' : W → α}
    (h : ∀ x, σ' (f x) = σ x) : ∀ a : Val V, (a.rename f).eval m σ' = a.eval m σ
  | .var x => h x
  | .unit => rfl
  | .pair a b => by
      simp only [Val.rename, Val.eval, Val.eval_rename m f h a, Val.eval_rename m f h b]

theorem Op.eval_rename [Monad M] (m : Model F M α) (f : V → W) {σ : V → α} {σ' : W → α}
    (h : ∀ x, σ' (f x) = σ x) (o : Op V F) : (o.rename f).eval m σ' = o.eval m σ := by
  cases o <;> simp only [Op.rename, Op.eval, Val.eval_rename m f h]

theorem upd_rename [DecidableEq V] [DecidableEq W] {f : V → W} (hf : Function.Injective f)
    {σ : V → α} {σ' : W → α} (h : ∀ x, σ' (f x) = σ x) (x : V) (a : α) :
    ∀ y, upd σ' (f x) a (f y) = upd σ x a y := by
  intro y
  simp only [upd, hf.eq_iff]
  split <;> simp [h]

variable [Monad M] [LawfulMonad M] [DecidableEq V] [DecidableEq W] [DecidableEq L]

/-- **Register renaming invariance** (bind-congruence form): renaming registers injectively does
not change the store semantics, up to the renaming of the final store. -/
theorem Region.evalRTL_rename (m : Model F M α) {f : V → W} (hf : Function.Injective f)
    {β : Type w} :
    ∀ (r : Region V L F) (σ : V → α) (σ' : W → α), (∀ x, σ' (f x) = σ x) →
      ∀ (K : L × α × (V → α) → M β) (K' : L × α × (W → α) → M β),
      (∀ l a τ τ', (∀ x, τ' (f x) = τ x) → K' (l, a, τ') = K (l, a, τ)) →
      ((r.rename f).evalRTL m σ' >>= K') = (r.evalRTL m σ >>= K)
  | .br ℓ a, σ, σ', h, K, K', hK => by
      simp only [Region.rename, Region.evalRTL, pure_bind, Val.eval_rename m f h]
      exact hK _ _ _ _ h
  | .let1 x o r, σ, σ', h, K, K', hK => by
      simp only [Region.rename, Region.evalRTL, bind_assoc, Op.eval_rename m f h]
      congr 1; funext a
      exact Region.evalRTL_rename m hf r _ _ (upd_rename hf h x a) K K' hK
  | .let2 x y o r, σ, σ', h, K, K', hK => by
      simp only [Region.rename, Region.evalRTL, bind_assoc, Op.eval_rename m f h]
      congr 1; funext a; congr 1; funext p
      exact Region.evalRTL_rename m hf r _ _
        (upd_rename hf (upd_rename hf h x p.1) y p.2) K K' hK
  | .case o x r y s, σ, σ', h, K, K', hK => by
      simp only [Region.rename, Region.evalRTL, bind_assoc, Op.eval_rename m f h]
      congr 1; funext a; congr 1; funext c
      cases c with
      | inl b => exact Region.evalRTL_rename m hf r _ _ (upd_rename hf h x b) K K' hK
      | inr b => exact Region.evalRTL_rename m hf s _ _ (upd_rename hf h y b) K K' hK
  | .join r ℓ x t, σ, σ', h, K, K', hK => by
      simp only [Region.rename, Region.evalRTL, bind_assoc]
      apply Region.evalRTL_rename m hf r σ σ' h
      intro l a τ τ' hτ
      dsimp only
      split
      · exact Region.evalRTL_rename m hf t _ _ (upd_rename hf hτ x a) K K' hK
      · simp only [pure_bind]; exact hK _ _ _ _ hτ

/-- Observable λRTL semantics is invariant under injective register renaming. -/
theorem Region.evalObs_rename (m : Model F M α) {f : V → W} (hf : Function.Injective f)
    (r : Region V L F) {σ : V → α} {σ' : W → α} (h : ∀ x, σ' (f x) = σ x) :
    (r.rename f).evalObs m σ' = r.evalObs m σ := by
  simp only [Region.evalObs, map_eq_pure_bind]
  exact Region.evalRTL_rename m hf r σ σ' h _ _ (fun _ _ _ _ _ => rfl)

end Silmaril.Proofs.SSA.LambdaRTL.Rename
