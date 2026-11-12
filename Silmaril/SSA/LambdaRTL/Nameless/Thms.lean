module

public import Silmaril.SSA.LambdaRTL.Nameless.Defs
public import Silmaril.SSA.LambdaRTL.Thms
import Silmaril.Proofs.SSA.LambdaRTL.Nameless
import Silmaril.Proofs.SSA.LambdaRTL.Rename

/-!
# Nameless presentation of acyclic λSSA: checked results

* `Region.eval_toDB`, `Region.eval_toDB_env`: **adequacy** of the de Bruijn translation —
  `(r.toDB Γ).eval m η = r.evalSSA m ρ` whenever `r.fv ⊆ Γ.toFinset` and `η` represents `ρ`
  along `Γ` (`Agree Γ η ρ`; e.g. `η = env Γ ρ d`). No hypothesis on `Γ` (duplicates allowed:
  the first occurrence wins, i.e. shadowing is lexical).
* `Region.ws_toDB`: `toDB` of a term whose free variables are in `Γ` is well-scoped.
* `Region.toDB_rename`: `(r.rename f).toDB (Γ.map f) = r.toDB Γ` when `f` is injective on the
  names of `Γ` together with all names occurring in `r` (`Region.vars`); in particular for
  injective `f` (`Region.toDB_rename_of_injective`).
* `DB.Region.eval_rename`, `DB.Region.eval_wk`, `DB.Region.ws_rename`, `DB.Region.eval_congr`:
  de Bruijn renamings/weakening and their action on evaluation and scope.
* `DB.Region.toDB_ofDB`: **round trip** `toDB Γ (ofDB S Γ d) = d` for `d.WS Γ.length` and
  `Γ.Nodup`. `DB.Region.isSSA_ofDB`: the back translation is dominance-scoped SSA.
* `Region.alphaEq_ofDB_toDB`: `ofDB (toDB r) ≈α r`; `Region.evalSSA_eq_of_alphaEq`: the lexical
  semantics is invariant under α-equivalence.
* `*_mapOp`: all translations commute with instruction renaming.
* `Region.evalObs_rename`: the λRTL store semantics is invariant under injective register
  renaming (`σ' ∘ f = σ`); bind-congruence form `Region.evalRTL_rename`.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL

universe v w

section

variable {V W L : Type w} {F F' : Type v} {M : Type w → Type w} {α : Type w}

/-! ## Contexts and environments -/

theorem idx_lt_length_iff [DecidableEq V] (x : V) (Γ : List V) : idx x Γ < Γ.length ↔ x ∈ Γ :=
  Silmaril.Proofs.SSA.LambdaRTL.Nameless.idx_lt_length_iff x Γ

theorem agree_env [DecidableEq V] (Γ : List V) (ρ : V → α) (d : α) : Agree Γ (env Γ ρ d) ρ :=
  Silmaril.Proofs.SSA.LambdaRTL.Nameless.agree_env Γ ρ d

theorem agree_comp [DecidableEq V] (Γ : List V) (η : ℕ → α) :
    Agree Γ η (fun x => η (idx x Γ)) :=
  Silmaril.Proofs.SSA.LambdaRTL.Nameless.agree_comp Γ η

theorem Supply.length_ctx [DecidableEq V] (S : Supply V) (n : ℕ) : (S.ctx n).length = n :=
  Silmaril.Proofs.SSA.LambdaRTL.Nameless.Supply.length_ctx S n

theorem Supply.nodup_ctx [DecidableEq V] (S : Supply V) (n : ℕ) : (S.ctx n).Nodup :=
  Silmaril.Proofs.SSA.LambdaRTL.Nameless.Supply.nodup_ctx S n

/-! ## Adequacy -/

/-- **Adequacy of `toDB`.** -/
theorem Region.eval_toDB [Monad M] [DecidableEq V] [DecidableEq L] (m : Model F M α)
    (r : Region V L F) {Γ : List V} {η : ℕ → α} {ρ : V → α} (h : Agree Γ η ρ)
    (hr : r.fv ⊆ Γ.toFinset) : (r.toDB Γ).eval m η = r.evalSSA m ρ :=
  Silmaril.Proofs.SSA.LambdaRTL.Nameless.Region.eval_toDB m r h hr

/-- **Adequacy of `toDB`** with the canonical environment of a context (the default `d` is read
only at indices `≥ Γ.length`, which `r.toDB Γ` never reads). -/
theorem Region.eval_toDB_env [Monad M] [DecidableEq V] [DecidableEq L] (m : Model F M α)
    (r : Region V L F) {Γ : List V} (hr : r.fv ⊆ Γ.toFinset) (ρ : V → α) (d : α) :
    (r.toDB Γ).eval m (env Γ ρ d) = r.evalSSA m ρ :=
  Region.eval_toDB m r (agree_env Γ ρ d) hr

theorem Region.ws_toDB [DecidableEq V] (r : Region V L F) {Γ : List V}
    (hr : r.fv ⊆ Γ.toFinset) : (r.toDB Γ).WS Γ.length :=
  Silmaril.Proofs.SSA.LambdaRTL.Nameless.Region.ws_toDB r Γ hr

/-! ## Renaming names -/

/-- **Renaming invariance.** -/
theorem Region.toDB_rename [DecidableEq V] [DecidableEq W] (f : V → W) (r : Region V L F)
    (Γ : List V) (hf : Set.InjOn f {w | w ∈ Γ ∨ w ∈ r.vars}) :
    (r.rename f).toDB (Γ.map f) = r.toDB Γ :=
  Silmaril.Proofs.SSA.LambdaRTL.Nameless.Region.toDB_rename f r Γ hf

theorem Region.toDB_rename_of_injective [DecidableEq V] [DecidableEq W] {f : V → W}
    (hf : Function.Injective f) (r : Region V L F) (Γ : List V) :
    (r.rename f).toDB (Γ.map f) = r.toDB Γ :=
  Region.toDB_rename f r Γ (fun _ _ _ _ e => hf e)

/-- Injective renaming preserves α-equivalence. -/
theorem Region.AlphaEq.rename [DecidableEq V] [DecidableEq W] {f : V → W}
    (hf : Function.Injective f) {Γ : List V} {r r' : Region V L F} (h : r.AlphaEq Γ r') :
    (r.rename f).AlphaEq (Γ.map f) (r'.rename f) := by
  unfold Region.AlphaEq
  rw [Region.toDB_rename_of_injective hf, Region.toDB_rename_of_injective hf]
  exact h

/-! ## de Bruijn renaming -/

theorem DB.Region.ws_rename (r : DB.Region L F) {ξ : ℕ → ℕ} {n k : ℕ}
    (hξ : ∀ i < n, ξ i < k) (h : r.WS n) : (r.rename ξ).WS k :=
  Silmaril.Proofs.SSA.LambdaRTL.Nameless.DB.Region.ws_rename r hξ h

theorem DB.Region.ws_wk (r : DB.Region L F) {n : ℕ} (h : r.WS n) : r.wk.WS (n + 1) :=
  DB.Region.ws_rename r (fun _ hi => Nat.succ_lt_succ hi) h

theorem DB.Region.eval_rename [Monad M] [DecidableEq L] (m : Model F M α) (r : DB.Region L F)
    (ξ : ℕ → ℕ) (η : ℕ → α) : (r.rename ξ).eval m η = r.eval m (η ∘ ξ) :=
  Silmaril.Proofs.SSA.LambdaRTL.Nameless.DB.Region.eval_rename m r ξ η

theorem DB.Region.eval_wk [Monad M] [DecidableEq L] (m : Model F M α) (r : DB.Region L F)
    (a : α) (η : ℕ → α) : r.wk.eval m (DB.cons a η) = r.eval m η :=
  Silmaril.Proofs.SSA.LambdaRTL.Nameless.DB.Region.eval_wk m r a η

/-- Well-scoped terms only read the first `n` entries of the environment. -/
theorem DB.Region.eval_congr [Monad M] [DecidableEq L] (m : Model F M α) (r : DB.Region L F)
    {n : ℕ} {η₁ η₂ : ℕ → α} (hη : ∀ i < n, η₁ i = η₂ i) (h : r.WS n) :
    r.eval m η₁ = r.eval m η₂ :=
  Silmaril.Proofs.SSA.LambdaRTL.Nameless.DB.Region.eval_congr m r hη h

/-! ## Back translation and α-equivalence -/

/-- **Round trip** `toDB ∘ ofDB = id` on well-scoped terms in a duplicate-free context. -/
theorem DB.Region.toDB_ofDB [DecidableEq V] (S : Supply V) {Γ : List V} (hΓ : Γ.Nodup)
    (d : DB.Region L F) (hd : d.WS Γ.length) : (d.ofDB S Γ).toDB Γ = d :=
  Silmaril.Proofs.SSA.LambdaRTL.Nameless.Region.toDB_ofDB S Γ d hΓ hd

/-- The back translation is dominance-scoped SSA in its context. -/
theorem DB.Region.isSSA_ofDB [DecidableEq V] (S : Supply V) (Γ : List V) (d : DB.Region L F)
    (hd : d.WS Γ.length) : (d.ofDB S Γ).IsSSA Γ.toFinset :=
  Silmaril.Proofs.SSA.LambdaRTL.Nameless.Region.isSSA_ofDB S Γ d hd

theorem DB.Region.fv_ofDB [DecidableEq V] (S : Supply V) (Γ : List V) (d : DB.Region L F)
    (hd : d.WS Γ.length) : (d.ofDB S Γ).fv ⊆ Γ.toFinset :=
  Region.fv_subset_of_isSSA (DB.Region.isSSA_ofDB S Γ d hd)

/-- Adequacy of the back translation. -/
theorem DB.Region.evalSSA_ofDB [Monad M] [DecidableEq V] [DecidableEq L] (m : Model F M α)
    (S : Supply V) {Γ : List V} (hΓ : Γ.Nodup) (d : DB.Region L F) (hd : d.WS Γ.length)
    {η : ℕ → α} {ρ : V → α} (h : Agree Γ η ρ) : (d.ofDB S Γ).evalSSA m ρ = d.eval m η := by
  rw [← Region.eval_toDB m _ h (DB.Region.fv_ofDB S Γ d hd), DB.Region.toDB_ofDB S hΓ d hd]

theorem Region.alphaEq_equivalence [DecidableEq V] (Γ : List V) :
    Equivalence (Region.AlphaEq (L := L) (F := F) Γ) :=
  ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- `ofDB (toDB r) ≈α r`. -/
theorem Region.alphaEq_ofDB_toDB [DecidableEq V] (S : Supply V) {Γ : List V} (hΓ : Γ.Nodup)
    (r : Region V L F) (hr : r.fv ⊆ Γ.toFinset) : ((r.toDB Γ).ofDB S Γ).AlphaEq Γ r :=
  DB.Region.toDB_ofDB S hΓ _ (Region.ws_toDB r hr)

/-- **α-invariance** of the lexical semantics. -/
theorem Region.evalSSA_eq_of_alphaEq [Monad M] [DecidableEq V] [DecidableEq L]
    (m : Model F M α) {Γ : List V} {r r' : Region V L F} (h : r.AlphaEq Γ r')
    (hr : r.fv ⊆ Γ.toFinset) (hr' : r'.fv ⊆ Γ.toFinset) (ρ : V → α) :
    r.evalSSA m ρ = r'.evalSSA m ρ := by
  rw [← Region.eval_toDB_env m r hr ρ m.unit, ← Region.eval_toDB_env m r' hr' ρ m.unit]
  exact congrArg (fun d => DB.Region.eval m d (env Γ ρ m.unit)) h

/-! ## Instruction renaming -/

theorem Region.toDB_mapOp [DecidableEq V] (h : F → F') (Γ : List V) (r : Region V L F) :
    (r.mapOp h).toDB Γ = (r.toDB Γ).mapOp h :=
  Silmaril.Proofs.SSA.LambdaRTL.Nameless.Region.toDB_mapOp h Γ r

theorem DB.Region.ofDB_mapOp [DecidableEq V] (h : F → F') (S : Supply V) (Γ : List V)
    (d : DB.Region L F) : (d.mapOp h).ofDB S Γ = (d.ofDB S Γ).mapOp h :=
  Silmaril.Proofs.SSA.LambdaRTL.Nameless.Region.ofDB_mapOp h S Γ d

theorem DB.Region.ws_mapOp (h : F → F') (n : ℕ) (d : DB.Region L F) :
    (d.mapOp h).WS n ↔ d.WS n :=
  Silmaril.Proofs.SSA.LambdaRTL.Nameless.DB.Region.ws_mapOp h n d

theorem DB.Region.eval_mapOp [Monad M] [DecidableEq L] (h : F → F') (m : Model F' M α)
    (d : DB.Region L F) (η : ℕ → α) : (d.mapOp h).eval m η = d.eval (m.reduct h) η :=
  Silmaril.Proofs.SSA.LambdaRTL.Nameless.DB.Region.eval_mapOp h m d η

theorem DB.Op.mapOp_id (o : DB.Op F) : o.mapOp id = o := by cases o <;> rfl

theorem DB.Op.mapOp_comp {F'' : Type v} (h : F → F') (k : F' → F'') (o : DB.Op F) :
    o.mapOp (k ∘ h) = (o.mapOp h).mapOp k := by cases o <;> rfl

theorem DB.Region.mapOp_id : ∀ d : DB.Region L F, d.mapOp id = d
  | .br _ _ => rfl
  | .let1 o r => by simp only [DB.Region.mapOp, DB.Op.mapOp_id, DB.Region.mapOp_id r]
  | .let2 o r => by simp only [DB.Region.mapOp, DB.Op.mapOp_id, DB.Region.mapOp_id r]
  | .case o r s => by
      simp only [DB.Region.mapOp, DB.Op.mapOp_id, DB.Region.mapOp_id r, DB.Region.mapOp_id s]
  | .join r _ t => by simp only [DB.Region.mapOp, DB.Region.mapOp_id r, DB.Region.mapOp_id t]

theorem DB.Region.mapOp_comp {F'' : Type v} (h : F → F') (k : F' → F'') :
    ∀ d : DB.Region L F, d.mapOp (k ∘ h) = (d.mapOp h).mapOp k
  | .br _ _ => rfl
  | .let1 o r => by
      simp only [DB.Region.mapOp, DB.Op.mapOp_comp h k o, DB.Region.mapOp_comp h k r]
  | .let2 o r => by
      simp only [DB.Region.mapOp, DB.Op.mapOp_comp h k o, DB.Region.mapOp_comp h k r]
  | .case o r s => by
      simp only [DB.Region.mapOp, DB.Op.mapOp_comp h k o, DB.Region.mapOp_comp h k r,
        DB.Region.mapOp_comp h k s]
  | .join r _ t => by
      simp only [DB.Region.mapOp, DB.Region.mapOp_comp h k r, DB.Region.mapOp_comp h k t]


section RegisterRename

variable [Monad M] [LawfulMonad M] [DecidableEq V] [DecidableEq W] [DecidableEq L]

/-- **Register renaming invariance** of the λRTL store semantics (bind-congruence form). -/
theorem Region.evalRTL_rename (m : Model F M α) {f : V → W} (hf : Function.Injective f)
    {β : Type w} (r : Region V L F) (σ : V → α) (σ' : W → α) (h : ∀ x, σ' (f x) = σ x)
    (K : L × α × (V → α) → M β) (K' : L × α × (W → α) → M β)
    (hK : ∀ l a τ τ', (∀ x, τ' (f x) = τ x) → K' (l, a, τ') = K (l, a, τ)) :
    ((r.rename f).evalRTL m σ' >>= K') = (r.evalRTL m σ >>= K) :=
  Silmaril.Proofs.SSA.LambdaRTL.Rename.Region.evalRTL_rename m hf r σ σ' h K K' hK

/-- Observable λRTL semantics is invariant under injective register renaming. -/
theorem Region.evalObs_rename (m : Model F M α) {f : V → W} (hf : Function.Injective f)
    (r : Region V L F) {σ : V → α} {σ' : W → α} (h : ∀ x, σ' (f x) = σ x) :
    (r.rename f).evalObs m σ' = r.evalObs m σ :=
  Silmaril.Proofs.SSA.LambdaRTL.Rename.Region.evalObs_rename m hf r h

end RegisterRename

end

end Silmaril.SSA.LambdaRTL
