module

public import Silmaril.Calculi.PCF.Adequacy

/-! # Extensionality

§7.3 of the notes, for PCF and for PCF+`por`. Formal approximation is a
one-sided form of contextual equivalence: for closed terms,
`t₁ ≤ctx t₂ ⇔ ⟦t₁⟧ ⊲ t₂` (`ctxLe_iff_approx`). Two lemmas lead there:

* the contextual preorder preserves approximation (`Approx.of_ctxLe`);
* the contextual preorder between closed terms is determined by application
  contexts `f −` with `f : τ -> bool` (`ctxLe_iff_app`).

For the second, as in the notes, a closing context `C : γ` with a result `v`
becomes the closed function `f = fun x:τ. g C[x]`, where the closed test
`g : γ -> bool` returns `true` exactly on terms evaluating to `v`
(`exists_test`). The function is `TypedLambda.Context.close` applied to the context
`g C` (`Eval.app_close_iff`). The notes obtain `g` from Turing completeness; a
conditional suffices for booleans and a recursion on the numeral with `zero?`
and `pred` for numbers (`Term.testBool`, `Term.testNum`). The tests are built
from term formers `Term.eqBool`, `Term.eqNum` that can be applied in any
context.

The correspondence transfers extensionality of the domain order to the
contextual preorder (`ctxLe_iff_eval`, `ctxLe_arrow_iff`, and their
contextual-equivalence forms): at ground types `≤ctx` is inclusion of results,
and at function types it is tested pointwise on closed arguments. Terms with
the same results are contextually equivalent (`CtxEquiv.of_eval_iff`), so
β-conversion holds up to `≅ctx` (`ctxEquiv_beta`). The converse holds at ground
types only: `Ω_{nat -> nat} ≅ctx fun x:nat. Ω_nat`, but the second is a value
and the first diverges (`ctxEquiv_omega_lam_omega`).
-/

@[expose] public section

namespace Silmaril.Calculi.PCF


open OmegaCompletePartialOrder Silmaril.Semantics.Domain TypedLambda Cslib.LambdaCalculus.LocallyNameless.Stlc

variable {p : Bool}

namespace Eval

/-- `fun x:σ. C[x]` applied to `t` has the results of `C[t]`. -/
theorem app_close_iff {σ γ : Ty} (C : TypedLambda.Context (sig p) [] σ [] γ) (t : Closed p σ)
    (v : Closed p γ) : .app C.close t ⇓ v ↔ C.plug t ⇓ v := by
  rw [Context.close, app_lam_iff, Context.ofClosed_plug_subst1]

end Eval

/-! ### Testing for a ground value -/

section Tests

variable {Γ : Ctx Base}

/-- `eqₙ` tests for the numeral `n̄`: `eqₙ(e) ⇓ true` iff `e ⇓ n̄`. -/
theorem Eval.eqNum_iff (n : ℕ) (e : Closed p .nat) :
    Term.eqNum n e ⇓ .tt ↔ e ⇓ Term.num n := by
  induction n generalizing e with
  | zero => exact isZero_tt_iff
  | succ n ih =>
      rw [Term.eqNum, ite_iff, ih, pred_iff]
      refine ⟨fun h => h.elim (fun h => absurd h.2 not_ff_tt) fun h => h.2,
        fun h => .inr ⟨isZero_ff_iff.2 ⟨_, h⟩, h⟩⟩

/-- `eq_b` tests for the boolean `b`: `eq_b(e) ⇓ true` iff `e ⇓ b`. -/
theorem Eval.eqBool_iff (b : Bool) (e : Closed p .bool) :
    Term.eqBool b e ⇓ .tt ↔ e ⇓ Term.bool b := by
  cases b <;> rw [Term.eqBool, ite_iff]
  · exact ⟨fun h => h.elim (fun h => absurd h.2 not_ff_tt) fun h => h.1,
      fun h => .inr ⟨h, .val .tt⟩⟩
  · exact ⟨fun h => h.elim (fun h => h.1) fun h => absurd h.2 not_ff_tt,
      fun h => .inl ⟨h, .val .tt⟩⟩

/-- The closed test `fun x:nat. eqₙ(x)` for the numeral `n̄`. -/
def Term.testNum (n : ℕ) : Closed p (Ty.nat ⤳ Ty.bool) := .lam (Term.eqNum n Term.v0)

/-- The closed test `fun x:bool. eq_b(x)` for the boolean `b`. -/
def Term.testBool (b : Bool) : Closed p (Ty.bool ⤳ Ty.bool) := .lam (Term.eqBool b Term.v0)

/-- `(fun x:nat. eqₙ(x)) e ⇓ true` iff `e ⇓ n̄`. -/
theorem Eval.app_testNum_iff (n : ℕ) (e : Closed p .nat) :
    .app (Term.testNum n) e ⇓ .tt ↔ e ⇓ Term.num n := by
  rw [Term.testNum, app_lam_iff, Term.subst1, Term.subst_eqNum]
  exact eqNum_iff n e

/-- `(fun x:bool. eq_b(x)) e ⇓ true` iff `e ⇓ b`. -/
theorem Eval.app_testBool_iff (b : Bool) (e : Closed p .bool) :
    .app (Term.testBool b) e ⇓ .tt ↔ e ⇓ Term.bool b := by
  rw [Term.testBool, app_lam_iff, Term.subst1, Term.subst_eqBool]
  exact eqBool_iff b e

/-- A value `v` of ground type has a closed test `g : γ -> bool`:
`g e ⇓ true` iff `e ⇓ v`. -/
theorem exists_test {γ : Ty} (hγ : γ.IsGround) {v : Closed p γ} (hv : Value v) :
    ∃ g : Closed p (γ ⤳ Ty.bool), ∀ e : Closed p γ, .app g e ⇓ .tt ↔ e ⇓ v := by
  match γ, hγ, v, hv with
  | .base .nat, _, _, hv =>
      obtain ⟨n, rfl⟩ := hv.eq_num
      exact ⟨Term.testNum n, Eval.app_testNum_iff n⟩
  | .base .bool, _, _, hv =>
      obtain ⟨b, rfl⟩ := hv.eq_bool
      exact ⟨Term.testBool b, Eval.app_testBool_iff b⟩

end Tests

/-! ### Formal approximation and the contextual preorder -/

section Preorder

variable {τ : Ty}

/-- Lemma 36: the contextual preorder preserves formal approximation: if
`t₁ ≤ctx t₂` and `d ⊲ t₁` then `d ⊲ t₂`. -/
theorem Approx.of_ctxLe : (τ : Ty) → {d : (model p).ty τ} → {t₁ t₂ : Closed p τ} →
    t₁ ≤ctx t₂ → Approx τ d t₁ → Approx τ d t₂
  | .base .nat, _, _, _, h, ha =>
      Approx.of_eval _ (fun _ => Observation.CtxLe.eval (O := obs p) (γ := Ty.nat) trivial h) ha
  | .base .bool, _, _, _, h, ha =>
      Approx.of_eval _ (fun _ => Observation.CtxLe.eval (O := obs p) (γ := Ty.bool) trivial h) ha
  | .arrow _ τ, _, _, _, h, ha => fun e u he =>
      of_ctxLe τ (Observation.CtxLe.app h u) (ha e u he)

/-- Lemma 37: application contexts suffice. For closed terms, `t₁ ≤ctx t₂`
iff for every closed `f : τ -> bool`, `f t₁ ⇓ true` implies `f t₂ ⇓ true`. -/
theorem ctxLe_iff_app {t₁ t₂ : Closed p τ} :
    t₁ ≤ctx t₂ ↔ ∀ f : Closed p (τ ⤳ Ty.bool), .app f t₁ ⇓ .tt → .app f t₂ ⇓ .tt := by
  refine ⟨fun h f => Observation.CtxLe.eval (O := obs p) (γ := Ty.bool) trivial
    (Observation.CtxLe.app_right f h), fun H γ hγ C v hv => ?_⟩
  obtain ⟨g, hg⟩ := exists_test hγ hv.value
  -- `f = fun x:τ. g C[x]` returns `true` on `t` iff `C[t] ⇓ v`.
  have key : ∀ t, .app (Context.appR g C).close t ⇓ .tt ↔ C.plug t ⇓ v :=
    fun t => (Eval.app_close_iff _ t _).trans (hg _)
  exact (key t₂).1 (H _ ((key t₁).2 hv))

/-- Proposition 38: for closed terms, `t₁ ≤ctx t₂` iff `⟦t₁⟧ ⊲ t₂`. -/
theorem ctxLe_iff_approx {t₁ t₂ : Closed p τ} : t₁ ≤ctx t₂ ↔ Approx τ (denoteClosed t₁) t₂ := by
  refine ⟨fun h => Approx.of_ctxLe τ h (approx_denote t₁), fun h => ?_⟩
  refine ctxLe_iff_app.2 fun f hf => ?_
  -- Equation (16): `⟦f t₁⟧ = ⟦f⟧(⟦t₁⟧) ⊲ f t₂`, and `⟦f t₁⟧ = true` by soundness.
  have h16 : Approx .bool (Model.app (denoteClosed f) (denoteClosed t₁)) (.app f t₂) :=
    approx_denote f _ _ h
  exact h16 true (Eval.denoteClosed_eq hf)

/-- If every result of `t₁` is a result of `t₂`, then `t₁ ≤ctx t₂`. -/
theorem CtxLe.of_eval {t₁ t₂ : Closed p τ} (H : ∀ v, t₁ ⇓ v → t₂ ⇓ v) : t₁ ≤ctx t₂ :=
  ctxLe_iff_approx.2 (Approx.of_eval τ H (approx_denote t₁))

/-- Proposition 39 at ground types: `t₁ ≤ctx t₂` iff every result of `t₁` is
a result of `t₂`. -/
theorem ctxLe_iff_eval {γ : Ty} (hγ : γ.IsGround) {t₁ t₂ : Closed p γ} :
    t₁ ≤ctx t₂ ↔ ∀ v, t₁ ⇓ v → t₂ ⇓ v :=
  ⟨fun h _ => Observation.CtxLe.eval (O := obs p) hγ h, CtxLe.of_eval⟩

/-- Proposition 39 at function types: `t₁ ≤ctx t₂ : σ -> τ` iff
`t₁ u ≤ctx t₂ u : τ` for every closed `u : σ`. -/
theorem ctxLe_arrow_iff {σ : Ty} {t₁ t₂ : Closed p (σ ⤳ τ)} :
    t₁ ≤ctx t₂ ↔ ∀ u : Closed p σ, .app t₁ u ≤ctx .app t₂ u :=
  ⟨fun h u => Observation.CtxLe.app h u, fun H => ctxLe_iff_approx.2 fun e u he =>
    Approx.of_ctxLe τ (H u) (approx_denote t₁ e u he)⟩

end Preorder

/-! ### Contextual equivalence -/

section Equivalence

variable {τ : Ty}

/-- For closed terms, `t₁ ≅ctx t₂` iff `⟦t₁⟧ ⊲ t₂` and `⟦t₂⟧ ⊲ t₁`. -/
theorem ctxEquiv_iff_approx {t₁ t₂ : Closed p τ} :
    t₁ ≅ctx t₂ ↔ Approx τ (denoteClosed t₁) t₂ ∧ Approx τ (denoteClosed t₂) t₁ := by
  rw [← ctxLe_iff_approx, ← ctxLe_iff_approx]
  exact Observation.ctxEquiv_iff_le

/-- Proposition 39 at function types, for contextual equivalence:
`t₁ ≅ctx t₂ : σ -> τ` iff `t₁ u ≅ctx t₂ u : τ` for every closed `u : σ`. -/
theorem ctxEquiv_arrow_iff {σ : Ty} {t₁ t₂ : Closed p (σ ⤳ τ)} :
    t₁ ≅ctx t₂ ↔ ∀ u : Closed p σ, .app t₁ u ≅ctx .app t₂ u := by
  refine Observation.ctxEquiv_iff_le.trans ⟨fun h u => ?_, fun h => ?_⟩
  · exact Observation.ctxEquiv_iff_le.2 ⟨ctxLe_arrow_iff.1 h.1 u, ctxLe_arrow_iff.1 h.2 u⟩
  · exact ⟨ctxLe_arrow_iff.2 fun u => (Observation.ctxEquiv_iff_le.1 (h u)).1,
      ctxLe_arrow_iff.2 fun u => (Observation.ctxEquiv_iff_le.1 (h u)).2⟩

/-- Closed terms with the same results are contextually equivalent. -/
theorem CtxEquiv.of_eval_iff {t₁ t₂ : Closed p τ} (H : ∀ v, t₁ ⇓ v ↔ t₂ ⇓ v) : t₁ ≅ctx t₂ :=
  Observation.ctxEquiv_iff_le.2
    ⟨CtxLe.of_eval fun v => (H v).1, CtxLe.of_eval fun v => (H v).2⟩

/-- Proposition 39 at ground types, for contextual equivalence: `t₁ ≅ctx t₂`
iff `t₁` and `t₂` have the same results. -/
theorem ctxEquiv_iff_eval {γ : Ty} (hγ : γ.IsGround) {t₁ t₂ : Closed p γ} :
    t₁ ≅ctx t₂ ↔ ∀ v, t₁ ⇓ v ↔ t₂ ⇓ v :=
  ⟨fun h v => Observation.CtxEquiv.eval_iff (O := obs p) hγ h v, CtxEquiv.of_eval_iff⟩

/-- β-conversion holds up to contextual equivalence:
`(fun x:σ. t) u ≅ctx t[u/x]` for closed `u`. -/
theorem ctxEquiv_beta {σ : Ty} (t : Term p [σ] τ) (u : Closed p σ) :
    .app (.lam t) u ≅ctx t.subst1 u :=
  CtxEquiv.of_eval_iff fun _ => Eval.app_lam_iff

/-- At function types, contextually equivalent terms need not have the same
results: `Ω_{nat -> nat} ≅ctx fun x:nat. Ω_nat`, but the second evaluates to
itself and the first diverges. -/
theorem ctxEquiv_omega_lam_omega :
    (Term.omega (Ty.nat ⤳ Ty.nat) : Closed p _) ≅ctx .lam (Term.omega Ty.nat) ∧
      (.lam (Term.omega Ty.nat) : Closed p (Ty.nat ⤳ Ty.nat)) ⇓ .lam (Term.omega Ty.nat) ∧
      Diverges (Term.omega (Ty.nat ⤳ Ty.nat) : Closed p _) :=
  ⟨CtxEquiv.of_denote_eq denote_lam_omega.symm, .val (.lam _), omega_diverges⟩

end Equivalence

end Silmaril.Calculi.PCF
