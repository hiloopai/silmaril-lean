module

public import Silmaril.Calculi.LambdaCube.STLC.Defs

@[expose] public section

set_option autoImplicit true

/-! Evaluation, substitution and βη soundness proofs for typed STLC. -/

namespace Silmaril.Proofs.Calculi.LambdaCube.STLC

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Calculi.TypedLambda Silmaril.Calculi.LambdaCube.STLC
open Cslib.LambdaCalculus.LocallyNameless.Stlc

/-- Set evaluation commutes with variable renaming. -/
theorem eval_rename {S : Signature} (M : SetModel S) {Γ Δ τ}
    (r : Ren Γ Δ) (t : Term S Γ τ) (ρ : Tuple (carrier M.base) Δ) :
    eval M (t.rename r) ρ = eval M t (fun a x => ρ a (r a x)) := by
  induction t generalizing Δ with
  | var => rfl
  | lam t ih =>
      funext d
      rw [show (eval M ((Term.lam t).rename r) ρ) d =
        eval M (t.rename (Ren.lift r)) (Tuple.cons d ρ) from rfl, ih]
      congr 1
      exact Tuple.ext fun _ x => by cases x <;> rfl
  | app t u iht ihu => simp only [Term.rename, eval, iht, ihu]
  | op o args ih => simp only [Term.rename, eval, ih]

/-- Set evaluation commutes with substitution. -/
theorem eval_subst {S : Signature} (M : SetModel S) {Γ Δ τ}
    (s : Subst S Γ Δ) (t : Term S Γ τ) (ρ : Tuple (carrier M.base) Δ) :
    eval M (t.subst s) ρ = eval M t (fun a x => eval M (s a x) ρ) := by
  induction t generalizing Δ with
  | var => rfl
  | lam t ih =>
      funext d
      change eval M (t.subst _) (Tuple.cons d ρ) = _
      rw [ih]
      congr 1
      apply Tuple.ext
      intro a x
      cases x with
      | zero => rfl
      | succ x => exact eval_rename M _ _ _
  | app t u iht ihu => simp only [Term.subst, eval, iht, ihu]
  | op o args ih => simp only [Term.subst, eval, ih]

/-- Set evaluation commutes with one-variable substitution. -/
theorem eval_substOne {S : Signature} (M : SetModel S) {Γ σ τ}
    (t : Term S (σ :: Γ) τ) (u : Term S Γ σ) (ρ : Tuple (carrier M.base) Γ) :
    eval M (t.subst1 u) ρ = eval M t (Tuple.cons (eval M u ρ) ρ) := by
  rw [Term.subst1, eval_subst]
  congr 1
  exact Tuple.ext fun _ x => by cases x <;> rfl

/-- Set evaluation is compositional for the existing one-hole contexts. -/
theorem eval_plug {S : Signature} (M : SetModel S) {Γ Δ σ τ}
    {t u : Term S Δ σ} (h : ∀ ρ, eval M t ρ = eval M u ρ)
    (C : Context S Δ σ Γ τ) : ∀ ρ, eval M (C.plug t) ρ = eval M (C.plug u) ρ := by
  induction C with
  | hole => exact h
  | lam C ih => intro ρ; funext d; exact ih _
  | appL C u ih => intro ρ; exact congrFun (ih ρ) _
  | appR g C ih => intro ρ; exact congrArg (eval M g ρ) (ih ρ)
  | op o args x C ih =>
      intro ρ
      change M.op o (Tuple.map (fun _ v => eval M v ρ) (args.set x (C.plug t))) =
        M.op o (Tuple.map (fun _ v => eval M v ρ) (args.set x (C.plug u)))
      rw [Tuple.map_set, Tuple.map_set, ih ρ]

/-- Soundness for set semantics, including arbitrary open-term contexts. -/
theorem soundness {S : Signature} (M : SetModel S) {Γ τ} {t u : Term S Γ τ}
    (h : Equates t u) : Holds M (.equation t u) := by
  induction h with
  | refl t => intro ρ; rfl
  | symm _ ih => intro ρ; exact (ih ρ).symm
  | trans _ _ ih₁ ih₂ => intro ρ; exact (ih₁ ρ).trans (ih₂ ρ)
  | beta t u => intro ρ; exact (eval_substOne M t u ρ).symm
  | eta t =>
      intro ρ
      funext d
      change eval M t.weaken (Tuple.cons d ρ) d = eval M t ρ d
      rw [Term.weaken, eval_rename]
      rfl
  | context C _ ih => exact eval_plug M ih C

/-- The entire βη theory is sound in any cartesian closed category,
by the existing categorical substitution and context lemmas. -/
theorem categorical_soundness {C : Type u} [Category.{v} C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] {S : Signature}
    (M : CatModel S C) {Γ τ} {t u : Term S Γ τ} (h : Equates t u) :
    M.interp t = M.interp u := by
  induction h with
  | refl t => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | beta t u => exact M.interp_beta t u
  | eta t => exact M.interp_eta t
  | context C _ ih => exact M.interp_plug_eq ih C

/-- Categorical β soundness is already available for every CCC. -/
theorem categorical_beta {C : Type u} [Category.{v} C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] {S : Signature}
    (M : CatModel S C) {Γ σ τ} (t : Term S (σ :: Γ) τ) (a : Term S Γ σ) :
    M.interp (.app (.lam t) a) = M.interp (t.subst1 a) := M.interp_beta t a

end Silmaril.Proofs.Calculi.LambdaCube.STLC
