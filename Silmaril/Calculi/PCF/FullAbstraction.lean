module

public import Silmaril.Calculi.PCF.Extensionality
public import Silmaril.Calculi.PCF.Undefinability
public import Silmaril.Calculi.PCF.Adequacy
public import Silmaril.Calculi.PCF.Density
public import Silmaril.Calculi.TypedLambda.FullAbstraction

/-! # Full abstraction

A denotational model is *fully abstract* when contextually equivalent terms
have equal denotations (`FullyAbstract`); the converse holds for the PCF model
by adequacy. The domain model of PCF is not fully abstract. The witnesses are
the terms

```
T_b = fun f : bool -> bool -> bool.
        if (f true Ω) then
          if (f Ω true) then
            if (f false false) then Ω else b
          else Ω
        else Ω
```

(`Term.tcase b`), which test the three entries of the table of parallel or
that characterize it (`PorSpec`). Denotationally they differ, since
`⟦T_b⟧(por) = b` (`app_denote_tcase_porElem`, `denote_tcase_ne`). Yet
`⟦T_b⟧` sends the denotation of every closed PCF term to `⊥`
(`app_denote_tcase_denoteClosed`), since otherwise that denotation would
satisfy `PorSpec` and be parallel or, contradicting `por_undefinable`. By
soundness, `T_b t` then diverges for every closed PCF term `t`
(`tcase_app_diverges`), so by extensionality (`ctxEquiv_arrow_iff`,
`ctxEquiv_iff_eval`) `T_true ≅ctx T_false` in PCF (`tcase_ctxEquiv`), and the
model of PCF is not fully abstract (`not_fullyAbstract`).

In PCF+`por` the two terms are distinguished by the context `− por`, since
`T_b (fun x. fun y. por(x, y)) ⇓ b` (`eval_tcase_app_porLam`). So the
inclusion of PCF into PCF+`por`, which reflects contextual equivalence
(`CtxEquiv.of_embed`), does not preserve it (`not_ctxEquiv_embed_tcase`).

## Full abstraction for PCF+`por`

Adding `por` repairs this: the model of PCF+`por` is fully abstract
(`fullyAbstract_por`, Plotkin). Every element of `⟦τ⟧` is the supremum of an
ω-chain of definable elements (`exists_chain_definable`), and at base type the
order reflects evaluation (`denoteClosed_le_of_eval_imp`, by adequacy). The
generic argument `Observation.denote_le_of_ctxLe` then turns `t₁ ≤ctx t₂` into
`⟦t₁⟧ ⊑ ⟦t₂⟧` (`denote_le_of_ctxLe`); with soundness and adequacy this gives
`ctxLe_iff_denote_le` and `ctxEquiv_iff_denote_eq`.
-/

@[expose] public section

namespace Silmaril.Calculi.PCF


open OmegaCompletePartialOrder Silmaril.Semantics.Domain TypedLambda Cslib.LambdaCalculus.LocallyNameless.Stlc

/-- The domain model of PCF (`p = false`) or of PCF+`por` (`p = true`) is
fully abstract when contextually equivalent terms have equal denotations. -/
def FullyAbstract (p : Bool) : Prop :=
  ∀ {Γ : Ctx Base} {τ : Ty} (t₁ t₂ : Term p Γ τ), t₁ ≅ctx t₂ → denote t₁ = denote t₂

section Tcase

variable {p : Bool} {Γ : Ctx Base}

/-- The body of `T_b`, with `f` the innermost variable. -/
def Term.tcaseBody (b : Bool) : Term p (Ty.bool₂ :: Γ) Ty.bool :=
  let call (x y : Term p (Ty.bool₂ :: Γ) Ty.bool) := TypedLambda.Term.app (.app Term.v0 x) y
  Term.ite (call Term.tt (Term.omega _))
    (Term.ite (call (Term.omega _) Term.tt)
      (Term.ite (call Term.ff Term.ff) (Term.omega _) (Term.bool b))
      (Term.omega _))
    (Term.omega _)

/-- The term `T_b = fun f. if (f true Ω) then if (f Ω true) then
if (f false false) then Ω else b else Ω else Ω`. -/
def Term.tcase (b : Bool) : Term p Γ (Ty.bool₂ ⤳ Ty.bool) :=
  .lam (Term.tcaseBody b)

/-- The function denoted by `T_b`: it tests the three entries of `PorSpec`. -/
noncomputable def tcaseFun (b : Bool) (f : (model p).ty Ty.bool₂) : Part Bool :=
  condFun (app₂ f (.some true) .none)
    (condFun (app₂ f .none (.some true))
      (condFun (app₂ f (.some false) (.some false)) .none (.some b))
      .none)
    .none

/-- `⟦T_b⟧(f)` is `tcaseFun b f`, using `⟦Ω⟧ = ⊥`. -/
theorem app_denote_tcase (b : Bool) (ρ : (model p).Env Γ) (f : (model p).ty Ty.bool₂) :
    Model.app (denote (Term.tcase b : Term p Γ _) ρ) f = tcaseFun b f := by
  change denote (Term.tcaseBody b) (f ::ₜ ρ) = _
  rw [Term.tcaseBody, denote_ite, denote_ite, denote_ite]
  repeat rw [Model.denote_app]
  rw [denote_omega, denote_bool]
  rfl

/-- `⟦T_b⟧(por) = b`. -/
theorem app_denote_tcase_porElem (b : Bool) (ρ : (model p).Env Γ) :
    Model.app (denote (Term.tcase b : Term p Γ _) ρ) porElem = Part.some b := by
  rw [app_denote_tcase, tcaseFun, porElem_app, porElem_app, porElem_app]
  simp

/-- `⟦T_true⟧ ≠ ⟦T_false⟧` in every environment, since they differ at `por`. -/
theorem denote_tcase_true_ne_false (ρ : (model p).Env Γ) :
    denote (Term.tcase true : Term p Γ _) ρ ≠ denote (Term.tcase false) ρ := by
  intro h
  have := app_denote_tcase_porElem (Γ := Γ) true ρ
  rw [h, app_denote_tcase_porElem] at this
  exact Bool.false_ne_true (Part.some_injective this)

/-- `⟦T_true⟧ ≠ ⟦T_false⟧` as continuous maps on environments. -/
theorem denote_tcase_ne : denote (Term.tcase true : Term p Γ _) ≠ denote (Term.tcase false) :=
  fun h => denote_tcase_true_ne_false (fun _ _ => ⊥) (DFunLike.congr_fun h _)

/-- `⟦T_b⟧` sends the denotation of every closed PCF term
`t : bool -> bool -> bool` to `⊥`: `⟦T_b⟧(⟦t⟧)` can only be defined if `⟦t⟧`
satisfies `PorSpec`, which would make it parallel or. -/
theorem app_denote_tcase_denoteClosed (b : Bool) (ρ : (model false).Env Γ)
    (t : Closed false Ty.bool₂) :
    Model.app (denote (Term.tcase b : Term false Γ _) ρ) (denoteClosed t) = Part.none := by
  have hne := not_porSpec_denoteClosed t
  rw [app_denote_tcase, tcaseFun]
  generalize denoteClosed t = f at hne
  rcases part_bool_cases (app₂ f (Part.some true) Part.none) with h₁ | h₁ | h₁ <;>
    rcases part_bool_cases (app₂ f Part.none (Part.some true)) with h₂ | h₂ | h₂ <;>
    rcases part_bool_cases (app₂ f (Part.some false) (Part.some false))
      with h₃ | h₃ | h₃ <;>
    simp only [h₁, h₂, h₃, condFun_none, condFun_true, condFun_false] <;>
    first | rfl | exact absurd ⟨h₁, h₂, h₃⟩ hne

/-! ### `T_true ≅ctx T_false` in PCF -/

/-- `T_b t` diverges for every closed PCF term `t : bool -> bool -> bool`: by
soundness a result would be a defined value of `⟦T_b⟧(⟦t⟧) = ⊥`. -/
theorem tcase_app_diverges (b : Bool) (t : Closed false Ty.bool₂) :
    Diverges (.app (Term.tcase b) t) :=
  diverges_of_denote_eq_bot (γ := Ty.bool) trivial
    (app_denote_tcase_denoteClosed b Tuple.nil t)

/-- `T_true ≅ctx T_false` in PCF, by extensionality: for every closed `t`,
neither `T_true t` nor `T_false t` has a result. -/
theorem tcase_ctxEquiv :
    (Term.tcase true : Closed false (Ty.bool₂ ⤳ Ty.bool)) ≅ctx Term.tcase false :=
  ctxEquiv_arrow_iff.2 fun t => (ctxEquiv_iff_eval (γ := Ty.bool) trivial).2 fun v =>
    ⟨fun h => (tcase_app_diverges true t v h).elim,
      fun h => (tcase_app_diverges false t v h).elim⟩

/-- The domain model of PCF is not fully abstract: `T_true ≅ctx T_false`, but
`⟦T_true⟧ ≠ ⟦T_false⟧`. -/
theorem not_fullyAbstract : ¬ FullyAbstract false :=
  fun h => denote_tcase_ne (h _ _ tcase_ctxEquiv)

/-! ### `T_true` and `T_false` in PCF+`por` -/

/-- In PCF+`por`, a term `t` with `⟦t⟧(por) = b` sends
`fun x. fun y. por(x, y)` to `b`. -/
theorem eval_app_porLam {t : Closed true (Ty.bool₂ ⤳ Ty.bool)} {b : Bool}
    (h : Model.app (denoteClosed t) porElem = Part.some b) : .app t Term.porLam ⇓ Term.bool b :=
  adequacy_bool (by rw [← denote_porLam Tuple.nil] at h; exact h)

/-- `T_b (fun x. fun y. por(x, y)) ⇓ b` in PCF+`por`. -/
theorem eval_tcase_app_porLam (b : Bool) :
    .app (Term.tcase b : Closed true _) Term.porLam ⇓ Term.bool b :=
  eval_app_porLam (app_denote_tcase_porElem b Tuple.nil)

/-- Terms `t₁`, `t₂` of PCF+`por` with `⟦t₁⟧(por) = true` and
`⟦t₂⟧(por) = false` are not contextually equivalent: the context `− por`
distinguishes them. -/
theorem not_ctxEquiv_of_app_porElem {t₁ t₂ : Closed true (Ty.bool₂ ⤳ Ty.bool)}
    (h₁ : Model.app (denoteClosed t₁) porElem = Part.some true)
    (h₂ : Model.app (denoteClosed t₂) porElem = Part.some false) : ¬ t₁ ≅ctx t₂ := fun h => by
  have e := (h Ty.bool trivial (.appL .hole Term.porLam) Term.tt).1 (eval_app_porLam h₁)
  cases Eval.det e (eval_app_porLam h₂)

/-- `T_true` and `T_false` are not contextually equivalent in PCF+`por`. -/
theorem not_ctxEquiv_tcase_por :
    ¬ (Term.tcase true : Closed true (Ty.bool₂ ⤳ Ty.bool)) ≅ctx Term.tcase false :=
  not_ctxEquiv_of_app_porElem (app_denote_tcase_porElem _ _) (app_denote_tcase_porElem _ _)

/-- The inclusion of PCF into PCF+`por` does not preserve contextual
equivalence: the images of `T_true ≅ctx T_false` are distinguished by
parallel or. -/
theorem not_ctxEquiv_embed_tcase :
    ¬ Term.embed (Term.tcase true : Closed false (Ty.bool₂ ⤳ Ty.bool)) ≅ctx
      Term.embed (Term.tcase false) := by
  refine not_ctxEquiv_of_app_porElem ?_ ?_
  · have h := app_denote_tcase_porElem (p := false) (Γ := []) true Tuple.nil
    rw [← denote_embed] at h
    exact h
  · have h := app_denote_tcase_porElem (p := false) (Γ := []) false Tuple.nil
    rw [← denote_embed] at h
    exact h

/-- The inclusion of PCF into PCF+`por` reflects but does not preserve
contextual equivalence. -/
theorem exists_ctxEquiv_not_embed :
    ∃ t₁ t₂ : Closed false (Ty.bool₂ ⤳ Ty.bool), t₁ ≅ctx t₂ ∧ ¬ t₁.embed ≅ctx t₂.embed :=
  ⟨_, _, tcase_ctxEquiv, not_ctxEquiv_embed_tcase⟩

end Tcase

section Por

/-- Ground reflection: at base type, if every result of `t` is a result of `u`
then `⟦t⟧ ⊑ ⟦u⟧`. By adequacy, a defined `⟦t⟧` is the denotation of a result of
`t`, hence of a result of `u`, hence equal to `⟦u⟧` by soundness. -/
theorem denoteClosed_le_of_eval_imp {p : Bool} {b : Base} {t u : Closed p (.base b)}
    (h : ∀ v, t ⇓ v → u ⇓ v) : denoteClosed t ≤ denoteClosed u := by
  cases b with
  | nat =>
      rcases Part.eq_none_or_eq_some (denoteClosed t : Part ℕ) with ht | ⟨k, ht⟩
      · rw [ht]; exact bot_le
      · have hu : denoteClosed u = (Part.some k : Part ℕ) :=
          (Eval.denoteClosed_eq (h _ (adequacy_nat ht))).trans (denote_num (ρ := Tuple.nil) k)
        change (denoteClosed t : Part ℕ) ≤ denoteClosed u
        rw [ht, hu]
  | bool =>
      rcases Part.eq_none_or_eq_some (denoteClosed t : Part Bool) with ht | ⟨k, ht⟩
      · rw [ht]; exact bot_le
      · have hu : denoteClosed u = (Part.some k : Part Bool) :=
          (Eval.denoteClosed_eq (h _ (adequacy_bool ht))).trans (denote_bool (ρ := Tuple.nil) k)
        change (denoteClosed t : Part Bool) ≤ denoteClosed u
        rw [ht, hu]

/-- In PCF+`por`, the contextual preorder implies the denotational order. -/
theorem denote_le_of_ctxLe {Γ : Ctx Base} {τ : Ty} {t₁ t₂ : Term true Γ τ}
    (h : t₁ ≤ctx t₂) : denote t₁ ≤ denote t₂ :=
  Observation.denote_le_of_ctxLe (O := obs true) (M := model true) (fun _ => trivial)
    (fun _ _ _ h => denoteClosed_le_of_eval_imp h) (fun _ d => exists_chain_definable d) h

/-- In PCF+`por`, the contextual preorder coincides with the denotational order. -/
theorem ctxLe_iff_denote_le {Γ : Ctx Base} {τ : Ty} (t₁ t₂ : Term true Γ τ) :
    t₁ ≤ctx t₂ ↔ denote t₁ ≤ denote t₂ :=
  ⟨denote_le_of_ctxLe, CtxLe.of_denote_le⟩

/-- In PCF+`por`, contextual equivalence coincides with denotational equality. -/
theorem ctxEquiv_iff_denote_eq {Γ : Ctx Base} {τ : Ty} (t₁ t₂ : Term true Γ τ) :
    t₁ ≅ctx t₂ ↔ denote t₁ = denote t₂ :=
  ⟨fun h => le_antisymm (denote_le_of_ctxLe (Observation.ctxEquiv_iff_le.1 h).1)
      (denote_le_of_ctxLe (Observation.ctxEquiv_iff_le.1 h).2),
    CtxEquiv.of_denote_eq⟩

/-- The domain model of PCF+`por` is fully abstract. -/
theorem fullyAbstract_por : FullyAbstract true :=
  fun t₁ t₂ => (ctxEquiv_iff_denote_eq t₁ t₂).1

/-- For closed PCF+`por` terms, contextual equivalence coincides with equality of
denotations. -/
theorem ctxEquiv_iff_denoteClosed_eq {τ : Ty} (t₁ t₂ : Closed true τ) :
    t₁ ≅ctx t₂ ↔ denoteClosed t₁ = denoteClosed t₂ :=
  (ctxEquiv_iff_denote_eq t₁ t₂).trans Model.denote_eq_iff_denoteClosed_eq

/-- For closed PCF+`por` terms, the contextual preorder coincides with the order of
denotations. -/
theorem ctxLe_iff_denoteClosed_le {τ : Ty} (t₁ t₂ : Closed true τ) :
    t₁ ≤ctx t₂ ↔ denoteClosed t₁ ≤ denoteClosed t₂ :=
  (ctxLe_iff_denote_le t₁ t₂).trans Model.denote_le_iff_denoteClosed_le

end Por

end Silmaril.Calculi.PCF
