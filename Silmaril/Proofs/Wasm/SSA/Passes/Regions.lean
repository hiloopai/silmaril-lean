module

public import Silmaril.Proofs.Wasm.SSA.Passes.Terms

/-!
# Soundness of the region passes

`simpR_sound`: every evaluation of a region is an evaluation of its
simplification. `dce_sound`: the same for dead-binding elimination, through
a renaming lemma that only constrains the variables a region mentions
(`Region.Eval.rename_mentions`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.Passes

open Silmaril.Wasm.SSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (extend Env)
open Silmaril.DeBruijn (lift liftN)

/-! ## The simplifier -/

/-- `simpR` on a `case` that takes its left branch: a literal `inl t` scrutinee
becomes a `let₁`, any other stays a `case`. -/
private theorem simpR_case_inl_sound (cfg : SimpCfg) {F : Facts} {T : Tys} {env : Env WVal}
    {a : Tm Prim} {l r : Region Prim} {s s' : Unit} {lab : Nat} {va v : SVal}
    (ha : Semantics.Tm.Eval instr env (simpTm cfg F T a) () (.inl va) ())
    (ih : ∀ {F : Facts} {T : Tys}, FactsOK F (extend env va) →
      Semantics.Region.Eval instr (extend env va) (simpR cfg F T l) s lab v s')
    (hF : FactsOK F env) :
    Semantics.Region.Eval instr env (simpR cfg F T (.case a l r)) s lab v s' := by
  simp only [simpR]
  split
  next t heq =>
    have ht : Semantics.Tm.Eval instr env t () va () := by
      cases (heq ▸ ha : Semantics.Tm.Eval instr env (.inl t) () (.inl va) ()) with
      | inl ht => exact ht
    exact .let₁ ht (ih (hF.push _ _ fun _ e => Option.some.inj e ▸ ht))
  next t heq =>
    nomatch (heq ▸ ha : Semantics.Tm.Eval instr env (.inr t) () (.inl va) ())
  next => exact .case_inl ha (ih (hF.none _))

/-- `simpR` on a `case` that takes its right branch. -/
private theorem simpR_case_inr_sound (cfg : SimpCfg) {F : Facts} {T : Tys} {env : Env WVal}
    {a : Tm Prim} {l r : Region Prim} {s s' : Unit} {lab : Nat} {va v : SVal}
    (ha : Semantics.Tm.Eval instr env (simpTm cfg F T a) () (.inr va) ())
    (ih : ∀ {F : Facts} {T : Tys}, FactsOK F (extend env va) →
      Semantics.Region.Eval instr (extend env va) (simpR cfg F T r) s lab v s')
    (hF : FactsOK F env) :
    Semantics.Region.Eval instr env (simpR cfg F T (.case a l r)) s lab v s' := by
  simp only [simpR]
  split
  next t heq =>
    nomatch (heq ▸ ha : Semantics.Tm.Eval instr env (.inl t) () (.inr va) ())
  next t heq =>
    have ht : Semantics.Tm.Eval instr env t () va () := by
      cases (heq ▸ ha : Semantics.Tm.Eval instr env (.inr t) () (.inr va) ()) with
      | inr ht => exact ht
    exact .let₁ ht (ih (hF.push _ _ fun _ e => Option.some.inj e ▸ ht))
  next => exact .case_inr ha (ih (hF.none _))

theorem simpR_sound (cfg : SimpCfg) {env : Env WVal} {r : Region Prim} {s s' : Unit} {l : Nat}
    {v : SVal} (h : Semantics.Region.Eval instr env r s l v s') :
    ∀ {F : Facts} {T : Tys}, FactsOK F env →
      Semantics.Region.Eval instr env (simpR cfg F T r) s l v s' := by
  induction h using Semantics.Region.Eval.rec
      (motive_2 := fun env _ blocks first initial s label value s' _ =>
        ∀ {F : Facts} {T : Tys}, FactsOK F env →
          Semantics.Region.Follow instr env (fun i => simpR cfg (none :: F) (none :: T) (blocks i))
            first initial s label value s') with
  | br arg =>
      intro F T hF
      cases ‹Unit›; cases ‹Unit›
      exact .br (simpTm_sound cfg (T := T) arg hF)
  | let₁ arg _ ih =>
      intro F T hF
      cases ‹Unit›; cases ‹Unit›
      exact .let₁ (simpTm_sound' cfg (T := T) hF arg)
        (ih (hF.push _ _ fun _ e => Option.some.inj e ▸ simpTm_sound' cfg (T := T) hF arg))
  | let₂ arg _ ih =>
      intro F T hF
      cases ‹Unit›; cases ‹Unit›
      exact .let₂ (simpTm_sound cfg (T := T) arg hF) (ih ((hF.none _).none _))
  | case_inl arg _ ih =>
      intro F T hF
      cases ‹Unit›; cases ‹Unit›; cases ‹Unit›
      exact simpR_case_inl_sound cfg (simpTm_sound cfg arg hF) ih hF
  | case_inr arg _ ih =>
      intro F T hF
      cases ‹Unit›; cases ‹Unit›; cases ‹Unit›
      exact simpR_case_inr_sound cfg (simpTm_sound cfg arg hF) ih hF
  | cfg _ _ ihEntry ihFollow =>
      intro F T hF
      exact .cfg (ihEntry hF) (ihFollow hF)
  | exit outside => exact .exit outside
  | step inside _ _ ihHead ihTail =>
      exact .step inside (ihHead (FactsOK.none ‹_› _)) (ihTail ‹_›)

/-! ## Renaming the mentioned variables -/

theorem lift_ok {env env' : Env WVal} {ρ : Nat → Nat} {P : Nat → Prop}
    (h : ∀ i, P (i + 1) → env' (ρ i) = env i) (v : SVal) :
    ∀ i, P i → extend env' v (lift ρ i) = extend env v i
  | 0, _ => rfl
  | i + 1, hi => h i hi

theorem Tm.Eval.rename_mentions {env : Env WVal} {a : Tm Prim} {s s' : Unit} {v : SVal}
    (h : Semantics.Tm.Eval instr env a s v s') :
    ∀ {env' : Env WVal} {ρ : Nat → Nat}, (∀ i, Tm.mentions i a = true → env' (ρ i) = env i) →
      Semantics.Tm.Eval instr env' (a.rename ρ) s v s' := by
  induction h with
  | var =>
      intro env' ρ hρ
      exact .var_of_eq (hρ _ (by simp [Tm.mentions]))
  | op _ step ih =>
      intro env' ρ hρ
      exact .op (ih fun i hi => hρ i (by simpa [Tm.mentions] using hi)) step
  | let₁ _ _ ih₁ ih₂ =>
      intro env' ρ hρ
      exact .let₁ (ih₁ fun i hi => hρ i (by simp [Tm.mentions, hi]))
        (ih₂ (lift_ok (fun i hi => hρ i (by simp [Tm.mentions, hi])) _))
  | unit => intro _ _ _; exact .unit
  | pair _ _ ih₁ ih₂ =>
      intro env' ρ hρ
      exact .pair (ih₁ fun i hi => hρ i (by simp [Tm.mentions, hi]))
        (ih₂ fun i hi => hρ i (by simp [Tm.mentions, hi]))
  | let₂ _ _ ih₁ ih₂ =>
      intro env' ρ hρ
      exact .let₂ (ih₁ fun i hi => hρ i (by simp [Tm.mentions, hi]))
        (ih₂ (lift_ok (P := fun i => Tm.mentions i _ = true)
          (lift_ok (P := fun i => Tm.mentions (i + 1) _ = true)
            (fun i hi => hρ i (by simp [Tm.mentions, hi])) _) _))
  | inl _ ih => intro env' ρ hρ; exact .inl (ih fun i hi => hρ i (by simpa [Tm.mentions] using hi))
  | inr _ ih => intro env' ρ hρ; exact .inr (ih fun i hi => hρ i (by simpa [Tm.mentions] using hi))
  | case_inl _ _ ih₁ ih₂ =>
      intro env' ρ hρ
      exact .case_inl (ih₁ fun i hi => hρ i (by simp [Tm.mentions, hi]))
        (ih₂ (lift_ok (fun i hi => hρ i (by simp [Tm.mentions, hi])) _))
  | case_inr _ _ ih₁ ih₂ =>
      intro env' ρ hρ
      exact .case_inr (ih₁ fun i hi => hρ i (by simp [Tm.mentions, hi]))
        (ih₂ (lift_ok (fun i hi => hρ i (by simp [Tm.mentions, hi])) _))

theorem Region.Eval.rename_mentions {env : Env WVal} {r : Region Prim} {s s' : Unit} {l : Nat}
    {v : SVal} (h : Semantics.Region.Eval instr env r s l v s') :
    ∀ {env' : Env WVal} {ρ : Nat → Nat}, (∀ i, Region.mentions i r = true → env' (ρ i) = env i) →
      Semantics.Region.Eval instr env' (r.renameVars ρ) s l v s' := by
  induction h using Semantics.Region.Eval.rec
      (motive_2 := fun env _ blocks first initial s label value s' _ =>
        ∀ {env' : Env WVal} {ρ : Nat → Nat},
          (∀ i, (∃ j, Region.mentions (i + 1) (blocks j) = true) → env' (ρ i) = env i) →
          Semantics.Region.Follow instr env' (fun i => (blocks i).renameVars (lift ρ))
            first initial s label value s') with
  | br arg =>
      intro env' ρ hρ
      exact .br (Tm.Eval.rename_mentions arg fun i hi => hρ i (by simpa [Region.mentions] using hi))
  | let₁ arg _ ih =>
      intro env' ρ hρ
      exact .let₁ (Tm.Eval.rename_mentions arg fun i hi => hρ i (by simp [Region.mentions, hi]))
        (ih (lift_ok (fun i hi => hρ i (by simp [Region.mentions, hi])) _))
  | let₂ arg _ ih =>
      intro env' ρ hρ
      exact .let₂ (Tm.Eval.rename_mentions arg fun i hi => hρ i (by simp [Region.mentions, hi]))
        (ih (lift_ok (P := fun i => Region.mentions i _ = true)
          (lift_ok (P := fun i => Region.mentions (i + 1) _ = true)
            (fun i hi => hρ i (by simp [Region.mentions, hi])) _) _))
  | case_inl arg _ ih =>
      intro env' ρ hρ
      exact .case_inl (Tm.Eval.rename_mentions arg fun i hi => hρ i (by simp [Region.mentions, hi]))
        (ih (lift_ok (fun i hi => hρ i (by simp [Region.mentions, hi])) _))
  | case_inr arg _ ih =>
      intro env' ρ hρ
      exact .case_inr (Tm.Eval.rename_mentions arg fun i hi => hρ i (by simp [Region.mentions, hi]))
        (ih (lift_ok (fun i hi => hρ i (by simp [Region.mentions, hi])) _))
  | cfg _ _ ihEntry ihFollow =>
      intro env' ρ hρ
      refine .cfg (ihEntry fun i hi => hρ i (by simp [Region.mentions, hi])) (ihFollow ?_)
      rintro i ⟨j, hj⟩
      refine hρ i ?_
      simp only [Region.mentions, Bool.or_eq_true, List.any_eq_true]
      exact .inr ⟨j, List.mem_finRange j, hj⟩
  | exit outside => exact .exit outside
  | step inside _ _ ihHead ihTail hρ =>
      exact .step inside (ihHead (lift_ok (fun i hi => hρ i ⟨_, hi⟩) _)) (ihTail hρ)

/-! ## Dead bindings -/

/-- Dead-binding elimination at a `let₁`: the binding is kept, or it is unused
in the eliminated body, which then runs one variable lower. -/
private theorem dce_let₁_sound {env : Env WVal} {a : Tm Prim} {b : Region Prim} {s s₁ s₂ : Unit}
    {l : Nat} {va v : SVal} (arg : Semantics.Tm.Eval instr env a s va s₁)
    (ih : Semantics.Region.Eval instr (extend env va) (dce b) s₁ l v s₂) :
    Semantics.Region.Eval instr env (dce (.let₁ a b)) s l v s₂ := by
  simp only [dce]
  split
  · exact .let₁ arg ih
  next hm =>
    split
    · refine Region.Eval.rename_mentions ih fun i hi => ?_
      cases i with
      | zero => exact absurd hi hm
      | succ i => rfl
    · exact .let₁ arg ih

/-- Dead-binding elimination at a `let₂` of a pair. -/
private theorem dce_let₂_sound {env : Env WVal} {a : Tm Prim} {b : Region Prim} {s s₁ s₂ : Unit}
    {l : Nat} {va vb v : SVal} (arg : Semantics.Tm.Eval instr env a s (.pair va vb) s₁)
    (ih : Semantics.Region.Eval instr (extend (extend env va) vb) (dce b) s₁ l v s₂) :
    Semantics.Region.Eval instr env (dce (.let₂ a b)) s l v s₂ := by
  simp only [dce]
  split
  · exact .let₂ arg ih
  next hm =>
    have hm' : ¬Region.mentions 0 (dce b) = true ∧ ¬Region.mentions 1 (dce b) = true := by
      simpa only [Bool.or_eq_true, not_or] using hm
    split
    · split
      · refine Region.Eval.rename_mentions ih fun i hi => ?_
        match i, hi with
        | 0, hi => exact absurd hi hm'.1
        | 1, hi => exact absurd hi hm'.2
        | i + 2, _ => rfl
      · exact .let₂ arg ih
    · exact .let₂ arg ih

theorem dce_sound {env : Env WVal} {r : Region Prim} {s s' : Unit} {l : Nat} {v : SVal}
    (h : Semantics.Region.Eval instr env r s l v s') :
    Semantics.Region.Eval instr env (dce r) s l v s' := by
  induction h using Semantics.Region.Eval.rec
      (motive_2 := fun env _ blocks first initial s label value s' _ =>
        Semantics.Region.Follow instr env (fun i => dce (blocks i)) first initial s label value s')
    with
  | br arg => exact .br arg
  | let₁ arg _ ih => exact dce_let₁_sound arg ih
  | let₂ arg _ ih => exact dce_let₂_sound arg ih
  | case_inl arg _ ih => exact .case_inl arg ih
  | case_inr arg _ ih => exact .case_inr arg ih
  | cfg _ _ ihEntry ihFollow => exact .cfg ihEntry ihFollow
  | exit outside => exact .exit outside
  | step inside _ _ ihHead ihTail => exact .step inside ihHead ihTail

/-! ## Functions -/

theorem simp_run (cfg : SimpCfg) {f : SFunc} {args : List WVal} {o : FOut}
    (h : f.Run args o) : (f.simp cfg).Run args o := by
  obtain ⟨hl, l, v, he, hd⟩ := h
  exact ⟨hl, l, v, simpR_sound cfg he (FactsOK.nil _), hd⟩

theorem dce_run {f : SFunc} {args : List WVal} {o : FOut}
    (h : f.Run args o) : f.dce.Run args o := by
  obtain ⟨hl, l, v, he, hd⟩ := h
  exact ⟨hl, l, v, dce_sound he, hd⟩

theorem run_deterministic {f : SFunc} {args : List WVal} {o₁ o₂ : FOut}
    (h₁ : f.Run args o₁) (h₂ : f.Run args o₂) : o₁ = o₂ := by
  obtain ⟨_, l₁, v₁, he₁, hd₁⟩ := h₁
  obtain ⟨_, l₂, v₂, he₂, hd₂⟩ := h₂
  obtain ⟨rfl, rfl, -⟩ := Semantics.Region.Eval.deterministic instr_deterministic he₁ he₂
  exact Option.some.inj (hd₁.symm.trans hd₂)

end Silmaril.Proofs.Wasm.SSA.Passes
