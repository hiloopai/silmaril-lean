module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.Utf8Mono.Eval
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Type

/-!
# Environment monotonicity of the typing relation across one rebound definition (unrefined)

`Sem.monoTypAt_succ` with the environment changing instead of the fuel, for any `EnvExt e₁ e₂ x₀`:
at every fuel, every member of the typing block (`hasTyp` and its six helpers) answers in `e₂` at
least what it answers in `e₁` (`extMonoTypAt`). The calls out of the block go to the evaluator,
where `extMonoAt` applies; the type tables are the same (`EnvExt.typs`). The proof is round 7's
`Raw/…/Round7/Utf8/MonoTyp.lean` with the two environments abstracted. Kept unrefined, like its
model.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Mono

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Sem.Res

/-- **Monotonicity of the typing block at fuel `n`** (fields as `Sem.MonoTypAt`). -/
structure ExtMonoTypAt (e₁ e₂ : Env) (n : Nat) : Prop where
  typ : ∀ ρ t v, hasTyp n e₁ ρ t v ⊑ hasTyp n e₂ ρ t v
  tup : ∀ ρ bs vs, hasTypTup n e₁ ρ bs vs ⊑ hasTypTup n e₂ ρ bs vs
  list : ∀ ρ t vs, hasTypList n e₁ ρ t vs ⊑ hasTypList n e₂ ρ t vs
  defTyp : ∀ ρ dt v, hasTypDef n e₁ ρ dt v ⊑ hasTypDef n e₂ ρ dt v
  fields : ∀ ρ fs gs, hasTypFields n e₁ ρ fs gs ⊑ hasTypFields n e₂ ρ fs gs
  case : ∀ ρ cs op w, hasTypCase n e₁ ρ cs op w ⊑ hasTypCase n e₂ ρ cs op w
  insts : ∀ insts ws v, hasTypInsts n e₁ insts ws v ⊑ hasTypInsts n e₂ insts ws v

theorem extMonoTypAt_zero (e₁ e₂ : Env) : ExtMonoTypAt e₁ e₂ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros; simp only [hasTyp]; exact Res.oof_le _
  · intros; simp only [hasTypTup]; exact Res.oof_le _
  · intros; simp only [hasTypList]; exact Res.oof_le _
  · intros; simp only [hasTypDef]; exact Res.oof_le _
  · intros; simp only [hasTypFields]; exact Res.oof_le _
  · intros; simp only [hasTypCase]; exact Res.oof_le _
  · intros; simp only [hasTypInsts]; exact Res.oof_le _

/-- **The inductive step**: `Sem.monoTypAt_succ`'s case analysis, with the environment changing
instead of the fuel. -/
theorem extMonoTypAt_succ {e₁ e₂ : Env} {x₀ : IL.Id} (hS : EnvExt e₁ e₂ x₀) (m : Nat)
    (ih : ExtMonoTypAt e₁ e₂ m) : ExtMonoTypAt e₁ e₂ (m + 1) := by
  have hev := extMonoAt hS m
  have premsOk_env : ∀ ρ prems, premsOk m e₁ ρ prems ⊑ premsOk m e₂ ρ prems :=
    fun ρ prems => Res.elimUndef_le (hev.premsHold ρ prems) (fun _ => Res.Le.refl _)
      (fun _ => Res.Le.refl _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- `hasTyp`
  · intro ρ t v
    cases t with
    | boolT => simp only [hasTyp]; exact Res.Le.refl _
    | numT t => simp only [hasTyp]; exact Res.Le.refl _
    | textT => simp only [hasTyp]; exact Res.Le.refl _
    | tupT bs =>
        simp only [hasTyp]
        cases hv : v.asTuple? with
        | none => exact Res.Le.refl _
        | some vs => exact ih.tup _ _ _
    | iterT t it =>
        cases it with
        | opt =>
            simp only [hasTyp]
            cases hv : v.asOpt? with
            | none => exact Res.Le.refl _
            | some o =>
                cases o with
                | none => exact Res.Le.refl _
                | some w => exact ih.typ _ _ _
        | list =>
            simp only [hasTyp]
            cases hv : v.asList? with
            | none => exact Res.Le.refl _
            | some vs => exact ih.list _ _ _
        | list1 =>
            simp only [hasTyp]
            cases hv : v.asList? with
            | none => exact Res.Le.refl _
            | some vs => exact ite_le (Res.Le.refl _) (ih.list _ _ _)
        | listN e x =>
            simp only [hasTyp]
            cases hv : v.asList? with
            | none => exact Res.Le.refl _
            | some vs =>
                refine Res.bind_le (hev.exp _ _) fun kv => ?_
                refine Res.bind_le (Res.Le.refl _) fun k => ?_
                exact iteFalse_le (ih.list _ _ _)
    | varT x args =>
        simp only [hasTyp, hS.typs]
        cases hl : localTyp? ρ x args with
        | some t => exact ih.typ _ _ _
        | none =>
            refine Res.bind_le (Res.Le.refl _) fun td => ?_
            refine Res.bind_le (hev.args _ _) fun ws => ?_
            exact ih.insts _ _ _
  -- `hasTypTup`
  · intro ρ bs vs
    cases bs with
    | nil => cases vs <;> (simp only [hasTypTup]; exact Res.Le.refl _)
    | cons b bs =>
        cases b with
        | mk x t =>
            cases vs with
            | nil => simp only [hasTypTup]; exact Res.Le.refl _
            | cons v vs =>
                simp only [hasTypTup]
                exact Res.bind_le (ih.typ _ _ _) fun _ =>
                  iteFalse_le (ih.tup _ _ _)
  -- `hasTypList`
  · intro ρ t vs
    cases vs with
    | nil => simp only [hasTypList]; exact Res.Le.refl _
    | cons v vs =>
        simp only [hasTypList]
        exact Res.bind_le (ih.typ _ _ _) fun _ => iteFalse_le (ih.list _ _ _)
  -- `hasTypDef`
  · intro ρ dt v
    cases dt with
    | aliasT t => simp only [hasTypDef]; exact ih.typ _ _ _
    | structT fs =>
        simp only [hasTypDef]
        cases hv : v.asStruct? with
        | none => exact Res.Le.refl _
        | some gs => exact ih.fields _ _ _
    | variantT cs =>
        simp only [hasTypDef]
        cases hv : v.asCase? with
        | none => exact Res.Le.refl _
        | some p => exact ih.case _ _ _ _
  -- `hasTypFields`
  · intro ρ fs gs
    cases fs with
    | nil => cases gs <;> (simp only [hasTypFields]; exact Res.Le.refl _)
    | cons f fs =>
        cases f with
        | mk a t qs prems =>
            cases gs with
            | nil => simp only [hasTypFields]; exact Res.Le.refl _
            | cons g gs =>
                obtain ⟨a', w⟩ := g
                simp only [hasTypFields]
                refine iteFalse_le ?_
                refine Res.bind_le (ih.typ _ _ _) fun _ => iteFalse_le ?_
                exact Res.bind_le (premsOk_env _ _) fun _ =>
                  iteFalse_le (ih.fields _ _ _)
  -- `hasTypCase`
  · intro ρ cs op w
    cases cs with
    | nil => simp only [hasTypCase]; exact Res.Le.refl _
    | cons c cs =>
        cases c with
        | mk op' t qs prems =>
            simp only [hasTypCase]
            refine ite_le ?_ (ih.case _ _ _ _)
            refine Res.bind_le (ih.typ _ _ _) fun _ => iteFalse_le ?_
            refine Res.elimUndef_le (bindQuants_le (fun _ _ => hev.exp _ _)
              (fun _ _ _ => ih.typ _ _ _) _ _) (fun o => ?_) (fun _ => Res.Le.refl _)
            cases o with
            | none => exact Res.Le.refl _
            | some ρq => exact premsOk_env _ _
  -- `hasTypInsts`
  · intro insts ws v
    cases insts with
    | nil => simp only [hasTypInsts]; exact Res.Le.refl _
    | cons i insts =>
        cases i with
        | instD qs pats dt =>
            simp only [hasTypInsts]
            exact Res.elimUndef_le (hev.matchArgs _ _ _)
              (fun _ => ih.defTyp _ _ _) (fun _ => ih.insts _ _ _)

/-- **Monotonicity of the typing block**, at every fuel. -/
theorem extMonoTypAt {e₁ e₂ : Env} {x₀ : IL.Id} (hS : EnvExt e₁ e₂ x₀) : ∀ n, ExtMonoTypAt e₁ e₂ n
  | 0 => extMonoTypAt_zero e₁ e₂
  | n + 1 => extMonoTypAt_succ hS n (extMonoTypAt hS n)

end Silmaril.Wasm.SpecTec.Sim20.Utf8Mono
