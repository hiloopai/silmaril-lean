module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.Utf8.Mono

/-!
# Round 7: environment monotonicity of the typing relation, `simEnv B` to `utf8Env B` (unrefined)

`Sem.monoTypAt_succ` with the environment changing instead of the fuel: at every fuel, every
member of the typing block (`hasTyp` and its six helpers) answers in `utf8Env B` at least what it
answers in `simEnv B` (`envMonoTypAt`). The calls out of the block go to the evaluator, where
`envMonoAt` applies. The proof is a copy of `Sem.monoTypAt_succ` (in
`Raw/…/SpecTec/Sem/Type.lean`). Consequences, in `Proofs/…/Round7/Utf8/MonoDerive.lean`:
`hasTyp_utf8Env` (`HasTyp`), `typedV_utf8Env` (`TypedV`) and `quantsOk_utf8Env` (`QuantsOk`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Sem.Res

variable (B : Builtins)

/-- **Environment monotonicity of the typing block at fuel `n`** (fields as `Sem.MonoTypAt`). -/
structure EnvMonoTypAt (n : Nat) : Prop where
  typ : ∀ ρ t v, hasTyp n (simEnv B) ρ t v ⊑ hasTyp n (utf8Env B) ρ t v
  tup : ∀ ρ bs vs, hasTypTup n (simEnv B) ρ bs vs ⊑ hasTypTup n (utf8Env B) ρ bs vs
  list : ∀ ρ t vs, hasTypList n (simEnv B) ρ t vs ⊑ hasTypList n (utf8Env B) ρ t vs
  defTyp : ∀ ρ dt v, hasTypDef n (simEnv B) ρ dt v ⊑ hasTypDef n (utf8Env B) ρ dt v
  fields : ∀ ρ fs gs, hasTypFields n (simEnv B) ρ fs gs ⊑ hasTypFields n (utf8Env B) ρ fs gs
  case : ∀ ρ cs op w, hasTypCase n (simEnv B) ρ cs op w ⊑ hasTypCase n (utf8Env B) ρ cs op w
  insts : ∀ insts ws v, hasTypInsts n (simEnv B) insts ws v ⊑ hasTypInsts n (utf8Env B) insts ws v

theorem envMonoTypAt_zero : EnvMonoTypAt B 0 := by
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
theorem envMonoTypAt_succ (hB : ∀ ws, B.call "utf8" ws = none) (m : Nat)
    (ih : EnvMonoTypAt B m) : EnvMonoTypAt B (m + 1) := by
  have hev := envMonoAt B hB m
  have premsOk_env : ∀ ρ prems, premsOk m (simEnv B) ρ prems ⊑ premsOk m (utf8Env B) ρ prems :=
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
        simp only [hasTyp, findTyp?_utf8Env]
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

/-- **Environment monotonicity of the typing block**, at every fuel. -/
theorem envMonoTypAt (hB : ∀ ws, B.call "utf8" ws = none) : ∀ n, EnvMonoTypAt B n
  | 0 => envMonoTypAt_zero B
  | n + 1 => envMonoTypAt_succ B hB n (envMonoTypAt hB n)

end Silmaril.Wasm.SpecTec.Sim.Round7
