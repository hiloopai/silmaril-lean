module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.VecTyp.Eval

/-!
# Harmless types type alike under builtins that agree away from `bad` (unrefined)

`TBAgreeAt bad env B' n`: at fuel `n`, every member of the typing block answers in
`env.withBuiltins B'` at least what it answers in `env`, on harmless types, in scopes whose
definition variables avoid `bad` and whose type variables are bound to harmless types, provided
the definitions of `env` outside `bad` and all its types are harmless and `B'` agrees with
`env.builtins` outside `bad` (`BAgree`).

A copy of `RelFree.tAgreeAt_succ` (`Raw/…/Sim20/RelFree/Typ.lean`) with `env.withBuiltins B'` for
`withRels env r` and the evaluator calls going to `VecTyp.bagreeAt`. No case changes: the typing
block reads the builtins only through the evaluator. Kept unrefined, like its model.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecTyp

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Sem.Res
open Silmaril.Wasm.SpecTec.Sim20.RelFree
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (Ev evExp evExps evArg evArgs evPrem evPrems evIter evTyp
  evBinds evDefTyp evTFields evTCases evParams evParam evInst bind_le_of elimUndef_le_of mapM_ok_mem
  mem_of_find?)
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (typsPres caseScope_typs bindQuants_typs quantOf_mem
  matchSymV_typs)

variable (bad) (env : Env) (B' : Builtins)

/-- **Environment monotonicity of the typing block in the builtins at fuel `n`**, on
harmless types. -/
structure TBAgreeAt (n : Nat) : Prop where
  typ : ∀ ρ t v, DefsOk bad ρ → TypsOk bad ρ → GoodEvs bad (evTyp t) →
    hasTyp n env ρ t v ⊑ hasTyp n (env.withBuiltins B') ρ t v
  tup : ∀ ρ bs vs, DefsOk bad ρ → TypsOk bad ρ → GoodEvs bad (evBinds bs) →
    hasTypTup n env ρ bs vs ⊑ hasTypTup n (env.withBuiltins B') ρ bs vs
  list : ∀ ρ t vs, DefsOk bad ρ → TypsOk bad ρ → GoodEvs bad (evTyp t) →
    hasTypList n env ρ t vs ⊑ hasTypList n (env.withBuiltins B') ρ t vs
  defTyp : ∀ ρ dt v, DefsOk bad ρ → TypsOk bad ρ → GoodEvs bad (evDefTyp dt) →
    hasTypDef n env ρ dt v ⊑ hasTypDef n (env.withBuiltins B') ρ dt v
  fields : ∀ ρ fs gs, DefsOk bad ρ → TypsOk bad ρ → GoodEvs bad (evTFields fs) →
    hasTypFields n env ρ fs gs ⊑ hasTypFields n (env.withBuiltins B') ρ fs gs
  case : ∀ ρ cs op w, DefsOk bad ρ → TypsOk bad ρ → GoodEvs bad (evTCases cs) →
    hasTypCase n env ρ cs op w ⊑ hasTypCase n (env.withBuiltins B') ρ cs op w
  insts : ∀ insts ws v, (∀ w ∈ ws, ArgOk bad w) → (∀ w ∈ ws, ArgTyOk bad w) →
    (∀ i ∈ insts, GoodEvs bad (evInst i)) →
    hasTypInsts n env insts ws v ⊑ hasTypInsts n (env.withBuiltins B') insts ws v

theorem tbagreeAt_zero : TBAgreeAt bad env B' 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intros
  · simp only [hasTyp]; exact Res.oof_le _
  · simp only [hasTypTup]; exact Res.oof_le _
  · simp only [hasTypList]; exact Res.oof_le _
  · simp only [hasTypDef]; exact Res.oof_le _
  · simp only [hasTypFields]; exact Res.oof_le _
  · simp only [hasTypCase]; exact Res.oof_le _
  · simp only [hasTypInsts]; exact Res.oof_le _

/-- `bindQuants` on harmless defining conjuncts. -/
theorem bindQuants_le_b (m : Nat) (hev : BAgreeAt bad env B' m)
    (hQ : ∀ ρ t v, DefsOk bad ρ → TypsOk bad ρ → GoodEvs bad (evTyp t) →
      hasTyp m env ρ t v ⊑ hasTyp m (env.withBuiltins B') ρ t v) :
    ∀ ρ ds, DefsOk bad ρ → TypsOk bad ρ →
      (∀ d ∈ ds, GoodEvs bad (evExp d.2.2) ∧ GoodEvs bad (evTyp d.2.1)) →
      bindQuants (fun ρ e => evalExp m env ρ e) (fun ρ t v => hasTyp m env ρ t v) ρ ds ⊑
        bindQuants (fun ρ e => evalExp m (env.withBuiltins B') ρ e)
          (fun ρ t v => hasTyp m (env.withBuiltins B') ρ t v) ρ ds
  | ρ, ds, hD, hT, hds => by
    induction ds generalizing ρ with
    | nil => simp only [bindQuants]; exact Res.Le.refl _
    | cons d ds ihd =>
      obtain ⟨x, t, e⟩ := d
      have h₀ := hds _ List.mem_cons_self
      simp only [bindQuants]
      refine Res.bind_le (hev.exp ρ e hD h₀.1) fun v =>
        Res.bind_le (hQ ρ t v hD hT h₀.2) fun c => ?_
      cases c
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact Res.Le.refl _
      · exact ihd (ρ.bindVal x v) (defsOk_bindVal hD x v) hT
          fun d hd => hds d (List.mem_cons_of_mem _ hd)

/-- **The inductive step.** -/
theorem tbagreeAt_succ (hDG : DefsGood bad env) (hB : BAgree bad env.builtins B') (hTG : TypsGood bad env) (m : Nat)
    (ih : TBAgreeAt bad env B' m) : TBAgreeAt bad env B' (m + 1) := by
  have hev := bagreeAt bad env B' hDG hB m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- `hasTyp`
  · intro ρ t v hD hT ht
    cases t with
    | boolT => simp only [hasTyp]; exact Res.Le.refl _
    | numT t => simp only [hasTyp]; exact Res.Le.refl _
    | textT => simp only [hasTyp]; exact Res.Le.refl _
    | tupT bs =>
        simp only [evTyp] at ht
        simp only [hasTyp]
        cases hvt : v.asTuple? with
        | none => exact Res.Le.refl _
        | some vs => exact ih.tup _ _ _ hD hT ht
    | iterT t it =>
        simp only [evTyp, goodEvs_append] at ht
        cases it with
        | opt =>
            simp only [hasTyp]
            cases hvo : v.asOpt? with
            | none => exact Res.Le.refl _
            | some o =>
                cases o with
                | none => exact Res.Le.refl _
                | some w => exact ih.typ _ _ _ hD hT ht.1
        | list =>
            simp only [hasTyp]
            cases hvl : v.asList? with
            | none => exact Res.Le.refl _
            | some vs => exact ih.list _ _ _ hD hT ht.1
        | list1 =>
            simp only [hasTyp]
            cases hvl : v.asList? with
            | none => exact Res.Le.refl _
            | some vs => exact ite_le (Res.Le.refl _) (ih.list _ _ _ hD hT ht.1)
        | listN e x =>
            have hGe : GoodEvs bad (evExp e) := by simpa [evIter] using ht.2
            simp only [hasTyp]
            cases hvl : v.asList? with
            | none => exact Res.Le.refl _
            | some vs =>
                refine Res.bind_le (hev.exp _ _ hD hGe) fun kv => ?_
                refine Res.bind_le (Res.Le.refl _) fun k => ?_
                exact iteFalse_le (ih.list _ _ _ hD hT ht.1)
    | varT x args =>
        simp only [evTyp, goodEvs_cons] at ht
        simp only [hasTyp]
        cases hl : localTyp? ρ x args with
        | some t' =>
            have ht' : GoodEvs bad (evTyp t') := by
              cases args with
              | nil =>
                  simp only [localTyp?] at hl
                  exact hT (x, t') (mem_of_find? hl)
              | cons _ _ => simp [localTyp?] at hl
            exact ih.typ _ _ _ hD hT ht'
        | none =>
            refine bind_le_of (Res.Le.refl _) fun td htd => ?_
            have htd' : env.findTyp? x = some td := Res.ofOption_eq_ok.1 htd
            refine bind_le_of (hev.args _ _ hD ht.2) fun ws hws => ?_
            exact ih.insts _ _ _ (evalArgs_argOk hD ht.2 hws) (evalArgs_argTyOk hT ht.2 hws)
              (hTG x td htd')
  -- `hasTypTup`
  · intro ρ bs vs hD hT hbs
    cases bs with
    | nil => cases vs <;> (simp only [hasTypTup]; exact Res.Le.refl _)
    | cons bd bs =>
        cases bd with
        | mk x t =>
            simp only [evBinds, goodEvs_append] at hbs
            cases vs with
            | nil => simp only [hasTypTup]; exact Res.Le.refl _
            | cons v vs =>
                simp only [hasTypTup]
                exact Res.bind_le (ih.typ _ _ _ hD hT hbs.1) fun _ =>
                  iteFalse_le (ih.tup _ _ _ (defsOk_bindVal hD x v) (typsOk_bindVal hT x v) hbs.2)
  -- `hasTypList`
  · intro ρ t vs hD hT ht
    cases vs with
    | nil => simp only [hasTypList]; exact Res.Le.refl _
    | cons v vs =>
        simp only [hasTypList]
        exact Res.bind_le (ih.typ _ _ _ hD hT ht) fun _ => iteFalse_le (ih.list _ _ _ hD hT ht)
  -- `hasTypDef`
  · intro ρ dt v hD hT hdt
    cases dt with
    | aliasT t => simp only [evDefTyp] at hdt; simp only [hasTypDef]; exact ih.typ _ _ _ hD hT hdt
    | structT fs =>
        simp only [evDefTyp] at hdt
        simp only [hasTypDef]
        cases hvs : v.asStruct? with
        | none => exact Res.Le.refl _
        | some gs => exact ih.fields _ _ _ hD hT hdt
    | variantT cs =>
        simp only [evDefTyp] at hdt
        simp only [hasTypDef]
        cases hvc : v.asCase? with
        | none => exact Res.Le.refl _
        | some p =>
            obtain ⟨op, w⟩ := p
            exact ih.case _ _ _ _ hD hT hdt
  -- `hasTypFields`
  · intro ρ fs gs hD hT hfs
    cases fs with
    | nil => cases gs <;> (simp only [hasTypFields]; exact Res.Le.refl _)
    | cons f fs =>
        cases f with
        | mk a t qs prems =>
            simp only [evTFields, goodEvs_append] at hfs
            obtain ⟨⟨⟨hft, -⟩, hpr⟩, hfs⟩ := hfs
            cases gs with
            | nil => simp only [hasTypFields]; exact Res.Le.refl _
            | cons g gs =>
                obtain ⟨a', w⟩ := g
                simp only [hasTypFields]
                by_cases haa : a = a'
                · subst haa
                  simp only [↓reduceIte]
                  refine Res.bind_le (ih.typ _ _ _ hD hT hft) fun c => iteFalse_le ?_
                  have hcs := caseScope_typs ρ t w
                  refine Res.bind_le (Res.elimUndef_le
                    (hev.premsHold _ _ (defsOk_of_defs hD hcs.2) hpr)
                    (fun _ => Res.Le.refl _) (fun _ => Res.Le.refl _)) fun _ => ?_
                  exact iteFalse_le (ih.fields _ _ _ hD hT hfs)
                · simp only [haa, ↓reduceIte]
                  exact Res.Le.refl _
  -- `hasTypCase`
  · intro ρ cs op w hD hT hcs
    cases cs with
    | nil => simp only [hasTypCase]; exact Res.Le.refl _
    | cons c cs =>
        cases c with
        | mk op' t qs prems =>
            simp only [evTCases, goodEvs_append] at hcs
            obtain ⟨⟨⟨hct, hq⟩, hpr⟩, hcs⟩ := hcs
            simp only [hasTypCase]
            refine ite_le ?_ (ih.case _ _ _ _ hD hT hcs)
            refine Res.bind_le (ih.typ _ _ _ hD hT hct) fun _ => iteFalse_le ?_
            have hcsc := caseScope_typs ρ t w
            refine elimUndef_le_of (bindQuants_le_b bad env B' m hev ih.typ _ _
              (defsOk_of_defs hD hcsc.2) (typsOk_of_typs hT hcsc.1) (quantDefs_ok hpr hq))
              (fun o ho => ?_) (fun _ => Res.Le.refl _)
            cases o with
            | none => exact Res.Le.refl _
            | some ρq =>
                have hq' := bindQuants_typs _ _ _ ho
                exact Res.elimUndef_le
                  (hev.premsHold _ _ (defsOk_of_defs (defsOk_of_defs hD hcsc.2) hq'.2) hpr)
                  (fun _ => Res.Le.refl _) (fun _ => Res.Le.refl _)
  -- `hasTypInsts`
  · intro insts ws v hW hWT hins
    cases insts with
    | nil => simp only [hasTypInsts]; exact Res.Le.refl _
    | cons i insts =>
        cases i with
        | instD qs pats dt =>
            have hi := hins _ List.mem_cons_self
            simp only [evInst, goodEvs_append] at hi
            simp only [hasTypInsts]
            exact elimUndef_le_of (hev.matchArgs _ _ _ defsOk_empty hi.1.2 hW)
              (fun ρ' h' => ih.defTyp _ _ _ (matchArgs_defsOk m defsOk_empty hW h')
                (matchArgs_typsOk m typsOk_empty hWT h') hi.2)
              (fun _ => ih.insts _ _ _ hW hWT fun i hi => hins i (List.mem_cons_of_mem _ hi))

/-- **Harmless types type in `env.withBuiltins B'` at least as in `env`**, at every fuel. -/
theorem tbagreeAt (hDG : DefsGood bad env) (hB : BAgree bad env.builtins B') (hTG : TypsGood bad env) : ∀ n, TBAgreeAt bad env B' n
  | 0 => tbagreeAt_zero bad env B'
  | n + 1 => tbagreeAt_succ bad env B' hDG hB hTG n (tbagreeAt hDG hB hTG n)

end Silmaril.Wasm.SpecTec.Sim20.VecTyp
