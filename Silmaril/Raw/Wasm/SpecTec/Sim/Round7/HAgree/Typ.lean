module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HAgree.Basic

/-!
# Round 7, memory SIMD: away from `$vbytes_`, `simEnv B₁` types no more than `simEnv B₂` (unrefined)

The typing half of the declarative `$vbytes_` transfer. For builtins `B₁`, `B₂` that agree off
`$vbytes_` (`VAgree.AgreeOff`), at every fuel, every member of the typing block answers in
`simEnv B₂` at least what it answers in `simEnv B₁` (`TAgreeAt`), provided the type is `RG` (every
reference is reachable from `Step` and none is `$vbytes_`, `Step` or `Step_read`), the scope's
definition variables are `GoodName` (`VAgree.DefsOk`) and its type variables are bound to `RG`
types (`TypsG`).

The proof is `Round7.TypAgree.tAgreeAt_succ` (the `$utf8` case) with `utf8Env B`/`simEnv B`
replaced by `simEnv B₁`/`simEnv B₂`, the checks `tyOk A S` replaced by `RG`, and no invariant on
values: no type `Step` reaches refers to `$vbytes_`, so no field has to be exempted. Every type
`simEnv B` finds under a reachable name is `RG` by the closure of `stepReach` (`rg_inst`). The
calls out of the typing block go to the evaluator, where `VAgree.agreeAt` applies. Kept
unrefined, like the original; the equalities are in `Proofs/…/Round7/VDecl/TypEq.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Sem.Res
open Round7.Script (Ev evRefs evTyp evExp evArg evArgs evPrem evPrems evParam evParams
  evInst evBinds evDefTyp evTFields evTCases evIter stepReach bind_le_of elimUndef_le_of
  mem_of_find?)

variable (B₁ B₂ : Builtins)

/-- **Reverse environment monotonicity of the typing block at fuel `n`**, on `RG` types. -/
structure TAgreeAt (n : Nat) : Prop where
  typ : ∀ ρ t v, DefsOk ρ → TypsG ρ → RG (evTyp t) →
    hasTyp n (simEnv B₁) ρ t v ⊑ hasTyp n (simEnv B₂) ρ t v
  tup : ∀ ρ bs vs, DefsOk ρ → TypsG ρ → RG (evBinds bs) →
    hasTypTup n (simEnv B₁) ρ bs vs ⊑ hasTypTup n (simEnv B₂) ρ bs vs
  list : ∀ ρ t vs, DefsOk ρ → TypsG ρ → RG (evTyp t) →
    hasTypList n (simEnv B₁) ρ t vs ⊑ hasTypList n (simEnv B₂) ρ t vs
  defTyp : ∀ ρ dt v, DefsOk ρ → TypsG ρ → RG (evDefTyp dt) →
    hasTypDef n (simEnv B₁) ρ dt v ⊑ hasTypDef n (simEnv B₂) ρ dt v
  fields : ∀ ρ fs gs, DefsOk ρ → TypsG ρ → RG (evTFields fs) →
    hasTypFields n (simEnv B₁) ρ fs gs ⊑ hasTypFields n (simEnv B₂) ρ fs gs
  case : ∀ ρ cs op w, DefsOk ρ → TypsG ρ → RG (evTCases cs) →
    hasTypCase n (simEnv B₁) ρ cs op w ⊑ hasTypCase n (simEnv B₂) ρ cs op w
  insts : ∀ insts ws v, (∀ w ∈ ws, ArgOk w) → (∀ w ∈ ws, ArgTyG w) →
    (∀ i ∈ insts, RG (evInst i)) →
    hasTypInsts n (simEnv B₁) insts ws v ⊑ hasTypInsts n (simEnv B₂) insts ws v

theorem tAgreeAt_zero : TAgreeAt B₁ B₂ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intros
  · simp only [hasTyp]; exact Res.oof_le _
  · simp only [hasTypTup]; exact Res.oof_le _
  · simp only [hasTypList]; exact Res.oof_le _
  · simp only [hasTypDef]; exact Res.oof_le _
  · simp only [hasTypFields]; exact Res.oof_le _
  · simp only [hasTypCase]; exact Res.oof_le _
  · simp only [hasTypInsts]; exact Res.oof_le _

/-- `bindQuants` on `RG` defining conjuncts. -/
theorem bindQuants_le_rg (m : Nat) (hev : AgreeAt B₁ B₂ m)
    (hQ : ∀ ρ t v, DefsOk ρ → TypsG ρ → RG (evTyp t) →
      hasTyp m (simEnv B₁) ρ t v ⊑ hasTyp m (simEnv B₂) ρ t v) :
    ∀ ρ ds, DefsOk ρ → TypsG ρ → (∀ d ∈ ds, RG (evExp d.2.2) ∧ RG (evTyp d.2.1)) →
      bindQuants (fun ρ e => evalExp m (simEnv B₁) ρ e) (fun ρ t v => hasTyp m (simEnv B₁) ρ t v)
          ρ ds ⊑
        bindQuants (fun ρ e => evalExp m (simEnv B₂) ρ e) (fun ρ t v => hasTyp m (simEnv B₂) ρ t v)
          ρ ds
  | ρ, ds, hD, hT, hds => by
    induction ds generalizing ρ with
    | nil => simp only [bindQuants]; exact Res.Le.refl _
    | cons d ds ihd =>
      obtain ⟨x, t, e⟩ := d
      have h₀ := hds _ List.mem_cons_self
      simp only [bindQuants]
      refine Res.bind_le (hev.exp ρ e hD (goodEvs_of_rg h₀.1)) fun v =>
        Res.bind_le (hQ ρ t v hD hT h₀.2) fun c => ?_
      cases c
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact Res.Le.refl _
      · exact ihd (ρ.bindVal x v) (defsOk_bindVal hD x v) (typsG_bindVals hT [(x, v)])
          fun d hd => hds d (List.mem_cons_of_mem _ hd)

/-- **The inductive step.** -/
theorem tAgreeAt_succ (hB : AgreeOff B₁ B₂) (m : Nat) (ih : TAgreeAt B₁ B₂ m) :
    TAgreeAt B₁ B₂ (m + 1) := by
  have hev := agreeAt B₁ B₂ hB m
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
        simp only [evTyp, rg_append] at ht
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
            have hGe : GoodEvs (evExp e) := goodEvs_of_rg (by simpa [evIter] using ht.2)
            simp only [hasTyp]
            cases hvl : v.asList? with
            | none => exact Res.Le.refl _
            | some vs =>
                refine Res.bind_le (hev.exp _ _ hD hGe) fun kv => ?_
                refine Res.bind_le (Res.Le.refl _) fun k => ?_
                exact iteFalse_le (ih.list _ _ _ hD hT ht.1)
    | varT x args =>
        simp only [evTyp, rg_cons_ref] at ht
        simp only [hasTyp]
        cases hl : localTyp? ρ x args with
        | some t' =>
            have ht' : RG (evTyp t') := by
              cases args with
              | nil =>
                  simp only [localTyp?] at hl
                  exact hT (x, t') (mem_of_find? hl)
              | cons _ _ => simp [localTyp?] at hl
            exact ih.typ _ _ _ hD hT ht'
        | none =>
            refine bind_le_of (Res.Le.refl _) fun td htd => ?_
            have htd' : (simEnv B₁).findTyp? x = some td := by
              cases hf : (simEnv B₁).findTyp? x with
              | none => rw [hf] at htd; simp [Res.ofOption] at htd
              | some td' => rw [hf] at htd; simp [Res.ofOption] at htd; rw [htd]
            have hGa := goodEvs_of_rg ht.2
            refine bind_le_of (hev.args _ _ hD hGa) fun ws hws => ?_
            exact ih.insts _ _ _ (evalArgs_argOk hD hGa hws) (evalArgs_argTyG hT ht.2 hws)
              (rg_inst htd' ht.1.1)
  -- `hasTypTup`
  · intro ρ bs vs hD hT hbs
    cases bs with
    | nil => cases vs <;> (simp only [hasTypTup]; exact Res.Le.refl _)
    | cons bd bs =>
        cases bd with
        | mk x t =>
            simp only [evBinds, rg_append] at hbs
            cases vs with
            | nil => simp only [hasTypTup]; exact Res.Le.refl _
            | cons v vs =>
                simp only [hasTypTup]
                exact Res.bind_le (ih.typ _ _ _ hD hT hbs.1) fun _ =>
                  iteFalse_le (ih.tup _ _ _ (defsOk_bindVal hD x v) (typsG_bindVals hT [(x, v)])
                    hbs.2)
  -- `hasTypList`
  · intro ρ t vs hD hT ht
    cases vs with
    | nil => simp only [hasTypList]; exact Res.Le.refl _
    | cons v vs =>
        simp only [hasTypList]
        exact Res.bind_le (ih.typ _ _ _ hD hT ht) fun _ =>
          iteFalse_le (ih.list _ _ _ hD hT ht)
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
            simp only [evTFields, rg_append] at hfs
            obtain ⟨⟨⟨hft, -⟩, hpr⟩, hfs⟩ := hfs
            have hGp := goodEvs_of_rg hpr
            cases gs with
            | nil => simp only [hasTypFields]; exact Res.Le.refl _
            | cons g gs =>
                obtain ⟨a', w⟩ := g
                simp only [hasTypFields]
                by_cases haa : a = a'
                · subst haa
                  simp only [↓reduceIte]
                  refine Res.bind_le (ih.typ _ _ _ hD hT hft) fun c => ?_
                  refine iteFalse_le ?_
                  have hcs := TypAgree.caseScope_typs ρ t w
                  refine Res.bind_le (Res.elimUndef_le
                    (hev.premsHold _ _ (defsOk_of_defs hD hcs.2) hGp)
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
            simp only [evTCases, rg_append] at hcs
            obtain ⟨⟨⟨hct, hq⟩, hpr⟩, hcs⟩ := hcs
            have hGp := goodEvs_of_rg hpr
            simp only [hasTypCase]
            refine ite_le ?_ (ih.case _ _ _ _ hD hT hcs)
            refine Res.bind_le (ih.typ _ _ _ hD hT hct) fun _ => iteFalse_le ?_
            have hcsc := TypAgree.caseScope_typs ρ t w
            refine elimUndef_le_of (bindQuants_le_rg B₁ B₂ m hev ih.typ _ _
              (defsOk_of_defs hD hcsc.2) (typsG_of_typs hT hcsc.1) (quantDefs_rg hpr hq))
              (fun o ho => ?_) (fun _ => Res.Le.refl _)
            cases o with
            | none => exact Res.Le.refl _
            | some ρq =>
                have hq' := TypAgree.bindQuants_typs _ _ _ ho
                exact Res.elimUndef_le
                  (hev.premsHold _ _ (defsOk_of_defs (defsOk_of_defs hD hcsc.2) hq'.2) hGp)
                  (fun _ => Res.Le.refl _) (fun _ => Res.Le.refl _)
  -- `hasTypInsts`
  · intro insts ws v hW hWT hins
    cases insts with
    | nil => simp only [hasTypInsts]; exact Res.Le.refl _
    | cons i insts =>
        cases i with
        | instD qs pats dt =>
            have hi := hins _ List.mem_cons_self
            simp only [evInst, rg_append] at hi
            have hGp := goodEvs_of_rg hi.1.2
            simp only [hasTypInsts]
            exact elimUndef_le_of (hev.matchArgs _ _ _ defsOk_empty hGp hW)
              (fun ρ' h' => ih.defTyp _ _ _ (matchArgs_defsOk m defsOk_empty hW h')
                (matchArgs_typsG m typsG_empty hWT h') hi.2)
              (fun _ => ih.insts _ _ _ hW hWT fun j hj => hins j (List.mem_cons_of_mem _ hj))

/-- **The agreement of the typing block, at every fuel.** -/
theorem tAgreeAt (hB : AgreeOff B₁ B₂) : ∀ n, TAgreeAt B₁ B₂ n
  | 0 => tAgreeAt_zero B₁ B₂
  | n + 1 => tAgreeAt_succ B₁ B₂ hB n (tAgreeAt hB n)

end Silmaril.Wasm.SpecTec.Sim.Round7.HAgree
