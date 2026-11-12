module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.RelFree.Eval
public import Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.Thms

/-!
# Relation-free types type alike under any relation table (unrefined)

`TAgreeAt bad env r n`: at fuel `n`, every member of the typing block answers in `withRels env r`
at least what it answers in `env`, on harmless types (`GoodEvs bad (evTyp t)` and its siblings), in
scopes whose definition variables avoid `bad` (`DefsOk`) and whose type variables are bound to
harmless types (`TypsOk`), provided the definitions of `env` outside `bad` and all its types are
harmless (`DefsGood`, `TypsGood`).

The proof is `Round7.TypAgree.tAgreeAt_succ` (`Round7/TypAgree/Agree.lean`) with one invariant
for every type, no value invariant, and the evaluator calls going to `RelFree.agreeAt`. Kept
unrefined, like its model; the equalities are in `Proofs/…/Sim20/RelFreeEq.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.RelFree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Sem.Res
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (Ev evExp evExps evArg evArgs evPrem evPrems evIter evTyp
  evBinds evDefTyp evTFields evTCases evParams evParam evInst bind_le_of elimUndef_le_of mapM_ok_mem
  mem_of_find?)
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (typsPres caseScope_typs bindQuants_typs quantOf_mem
  matchSymV_typs)

variable {bad : List String}

/-! ## Type variables -/

/-- A type argument is harmless. -/
def ArgTyOk (bad : List String) : ArgV → Prop
  | .typ t => GoodEvs bad (evTyp t)
  | _ => True

theorem typsOk_empty : TypsOk bad VarEnv.empty := by
  simp [TypsOk, VarEnv.empty, Map.empty]

theorem typsOk_of_typs {ρ ρ' : VarEnv} (h : TypsOk bad ρ) (he : ρ'.typs = ρ.typs) :
    TypsOk bad ρ' := by
  intro p hp; rw [he] at hp; exact h p hp

theorem typsOk_bindVal {ρ : VarEnv} (h : TypsOk bad ρ) (x : IL.Id) (v : Value) :
    TypsOk bad (ρ.bindVal x v) := h

theorem typsOk_bindTyp {ρ : VarEnv} (h : TypsOk bad ρ) (x : IL.Id) {t : Typ}
    (ht : GoodEvs bad (evTyp t)) : TypsOk bad (ρ.bindTyp x t) := by
  intro p hp
  simp only [VarEnv.bindTyp, Map.bind] at hp
  split at hp
  · exact h p hp
  · rcases List.mem_cons.1 hp with rfl | hp
    · exact ht
    · exact h p hp

theorem matchTypV_typsOk {env : Env} {ρ ρ' : VarEnv} {pat t : Typ}
    (h : TypsOk bad ρ) (ht : GoodEvs bad (evTyp t)) (hm : matchTypV env ρ pat t = .ok ρ') :
    TypsOk bad ρ' := by
  unfold matchTypV at hm
  repeat (first | (split at hm) | (cases hm; exact h) | (cases hm; exact typsOk_bindTyp h _ ht) |
    (cases hm))

theorem matchArg_typsOk {env : Env} {n : Nat} {ρ ρ' : VarEnv} {a : Arg}
    {w : ArgV} (h : TypsOk bad ρ) (hw : ArgTyOk bad w) (hm : matchArg n env ρ a w = .ok ρ') :
    TypsOk bad ρ' := by
  rcases n with _ | n
  · simp [matchArg] at hm
  cases a <;> cases w <;> simp only [matchArg] at hm
  case expA.val e v =>
    split at hm
    · exact typsOk_of_typs h ((typsPres env n).matchExp _ _ _ _ hm)
    · cases hm
  case typA.typ => exact matchTypV_typsOk h hw hm
  case defA.defName y x => cases hm; exact h
  case gramA.gram => exact typsOk_of_typs h (matchSymV_typs hm)
  all_goals cases hm

theorem matchArgs_typsOk {env : Env} :
    ∀ (n : Nat) {ρ ρ' : VarEnv} {ags : List Arg} {ws : List ArgV}, TypsOk bad ρ →
      (∀ w ∈ ws, ArgTyOk bad w) → matchArgs n env ρ ags ws = .ok ρ' → TypsOk bad ρ'
  | 0, _, _, _, _, _, _, hm => by simp [matchArgs] at hm
  | n + 1, ρ, ρ', ags, ws, h, hw, hm => by
    cases ags with
    | nil => cases ws <;> simp only [matchArgs] at hm <;> cases hm; exact h
    | cons a ags =>
      cases ws with
      | nil => simp only [matchArgs] at hm; cases hm
      | cons w ws =>
        simp only [matchArgs, Res.bind_eq_ok] at hm
        obtain ⟨ρ₁, h₁, h₂⟩ := hm
        exact matchArgs_typsOk n (matchArg_typsOk h (hw w List.mem_cons_self) h₁)
          (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw')) h₂

theorem resolveTyp_ok {ρ : VarEnv} (h : TypsOk bad ρ) {t : Typ}
    (ht : GoodEvs bad (evTyp t)) : GoodEvs bad (evTyp (resolveTyp ρ t)) := by
  unfold resolveTyp
  split
  · rename_i x
    cases hf : ρ.findTyp? x with
    | none => exact ht
    | some t' => exact h (x, t') (mem_of_find? hf)
  · exact ht

/-- **Evaluated type arguments are harmless.** -/
theorem evalArgs_argTyOk {env : Env} {n : Nat} {ρ : VarEnv} {ags : List Arg}
    {ws : List ArgV} (h : TypsOk bad ρ) (hA : GoodEvs bad (evArgs ags))
    (he : evalArgs n env ρ ags = .ok ws) : ∀ w ∈ ws, ArgTyOk bad w := by
  rcases n with _ | n
  · simp [evalArgs] at he
  simp only [evalArgs] at he
  intro w hw
  obtain ⟨a, ha, hfa⟩ := mapM_ok_mem he w hw
  have hGa := goodEvs_args hA a ha
  rcases n with _ | n
  · simp [evalArg] at hfa
  cases a <;> simp only [evalArg] at hfa
  case expA e =>
    obtain ⟨_, _, rfl⟩ := Res.map_eq_ok.1 hfa
    trivial
  case typA t => cases hfa; exact resolveTyp_ok h (by simpa [evArg] using hGa)
  case defA x => cases hfa; trivial
  case gramA => cases hfa; trivial

/-! ## Defining conjuncts of variant cases -/

theorem goodEvs_params : ∀ {qs : List Param}, GoodEvs bad (evParams qs) →
    ∀ x t, Param.expP x t ∈ qs → GoodEvs bad (evTyp t)
  | [], _ => by simp
  | q :: qs, h => by
    simp only [evParams, goodEvs_append] at h
    intro x t hq
    rcases List.mem_cons.1 hq with rfl | hq
    · simpa [evParam] using h.1
    · exact goodEvs_params h.2 x t hq

theorem quantEqs_ok {qs : List Param} {e : Exp} (hG : GoodEvs bad (evExp e)) :
    ∀ d ∈ quantEqs qs e, GoodEvs bad (evExp d.2.2) ∧ Param.expP d.1 d.2.1 ∈ qs := by
  fun_induction quantEqs qs e with
  | case1 τ a b iha ihb =>
    have hG' : GoodEvs bad (evExp a) ∧ GoodEvs bad (evExp b) := by
      simpa only [evExp, goodEvs_append] using hG
    intro d hd
    rcases List.mem_append.1 hd with hd₁ | hd₂
    · exact iha hG'.1 d hd₁
    · exact ihb hG'.2 d hd₂
  | case2 τ a b x t hq =>
    have hG' : GoodEvs bad (evExp a) ∧ GoodEvs bad (evExp b) := by
      simpa only [evExp, goodEvs_append] using hG
    intro d hd
    have hd' : d = (x, t, a) := List.mem_singleton.1 hd
    rw [hd']
    exact ⟨hG'.1, quantOf_mem hq⟩
  | case3 τ a b _ x t hq =>
    have hG' : GoodEvs bad (evExp a) ∧ GoodEvs bad (evExp b) := by
      simpa only [evExp, goodEvs_append] using hG
    intro d hd
    have hd' : d = (x, t, b) := List.mem_singleton.1 hd
    rw [hd']
    exact ⟨hG'.2, quantOf_mem hq⟩
  | case4 => intro d hd; simp at hd
  | case5 => intro d hd; simp at hd

theorem quantDefs_ok {qs : List Param} {prems : List Prem}
    (hG : GoodEvs bad (evPrems prems)) (hq : GoodEvs bad (evParams qs)) :
    ∀ d ∈ quantDefs qs prems, GoodEvs bad (evExp d.2.2) ∧ GoodEvs bad (evTyp d.2.1) := by
  intro d hd
  simp only [quantDefs, List.mem_flatMap] at hd
  obtain ⟨pr, hpr, hd⟩ := hd
  have hGpr := goodEvs_prems hG pr hpr
  cases pr with
  | ifPr e =>
    simp only [evPrem] at hGpr
    obtain ⟨h₁, h₂⟩ := quantEqs_ok hGpr d hd
    exact ⟨h₁, goodEvs_params hq _ _ h₂⟩
  | rulePr _ _ _ _ => simp at hd
  | letPr _ _ => simp at hd
  | elsePr => simp at hd
  | iterPr _ _ => simp at hd

/-! ## The agreement -/

variable (bad) (env : Env) (r : Map RelDef)

/-- **Environment monotonicity of the typing block in the relation table at fuel `n`**, on
harmless types. -/
structure TAgreeAt (n : Nat) : Prop where
  typ : ∀ ρ t v, DefsOk bad ρ → TypsOk bad ρ → GoodEvs bad (evTyp t) →
    hasTyp n env ρ t v ⊑ hasTyp n (withRels env r) ρ t v
  tup : ∀ ρ bs vs, DefsOk bad ρ → TypsOk bad ρ → GoodEvs bad (evBinds bs) →
    hasTypTup n env ρ bs vs ⊑ hasTypTup n (withRels env r) ρ bs vs
  list : ∀ ρ t vs, DefsOk bad ρ → TypsOk bad ρ → GoodEvs bad (evTyp t) →
    hasTypList n env ρ t vs ⊑ hasTypList n (withRels env r) ρ t vs
  defTyp : ∀ ρ dt v, DefsOk bad ρ → TypsOk bad ρ → GoodEvs bad (evDefTyp dt) →
    hasTypDef n env ρ dt v ⊑ hasTypDef n (withRels env r) ρ dt v
  fields : ∀ ρ fs gs, DefsOk bad ρ → TypsOk bad ρ → GoodEvs bad (evTFields fs) →
    hasTypFields n env ρ fs gs ⊑ hasTypFields n (withRels env r) ρ fs gs
  case : ∀ ρ cs op w, DefsOk bad ρ → TypsOk bad ρ → GoodEvs bad (evTCases cs) →
    hasTypCase n env ρ cs op w ⊑ hasTypCase n (withRels env r) ρ cs op w
  insts : ∀ insts ws v, (∀ w ∈ ws, ArgOk bad w) → (∀ w ∈ ws, ArgTyOk bad w) →
    (∀ i ∈ insts, GoodEvs bad (evInst i)) →
    hasTypInsts n env insts ws v ⊑ hasTypInsts n (withRels env r) insts ws v

theorem tAgreeAt_zero : TAgreeAt bad env r 0 := by
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
theorem bindQuants_le_rf (m : Nat) (hev : AgreeAt bad env r m)
    (hQ : ∀ ρ t v, DefsOk bad ρ → TypsOk bad ρ → GoodEvs bad (evTyp t) →
      hasTyp m env ρ t v ⊑ hasTyp m (withRels env r) ρ t v) :
    ∀ ρ ds, DefsOk bad ρ → TypsOk bad ρ →
      (∀ d ∈ ds, GoodEvs bad (evExp d.2.2) ∧ GoodEvs bad (evTyp d.2.1)) →
      bindQuants (fun ρ e => evalExp m env ρ e) (fun ρ t v => hasTyp m env ρ t v) ρ ds ⊑
        bindQuants (fun ρ e => evalExp m (withRels env r) ρ e)
          (fun ρ t v => hasTyp m (withRels env r) ρ t v) ρ ds
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
theorem tAgreeAt_succ (hDG : DefsGood bad env) (hTG : TypsGood bad env) (m : Nat)
    (ih : TAgreeAt bad env r m) : TAgreeAt bad env r (m + 1) := by
  have hev := agreeAt bad env r hDG m
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
            refine elimUndef_le_of (bindQuants_le_rf bad env r m hev ih.typ _ _
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

/-- **Harmless types type in `withRels env r` at least as in `env`**, at every fuel. -/
theorem tAgreeAt (hDG : DefsGood bad env) (hTG : TypsGood bad env) : ∀ n, TAgreeAt bad env r n
  | 0 => tAgreeAt_zero bad env r
  | n + 1 => tAgreeAt_succ bad env r hDG hTG n (tAgreeAt hDG hTG n)

end Silmaril.Wasm.SpecTec.Sim20.RelFree
