module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8ElseEq
public import Silmaril.Wasm.SpecTec.Sim20.ElseAgree.Thms

/-!
# Types off `bad` type alike across an `EnvExt` pair (unrefined)

`EnvExt e₁ e₂ x₀` with `Clean e₁ x₀`: the two environments have the same type tables, and they
evaluate alike on terms that never reach `x₀` (`Utf8Else.evalExp_eq` and its siblings). Let `bad`
be a set of type names, closed in `e₁` (`ElseAgree.TypOff`), such that every type of `e₁` outside
`bad` never refers to `x₀` (`TypFreeOff`). Then every member of the typing block answers alike in
`e₁` and `e₂`, at every fuel, on types that avoid `bad` and `x₀`, in scopes whose type variables
are bound to such types and whose definition variables avoid `x₀` (`tEqAt`, `hasTyp_iff`).

The proof is `Sim20.ElseAgree.tEqAt_succ` (`Raw/…/Sim20/ElseAgree/Typ.lean`) with the evaluator
equalities restricted to terms that never reach `x₀`: the bound of a `listN` type, the arguments
of a type application, record-field and variant-case premises, defining conjuncts of case
quantifiers and instance patterns. Each is part of the events of the type or of a type
instance, so it is `GoodEvs x₀`. Kept unrefined, like its model.

For the 2.0 script and `$utf8`, `bad` is `badU20`, the types that reach `name`: `name` is the only
type that calls `$utf8`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Else

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Sem.Res
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (Ev evExp evExps evArg evArgs evPrem evPrems evIter
  evTyp evBinds evDefTyp evTFields evTCases evParams evParam evInst mapM_ok_mem mem_of_find?
  matchTypV_defs)
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (typsPres caseScope_typs quantOf_mem matchSymV_typs
  bindQuants_typs)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (tyEvB GoodT TypsOkT ArgTyOkT TypOff goodT_append
  goodT_cons goodT_args typsOkT_empty typsOkT_of_typs matchArgs_typsOkT evalArgs_argTyOkT
  quantDefs_typ bind_congr' elimUndef_congr')
open Silmaril.Wasm.SpecTec.Sim20.Utf8Mono (EnvExt)

variable {x₀ : String}

/-! ## Type variables bound to types that avoid `x₀` -/

/-- Every type variable of `ρ` is bound to a type that never refers to `x₀`. -/
def TypsEv (x₀ : String) (ρ : VarEnv) : Prop := ∀ p ∈ ρ.typs, GoodEvs x₀ (evTyp p.2)

/-- A type argument that never refers to `x₀`. -/
def ArgTyEv (x₀ : String) : ArgV → Prop
  | .typ t => GoodEvs x₀ (evTyp t)
  | _ => True

theorem typsEv_empty : TypsEv x₀ VarEnv.empty := by
  simp [TypsEv, VarEnv.empty, Map.empty]

theorem typsEv_of_typs {ρ ρ' : VarEnv} (h : TypsEv x₀ ρ) (he : ρ'.typs = ρ.typs) :
    TypsEv x₀ ρ' := by
  intro p hp; rw [he] at hp; exact h p hp

theorem typsEv_bindTyp {ρ : VarEnv} (h : TypsEv x₀ ρ) (x : IL.Id) {t : Typ}
    (ht : GoodEvs x₀ (evTyp t)) : TypsEv x₀ (ρ.bindTyp x t) := by
  intro p hp
  simp only [VarEnv.bindTyp, Map.bind] at hp
  split at hp
  · exact h p hp
  · rcases List.mem_cons.1 hp with rfl | hp
    · exact ht
    · exact h p hp

theorem matchTypV_typsEv {env : Env} {ρ ρ' : VarEnv} {pat t : Typ}
    (h : TypsEv x₀ ρ) (ht : GoodEvs x₀ (evTyp t)) (hm : matchTypV env ρ pat t = .ok ρ') :
    TypsEv x₀ ρ' := by
  unfold matchTypV at hm
  repeat (first | (split at hm) | (cases hm; exact h) | (cases hm; exact typsEv_bindTyp h _ ht) |
    (cases hm))

theorem matchArg_typsEv {env : Env} {n : Nat} {ρ ρ' : VarEnv} {a : Arg}
    {w : ArgV} (h : TypsEv x₀ ρ) (hw : ArgTyEv x₀ w) (hm : matchArg n env ρ a w = .ok ρ') :
    TypsEv x₀ ρ' := by
  rcases n with _ | n
  · simp [matchArg] at hm
  cases a <;> cases w <;> simp only [matchArg] at hm
  case expA.val e v =>
    split at hm
    · exact typsEv_of_typs h ((typsPres env n).matchExp _ _ _ _ hm)
    · cases hm
  case typA.typ => exact matchTypV_typsEv h hw hm
  case defA.defName y x => cases hm; exact h
  case gramA.gram => exact typsEv_of_typs h (matchSymV_typs hm)
  all_goals cases hm

theorem matchArgs_typsEv {env : Env} :
    ∀ (n : Nat) {ρ ρ' : VarEnv} {ags : List Arg} {ws : List ArgV}, TypsEv x₀ ρ →
      (∀ w ∈ ws, ArgTyEv x₀ w) → matchArgs n env ρ ags ws = .ok ρ' → TypsEv x₀ ρ'
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
        exact matchArgs_typsEv n (matchArg_typsEv h (hw w List.mem_cons_self) h₁)
          (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw')) h₂

theorem resolveTyp_ev {ρ : VarEnv} (h : TypsEv x₀ ρ) {t : Typ}
    (ht : GoodEvs x₀ (evTyp t)) : GoodEvs x₀ (evTyp (resolveTyp ρ t)) := by
  unfold resolveTyp
  split
  · rename_i x
    cases hf : ρ.findTyp? x with
    | none => exact ht
    | some t' => exact h (x, t') (mem_of_find? hf)
  · exact ht

/-- **Evaluated type arguments avoid `x₀`.** -/
theorem evalArgs_argTyEv {env : Env} {n : Nat} {ρ : VarEnv} {ags : List Arg}
    {ws : List ArgV} (h : TypsEv x₀ ρ) (hA : GoodEvs x₀ (evArgs ags))
    (he : evalArgs n env ρ ags = .ok ws) : ∀ w ∈ ws, ArgTyEv x₀ w := by
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
  case typA t => cases hfa; exact resolveTyp_ev h (by simpa [evArg] using hGa)
  case defA x => cases hfa; trivial
  case gramA => cases hfa; trivial

/-! ## Defining conjuncts of variant cases -/

theorem goodEvs_params : ∀ {qs : List Param}, GoodEvs x₀ (evParams qs) →
    ∀ x t, Param.expP x t ∈ qs → GoodEvs x₀ (evTyp t)
  | [], _ => by simp
  | q :: qs, h => by
    simp only [evParams, goodEvs_append] at h
    intro x t hq
    rcases List.mem_cons.1 hq with rfl | hq
    · simpa [evParam] using h.1
    · exact goodEvs_params h.2 x t hq

theorem quantEqs_ev {qs : List Param} {e : Exp} (hG : GoodEvs x₀ (evExp e)) :
    ∀ d ∈ quantEqs qs e, GoodEvs x₀ (evExp d.2.2) ∧ Param.expP d.1 d.2.1 ∈ qs := by
  fun_induction quantEqs qs e with
  | case1 τ a b iha ihb =>
    have hG' : GoodEvs x₀ (evExp a) ∧ GoodEvs x₀ (evExp b) := by
      simpa only [evExp, goodEvs_append] using hG
    intro d hd
    rcases List.mem_append.1 hd with hd₁ | hd₂
    · exact iha hG'.1 d hd₁
    · exact ihb hG'.2 d hd₂
  | case2 τ a b x t hq =>
    have hG' : GoodEvs x₀ (evExp a) ∧ GoodEvs x₀ (evExp b) := by
      simpa only [evExp, goodEvs_append] using hG
    intro d hd
    have hd' : d = (x, t, a) := List.mem_singleton.1 hd
    rw [hd']
    exact ⟨hG'.1, quantOf_mem hq⟩
  | case3 τ a b _ x t hq =>
    have hG' : GoodEvs x₀ (evExp a) ∧ GoodEvs x₀ (evExp b) := by
      simpa only [evExp, goodEvs_append] using hG
    intro d hd
    have hd' : d = (x, t, b) := List.mem_singleton.1 hd
    rw [hd']
    exact ⟨hG'.2, quantOf_mem hq⟩
  | case4 => intro d hd; simp at hd
  | case5 => intro d hd; simp at hd

/-- The defining conjuncts of a case avoid `x₀`, in their expressions and their types. -/
theorem quantDefs_ev {qs : List Param} {prems : List Prem} (hG : GoodEvs x₀ (evPrems prems))
    (hq : GoodEvs x₀ (evParams qs)) :
    ∀ d ∈ quantDefs qs prems, GoodEvs x₀ (evExp d.2.2) ∧ GoodEvs x₀ (evTyp d.2.1) := by
  intro d hd
  simp only [quantDefs, List.mem_flatMap] at hd
  obtain ⟨pr, hpr, hd⟩ := hd
  have hGpr := goodEvs_prems hG pr hpr
  cases pr with
  | ifPr e =>
    simp only [evPrem] at hGpr
    obtain ⟨h₁, h₂⟩ := quantEqs_ev hGpr d hd
    exact ⟨h₁, goodEvs_params hq _ _ h₂⟩
  | rulePr _ _ _ _ => simp at hd
  | letPr _ _ => simp at hd
  | elsePr => simp at hd
  | iterPr _ _ => simp at hd

/-- `bindQuants` answers alike when its oracles agree on the inputs that occur. -/
theorem bindQuants_offU {bad : List String} {ev₁ ev₂ : VarEnv → Exp → Res Value}
    {ty₁ ty₂ : VarEnv → Typ → Value → Res Bool}
    (hev : ∀ ρ e, DefsOk x₀ ρ → GoodEvs x₀ (evExp e) → ev₁ ρ e = ev₂ ρ e)
    (hty : ∀ ρ t v, DefsOk x₀ ρ → TypsOkT bad ρ → TypsEv x₀ ρ → GoodT bad (evTyp t) →
      GoodEvs x₀ (evTyp t) → ty₁ ρ t v = ty₂ ρ t v) :
    ∀ ρ ds, DefsOk x₀ ρ → TypsOkT bad ρ → TypsEv x₀ ρ → (∀ d ∈ ds, GoodT bad (evTyp d.2.1)) →
      (∀ d ∈ ds, GoodEvs x₀ (evExp d.2.2) ∧ GoodEvs x₀ (evTyp d.2.1)) →
      bindQuants ev₁ ty₁ ρ ds = bindQuants ev₂ ty₂ ρ ds
  | ρ, [], _, _, _, _, _ => by simp only [bindQuants]
  | ρ, (x, t, e) :: ds, hD, hT, hE, hds, hde => by
    simp only [bindQuants]
    have h₀ := hde _ List.mem_cons_self
    rw [hev ρ e hD h₀.1]
    refine bind_congr' fun v _ => ?_
    rw [hty ρ t v hD hT hE (hds _ List.mem_cons_self) h₀.2]
    refine bind_congr' fun b _ => ?_
    cases b
    · rfl
    · exact bindQuants_offU hev hty (ρ.bindVal x v) ds hD hT hE
        (fun d hd => hds d (List.mem_cons_of_mem _ hd))
        fun d hd => hde d (List.mem_cons_of_mem _ hd)

/-! ## The agreement -/

/-- **The types of `e₁` outside `bad` never refer to `x₀`.** -/
def TypFreeOff (bad : List String) (e₁ : Env) (x₀ : String) : Prop :=
  ∀ x td, bad.contains x = false → e₁.findTyp? x = some td → ∀ i ∈ td.2, GoodEvs x₀ (evInst i)

/-- **The typing block of `e₂` answers as that of `e₁` at fuel `n`**, on types off `bad` that
never refer to `x₀`. -/
structure TEqAt (bad : List String) (e₁ e₂ : Env) (x₀ : String) (n : Nat) : Prop where
  typ : ∀ ρ t v, DefsOk x₀ ρ → TypsOkT bad ρ → TypsEv x₀ ρ → GoodT bad (evTyp t) →
    GoodEvs x₀ (evTyp t) → hasTyp n e₂ ρ t v = hasTyp n e₁ ρ t v
  tup : ∀ ρ bs vs, DefsOk x₀ ρ → TypsOkT bad ρ → TypsEv x₀ ρ → GoodT bad (evBinds bs) →
    GoodEvs x₀ (evBinds bs) → hasTypTup n e₂ ρ bs vs = hasTypTup n e₁ ρ bs vs
  list : ∀ ρ t vs, DefsOk x₀ ρ → TypsOkT bad ρ → TypsEv x₀ ρ → GoodT bad (evTyp t) →
    GoodEvs x₀ (evTyp t) → hasTypList n e₂ ρ t vs = hasTypList n e₁ ρ t vs
  defTyp : ∀ ρ dt v, DefsOk x₀ ρ → TypsOkT bad ρ → TypsEv x₀ ρ → GoodT bad (evDefTyp dt) →
    GoodEvs x₀ (evDefTyp dt) → hasTypDef n e₂ ρ dt v = hasTypDef n e₁ ρ dt v
  fields : ∀ ρ fs gs, DefsOk x₀ ρ → TypsOkT bad ρ → TypsEv x₀ ρ → GoodT bad (evTFields fs) →
    GoodEvs x₀ (evTFields fs) → hasTypFields n e₂ ρ fs gs = hasTypFields n e₁ ρ fs gs
  case : ∀ ρ cs op w, DefsOk x₀ ρ → TypsOkT bad ρ → TypsEv x₀ ρ → GoodT bad (evTCases cs) →
    GoodEvs x₀ (evTCases cs) → hasTypCase n e₂ ρ cs op w = hasTypCase n e₁ ρ cs op w
  insts : ∀ insts ws v, (∀ w ∈ ws, ArgOk x₀ w) → (∀ w ∈ ws, ArgTyOkT bad w) →
    (∀ w ∈ ws, ArgTyEv x₀ w) → (∀ i ∈ insts, GoodT bad (evInst i)) →
    (∀ i ∈ insts, GoodEvs x₀ (evInst i)) → hasTypInsts n e₂ insts ws v = hasTypInsts n e₁ insts ws v

variable {bad : List String} {e₁ e₂ : Env}

theorem tEqAt_zero : TEqAt bad e₁ e₂ x₀ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    simp only [hasTyp, hasTypTup, hasTypList, hasTypDef, hasTypFields, hasTypCase, hasTypInsts]

theorem premsOk_eq (hS : EnvExt e₁ e₂ x₀) (hC : Clean e₁ x₀) (n : Nat) {ρ : VarEnv}
    {ps : List Prem} (hD : DefsOk x₀ ρ) (hG : GoodEvs x₀ (evPrems ps)) :
    premsOk n e₂ ρ ps = premsOk n e₁ ρ ps := by
  simp only [premsOk, premsHold_eq hS hC n hD hG]

/-- **The inductive step.** -/
theorem tEqAt_succ (hS : EnvExt e₁ e₂ x₀) (hC : Clean e₁ x₀) (hO : TypOff bad e₁ e₂)
    (hF : TypFreeOff bad e₁ x₀) (m : Nat) (ih : TEqAt bad e₁ e₂ x₀ m) :
    TEqAt bad e₁ e₂ x₀ (m + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- `hasTyp`
  · intro ρ t v hD hT hE ht hte
    cases t with
    | boolT => simp only [hasTyp]
    | numT t => simp only [hasTyp]
    | textT => simp only [hasTyp]
    | tupT bs =>
        simp only [evTyp] at ht hte
        simp only [hasTyp]
        cases v.asTuple? with
        | none => rfl
        | some vs => exact ih.tup _ _ _ hD hT hE ht hte
    | iterT t it =>
        simp only [evTyp, goodT_append] at ht
        simp only [evTyp, goodEvs_append] at hte
        cases it with
        | opt =>
            simp only [hasTyp]
            cases v.asOpt? with
            | none => rfl
            | some o =>
                cases o with
                | none => rfl
                | some w => exact ih.typ _ _ _ hD hT hE ht.1 hte.1
        | list =>
            simp only [hasTyp]
            cases v.asList? with
            | none => rfl
            | some vs => exact ih.list _ _ _ hD hT hE ht.1 hte.1
        | list1 =>
            simp only [hasTyp]
            cases v.asList? with
            | none => rfl
            | some vs => dsimp only; rw [ih.list _ _ _ hD hT hE ht.1 hte.1]
        | listN e x =>
            simp only [evIter] at hte
            simp only [hasTyp]
            cases v.asList? with
            | none => rfl
            | some vs =>
                rw [evalExp_eq hS hC m hD hte.2]
                refine bind_congr' fun kv _ => bind_congr' fun k _ => ?_
                rw [ih.list _ _ _ hD hT hE ht.1 hte.1]
    | varT x args =>
        simp only [evTyp, goodT_cons] at ht
        simp only [evTyp, goodEvs_cons] at hte
        simp only [hasTyp]
        cases hl : localTyp? ρ x args with
        | some t' =>
            have hl' : ρ.findTyp? x = some t' := by
              cases args with
              | nil => simpa only [localTyp?] using hl
              | cons _ _ => simp [localTyp?] at hl
            exact ih.typ _ _ _ hD hT hE (hT (x, t') (mem_of_find? hl'))
              (hE (x, t') (mem_of_find? hl'))
        | none =>
            have hx : bad.contains x = false := by simpa [tyEvB] using ht.1
            rw [hO.find x hx, evalArgs_eq hS hC m hD hte.2]
            refine bind_congr' fun td htd => bind_congr' fun ws hws => ?_
            exact ih.insts _ _ _ (evalArgs_argOk hD hte.2 hws) (evalArgs_argTyOkT hT ht.2 hws)
              (evalArgs_argTyEv hE hte.2 hws) (hO.closed x td hx (Res.ofOption_eq_ok.1 htd))
              (hF x td hx (Res.ofOption_eq_ok.1 htd))
  -- `hasTypTup`
  · intro ρ bs vs hD hT hE hbs hbe
    cases bs with
    | nil => cases vs <;> simp only [hasTypTup]
    | cons bd bs =>
        cases bd with
        | mk x t =>
            simp only [evBinds, goodT_append] at hbs
            simp only [evBinds, goodEvs_append] at hbe
            cases vs with
            | nil => simp only [hasTypTup]
            | cons v vs =>
                simp only [hasTypTup]
                rw [ih.typ _ _ _ hD hT hE hbs.1 hbe.1,
                  ih.tup (ρ.bindVal x v) bs vs hD hT hE hbs.2 hbe.2]
  -- `hasTypList`
  · intro ρ t vs hD hT hE ht hte
    cases vs with
    | nil => simp only [hasTypList]
    | cons v vs =>
        simp only [hasTypList]
        rw [ih.typ _ _ _ hD hT hE ht hte, ih.list _ _ _ hD hT hE ht hte]
  -- `hasTypDef`
  · intro ρ dt v hD hT hE hdt hde
    cases dt with
    | aliasT t =>
        simp only [evDefTyp] at hdt hde
        simp only [hasTypDef]
        exact ih.typ _ _ _ hD hT hE hdt hde
    | structT fs =>
        simp only [evDefTyp] at hdt hde
        simp only [hasTypDef]
        cases v.asStruct? with
        | none => rfl
        | some gs => exact ih.fields _ _ _ hD hT hE hdt hde
    | variantT cs =>
        simp only [evDefTyp] at hdt hde
        simp only [hasTypDef]
        cases v.asCase? with
        | none => rfl
        | some p =>
            obtain ⟨op, w⟩ := p
            exact ih.case _ _ _ _ hD hT hE hdt hde
  -- `hasTypFields`
  · intro ρ fs gs hD hT hE hfs hfe
    cases fs with
    | nil => cases gs <;> simp only [hasTypFields]
    | cons f fs =>
        cases f with
        | mk a t qs prems =>
            simp only [evTFields, goodT_append] at hfs
            simp only [evTFields, goodEvs_append] at hfe
            obtain ⟨⟨⟨hft, -⟩, -⟩, hfs⟩ := hfs
            obtain ⟨⟨⟨hfte, -⟩, hpe⟩, hfe⟩ := hfe
            cases gs with
            | nil => simp only [hasTypFields]
            | cons g gs =>
                obtain ⟨a', w⟩ := g
                simp only [hasTypFields]
                by_cases haa : a = a'
                · simp only [haa, ↓reduceIte]
                  rw [ih.typ _ _ _ hD hT hE hft hfte,
                    premsOk_eq hS hC m (defsOk_of_defs hD (caseScope_typs ρ t w).2) hpe,
                    ih.fields _ _ _ hD hT hE hfs hfe]
                · simp only [haa, ↓reduceIte]
  -- `hasTypCase`
  · intro ρ cs op w hD hT hE hcs hce
    cases cs with
    | nil => simp only [hasTypCase]
    | cons c cs =>
        cases c with
        | mk op' t qs prems =>
            simp only [evTCases, goodT_append] at hcs
            simp only [evTCases, goodEvs_append] at hce
            obtain ⟨⟨⟨hct, hq⟩, -⟩, hcs⟩ := hcs
            obtain ⟨⟨⟨hcte, hqe⟩, hpe⟩, hce⟩ := hce
            simp only [hasTypCase]
            rw [ih.case _ _ _ _ hD hT hE hcs hce, ih.typ _ _ _ hD hT hE hct hcte]
            have hsc := caseScope_typs ρ t w
            have hb := bindQuants_offU (bad := bad)
              (fun ρ e hD' hG => evalExp_eq hS hC m hD' hG) ih.typ
              (caseScope ρ t w) (quantDefs qs prems) (defsOk_of_defs hD hsc.2)
              (typsOkT_of_typs hT hsc.1) (typsEv_of_typs hE hsc.1) (quantDefs_typ hq)
              (quantDefs_ev hpe hqe)
            rw [hb]
            by_cases hop : op' = op
            · simp only [hop, ↓reduceIte]
              refine bind_congr' fun b _ => ?_
              cases b
              · rfl
              · simp only [↓reduceIte]
                refine elimUndef_congr' (fun o ho => ?_) rfl
                cases o with
                | none => rfl
                | some ρq =>
                    have hq' := bindQuants_typs _ _ _ ho
                    exact premsOk_eq hS hC m (defsOk_of_defs (defsOk_of_defs hD hsc.2) hq'.2) hpe
            · simp only [hop, ↓reduceIte]
  -- `hasTypInsts`
  · intro insts ws v hW hWT hWE hins hine
    cases insts with
    | nil => simp only [hasTypInsts]
    | cons i insts =>
        cases i with
        | instD qs pats dt =>
            have hi := hins _ List.mem_cons_self
            have hie := hine _ List.mem_cons_self
            simp only [evInst, goodT_append] at hi
            simp only [evInst, goodEvs_append] at hie
            simp only [hasTypInsts]
            rw [matchArgs_eq hS hC m defsOk_empty hie.1.2 hW]
            refine elimUndef_congr' (fun ρ' h' => ih.defTyp _ _ _
              (matchArgs_defsOk m defsOk_empty hW h') (matchArgs_typsOkT m typsOkT_empty hWT h')
              (matchArgs_typsEv m typsEv_empty hWE h') hi.2 hie.2) ?_
            exact ih.insts _ _ _ hW hWT hWE (fun i hi => hins i (List.mem_cons_of_mem _ hi))
              fun i hi => hine i (List.mem_cons_of_mem _ hi)

/-- **Types off `bad` that never refer to `x₀` type alike**, at every fuel. -/
theorem tEqAt (hS : EnvExt e₁ e₂ x₀) (hC : Clean e₁ x₀) (hO : TypOff bad e₁ e₂)
    (hF : TypFreeOff bad e₁ x₀) : ∀ n, TEqAt bad e₁ e₂ x₀ n
  | 0 => tEqAt_zero
  | n + 1 => tEqAt_succ hS hC hO hF n (tEqAt hS hC hO hF n)

/-- **`HasTyp` off `bad` and `x₀`.** -/
theorem hasTyp_iff (hS : EnvExt e₁ e₂ x₀) (hC : Clean e₁ x₀) (hO : TypOff bad e₁ e₂)
    (hF : TypFreeOff bad e₁ x₀) {ρ : VarEnv} {t : Typ} {v : Value} (hD : DefsOk x₀ ρ)
    (hT : TypsOkT bad ρ) (hE : TypsEv x₀ ρ) (ht : GoodT bad (evTyp t))
    (hte : GoodEvs x₀ (evTyp t)) : HasTyp e₂ ρ t v ↔ HasTyp e₁ ρ t v := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, ((tEqAt hS hC hO hF n).typ ρ t v hD hT hE ht hte).symm.trans hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, ((tEqAt hS hC hO hF n).typ ρ t v hD hT hE ht hte).trans hn⟩

end Silmaril.Wasm.SpecTec.Sim20.Utf8Else
