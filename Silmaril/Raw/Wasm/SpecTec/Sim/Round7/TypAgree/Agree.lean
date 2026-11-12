module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.TypAgree.Basic
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.Script.Agree

/-!
# Round 7: away from `name`, `utf8Env B` types no more than `simEnv B` (unrefined)

`Round7.envMonoTypAt` shows that `utf8Env B` types at least what `simEnv B` types. This file
proves the converse on checked types (`TAgreeAt`): at every fuel, every member of the typing
block answers in `simEnv B` at least what it answers in `utf8Env B`, provided

* the type is over the names `S` (`tyOk A S t`), with type arguments over `A`;
* the scope's definition variables are `GoodName` (`DefsOk`) and its type variables are bound to
  types over `A` (`TypsOk A ρ`);
* the value satisfies `P`, where `P` passes to the parts typing looks at, and with `b` a record's
  `EXPORTS` field is `[]` (`ValInv b P`).

The proof is `Round7.envMonoTypAt_succ` with the two environments exchanged and these invariants
threaded through (`tAgreeAt_succ`). The calls out of the typing block go to the evaluator, where
pass 7's `Round7.Script.agreeAt` applies. A record field named `EXPORTS` is the one place where
the type is not checked: with `b`, the value there is `[]`, and the two environments type `[]` at
a list type alike (`hasTyp_listNil`). Variant-case quantifiers are typed over `A` at computed
values, so the step takes the agreement over `A` at every value as a hypothesis (`hQ`).

Two instances: `tAgreeAt_A` (`tyA`, every value) and `tAgreeAt_B` (`tyB`, `ExpFree` values).
Kept unrefined, like `Round7/Utf8/MonoTyp.lean`; the equalities are in
`Proofs/…/Round7/TypAgree/Eq.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Sem.Res
open Silmaril.Wasm.SpecTec.Sim.Round7
open Silmaril.Wasm.SpecTec.Sim.Round7.Script

variable (B : Builtins)

/-- **Reverse environment monotonicity of the typing block at fuel `n`**, on checked inputs. -/
structure TAgreeAt (A S : List String) (b : Bool) (P : Value → Prop) (n : Nat) : Prop where
  typ : ∀ ρ t v, DefsOk ρ → TypsOk A ρ → tyOk A S t = true → P v →
    hasTyp n (utf8Env B) ρ t v ⊑ hasTyp n (simEnv B) ρ t v
  tup : ∀ ρ bs vs, DefsOk ρ → TypsOk A ρ → bindsOk A S bs = true → (∀ v ∈ vs, P v) →
    hasTypTup n (utf8Env B) ρ bs vs ⊑ hasTypTup n (simEnv B) ρ bs vs
  list : ∀ ρ t vs, DefsOk ρ → TypsOk A ρ → tyOk A S t = true → (∀ v ∈ vs, P v) →
    hasTypList n (utf8Env B) ρ t vs ⊑ hasTypList n (simEnv B) ρ t vs
  defTyp : ∀ ρ dt v, DefsOk ρ → TypsOk A ρ → defTypOk A S b dt = true → P v →
    hasTypDef n (utf8Env B) ρ dt v ⊑ hasTypDef n (simEnv B) ρ dt v
  fields : ∀ ρ fs gs, DefsOk ρ → TypsOk A ρ → fieldsOk A S b fs = true → (∀ p ∈ gs, P p.2) →
    (b = true → ∀ p ∈ gs, p.1 = "EXPORTS" → p.2 = .list []) →
    hasTypFields n (utf8Env B) ρ fs gs ⊑ hasTypFields n (simEnv B) ρ fs gs
  case : ∀ ρ cs op w, DefsOk ρ → TypsOk A ρ → casesOk A S cs = true → P w →
    hasTypCase n (utf8Env B) ρ cs op w ⊑ hasTypCase n (simEnv B) ρ cs op w
  insts : ∀ insts ws v, (∀ w ∈ ws, ArgOk w) → (∀ w ∈ ws, ArgTyOk A w) →
    instsOk A S b insts = true → P v →
    hasTypInsts n (utf8Env B) insts ws v ⊑ hasTypInsts n (simEnv B) insts ws v

theorem tAgreeAt_zero (A S : List String) (b : Bool) (P : Value → Prop) : TAgreeAt B A S b P 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intros
  · simp only [hasTyp]; exact Res.oof_le _
  · simp only [hasTypTup]; exact Res.oof_le _
  · simp only [hasTypList]; exact Res.oof_le _
  · simp only [hasTypDef]; exact Res.oof_le _
  · simp only [hasTypFields]; exact Res.oof_le _
  · simp only [hasTypCase]; exact Res.oof_le _
  · simp only [hasTypInsts]; exact Res.oof_le _

/-- Any two environments type `[]` at a list type alike. -/
theorem hasTyp_listNil (n : Nat) (env₁ env₂ : Env) (ρ : VarEnv) (t : Typ) :
    hasTyp n env₁ ρ (.iterT t .list) (.list []) = hasTyp n env₂ ρ (.iterT t .list) (.list []) := by
  rcases n with _ | _ | n
  · simp only [hasTyp]
  · simp only [hasTyp, Value.asList?, hasTypList]
  · simp only [hasTyp, Value.asList?, hasTypList]

/-- `bindQuants` on checked defining conjuncts. -/
theorem bindQuants_le_inv {A : List String} (m : Nat) (hev : AgreeAt B m)
    (hQ : ∀ ρ t v, DefsOk ρ → TypsOk A ρ → tyOk A A t = true →
      hasTyp m (utf8Env B) ρ t v ⊑ hasTyp m (simEnv B) ρ t v) :
    ∀ ρ ds, DefsOk ρ → TypsOk A ρ → (∀ d ∈ ds, GoodEvs (evExp d.2.2) ∧ tyOk A A d.2.1 = true) →
      bindQuants (fun ρ e => evalExp m (utf8Env B) ρ e) (fun ρ t v => hasTyp m (utf8Env B) ρ t v)
          ρ ds ⊑
        bindQuants (fun ρ e => evalExp m (simEnv B) ρ e) (fun ρ t v => hasTyp m (simEnv B) ρ t v)
          ρ ds
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

theorem typsOk_bindVal {A : List String} {ρ : VarEnv} (h : TypsOk A ρ) (x : IL.Id) (v : Value) :
    TypsOk A (ρ.bindVal x v) := h

/-- **The inductive step.** -/
theorem tAgreeAt_succ {A S : List String} {b : Bool} {P : Value → Prop} (hP : ValInv b P)
    (hAS : ∀ x, A.contains x = true → S.contains x = true)
    (hMap : ∀ x td, S.contains x = true → (simEnv B).findTyp? x = some td →
      instsOk A S b td.2 = true)
    (m : Nat) (ih : TAgreeAt B A S b P m)
    (hQ : ∀ ρ t v, DefsOk ρ → TypsOk A ρ → tyOk A A t = true →
      hasTyp m (utf8Env B) ρ t v ⊑ hasTyp m (simEnv B) ρ t v) :
    TAgreeAt B A S b P (m + 1) := by
  have hev := agreeAt B m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- `hasTyp`
  · intro ρ t v hD hT ht hv
    cases t with
    | boolT => simp only [hasTyp]; exact Res.Le.refl _
    | numT t => simp only [hasTyp]; exact Res.Le.refl _
    | textT => simp only [hasTyp]; exact Res.Le.refl _
    | tupT bs =>
        simp only [tyOk] at ht
        simp only [hasTyp]
        cases hvt : v.asTuple? with
        | none => exact Res.Le.refl _
        | some vs => exact ih.tup _ _ _ hD hT ht (hP.tup v vs hv hvt)
    | iterT t it =>
        simp only [tyOk, Bool.and_eq_true] at ht
        cases it with
        | opt =>
            simp only [hasTyp]
            cases hvo : v.asOpt? with
            | none => exact Res.Le.refl _
            | some o =>
                cases o with
                | none => exact Res.Le.refl _
                | some w => exact ih.typ _ _ _ hD hT ht.1 (hP.opt v w hv hvo)
        | list =>
            simp only [hasTyp]
            cases hvl : v.asList? with
            | none => exact Res.Le.refl _
            | some vs => exact ih.list _ _ _ hD hT ht.1 (hP.list v vs hv hvl)
        | list1 =>
            simp only [hasTyp]
            cases hvl : v.asList? with
            | none => exact Res.Le.refl _
            | some vs => exact ite_le (Res.Le.refl _) (ih.list _ _ _ hD hT ht.1 (hP.list v vs hv hvl))
        | listN e x =>
            have hGe : GoodEvs (evExp e) := by
              have := goodEvs_of_goodEvsB ht.2
              simpa [evIter] using this
            simp only [hasTyp]
            cases hvl : v.asList? with
            | none => exact Res.Le.refl _
            | some vs =>
                refine Res.bind_le (hev.exp _ _ hD hGe) fun kv => ?_
                refine Res.bind_le (Res.Le.refl _) fun k => ?_
                exact iteFalse_le (ih.list _ _ _ hD hT ht.1 (hP.list v vs hv hvl))
    | varT x args =>
        simp only [tyOk, Bool.and_eq_true] at ht
        simp only [hasTyp, findTyp?_utf8Env]
        cases hl : localTyp? ρ x args with
        | some t' =>
            have ht' : tyOk A A t' = true := by
              cases args with
              | nil =>
                  simp only [localTyp?] at hl
                  exact hT (x, t') (mem_of_find? hl)
              | cons _ _ => simp [localTyp?] at hl
            exact ih.typ _ _ _ hD hT (tyOk_mono hAS ht') hv
        | none =>
            refine bind_le_of (Res.Le.refl _) fun td htd => ?_
            have htd' : (simEnv B).findTyp? x = some td := by
              cases hf : (simEnv B).findTyp? x with
              | none => rw [hf] at htd; simp [Res.ofOption] at htd
              | some td' => rw [hf] at htd; simp [Res.ofOption] at htd; rw [htd]
            have hGa := goodEvs_of_argsOk ht.2
            refine bind_le_of (hev.args _ _ hD hGa) fun ws hws => ?_
            exact ih.insts _ _ _ (evalArgs_argOk hD hGa hws) (evalArgs_argTyOk hT ht.2 hws)
              (hMap x td ht.1 htd') hv
  -- `hasTypTup`
  · intro ρ bs vs hD hT hbs hvs
    cases bs with
    | nil => cases vs <;> (simp only [hasTypTup]; exact Res.Le.refl _)
    | cons bd bs =>
        cases bd with
        | mk x t =>
            simp only [bindsOk, Bool.and_eq_true] at hbs
            cases vs with
            | nil => simp only [hasTypTup]; exact Res.Le.refl _
            | cons v vs =>
                simp only [hasTypTup]
                exact Res.bind_le (ih.typ _ _ _ hD hT hbs.1 (hvs v List.mem_cons_self)) fun _ =>
                  iteFalse_le (ih.tup _ _ _ (defsOk_bindVal hD x v) (typsOk_bindVal hT x v) hbs.2
                    fun w hw => hvs w (List.mem_cons_of_mem _ hw))
  -- `hasTypList`
  · intro ρ t vs hD hT ht hvs
    cases vs with
    | nil => simp only [hasTypList]; exact Res.Le.refl _
    | cons v vs =>
        simp only [hasTypList]
        exact Res.bind_le (ih.typ _ _ _ hD hT ht (hvs v List.mem_cons_self)) fun _ =>
          iteFalse_le (ih.list _ _ _ hD hT ht fun w hw => hvs w (List.mem_cons_of_mem _ hw))
  -- `hasTypDef`
  · intro ρ dt v hD hT hdt hv
    cases dt with
    | aliasT t => simp only [defTypOk] at hdt; simp only [hasTypDef]; exact ih.typ _ _ _ hD hT hdt hv
    | structT fs =>
        simp only [defTypOk] at hdt
        simp only [hasTypDef]
        cases hvs : v.asStruct? with
        | none => exact Res.Le.refl _
        | some gs =>
            exact ih.fields _ _ _ hD hT hdt (hP.struct v gs hv hvs)
              fun hb => hP.exps hb v gs hv hvs
    | variantT cs =>
        simp only [defTypOk] at hdt
        simp only [hasTypDef]
        cases hvc : v.asCase? with
        | none => exact Res.Le.refl _
        | some p =>
            obtain ⟨op, w⟩ := p
            exact ih.case _ _ _ _ hD hT hdt (hP.case v op w hv hvc)
  -- `hasTypFields`
  · intro ρ fs gs hD hT hfs hgs hex
    cases fs with
    | nil => cases gs <;> (simp only [hasTypFields]; exact Res.Le.refl _)
    | cons f fs =>
        cases f with
        | mk a t qs prems =>
            simp only [fieldsOk, Bool.and_eq_true] at hfs
            obtain ⟨⟨hft, hpr⟩, hfs⟩ := hfs
            have hGp := goodEvs_of_goodEvsB hpr
            cases gs with
            | nil => simp only [hasTypFields]; exact Res.Le.refl _
            | cons g gs =>
                obtain ⟨a', w⟩ := g
                simp only [hasTypFields]
                by_cases haa : a = a'
                · subst haa
                  simp only [↓reduceIte]
                  have hw : P w := hgs _ List.mem_cons_self
                  have hrest : ∀ c : Bool,
                      (if c = true then
                          (do
                            let hp ← premsOk m (utf8Env B) (caseScope ρ t w) prems
                            if hp = true then hasTypFields m (utf8Env B) ρ fs gs else .ok false)
                        else .ok false) ⊑
                      (if c = true then
                          (do
                            let hp ← premsOk m (simEnv B) (caseScope ρ t w) prems
                            if hp = true then hasTypFields m (simEnv B) ρ fs gs else .ok false)
                        else .ok false) := by
                    intro c
                    refine iteFalse_le ?_
                    have hcs := caseScope_typs ρ t w
                    refine Res.bind_le (Res.elimUndef_le
                      (hev.premsHold _ _ (defsOk_of_defs hD hcs.2) hGp)
                      (fun _ => Res.Le.refl _) (fun _ => Res.Le.refl _)) fun _ => ?_
                    exact iteFalse_le (ih.fields _ _ _ hD hT hfs
                      (fun p hp => hgs p (List.mem_cons_of_mem _ hp))
                      fun hb p hp => hex hb p (List.mem_cons_of_mem _ hp))
                  by_cases hE : b = true ∧ a = "EXPORTS"
                  · obtain ⟨hb, rfl⟩ := hE
                    simp [hb] at hft
                    have hw0 : w = .list [] := hex hb _ List.mem_cons_self rfl
                    subst hw0
                    cases t with
                    | iterT t' it =>
                        cases it with
                        | list =>
                            rw [hasTyp_listNil m (utf8Env B) (simEnv B)]
                            exact Res.bind_le (Res.Le.refl _) hrest
                        | _ => simp [isListT] at hft
                    | _ => simp [isListT] at hft
                  · have hft' : tyOk A S t = true := by simpa [hE] using hft
                    exact Res.bind_le (ih.typ _ _ _ hD hT hft' hw) hrest
                · simp only [haa, ↓reduceIte]
                  exact Res.Le.refl _
  -- `hasTypCase`
  · intro ρ cs op w hD hT hcs hw
    cases cs with
    | nil => simp only [hasTypCase]; exact Res.Le.refl _
    | cons c cs =>
        cases c with
        | mk op' t qs prems =>
            simp only [casesOk, Bool.and_eq_true] at hcs
            obtain ⟨⟨⟨hct, hq⟩, hpr⟩, hcs⟩ := hcs
            have hGp := goodEvs_of_goodEvsB hpr
            simp only [hasTypCase]
            refine ite_le ?_ (ih.case _ _ _ _ hD hT hcs hw)
            refine Res.bind_le (ih.typ _ _ _ hD hT hct hw) fun _ => iteFalse_le ?_
            have hcsc := caseScope_typs ρ t w
            refine elimUndef_le_of (bindQuants_le_inv B m hev hQ _ _ (defsOk_of_defs hD hcsc.2)
              (typsOk_of_typs hT hcsc.1) (quantDefs_ok hGp hq)) (fun o ho => ?_)
              (fun _ => Res.Le.refl _)
            cases o with
            | none => exact Res.Le.refl _
            | some ρq =>
                have hq' := bindQuants_typs _ _ _ ho
                exact Res.elimUndef_le
                  (hev.premsHold _ _ (defsOk_of_defs (defsOk_of_defs hD hcsc.2) hq'.2) hGp)
                  (fun _ => Res.Le.refl _) (fun _ => Res.Le.refl _)
  -- `hasTypInsts`
  · intro insts ws v hW hWT hins hv
    cases insts with
    | nil => simp only [hasTypInsts]; exact Res.Le.refl _
    | cons i insts =>
        cases i with
        | instD qs pats dt =>
            simp only [instsOk, List.all_cons, Bool.and_eq_true] at hins
            obtain ⟨⟨hpats, hdt⟩, hins⟩ := hins
            have hGp := goodEvs_of_goodEvsB hpats
            simp only [hasTypInsts]
            exact elimUndef_le_of (hev.matchArgs _ _ _ defsOk_empty hGp hW)
              (fun ρ' h' => ih.defTyp _ _ _ (matchArgs_defsOk m defsOk_empty hW h')
                (matchArgs_typsOk m (typsOk_empty A) hWT h') hdt hv)
              (fun _ => ih.insts _ _ _ hW hWT hins hv)

/-- **The agreement over `tyA`, at every value.** -/
theorem tAgreeAt_A : ∀ n, TAgreeAt B tyA tyA false (fun _ => True) n
  | 0 => tAgreeAt_zero B _ _ _ _
  | n + 1 => tAgreeAt_succ B valInv_true tyA_sub_tyA (fun _ _ hS h => instsOk_A h hS) n
      (tAgreeAt_A n) fun ρ t v hD hT ht => (tAgreeAt_A n).typ ρ t v hD hT ht trivial

/-- **The agreement over `tyB`, at `ExpFree` values.** -/
theorem tAgreeAt_B : ∀ n, TAgreeAt B tyA tyB true ExpFree n
  | 0 => tAgreeAt_zero B _ _ _ _
  | n + 1 => tAgreeAt_succ B valInv_expFree tyA_sub_tyB (fun _ _ hS h => instsOk_B h hS) n
      (tAgreeAt_B n) fun ρ t v hD hT ht => (tAgreeAt_A B n).typ ρ t v hD hT ht trivial

end Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree
