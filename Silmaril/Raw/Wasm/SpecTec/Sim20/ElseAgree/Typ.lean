module

public import Silmaril.Wasm.SpecTec.Sim20.ElseAgree.Defs
public import Silmaril.Wasm.SpecTec.Sim20.StoreAgree.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.Thms

/-!
# Types off `bad` type alike (unrefined)

`e₁` and `e₂` are environments the evaluator cannot tell apart (`StoreAgree.EnvSame`) whose type
tables agree outside a set `bad` of type names, closed in `e₁` (`TypOff`). Then every member of
the typing block answers alike in `e₁` and `e₂`, at every fuel, on types that avoid `bad`, in
scopes whose type variables are bound to such types (`tEqAt`, `hasTyp_off_iff`).

The proof follows `Sim20.RelFree.tAgreeAt_succ` (`Raw/…/Sim20/RelFree/Typ.lean`) with equality
in place of `Res.Le`, type references in place of relation and definition references, and the
evaluator calls going to `StoreAgree.evalExp_eq` and its siblings. Kept unrefined, like its model.
The use is the `otherwise` premises of `simEnv20S` and `simEnv20T`, with `bad = tbad20`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.ElseAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Sem.Res
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (Ev evExp evExps evArg evArgs evPrem evPrems evIter evTyp
  evBinds evDefTyp evTFields evTCases evParams evParam evInst mapM_ok_mem mem_of_find?)
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (typsPres caseScope_typs quantOf_mem matchSymV_typs)
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (EnvSame evalExp_eq evalArgs_eq matchArgs_eq
  premsHold_eq)

variable {bad : List String}

/-! ## Events -/

@[simp] theorem goodT_nil : GoodT bad [] := by simp [GoodT]

@[simp] theorem goodT_cons {e : Ev} {l : List Ev} :
    GoodT bad (e :: l) ↔ tyEvB bad e = true ∧ GoodT bad l := by
  simp [GoodT]

@[simp] theorem goodT_append {l₁ l₂ : List Ev} :
    GoodT bad (l₁ ++ l₂) ↔ GoodT bad l₁ ∧ GoodT bad l₂ := by
  simp only [GoodT, List.mem_append]
  exact ⟨fun h => ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩,
    fun h e he => he.elim (h.1 e) (h.2 e)⟩

theorem goodT_of_all {l : List Ev} (h : l.all (tyEvB bad) = true) : GoodT bad l :=
  fun e he => List.all_eq_true.1 h e he

theorem goodT_args : ∀ {ags : List Arg}, GoodT bad (evArgs ags) → ∀ a ∈ ags, GoodT bad (evArg a)
  | [], _ => by simp
  | a :: ags, h => by
    simp only [evArgs, goodT_append] at h
    intro a' ha'
    rcases List.mem_cons.1 ha' with rfl | ha'
    · exact h.1
    · exact goodT_args h.2 a' ha'

theorem goodT_params : ∀ {qs : List Param}, GoodT bad (evParams qs) →
    ∀ x t, Param.expP x t ∈ qs → GoodT bad (evTyp t)
  | [], _ => by simp
  | q :: qs, h => by
    simp only [evParams, goodT_append] at h
    intro x t hq
    rcases List.mem_cons.1 hq with rfl | hq
    · simpa [evParam] using h.1
    · exact goodT_params h.2 x t hq

/-! ## Type variables -/

theorem typsOkT_empty : TypsOkT bad VarEnv.empty := by
  simp [TypsOkT, VarEnv.empty, Map.empty]

theorem typsOkT_of_typs {ρ ρ' : VarEnv} (h : TypsOkT bad ρ) (he : ρ'.typs = ρ.typs) :
    TypsOkT bad ρ' := by
  intro p hp; rw [he] at hp; exact h p hp

theorem typsOkT_bindTyp {ρ : VarEnv} (h : TypsOkT bad ρ) (x : IL.Id) {t : Typ}
    (ht : GoodT bad (evTyp t)) : TypsOkT bad (ρ.bindTyp x t) := by
  intro p hp
  simp only [VarEnv.bindTyp, Map.bind] at hp
  split at hp
  · exact h p hp
  · rcases List.mem_cons.1 hp with rfl | hp
    · exact ht
    · exact h p hp

theorem matchTypV_typsOkT {env : Env} {ρ ρ' : VarEnv} {pat t : Typ}
    (h : TypsOkT bad ρ) (ht : GoodT bad (evTyp t)) (hm : matchTypV env ρ pat t = .ok ρ') :
    TypsOkT bad ρ' := by
  unfold matchTypV at hm
  repeat (first | (split at hm) | (cases hm; exact h) | (cases hm; exact typsOkT_bindTyp h _ ht) |
    (cases hm))

theorem matchArg_typsOkT {env : Env} {n : Nat} {ρ ρ' : VarEnv} {a : Arg}
    {w : ArgV} (h : TypsOkT bad ρ) (hw : ArgTyOkT bad w) (hm : matchArg n env ρ a w = .ok ρ') :
    TypsOkT bad ρ' := by
  rcases n with _ | n
  · simp [matchArg] at hm
  cases a <;> cases w <;> simp only [matchArg] at hm
  case expA.val e v =>
    split at hm
    · exact typsOkT_of_typs h ((typsPres env n).matchExp _ _ _ _ hm)
    · cases hm
  case typA.typ => exact matchTypV_typsOkT h hw hm
  case defA.defName y x => cases hm; exact h
  case gramA.gram => exact typsOkT_of_typs h (matchSymV_typs hm)
  all_goals cases hm

theorem matchArgs_typsOkT {env : Env} :
    ∀ (n : Nat) {ρ ρ' : VarEnv} {ags : List Arg} {ws : List ArgV}, TypsOkT bad ρ →
      (∀ w ∈ ws, ArgTyOkT bad w) → matchArgs n env ρ ags ws = .ok ρ' → TypsOkT bad ρ'
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
        exact matchArgs_typsOkT n (matchArg_typsOkT h (hw w List.mem_cons_self) h₁)
          (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw')) h₂

theorem resolveTyp_okT {ρ : VarEnv} (h : TypsOkT bad ρ) {t : Typ}
    (ht : GoodT bad (evTyp t)) : GoodT bad (evTyp (resolveTyp ρ t)) := by
  unfold resolveTyp
  split
  · rename_i x
    cases hf : ρ.findTyp? x with
    | none => exact ht
    | some t' => exact h (x, t') (mem_of_find? hf)
  · exact ht

/-- **Evaluated type arguments avoid `bad`.** -/
theorem evalArgs_argTyOkT {env : Env} {n : Nat} {ρ : VarEnv} {ags : List Arg}
    {ws : List ArgV} (h : TypsOkT bad ρ) (hA : GoodT bad (evArgs ags))
    (he : evalArgs n env ρ ags = .ok ws) : ∀ w ∈ ws, ArgTyOkT bad w := by
  rcases n with _ | n
  · simp [evalArgs] at he
  simp only [evalArgs] at he
  intro w hw
  obtain ⟨a, ha, hfa⟩ := mapM_ok_mem he w hw
  have hGa := goodT_args hA a ha
  rcases n with _ | n
  · simp [evalArg] at hfa
  cases a <;> simp only [evalArg] at hfa
  case expA e =>
    obtain ⟨_, _, rfl⟩ := Res.map_eq_ok.1 hfa
    trivial
  case typA t => cases hfa; exact resolveTyp_okT h (by simpa [evArg] using hGa)
  case defA x => cases hfa; trivial
  case gramA => cases hfa; trivial

/-! ## Defining conjuncts of variant cases -/

theorem quantEqs_mem {qs : List Param} {e : Exp} :
    ∀ d ∈ quantEqs qs e, Param.expP d.1 d.2.1 ∈ qs := by
  fun_induction quantEqs qs e with
  | case1 τ a b iha ihb =>
    intro d hd
    rcases List.mem_append.1 hd with hd₁ | hd₂
    · exact iha d hd₁
    · exact ihb d hd₂
  | case2 τ a b x t hq =>
    intro d hd
    rw [List.mem_singleton.1 hd]
    exact quantOf_mem hq
  | case3 τ a b _ x t hq =>
    intro d hd
    rw [List.mem_singleton.1 hd]
    exact quantOf_mem hq
  | case4 => intro d hd; simp at hd
  | case5 => intro d hd; simp at hd

theorem quantDefs_typ {qs : List Param} {prems : List Prem} (hq : GoodT bad (evParams qs)) :
    ∀ d ∈ quantDefs qs prems, GoodT bad (evTyp d.2.1) := by
  intro d hd
  simp only [quantDefs, List.mem_flatMap] at hd
  obtain ⟨pr, -, hd⟩ := hd
  cases pr with
  | ifPr e => exact goodT_params hq _ _ (quantEqs_mem d hd)
  | rulePr _ _ _ _ => simp at hd
  | letPr _ _ => simp at hd
  | elsePr => simp at hd
  | iterPr _ _ => simp at hd

/-! ## Congruences -/

theorem bind_congr' {α β : Type} {r : Res α} {f₁ f₂ : α → Res β}
    (hf : ∀ a, r = .ok a → f₁ a = f₂ a) : (r >>= f₁) = (r >>= f₂) := by
  cases r with
  | error e => rfl
  | ok a => exact hf a rfl

theorem elimUndef_congr' {α β : Type} {r : Res α} {f₁ f₂ : α → Res β} {g₁ g₂ : Unit → Res β}
    (hf : ∀ a, r = .ok a → f₁ a = f₂ a) (hg : g₁ () = g₂ ()) :
    Res.elimUndef r f₁ g₁ = Res.elimUndef r f₂ g₂ := by
  cases r with
  | error e => cases e <;> simp [Res.elimUndef, hg]
  | ok a => simp [Res.elimUndef, hf a rfl]

theorem ifB_congr {b : Bool} {x₁ x₂ y : Res Bool} (h : x₁ = x₂) :
    (if b then x₁ else y) = (if b then x₂ else y) := by
  rw [h]

/-- `bindQuants` answers alike when its oracles agree on types off `bad`. -/
theorem bindQuants_off {ev₁ ev₂ : VarEnv → Exp → Res Value}
    {ty₁ ty₂ : VarEnv → Typ → Value → Res Bool} (hev : ∀ ρ e, ev₁ ρ e = ev₂ ρ e)
    (hty : ∀ ρ t v, TypsOkT bad ρ → GoodT bad (evTyp t) → ty₁ ρ t v = ty₂ ρ t v) :
    ∀ ρ ds, TypsOkT bad ρ → (∀ d ∈ ds, GoodT bad (evTyp d.2.1)) →
      bindQuants ev₁ ty₁ ρ ds = bindQuants ev₂ ty₂ ρ ds
  | ρ, [], _, _ => by simp only [bindQuants]
  | ρ, (x, t, e) :: ds, hT, hds => by
    simp only [bindQuants]
    rw [hev ρ e]
    refine bind_congr' fun v _ => ?_
    rw [hty ρ t v hT (hds _ List.mem_cons_self)]
    refine bind_congr' fun b _ => ?_
    cases b
    · rfl
    · exact bindQuants_off hev hty (ρ.bindVal x v) ds hT fun d hd => hds d (List.mem_cons_of_mem _ hd)

theorem premsOk_eq' {e₁ e₂ : Env} (hS : EnvSame e₁ e₂) (n : Nat) (ρ : VarEnv) (ps : List Prem) :
    premsOk n e₂ ρ ps = premsOk n e₁ ρ ps := by
  simp only [premsOk, premsHold_eq hS]

/-! ## The agreement -/

variable (bad) (e₁ e₂ : Env)

/-- **The typing block of `e₂` answers as that of `e₁` at fuel `n`**, on types off `bad`. -/
structure TEqAt (n : Nat) : Prop where
  typ : ∀ ρ t v, TypsOkT bad ρ → GoodT bad (evTyp t) → hasTyp n e₂ ρ t v = hasTyp n e₁ ρ t v
  tup : ∀ ρ bs vs, TypsOkT bad ρ → GoodT bad (evBinds bs) →
    hasTypTup n e₂ ρ bs vs = hasTypTup n e₁ ρ bs vs
  list : ∀ ρ t vs, TypsOkT bad ρ → GoodT bad (evTyp t) →
    hasTypList n e₂ ρ t vs = hasTypList n e₁ ρ t vs
  defTyp : ∀ ρ dt v, TypsOkT bad ρ → GoodT bad (evDefTyp dt) →
    hasTypDef n e₂ ρ dt v = hasTypDef n e₁ ρ dt v
  fields : ∀ ρ fs gs, TypsOkT bad ρ → GoodT bad (evTFields fs) →
    hasTypFields n e₂ ρ fs gs = hasTypFields n e₁ ρ fs gs
  case : ∀ ρ cs op w, TypsOkT bad ρ → GoodT bad (evTCases cs) →
    hasTypCase n e₂ ρ cs op w = hasTypCase n e₁ ρ cs op w
  insts : ∀ insts ws v, (∀ w ∈ ws, ArgTyOkT bad w) → (∀ i ∈ insts, GoodT bad (evInst i)) →
    hasTypInsts n e₂ insts ws v = hasTypInsts n e₁ insts ws v

theorem tEqAt_zero : TEqAt bad e₁ e₂ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    simp only [hasTyp, hasTypTup, hasTypList, hasTypDef, hasTypFields, hasTypCase, hasTypInsts]

variable {bad e₁ e₂}

/-- **The inductive step.** -/
theorem tEqAt_succ (hS : EnvSame e₁ e₂) (hO : TypOff bad e₁ e₂) (m : Nat)
    (ih : TEqAt bad e₁ e₂ m) : TEqAt bad e₁ e₂ (m + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- `hasTyp`
  · intro ρ t v hT ht
    cases t with
    | boolT => simp only [hasTyp]
    | numT t => simp only [hasTyp]
    | textT => simp only [hasTyp]
    | tupT bs =>
        simp only [evTyp] at ht
        simp only [hasTyp]
        cases v.asTuple? with
        | none => rfl
        | some vs => exact ih.tup _ _ _ hT ht
    | iterT t it =>
        simp only [evTyp, goodT_append] at ht
        cases it with
        | opt =>
            simp only [hasTyp]
            cases v.asOpt? with
            | none => rfl
            | some o =>
                cases o with
                | none => rfl
                | some w => exact ih.typ _ _ _ hT ht.1
        | list =>
            simp only [hasTyp]
            cases v.asList? with
            | none => rfl
            | some vs => exact ih.list _ _ _ hT ht.1
        | list1 =>
            simp only [hasTyp]
            cases v.asList? with
            | none => rfl
            | some vs => dsimp only; rw [ih.list _ _ _ hT ht.1]
        | listN e x =>
            simp only [hasTyp]
            cases v.asList? with
            | none => rfl
            | some vs =>
                rw [evalExp_eq hS]
                refine bind_congr' fun kv _ => bind_congr' fun k _ => ?_
                rw [ih.list _ _ _ hT ht.1]
    | varT x args =>
        simp only [evTyp, goodT_cons] at ht
        simp only [hasTyp]
        cases hl : localTyp? ρ x args with
        | some t' =>
            have ht' : GoodT bad (evTyp t') := by
              cases args with
              | nil =>
                  simp only [localTyp?] at hl
                  exact hT (x, t') (mem_of_find? hl)
              | cons _ _ => simp [localTyp?] at hl
            exact ih.typ _ _ _ hT ht'
        | none =>
            have hx : bad.contains x = false := by simpa [tyEvB] using ht.1
            rw [hO.find x hx, evalArgs_eq hS]
            refine bind_congr' fun td htd => bind_congr' fun ws hws => ?_
            exact ih.insts _ _ _ (evalArgs_argTyOkT hT ht.2 hws)
              (hO.closed x td hx (Res.ofOption_eq_ok.1 htd))
  -- `hasTypTup`
  · intro ρ bs vs hT hbs
    cases bs with
    | nil => cases vs <;> simp only [hasTypTup]
    | cons bd bs =>
        cases bd with
        | mk x t =>
            simp only [evBinds, goodT_append] at hbs
            cases vs with
            | nil => simp only [hasTypTup]
            | cons v vs =>
                simp only [hasTypTup]
                rw [ih.typ _ _ _ hT hbs.1, ih.tup (ρ.bindVal x v) bs vs hT hbs.2]
  -- `hasTypList`
  · intro ρ t vs hT ht
    cases vs with
    | nil => simp only [hasTypList]
    | cons v vs =>
        simp only [hasTypList]
        rw [ih.typ _ _ _ hT ht, ih.list _ _ _ hT ht]
  -- `hasTypDef`
  · intro ρ dt v hT hdt
    cases dt with
    | aliasT t => simp only [evDefTyp] at hdt; simp only [hasTypDef]; exact ih.typ _ _ _ hT hdt
    | structT fs =>
        simp only [evDefTyp] at hdt
        simp only [hasTypDef]
        cases v.asStruct? with
        | none => rfl
        | some gs => exact ih.fields _ _ _ hT hdt
    | variantT cs =>
        simp only [evDefTyp] at hdt
        simp only [hasTypDef]
        cases v.asCase? with
        | none => rfl
        | some p =>
            obtain ⟨op, w⟩ := p
            exact ih.case _ _ _ _ hT hdt
  -- `hasTypFields`
  · intro ρ fs gs hT hfs
    cases fs with
    | nil => cases gs <;> simp only [hasTypFields]
    | cons f fs =>
        cases f with
        | mk a t qs prems =>
            simp only [evTFields, goodT_append] at hfs
            obtain ⟨⟨⟨hft, -⟩, -⟩, hfs⟩ := hfs
            cases gs with
            | nil => simp only [hasTypFields]
            | cons g gs =>
                obtain ⟨a', w⟩ := g
                simp only [hasTypFields]
                by_cases haa : a = a'
                · simp only [haa, ↓reduceIte]
                  rw [ih.typ _ _ _ hT hft, premsOk_eq' hS, ih.fields _ _ _ hT hfs]
                · simp only [haa, ↓reduceIte]
  -- `hasTypCase`
  · intro ρ cs op w hT hcs
    cases cs with
    | nil => simp only [hasTypCase]
    | cons c cs =>
        cases c with
        | mk op' t qs prems =>
            simp only [evTCases, goodT_append] at hcs
            obtain ⟨⟨⟨hct, hq⟩, -⟩, hcs⟩ := hcs
            simp only [hasTypCase]
            rw [ih.case _ _ _ _ hT hcs, ih.typ _ _ _ hT hct]
            have hb := bindQuants_off (bad := bad) (fun ρ e => evalExp_eq hS m ρ e) ih.typ
              (caseScope ρ t w) (quantDefs qs prems)
              (typsOkT_of_typs hT (caseScope_typs ρ t w).1) (quantDefs_typ hq)
            rw [hb]
            simp only [premsOk_eq' hS]
  -- `hasTypInsts`
  · intro insts ws v hWT hins
    cases insts with
    | nil => simp only [hasTypInsts]
    | cons i insts =>
        cases i with
        | instD qs pats dt =>
            have hi := hins _ List.mem_cons_self
            simp only [evInst, goodT_append] at hi
            simp only [hasTypInsts]
            rw [matchArgs_eq hS]
            refine elimUndef_congr' (fun ρ' h' => ih.defTyp _ _ _
              (matchArgs_typsOkT m typsOkT_empty hWT h') hi.2) ?_
            exact ih.insts _ _ _ hWT fun i hi => hins i (List.mem_cons_of_mem _ hi)

/-- **Types off `bad` type alike**, at every fuel. -/
theorem tEqAt (hS : EnvSame e₁ e₂) (hO : TypOff bad e₁ e₂) : ∀ n, TEqAt bad e₁ e₂ n
  | 0 => tEqAt_zero bad e₁ e₂
  | n + 1 => tEqAt_succ hS hO n (tEqAt hS hO n)

/-- **`HasTyp` off `bad`.** -/
theorem hasTyp_off_iff (hS : EnvSame e₁ e₂) (hO : TypOff bad e₁ e₂) {ρ : VarEnv} {t : Typ}
    {v : Value} (hT : TypsOkT bad ρ) (ht : GoodT bad (evTyp t)) :
    HasTyp e₂ ρ t v ↔ HasTyp e₁ ρ t v := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, ((tEqAt hS hO n).typ ρ t v hT ht).symm.trans hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, ((tEqAt hS hO n).typ ρ t v hT ht).trans hn⟩

end Silmaril.Wasm.SpecTec.Sim20.ElseAgree
