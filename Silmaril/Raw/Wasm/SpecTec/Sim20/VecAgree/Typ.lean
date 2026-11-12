module

public import Silmaril.Wasm.SpecTec.Sim20.VecAgree.Defs
public import Silmaril.Wasm.SpecTec.Sim20.StoreAgree.Thms
public import Silmaril.Wasm.SpecTec.Sim20.ElseAgree.Thms

/-!
# Typing grows across an instance-list erratum, at `VOk` values (unrefined)

`e₁` and `e₂` evaluate alike (`StoreAgree.EnvSame`). Their type tables agree off the three
families `fams`; at a family `f`, `e₂` has an instance list `is₂` that, at a non-float shape,
answers what `e₁`'s list answers two units of fuel later, and at a float shape accepts every
nullary case of `fNames f` (`FamRel`). Every type of `e₁` mentions the families only as the
payload `payT f` of the case `opOf f` (`FamRel.ok`, `InstsOk`).

Then, at every fuel `n`, every member of the typing block that answers `true` in `e₁` at a `VOk`
value answers `true` in `e₂` at fuel `3 n + C` (`fAt`), and so `HasTyp e₁ ρ t v → HasTyp e₂ ρ t v`
for `VOk v` (`hasTyp_vec`). The factor `3` pays for the two instances `e₂` skips at a non-float
shape; `C` for the fuel the skip and the float answer need.

The proof follows `StoreAgree.sameTypAt_succ` (`Raw/…/Sim20/StoreAgree/Typ.lean`) with the fuel
shifted, the value invariant `VOk` threaded through as in `Round7.TypAgree.tAgreeAt_succ`, and the
family read in the scope that the payload's first binder `shape` builds. Kept unrefined, like its
models.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Sem.Res
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evTyp evBinds evArgs mem_of_find?)
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (caseScope_typs)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (GoodT TypsOkT ArgTyOkT tyEvB goodT_cons goodT_append
  typsOkT_empty typsOkT_of_typs matchArgs_typsOkT evalArgs_argTyOkT quantEqs_mem)
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (EnvSame evalExp_eq evalArgs_eq matchArgs_eq premsHold_eq
  bind_ok)

/-- **The tables of `e₂` repair those of `e₁` at the three families.** -/
structure FamRel (e₁ e₂ : Env) (C : Nat) : Prop where
  find : ∀ x td, fams.contains x = false → e₁.findTyp? x = some td → e₂.findTyp? x = some td
  fam : ∀ f ∈ fams, ∀ td, e₁.findTyp? f = some td → ∃ is₂, e₂.findTyp? f = some (td.1, is₂) ∧
    (∀ a k v, ¬ FloatSh a →
      hasTypInsts (k + C + 2) e₂ is₂ [.val a] v = hasTypInsts (k + C) e₂ td.2 [.val a] v) ∧
    (∀ a o k, FloatSh a → o ∈ fNames f →
      hasTypInsts (k + C) e₂ is₂ [.val a] (.case o (.tuple [])) = .ok true)
  ok : ∀ x td, e₁.findTyp? x = some td → InstsOk e₁ e₂ td.2

/-- **The typing block of `e₂` at fuel `3 n + C` answers `true` where that of `e₁` at `n` does**,
on checked types and `VOk` values. -/
structure FAt (e₁ e₂ : Env) (C n : Nat) : Prop where
  typ : ∀ ρ t v, TypsOkT fams ρ → TN e₁ ρ → TOk ρ t v → VOk v → hasTyp n e₁ ρ t v = .ok true →
    hasTyp (3 * n + C) e₂ ρ t v = .ok true
  tup : ∀ ρ bs vs, TypsOkT fams ρ → TN e₁ ρ → BOk ρ bs vs → (∀ v ∈ vs, VOk v) →
    hasTypTup n e₁ ρ bs vs = .ok true → hasTypTup (3 * n + C) e₂ ρ bs vs = .ok true
  list : ∀ ρ t vs, TypsOkT fams ρ → TN e₁ ρ → ffT t → (∀ v ∈ vs, VOk v) →
    hasTypList n e₁ ρ t vs = .ok true → hasTypList (3 * n + C) e₂ ρ t vs = .ok true
  defTyp : ∀ ρ dt v, TypsOkT fams ρ → TN e₁ ρ → DOk e₁ e₂ dt → VOk v →
    hasTypDef n e₁ ρ dt v = .ok true → hasTypDef (3 * n + C) e₂ ρ dt v = .ok true
  fields : ∀ ρ fs gs, TypsOkT fams ρ → TN e₁ ρ → (∀ f ∈ fs, match f with | .mk _ t _ _ => ffT t) →
    (∀ p ∈ gs, VOk p.2) →
    hasTypFields n e₁ ρ fs gs = .ok true → hasTypFields (3 * n + C) e₂ ρ fs gs = .ok true
  case : ∀ ρ cs op w, TypsOkT fams ρ → TN e₁ ρ → CasesOk e₁ e₂ cs → VOk (.case op w) →
    hasTypCase n e₁ ρ cs op w = .ok true → hasTypCase (3 * n + C) e₂ ρ cs op w = .ok true
  insts : ∀ is ws v, (∀ w ∈ ws, ArgTyOkT fams w) → InstsOk e₁ e₂ is → VOk v →
    hasTypInsts n e₁ is ws v = .ok true → hasTypInsts (3 * n + C) e₂ is ws v = .ok true

variable {e₁ e₂ : Env} {C : Nat}

theorem fAt_zero : FAt e₁ e₂ C 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    simp_all [hasTyp, hasTypTup, hasTypList, hasTypDef, hasTypFields, hasTypCase, hasTypInsts]

/-! ## Small facts -/

theorem bindIf_true {r x : Res Bool} :
    (do let b ← r; if b then x else .ok false) = .ok true ↔ r = .ok true ∧ x = .ok true := by
  constructor
  · intro h
    simp only [Res.bind_eq_ok] at h
    obtain ⟨b, hb, h⟩ := h
    cases b
    · simp at h
    · exact ⟨hb, by simpa using h⟩
  · rintro ⟨hr, hx⟩
    rw [hr]
    simpa using hx

theorem vOk_tuple {vs : List Value} (h : VOk (.tuple vs)) : ∀ w ∈ vs, VOk w := by
  cases h; assumption

theorem vOk_list {vs : List Value} (h : VOk (.list vs)) : ∀ w ∈ vs, VOk w := by
  cases h; assumption

theorem vOk_opt {w : Value} (h : VOk (.opt (some w))) : VOk w := by
  cases h with
  | opt h => exact h w rfl

theorem vOk_struct {gs : List (AtomS × Value)} (h : VOk (.struct gs)) : ∀ p ∈ gs, VOk p.2 := by
  cases h; assumption

theorem vOk_case {op : MixopS} {w : Value} (h : VOk (.case op w)) :
    VOk w ∧ ∀ f ∈ fams, op = opOf f → PayOk f w := by
  cases h with
  | case _ h₁ h₂ => exact ⟨h₁, h₂⟩

theorem ffT_varT {x : IL.Id} {args : List Arg} (h : ffT (.varT x args)) :
    fams.contains x = false ∧ GoodT fams (evArgs args) := by
  simp only [ffT, evTyp, goodT_cons, tyEvB] at h
  exact ⟨by simpa using h.1, h.2⟩

theorem ffT_iterT {t : Typ} {it : Iter} (h : ffT (.iterT t it)) : ffT t := by
  simp only [ffT, evTyp, goodT_append] at h
  exact h.1

theorem ffB_cons {x : IL.Id} {t : Typ} {bs : List TypBind} (h : ffB (.mk x t :: bs)) :
    ffT t ∧ ffB bs := by
  simp only [ffB, evBinds, goodT_append] at h
  exact h

theorem ffB_nil : ffB [] := by simp [ffB, evBinds, GoodT]

theorem ffT_shape : ffT (.varT "shape" []) := by
  simp [ffT, evTyp, evArgs, GoodT, tyEvB, fams]

theorem tOk_ff {ρ : VarEnv} {t : Typ} {v : Value} (h : ffT t) : TOk ρ t v := Or.inl h

theorem findVal_bindVal_shape (ρ : VarEnv) (v : Value) :
    (ρ.bindVal "shape" v).findVal? "shape" = some v := by
  simp [VarEnv.bindVal, VarEnv.findVal?, Map.bind]

set_option linter.unusedTactic false in
theorem evalArgs_shape {n : Nat} {env : Env} {ρ : VarEnv} {ws : List ArgV}
    (h : evalArgs n env ρ [.expA (.varE "shape")] = .ok ws) :
    ∃ a, ρ.findVal? "shape" = some a ∧ ws = [.val a] := by
  rcases n with _ | _ | _ | n <;>
    simp [evalArgs, evalArg, evalExp, List.mapM_cons] at h
  all_goals
    revert h
    cases hf : ρ.findVal? "shape" <;> simp

theorem tn_empty {env : Env} : TN env VarEnv.empty := by
  simp [TN, VarEnv.empty, Map.empty]

theorem tn_of_typs {env : Env} {ρ ρ' : VarEnv} (h : TN env ρ) (he : ρ'.typs = ρ.typs) :
    TN env ρ' := by
  intro p hp; rw [he] at hp; exact h p hp

theorem tn_bindTyp {env : Env} {ρ : VarEnv} (h : TN env ρ) {x : IL.Id} (hx : env.memTyp x = false)
    (t : Typ) : TN env (ρ.bindTyp x t) := by
  intro p hp
  simp only [VarEnv.bindTyp, Map.bind] at hp
  split at hp
  · exact h p hp
  · rcases List.mem_cons.1 hp with rfl | hp
    · exact hx
    · exact h p hp

theorem matchTypV_tn {env : Env} {ρ ρ' : VarEnv} {pat t : Typ} (h : TN env ρ)
    (hm : matchTypV env ρ pat t = .ok ρ') : TN env ρ' := by
  unfold matchTypV at hm
  repeat (first | (split at hm) | (cases hm; exact h) |
    (cases hm; exact tn_bindTyp h (by simpa using (by assumption : ¬ env.memTyp _ = true)) _) |
    (cases hm))

theorem matchArg_tn {env : Env} {n : Nat} {ρ ρ' : VarEnv} {a : Arg} {w : ArgV} (h : TN env ρ)
    (hm : matchArg n env ρ a w = .ok ρ') : TN env ρ' := by
  rcases n with _ | n
  · simp [matchArg] at hm
  cases a <;> cases w <;> simp only [matchArg] at hm
  case expA.val e v =>
    split at hm
    · exact tn_of_typs h ((Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.typsPres env n).matchExp _ _ _ _ hm)
    · cases hm
  case typA.typ => exact matchTypV_tn h hm
  case defA.defName y x => cases hm; exact h
  case gramA.gram => exact tn_of_typs h (Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.matchSymV_typs hm)
  all_goals cases hm

theorem matchArgs_tn {env : Env} :
    ∀ {n : Nat} {ρ ρ' : VarEnv} {ags : List Arg} {ws : List ArgV}, TN env ρ →
      matchArgs n env ρ ags ws = .ok ρ' → TN env ρ'
  | 0, _, _, _, _, _, hm => by simp [matchArgs] at hm
  | n + 1, ρ, ρ', ags, ws, h, hm => by
    cases ags with
    | nil => cases ws <;> simp only [matchArgs] at hm <;> cases hm; exact h
    | cons a ags =>
      cases ws with
      | nil => simp only [matchArgs] at hm; cases hm
      | cons w ws =>
        simp only [matchArgs, Res.bind_eq_ok] at hm
        obtain ⟨ρ₁, h₁, h₂⟩ := hm
        exact matchArgs_tn (matchArg_tn h h₁) h₂

/-- `bindQuants` answers alike when its oracles agree on the defining conjuncts. -/
theorem bindQuants_congr {P : VarEnv → Prop} (hP : ∀ ρ x v, P ρ → P (ρ.bindVal x v))
    {ev₁ ev₂ : VarEnv → Exp → Res Value}
    {ty₁ ty₂ : VarEnv → Typ → Value → Res Bool} (hev : ∀ ρ e, ev₁ ρ e = ev₂ ρ e) :
    ∀ (ds : List (IL.Id × Typ × Exp)), (∀ d ∈ ds, ∀ ρ v, P ρ → ty₁ ρ d.2.1 v = ty₂ ρ d.2.1 v) →
      ∀ ρ, P ρ → bindQuants ev₁ ty₁ ρ ds = bindQuants ev₂ ty₂ ρ ds
  | [], _, ρ, _ => rfl
  | (x, t, e) :: ds, hty, ρ, hρ => by
    simp only [bindQuants]
    rw [hev ρ e]
    cases ev₂ ρ e with
    | error err => rfl
    | ok v =>
      simp only [bind_ok]
      rw [hty _ List.mem_cons_self ρ v hρ]
      cases ty₂ ρ t v with
      | error err => rfl
      | ok b =>
        cases b
        · rfl
        · simp only [bind_ok, ↓reduceIte]
          exact bindQuants_congr hP hev ds (fun d hd => hty d (List.mem_cons_of_mem _ hd)) _
            (hP ρ x v hρ)

theorem quantDefs_mem {qs : List Param} {prems : List Prem} :
    ∀ d ∈ quantDefs qs prems, Param.expP d.1 d.2.1 ∈ qs := by
  intro d hd
  simp only [quantDefs, List.mem_flatMap] at hd
  obtain ⟨pr, -, hd⟩ := hd
  cases pr with
  | ifPr e => exact quantEqs_mem d hd
  | rulePr _ _ _ _ => simp at hd
  | letPr _ _ => simp at hd
  | elsePr => simp at hd
  | iterPr _ _ => simp at hd

/-- The hit branch of `hasTypCase` answering `true`. -/
theorem caseHit_true {n : Nat} {env : Env} {ρ : VarEnv} {t : Typ} {qs : List Param}
    {prems : List Prem} {w : Value}
    (h : (do
          let b ← hasTyp n env ρ t w
          if b then
            Res.elimUndef
              (bindQuants (fun ρ e => evalExp n env ρ e) (fun ρ t v => hasTyp n env ρ t v)
                (caseScope ρ t w) (quantDefs qs prems))
              (fun o => match o with
                | some ρq => premsOk n env ρq prems
                | none => .ok false)
              (fun _ => .ok false)
          else .ok false) = .ok true) :
    hasTyp n env ρ t w = .ok true ∧ ∃ ρq,
      bindQuants (fun ρ e => evalExp n env ρ e) (fun ρ t v => hasTyp n env ρ t v)
        (caseScope ρ t w) (quantDefs qs prems) = .ok (some ρq) ∧
      premsOk n env ρq prems = .ok true := by
  obtain ⟨h₁, h₂⟩ := bindIf_true.1 h
  refine ⟨h₁, ?_⟩
  revert h₂
  cases bindQuants (fun ρ e => evalExp n env ρ e) (fun ρ t v => hasTyp n env ρ t v)
    (caseScope ρ t w) (quantDefs qs prems) with
  | error err => cases err <;> simp [Res.elimUndef]
  | ok o =>
    cases o with
    | none => simp [Res.elimUndef]
    | some ρq => intro h; exact ⟨ρq, rfl, by simpa [Res.elimUndef] using h⟩

/-! ## The inductive step, member by member -/

section Step

variable (hS : EnvSame e₁ e₂) (hR : FamRel e₁ e₂ C) (m : Nat) (ih : FAt e₁ e₂ C m)
include hS hR ih

theorem typ_step (ρ : VarEnv) (t : Typ) (v : Value) (hT : TypsOkT fams ρ) (hN : TN e₁ ρ) (ht : TOk ρ t v)
    (hv : VOk v) (h : hasTyp (m + 1) e₁ ρ t v = .ok true) :
    hasTyp (3 * (m + 1) + C) e₂ ρ t v = .ok true := by
  have hK : 3 * (m + 1) + C = (3 * m + C + 2) + 1 := by omega
  have hle : 3 * m + C ≤ 3 * m + C + 2 := by omega
  rw [hK]
  cases t with
  | boolT => simpa only [hasTyp] using h
  | numT t => simpa only [hasTyp] using h
  | textT => simpa only [hasTyp] using h
  | tupT bs =>
    cases v with
    | tuple vs =>
      simp only [hasTyp, Value.asTuple?] at h ⊢
      have hb : BOk ρ bs vs := by
        rcases ht with hf | ⟨f, -, he, -⟩ | ⟨f, hf, he, hp⟩
        · exact Or.inl hf
        · simp [famT] at he
        · simp only [payT, Typ.tupT.injEq] at he
          exact Or.inr (Or.inl ⟨f, hf, he, hp⟩)
      exact hasTypTup_ok_of_le hle (ih.tup ρ bs vs hT hN hb (vOk_tuple hv) h)
    | _ => simp [hasTyp, Value.asTuple?] at h
  | iterT t it =>
    have hf : ffT t := by
      rcases ht with hf | ⟨f, -, he, -⟩ | ⟨f, -, he, -⟩
      · exact ffT_iterT hf
      · simp [famT] at he
      · simp [payT] at he
    cases it with
    | opt =>
      cases v with
      | opt o =>
        cases o with
        | none => simp only [hasTyp, Value.asOpt?]
        | some w =>
          simp only [hasTyp, Value.asOpt?] at h ⊢
          exact hasTyp_ok_of_le hle (ih.typ ρ t w hT hN (tOk_ff hf) (vOk_opt hv) h)
      | _ => simp [hasTyp, Value.asOpt?] at h
    | list =>
      cases v with
      | list vs =>
        simp only [hasTyp, Value.asList?] at h ⊢
        exact hasTypList_ok_of_le hle (ih.list ρ t vs hT hN hf (vOk_list hv) h)
      | _ => simp [hasTyp, Value.asList?] at h
    | list1 =>
      cases v with
      | list vs =>
        simp only [hasTyp, Value.asList?] at h ⊢
        split at h
        · simp at h
        · rw [ite_eq_right (by assumption)]
          exact hasTypList_ok_of_le hle (ih.list ρ t vs hT hN hf (vOk_list hv) h)
      | _ => simp [hasTyp, Value.asList?] at h
    | listN e x =>
      cases v with
      | list vs =>
        simp only [hasTyp, Value.asList?, Res.bind_eq_ok] at h ⊢
        obtain ⟨kv, hkv, k, hk, h⟩ := h
        refine ⟨kv, ?_, k, hk, ?_⟩
        · rw [evalExp_eq hS]
          exact evalExp_ok_of_le (by omega) hkv
        · split at h
          · rw [ite_eq_left (by assumption)]
            exact hasTypList_ok_of_le hle (ih.list ρ t vs hT hN hf (vOk_list hv) h)
          · simp at h
      | _ => simp [hasTyp, Value.asList?] at h
  | varT x args =>
    simp only [hasTyp] at h ⊢
    cases hl : localTyp? ρ x args with
    | some t' =>
      rw [hl] at h
      dsimp only at h ⊢
      have hl' : ρ.findTyp? x = some t' := by
        cases args with
        | nil => simpa only [localTyp?] using hl
        | cons _ _ => simp [localTyp?] at hl
      exact hasTyp_ok_of_le hle (ih.typ ρ t' v hT hN (tOk_ff (hT (x, t') (mem_of_find? hl'))) hv h)
    | none =>
      rw [hl] at h
      dsimp only at h ⊢
      simp only [Res.bind_eq_ok, Res.ofOption_eq_ok] at h ⊢
      obtain ⟨td, htd, ws, hws, h⟩ := h
      have hws' : evalArgs (3 * m + C + 2) e₂ ρ args = .ok ws := by
        rw [evalArgs_eq hS]; exact evalArgs_ok_of_le (by omega) hws
      rcases ht with hf | ⟨f, hf, he, hfa⟩ | ⟨f, -, he, -⟩
      · obtain ⟨hx, ha⟩ := ffT_varT hf
        refine ⟨td, hR.find x td hx htd, ws, hws', ?_⟩
        exact hasTypInsts_ok_of_le hle (ih.insts td.2 ws v (evalArgs_argTyOkT hT ha hws)
          (hR.ok x td htd) hv h)
      · simp only [famT, Typ.varT.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨a, hfa', rfl⟩ := evalArgs_shape hws
        obtain ⟨is₂, h₂, hskip, hfloat⟩ := hR.fam x hf td htd
        refine ⟨_, h₂, _, hws', ?_⟩
        by_cases hfs : FloatSh a
        · obtain ⟨o, ho, rfl⟩ := hfa a hfa' hfs
          have := hfloat a o (3 * m + 2) hfs ho
          rwa [show 3 * m + 2 + C = 3 * m + C + 2 by omega] at this
        · rw [hskip a (3 * m) v hfs]
          exact ih.insts td.2 [.val a] v (by simp [ArgTyOkT]) (hR.ok x td htd) hv h
      · simp [payT] at he

omit hS hR in
theorem tup_step (ρ : VarEnv) (bs : List TypBind) (vs : List Value) (hT : TypsOkT fams ρ) (hN : TN e₁ ρ)
    (hb : BOk ρ bs vs) (hvs : ∀ v ∈ vs, VOk v) (h : hasTypTup (m + 1) e₁ ρ bs vs = .ok true) :
    hasTypTup (3 * (m + 1) + C) e₂ ρ bs vs = .ok true := by
  have hK : 3 * (m + 1) + C = (3 * m + C + 2) + 1 := by omega
  have hle : 3 * m + C ≤ 3 * m + C + 2 := by omega
  rw [hK]
  cases bs with
  | nil => cases vs <;> simp_all [hasTypTup]
  | cons b bs =>
    obtain ⟨x, t⟩ := b
    cases vs with
    | nil => simp [hasTypTup] at h
    | cons v vs =>
      simp only [hasTypTup] at h ⊢
      obtain ⟨h₁, h₂⟩ := bindIf_true.1 h
      have hT' : TypsOkT fams (ρ.bindVal x v) := typsOkT_of_typs hT rfl
      have hN' : TN e₁ (ρ.bindVal x v) := tn_of_typs hN rfl
      have hv : VOk v := hvs v List.mem_cons_self
      have hvs' : ∀ w ∈ vs, VOk w := fun w hw => hvs w (List.mem_cons_of_mem _ hw)
      refine bindIf_true.2 ⟨?_, ?_⟩
      · refine hasTyp_ok_of_le hle (ih.typ ρ t v hT hN ?_ hv h₁)
        rcases hb with hf | ⟨f, -, he, -⟩ | ⟨f, hf, he, hfa⟩
        · exact tOk_ff (ffB_cons hf).1
        · simp only [payB, List.cons.injEq, TypBind.mk.injEq] at he
          rw [he.1.2]; exact tOk_ff ffT_shape
        · simp only [List.cons.injEq, TypBind.mk.injEq] at he
          obtain ⟨⟨-, rfl⟩, rfl⟩ := he
          cases vs with
          | nil => exact Or.inr (Or.inl ⟨f, hf, rfl, hfa v rfl⟩)
          | cons w vs => cases m <;> simp [hasTypTup] at h₂
      · refine hasTypTup_ok_of_le hle (ih.tup _ bs vs hT' hN' ?_ hvs' h₂)
        rcases hb with hf | ⟨f, hf, he, hp⟩ | ⟨f, -, he, -⟩
        · exact Or.inl (ffB_cons hf).2
        · simp only [payB, List.cons.injEq, TypBind.mk.injEq] at he
          obtain ⟨⟨rfl, -⟩, rfl⟩ := he
          refine Or.inr (Or.inr ⟨f, hf, rfl, ?_⟩)
          rintro b rfl a ha hfs
          rw [findVal_bindVal_shape] at ha
          cases ha
          exact hp v b rfl hfs
        · simp only [List.cons.injEq] at he
          rw [he.2]; exact Or.inl ffB_nil

omit hS hR in
theorem list_step (ρ : VarEnv) (t : Typ) (vs : List Value) (hT : TypsOkT fams ρ) (hN : TN e₁ ρ) (hf : ffT t)
    (hvs : ∀ v ∈ vs, VOk v) (h : hasTypList (m + 1) e₁ ρ t vs = .ok true) :
    hasTypList (3 * (m + 1) + C) e₂ ρ t vs = .ok true := by
  have hK : 3 * (m + 1) + C = (3 * m + C + 2) + 1 := by omega
  have hle : 3 * m + C ≤ 3 * m + C + 2 := by omega
  rw [hK]
  cases vs with
  | nil => simp [hasTypList]
  | cons v vs =>
    simp only [hasTypList] at h ⊢
    obtain ⟨h₁, h₂⟩ := bindIf_true.1 h
    exact bindIf_true.2
      ⟨hasTyp_ok_of_le hle (ih.typ ρ t v hT hN (tOk_ff hf) (hvs v List.mem_cons_self) h₁),
        hasTypList_ok_of_le hle
          (ih.list ρ t vs hT hN hf (fun w hw => hvs w (List.mem_cons_of_mem _ hw)) h₂)⟩

omit hS hR in
theorem defTyp_step (ρ : VarEnv) (dt : DefTyp) (v : Value) (hT : TypsOkT fams ρ) (hN : TN e₁ ρ)
    (hd : DOk e₁ e₂ dt) (hv : VOk v) (h : hasTypDef (m + 1) e₁ ρ dt v = .ok true) :
    hasTypDef (3 * (m + 1) + C) e₂ ρ dt v = .ok true := by
  have hK : 3 * (m + 1) + C = (3 * m + C + 2) + 1 := by omega
  have hle : 3 * m + C ≤ 3 * m + C + 2 := by omega
  rw [hK]
  cases dt with
  | aliasT t =>
    simp only [hasTypDef] at h ⊢
    exact hasTyp_ok_of_le hle (ih.typ ρ t v hT hN (tOk_ff hd) hv h)
  | structT fs =>
    cases v with
    | struct gs =>
      simp only [hasTypDef, Value.asStruct?] at h ⊢
      exact hasTypFields_ok_of_le hle (ih.fields ρ fs gs hT hN hd (vOk_struct hv) h)
    | _ => simp [hasTypDef, Value.asStruct?] at h
  | variantT cs =>
    cases v with
    | case op w =>
      simp only [hasTypDef, Value.asCase?] at h ⊢
      exact hasTypCase_ok_of_le hle (ih.case ρ cs op w hT hN hd hv h)
    | _ => simp [hasTypDef, Value.asCase?] at h

omit hR in
theorem fields_step (ρ : VarEnv) (fs : List TypField) (gs : List (AtomS × Value))
    (hT : TypsOkT fams ρ) (hN : TN e₁ ρ) (hfs : ∀ f ∈ fs, match f with | .mk _ t _ _ => ffT t)
    (hgs : ∀ p ∈ gs, VOk p.2) (h : hasTypFields (m + 1) e₁ ρ fs gs = .ok true) :
    hasTypFields (3 * (m + 1) + C) e₂ ρ fs gs = .ok true := by
  have hK : 3 * (m + 1) + C = (3 * m + C + 2) + 1 := by omega
  have hle : 3 * m + C ≤ 3 * m + C + 2 := by omega
  rw [hK]
  cases fs with
  | nil => cases gs <;> simp_all [hasTypFields]
  | cons f fs =>
    obtain ⟨a, t, qs, prems⟩ := f
    cases gs with
    | nil => simp [hasTypFields] at h
    | cons g gs =>
      obtain ⟨a', w⟩ := g
      simp only [hasTypFields] at h ⊢
      split at h
      · rw [ite_eq_left (by assumption)]
        obtain ⟨h₁, h₂⟩ := bindIf_true.1 h
        obtain ⟨h₃, h₄⟩ := bindIf_true.1 h₂
        have hft : ffT t := hfs _ List.mem_cons_self
        refine bindIf_true.2 ⟨hasTyp_ok_of_le hle (ih.typ ρ t w hT hN (tOk_ff hft)
          (hgs _ List.mem_cons_self) h₁), bindIf_true.2 ⟨?_, ?_⟩⟩
        · have hp : premsOk m e₂ (caseScope ρ t w) prems = .ok true := by
            simpa only [premsOk, premsHold_eq hS] using h₃
          exact premsOk_ok_of_le (by omega) hp
        · exact hasTypFields_ok_of_le hle (ih.fields ρ fs gs hT hN
            (fun f hf => hfs f (List.mem_cons_of_mem _ hf))
            (fun p hp => hgs p (List.mem_cons_of_mem _ hp)) h₄)
      · simp at h

omit hR in
theorem case_step (ρ : VarEnv) (cs : List TypCase) (op : MixopS) (w : Value)
    (hT : TypsOkT fams ρ) (hN : TN e₁ ρ) (hcs : CasesOk e₁ e₂ cs) (hv : VOk (.case op w))
    (h : hasTypCase (m + 1) e₁ ρ cs op w = .ok true) :
    hasTypCase (3 * (m + 1) + C) e₂ ρ cs op w = .ok true := by
  have hK : 3 * (m + 1) + C = (3 * m + C + 2) + 1 := by omega
  have hle : 3 * m + C ≤ 3 * m + C + 2 := by omega
  rw [hK]
  cases cs with
  | nil => simp [hasTypCase] at h
  | cons c cs =>
    obtain ⟨op', t, qs, prems⟩ := c
    have hc := hcs _ List.mem_cons_self
    simp only at hc
    obtain ⟨hpay, hq⟩ := hc
    simp only [hasTypCase] at h ⊢
    split at h
    · rename_i hop
      subst hop
      rw [ite_eq_left rfl]
      obtain ⟨h₁, ρq, h₂, h₃⟩ := caseHit_true h
      obtain ⟨hw, hpw⟩ := vOk_case hv
      have htw : TOk ρ t w := by
        rcases hpay with hf | ⟨f, hf, rfl, rfl⟩
        · exact tOk_ff hf
        · exact Or.inr (Or.inr ⟨f, hf, rfl, hpw f hf rfl⟩)
      have hb₂ : bindQuants (fun ρ e => evalExp m e₂ ρ e) (fun ρ t v => hasTyp m e₂ ρ t v)
          (caseScope ρ t w) (quantDefs qs prems) = .ok (some ρq) := by
        rw [← h₂]
        exact bindQuants_congr (P := TN e₁) (fun ρ x v h => tn_of_typs h rfl)
          (fun ρ e => evalExp_eq hS m ρ e) _
          (fun d hd ρ v hρ => hq d.1 d.2.1 (quantDefs_mem d hd) m ρ v hρ) _
          (tn_of_typs hN (caseScope_typs ρ t w).1)
      rw [hasTyp_ok_of_le hle (ih.typ ρ t w hT hN htw hw h₁)]
      simp only [bind_ok, ↓reduceIte]
      rw [bindQuants_ok_of_le (by omega) hb₂]
      simp only [Res.elimUndef_ok]
      have hp : premsOk m e₂ ρq prems = .ok true := by
        simpa only [premsOk, premsHold_eq hS] using h₃
      exact premsOk_ok_of_le (by omega) hp
    · rw [ite_eq_right (by assumption)]
      exact hasTypCase_ok_of_le hle (ih.case ρ cs op w hT hN
        (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) hv h)

omit hR in
theorem insts_step (is : List Inst) (ws : List ArgV) (v : Value) (hW : ∀ w ∈ ws, ArgTyOkT fams w)
    (hi : InstsOk e₁ e₂ is) (hv : VOk v) (h : hasTypInsts (m + 1) e₁ is ws v = .ok true) :
    hasTypInsts (3 * (m + 1) + C) e₂ is ws v = .ok true := by
  have hK : 3 * (m + 1) + C = (3 * m + C + 2) + 1 := by omega
  have hle : 3 * m + C ≤ 3 * m + C + 2 := by omega
  rw [hK]
  cases is with
  | nil => simp [hasTypInsts] at h
  | cons i is =>
    obtain ⟨qs, pats, dt⟩ := i
    have hd : DOk e₁ e₂ dt := hi _ List.mem_cons_self
    have hi' : InstsOk e₁ e₂ is := fun i hi₂ => hi i (List.mem_cons_of_mem _ hi₂)
    simp only [hasTypInsts] at h ⊢
    have hmono := (monoAt_of_le (show m ≤ 3 * m + C + 2 by omega)).matchArgs e₂ VarEnv.empty pats ws
    rw [matchArgs_eq hS] at hmono
    cases hm : matchArgs m e₁ VarEnv.empty pats ws with
    | ok ρ' =>
      rw [hm] at h hmono
      rw [hmono.ok rfl]
      simp only [Res.elimUndef_ok] at h ⊢
      exact hasTypDef_ok_of_le hle (ih.defTyp ρ' dt v
        (matchArgs_typsOkT m typsOkT_empty hW hm) (matchArgs_tn tn_empty hm) hd hv h)
    | error err =>
      rw [hm] at h hmono
      cases err with
      | undef =>
        rw [hmono.eq_of_ne_oof (by simp)]
        simp only [Res.elimUndef] at h ⊢
        exact hasTypInsts_ok_of_le hle (ih.insts is ws v hW hi' hv h)
      | outOfFuel => simp [Res.elimUndef] at h

end Step

theorem fAt_succ (hS : EnvSame e₁ e₂) (hR : FamRel e₁ e₂ C) (m : Nat) (ih : FAt e₁ e₂ C m) :
    FAt e₁ e₂ C (m + 1) :=
  ⟨typ_step hS hR m ih, tup_step m ih, list_step m ih, defTyp_step m ih,
    fields_step hS m ih, case_step hS m ih, insts_step hS m ih⟩

/-- **At every fuel.** -/
theorem fAt (hS : EnvSame e₁ e₂) (hR : FamRel e₁ e₂ C) : ∀ n, FAt e₁ e₂ C n
  | 0 => fAt_zero
  | n + 1 => fAt_succ hS hR n (fAt hS hR n)

/-- **`HasTyp` grows at `VOk` values**, on checked types. -/
theorem hasTyp_vec (hS : EnvSame e₁ e₂) (hR : FamRel e₁ e₂ C) {ρ : VarEnv} {t : Typ} {v : Value}
    (hT : TypsOkT fams ρ) (hN : TN e₁ ρ) (ht : TOk ρ t v) (hv : VOk v) (h : HasTyp e₁ ρ t v) :
    HasTyp e₂ ρ t v :=
  let ⟨n, hn⟩ := h
  ⟨3 * n + C, (fAt hS hR n).typ ρ t v hT hN ht hv hn⟩

end Silmaril.Wasm.SpecTec.Sim20.VecAgree
