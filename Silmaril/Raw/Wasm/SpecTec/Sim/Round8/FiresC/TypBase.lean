module

public import Silmaril.Wasm.SpecTec.Sim.Round8.FiresC.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.Script.Thms

/-!
# Round 8, typing across code erasure: the bookkeeping (unrefined)

Round 7's `Raw/…/Round7/EraseDer/TypBase.lean`, copied for `CODE` with every value in the swap
set. The related-scope bookkeeping (`TRel`) is gone: the erased scope is `eraseScope ρ`.

* `XT ρ`: every type variable of `ρ` is bound to a closed checked type (`xTy tyC`); matching
  checked type arguments keeps it (`matchArgs_xt`), and evaluated type arguments are checked
  (`evalArgs_argTyX`).
* `premsOk_er`, `caseScope_erase`: field and case premises read alike on `ρ` and `eraseScope ρ`.
* `quantDefs_x`: the defining conjuncts of a checked case are checked.
* `xInsts_of_find`: the instances of a `tyC` type are checked (from the kernel check
  `xTypMap_fixed`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.FiresC

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Erase (eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll (Hyps SG ER ArgIn grC gdC xExp xPrem xPrems
  xArgs xIter DefsG)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer (varsIn)

/-- The swap set: every value. -/
abbrev QT : Value → Prop := fun _ => True

/-! ## Type variables -/

/-- A closed checked type. -/
def TyX (t : Typ) : Prop := xTy tyC t = true ∧ varsIn [] (freeTyp t) = true

/-- **Every type variable is bound to a closed checked type.** -/
def XT (ρ : VarEnv) : Prop := ∀ p ∈ ρ.typs, TyX p.2

/-- A type argument that is a closed checked type. -/
def ArgTyX : ArgV → Prop
  | .typ t => TyX t
  | _ => True

theorem xt_empty : XT VarEnv.empty := fun _ hp => by cases hp

theorem xt_of_typs {ρ ρ' : VarEnv} (h : XT ρ) (he : ρ'.typs = ρ.typs) : XT ρ' := by
  intro p hp; rw [he] at hp; exact h p hp

theorem xt_bindTyp {ρ : VarEnv} (h : XT ρ) (x : IL.Id) {t : Typ} (ht : TyX t) :
    XT (ρ.bindTyp x t) := by
  intro p hp
  simp only [VarEnv.bindTyp, Map.bind] at hp
  split at hp
  · exact h p hp
  · rcases List.mem_cons.1 hp with rfl | hp
    · exact ht
    · exact h p hp

theorem matchTypV_xt {env : Env} {ρ ρ' : VarEnv} {pat t : Typ} (h : XT ρ) (ht : TyX t)
    (hm : matchTypV env ρ pat t = .ok ρ') : XT ρ' := by
  unfold matchTypV at hm
  repeat (first | (split at hm) | (cases hm; exact h) | (cases hm; exact xt_bindTyp h _ ht) |
    (cases hm))

theorem matchArg_xt {env : Env} {n : Nat} {ρ ρ' : VarEnv} {a : Arg} {w : ArgV} (h : XT ρ)
    (hw : ArgTyX w) (hm : matchArg n env ρ a w = .ok ρ') : XT ρ' := by
  rcases n with _ | n
  · simp [matchArg] at hm
  cases a <;> cases w <;> simp only [matchArg] at hm
  case expA.val e v =>
    split at hm
    · exact xt_of_typs h ((Round7.TypAgree.typsPres env n).matchExp _ _ _ _ hm)
    · cases hm
  case typA.typ => exact matchTypV_xt h hw hm
  case defA.defName y x => cases hm; exact h
  case gramA.gram => exact xt_of_typs h (Round7.TypAgree.matchSymV_typs hm)
  all_goals cases hm

theorem matchArgs_xt {env : Env} :
    ∀ (n : Nat) {ρ ρ' : VarEnv} {ags : List Arg} {ws : List ArgV}, XT ρ →
      (∀ w ∈ ws, ArgTyX w) → matchArgs n env ρ ags ws = .ok ρ' → XT ρ'
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
        exact matchArgs_xt n (matchArg_xt h (hw w List.mem_cons_self) h₁)
          (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw')) h₂

/-- Matching no patterns returns the scope it started from. -/
theorem matchArgs_nil {env : Env} {n : Nat} {ρ ρ' : VarEnv} {ws : List ArgV}
    (hm : matchArgs n env ρ [] ws = .ok ρ') : ρ' = ρ := by
  rcases n with _ | n
  · simp [matchArgs] at hm
  · cases ws <;> simp only [matchArgs] at hm <;> cases hm; rfl

theorem resolveTyp_x {ρ : VarEnv} (h : XT ρ) {t : Typ} (ht : TyX t) : TyX (resolveTyp ρ t) := by
  unfold resolveTyp
  split
  · rename_i x
    cases hf : ρ.findTyp? x with
    | none => exact ht
    | some t' => exact h (x, t') (Round7.Script.mem_of_find? hf)
  · exact ht

theorem xTyArgs_typA {t : Typ} :
    ∀ {ags : List Arg}, xTyArgs tyC ags = true → Arg.typA t ∈ ags → TyX t
  | [], _, ha => by simp at ha
  | b :: ags, hA, ha => by
    rcases List.mem_cons.1 ha with rfl | ha'
    · simp only [xTyArgs, Bool.and_eq_true] at hA; exact ⟨hA.1.1, hA.1.2⟩
    · cases b <;> simp only [xTyArgs, Bool.and_eq_true, Bool.false_eq_true] at hA
      · exact xTyArgs_typA hA.2 ha'
      · exact xTyArgs_typA hA.2 ha'

theorem xArgs_of_xTyArgs : ∀ {ags : List Arg}, xTyArgs tyC ags = true → xArgs grC gdC ags = true
  | [], _ => rfl
  | b :: ags, hA => by
    cases b <;> simp only [xTyArgs, Bool.and_eq_true, Bool.false_eq_true] at hA
    · simp only [xArgs, CodeErase.EraseAll.xArg, Bool.and_eq_true]
      exact ⟨hA.1, xArgs_of_xTyArgs hA.2⟩
    · simp only [xArgs, CodeErase.EraseAll.xArg, Bool.true_and]; exact xArgs_of_xTyArgs hA.2

/-- **Evaluated type arguments are closed checked types.** -/
theorem evalArgs_argTyX {env : Env} {n : Nat} {ρ : VarEnv} {ags : List Arg} {ws : List ArgV}
    (h : XT ρ) (hA : xTyArgs tyC ags = true) (he : evalArgs n env ρ ags = .ok ws) :
    ∀ w ∈ ws, ArgTyX w := by
  rcases n with _ | n
  · simp [evalArgs] at he
  simp only [evalArgs] at he
  intro w hw
  obtain ⟨a, ha, hfa⟩ := Round7.Script.mapM_ok_mem he w hw
  rcases n with _ | n
  · simp [evalArg] at hfa
  have hAa : ∀ t, a = .typA t → TyX t := fun t hat => xTyArgs_typA hA (hat ▸ ha)
  cases a <;> simp only [evalArg] at hfa
  case expA e =>
    obtain ⟨_, _, rfl⟩ := Res.map_eq_ok.1 hfa
    trivial
  case typA t => cases hfa; exact resolveTyp_x h (hAa t rfl)
  case defA x => cases hfa; trivial
  case gramA => cases hfa; trivial

/-! ## Premises -/

section
variable {Q : Value → Prop} {B : Builtins} (H : Hyps Q grC gdC (simEnv B))
include H

/-- **Field and case premises read alike** on a swap-set scope and its erasure. -/
theorem premsOk_er {ρ : VarEnv} {prems : List Prem} (hρ : SG Q gdC ρ)
    (hx : xPrems grC gdC prems = true) (n : Nat) :
    premsOk n (simEnv B) (eraseScope ρ) prems = premsOk n (simEnv B) ρ prems := by
  have hE := (CodeErase.EraseAll.eraseAt H n).premsHold ρ prems hρ hx
  simp only [premsOk, hE.1]
  cases premsHold n (simEnv B) ρ prems with
  | ok _ => rfl
  | error e => cases e <;> rfl

end

theorem typBinds_erase : ∀ (ρ : VarEnv) (bs : List TypBind) (vs : List Value),
    typBinds (eraseScope ρ) bs (vs.map eraseC) = eraseScope (typBinds ρ bs vs)
  | ρ, .mk x _ :: bs, v :: vs => by
    simp only [List.map_cons, typBinds]
    rw [← CodeErase.EraseAll.eraseScope_bindVal]
    exact typBinds_erase _ bs vs
  | _, [], _ => by simp [typBinds]
  | _, _ :: _, [] => by simp [typBinds]

theorem caseScope_erase (ρ : VarEnv) (t : Typ) (w : Value) :
    caseScope (eraseScope ρ) t (eraseC w) = eraseScope (caseScope ρ t w) := by
  cases t with
  | tupT bs =>
    rcases w with _ | _ | _ | vs | _ | _ | _ | (_ | _) <;>
      simp only [caseScope, CodeErase.Swap.eraseC_tuple'] <;>
      first | rfl | exact typBinds_erase ρ bs vs
  | _ => cases w <;> rfl

theorem sg_typBinds : ∀ {ρ : VarEnv} {bs : List TypBind} {vs : List Value}, SG QT gdC ρ →
    SG QT gdC (typBinds ρ bs vs)
  | ρ, .mk x _ :: bs, v :: vs, h => by
    simp only [typBinds]
    exact sg_typBinds (h.bindVal (CodeErase.EraseAll.allIn_true v))
  | _, [], _, h => by simpa [typBinds] using h
  | _, _ :: _, [], h => by simpa [typBinds] using h

theorem sg_caseScope {ρ : VarEnv} (h : SG QT gdC ρ) (t : Typ) (w : Value) :
    SG QT gdC (caseScope ρ t w) := by
  cases t with
  | tupT bs =>
    cases w with
    | tuple vs => exact sg_typBinds h
    | _ => exact h
  | _ => exact h

/-! ## Defining conjuncts -/

theorem xExp_cmp {op : CmpOp} {t : OpTyp} {a b : Exp} (h : xExp grC gdC (.cmpE op t a b) = true) :
    xExp grC gdC a = true ∧ xExp grC gdC b = true := by
  simpa [CodeErase.EraseAll.xExp] using h

theorem xExp_bin {op : BinOp} {t : OpTyp} {a b : Exp} (h : xExp grC gdC (.binE op t a b) = true) :
    xExp grC gdC a = true ∧ xExp grC gdC b = true := by
  simpa [CodeErase.EraseAll.xExp] using h

theorem quantEqs_x {qs : List Param} {e : Exp} (hG : xExp grC gdC e = true) :
    ∀ d ∈ quantEqs qs e, xExp grC gdC d.2.2 = true ∧ Param.expP d.1 d.2.1 ∈ qs := by
  fun_induction quantEqs qs e with
  | case1 τ a b iha ihb =>
    have hG' := xExp_bin hG
    intro d hd
    rcases List.mem_append.1 hd with hd₁ | hd₂
    · exact iha hG'.1 d hd₁
    · exact ihb hG'.2 d hd₂
  | case2 τ a b x t hq =>
    intro d hd
    have hd' : d = (x, t, a) := List.mem_singleton.1 hd
    rw [hd']
    exact ⟨(xExp_cmp hG).1, Round7.TypAgree.quantOf_mem hq⟩
  | case3 τ a b _ x t hq =>
    intro d hd
    have hd' : d = (x, t, b) := List.mem_singleton.1 hd
    rw [hd']
    exact ⟨(xExp_cmp hG).2, Round7.TypAgree.quantOf_mem hq⟩
  | case4 => intro d hd; simp at hd
  | case5 => intro d hd; simp at hd

theorem quantDefs_x {qs : List Param} {prems : List Prem} (hG : xPrems grC gdC prems = true)
    (hq : qs.all (fun q => match q with | .expP _ t => xTy tyC t | _ => true) = true) :
    ∀ d ∈ quantDefs qs prems, xExp grC gdC d.2.2 = true ∧ xTy tyC d.2.1 = true := by
  intro d hd
  simp only [quantDefs, List.mem_flatMap] at hd
  obtain ⟨pr, hpr, hd⟩ := hd
  have hGpr := CodeErase.EraseAll.xPrems_mem hG pr hpr
  cases pr with
  | ifPr e =>
    simp only [xPrem] at hGpr
    obtain ⟨h₁, h₂⟩ := quantEqs_x hGpr d hd
    refine ⟨h₁, ?_⟩
    have := List.all_eq_true.1 hq _ h₂
    simpa using this
  | rulePr _ _ _ _ => simp at hd
  | letPr _ _ => simp at hd
  | elsePr => simp at hd
  | iterPr _ _ => simp at hd

end Silmaril.Wasm.SpecTec.Sim.Round8.FiresC
