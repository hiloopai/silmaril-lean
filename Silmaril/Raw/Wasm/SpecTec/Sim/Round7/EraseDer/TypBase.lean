module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseDer.Else
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseDer.CheckTyp
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.EraseDer.CheckQuant
public import Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.Thms

/-!
# Round 7, typing across erasure: the bookkeeping (unrefined)

What the typing induction (`Round7/EraseDer/TypFwd.lean`) needs besides its induction
hypotheses:

* `XT ρ`: every type variable of `ρ` is bound to a closed checked type (`xTy tyB`); it holds of the
  scopes matching returns from checked type arguments (`matchArgs_xt`), and evaluated type
  arguments are checked (`evalArgs_argTyX`). Copies of `Round7.TypAgree.matchArgs_typsOk` and
  `evalArgs_argTyOk` with `xTy` for `tyOk`.
* `TRel S ρ ρ'`: `ErRel` on `S`, and the same type, definition and grammar variables. A swap-set
  scope is so related to its erasure (`tRel_of_sg`), and evaluation goes across at every fuel
  (`evalExp_er`, `evalArgs_er`).
* `premsOk_er`, `caseScope_erase`: field and case premises read alike.
* `quantDefs_x`: the defining conjuncts of a checked case are checked.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope ScopeIn find?_eraseScope)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (Hyps SG ER eraseAt ArgIn grE gdE xExp xPrem xPrems
  xArgs xIter DefsG)
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (tyB)

variable {Q : Value → Prop}

/-! ## Type variables -/

/-- A closed checked type. -/
def TyX (t : Typ) : Prop := xTy tyB t = true ∧ varsIn [] (freeTyp t) = true

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
    · exact xt_of_typs h ((TypAgree.typsPres env n).matchExp _ _ _ _ hm)
    · cases hm
  case typA.typ => exact matchTypV_xt h hw hm
  case defA.defName y x => cases hm; exact h
  case gramA.gram => exact xt_of_typs h (TypAgree.matchSymV_typs hm)
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

theorem resolveTyp_x {ρ : VarEnv} (h : XT ρ) {t : Typ} (ht : TyX t) : TyX (resolveTyp ρ t) := by
  unfold resolveTyp
  split
  · rename_i x
    cases hf : ρ.findTyp? x with
    | none => exact ht
    | some t' => exact h (x, t') (Script.mem_of_find? hf)
  · exact ht

theorem xTyArgs_typA {t : Typ} :
    ∀ {ags : List Arg}, xTyArgs tyB ags = true → Arg.typA t ∈ ags → TyX t
  | [], _, ha => by simp at ha
  | b :: ags, hA, ha => by
    rcases List.mem_cons.1 ha with rfl | ha'
    · simp only [xTyArgs, Bool.and_eq_true] at hA; exact ⟨hA.1.1, hA.1.2⟩
    · cases b <;> simp only [xTyArgs, Bool.and_eq_true, Bool.false_eq_true] at hA
      · exact xTyArgs_typA hA.2 ha'
      · exact xTyArgs_typA hA.2 ha'

theorem xArgs_of_xTyArgs : ∀ {ags : List Arg}, xTyArgs tyB ags = true → xArgs grE gdE ags = true
  | [], _ => rfl
  | b :: ags, hA => by
    cases b <;> simp only [xTyArgs, Bool.and_eq_true, Bool.false_eq_true] at hA
    · simp only [xArgs, EraseAll.xArg, Bool.and_eq_true]; exact ⟨hA.1, xArgs_of_xTyArgs hA.2⟩
    · simp only [xArgs, EraseAll.xArg, Bool.true_and]; exact xArgs_of_xTyArgs hA.2

/-- **Evaluated type arguments are closed checked types.** -/
theorem evalArgs_argTyX {env : Env} {n : Nat} {ρ : VarEnv} {ags : List Arg} {ws : List ArgV}
    (h : XT ρ) (hA : xTyArgs tyB ags = true) (he : evalArgs n env ρ ags = .ok ws) :
    ∀ w ∈ ws, ArgTyX w := by
  rcases n with _ | n
  · simp [evalArgs] at he
  simp only [evalArgs] at he
  intro w hw
  obtain ⟨a, ha, hfa⟩ := Script.mapM_ok_mem he w hw
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

/-! ## Related scopes for typing -/

/-- **`ErRel` on `S`, with the same type, definition and grammar variables.** -/
structure TRel (Q : Value → Prop) (S : Sets) (ρ ρ' : VarEnv) : Prop where
  er : ErRel Q gdE S ρ ρ'
  typs : ρ'.typs = ρ.typs
  defs : ρ'.defs = ρ.defs
  grams : ρ'.grams = ρ.grams

theorem TRel.mono {S T : Sets} {ρ ρ' : VarEnv} (h : TRel Q S ρ ρ') (hT : T ⊆ S) :
    TRel Q T ρ ρ' := ⟨h.er.mono hT, h.typs, h.defs, h.grams⟩

open Classical in
theorem aiPart_of_scopeIn {ρ : VarEnv} (h : ScopeIn Q ρ) : aiPart Q ρ = ρ := by
  simp only [aiPart]
  congr 1
  exact List.filter_eq_self.2 fun p hp => by simpa using h p hp

theorem tRel_of_sg {S : Sets} {ρ : VarEnv} (h : SG Q gdE ρ) : TRel Q S ρ (eraseScope ρ) := by
  have he : aiPart Q ρ = ρ := aiPart_of_scopeIn h.1
  refine ⟨⟨?_, ?_, h.2⟩, rfl, rfl, rfl⟩
  · rw [he]
  · rw [he]

theorem TRel.bindVal {S T : Sets} {ρ ρ' : VarEnv} (h : TRel Q S ρ ρ') {x : IL.Id} {v : Value}
    (hv : AllIn Q v) (hT : T.diff (boundVarid x) ⊆ S) :
    TRel Q T (ρ.bindVal x v) (ρ'.bindVal x (eraseV v)) := by
  have hb := h.er.bindVals (r := [(x, v)]) (fun p hp => by
    simp only [List.mem_singleton] at hp; subst hp; exact hv)
    (EvalFree.boundVarid_subset_keySet x) hT
  exact ⟨hb, h.typs, h.defs, h.grams⟩

theorem xt_of_tRel {S : Sets} {ρ ρ' : VarEnv} (h : TRel Q S ρ ρ') (hx : XT ρ) : XT ρ' :=
  xt_of_typs hx h.typs

/-- A closed type relates any two scopes with the same type, definition and grammar variables. -/
theorem tRel_closed {t : Typ} (ht : varsIn [] (freeTyp t) = true) {ρ ρ' : VarEnv}
    (hD : DefsG gdE ρ) (h₁ : ρ'.typs = ρ.typs) (h₂ : ρ'.defs = ρ.defs) (h₃ : ρ'.grams = ρ.grams) :
    TRel Q (freeTyp t) ρ ρ' := by
  have hv : ∀ x ∈ (freeTyp t).varid, False := fun x hx => by
    have := varsIn_mem ht x hx
    simp at this
  refine ⟨⟨⟨fun x hx => (hv x hx).elim, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩,
    ⟨fun x hx => (hv x hx).elim, fun x _ => ?_, fun x _ => ?_, fun x _ => ?_⟩, hD⟩,
    h₁, h₂, h₃⟩
  · show Map.find? ρ'.typs x = Map.find? ρ.typs x; rw [h₁]
  · show Map.find? ρ'.defs x = Map.find? ρ.defs x; rw [h₂]
  · show Map.find? ρ'.grams x = Map.find? ρ.grams x; rw [h₃]

section
variable {B : Builtins} (H : Hyps Q grE gdE (utf8Env B))
include H

/-- **Evaluation across related scopes, at every fuel.** -/
theorem evalExp_er {S : Sets} {ρ ρ' : VarEnv} {e : Exp} (h : ErRel Q gdE S ρ ρ')
    (hS : freeExp e ⊆ S) (hx : xExp grE gdE e = true) (n : Nat) :
    ER eraseV (AllIn Q) (evalExp n (utf8Env B) ρ e) (evalExp n (utf8Env B) ρ' e) := by
  have h' := h.mono hS
  rw [evalExp_agreeOn h'.ai, evalExp_agreeOn h'.er]
  exact (eraseAt H n).exp _ e (sg_aiPart h.defs) hx

theorem evalArgs_er {S : Sets} {ρ ρ' : VarEnv} {l : List Arg} (h : ErRel Q gdE S ρ ρ')
    (hS : freeArgs l ⊆ S) (hx : xArgs grE gdE l = true) (n : Nat) :
    ER (List.map eraseA) (fun ws => ∀ w ∈ ws, ArgIn Q gdE w)
      (evalArgs n (utf8Env B) ρ l) (evalArgs n (utf8Env B) ρ' l) := by
  have h' := h.mono hS
  rw [evalArgs_agreeOn h'.ai, evalArgs_agreeOn h'.er]
  exact (eraseAt H n).args _ l (sg_aiPart h.defs) hx

/-- **Field and case premises read alike** on a swap-set scope and its erasure. -/
theorem premsOk_er {ρ : VarEnv} {prems : List Prem} (hρ : SG Q gdE ρ)
    (hx : xPrems grE gdE prems = true) (n : Nat) :
    premsOk n (utf8Env B) (eraseScope ρ) prems = premsOk n (utf8Env B) ρ prems := by
  have hE := (eraseAt H n).premsHold ρ prems hρ hx
  simp only [premsOk, hE.1]
  cases premsHold n (utf8Env B) ρ prems with
  | ok _ => rfl
  | error e => cases e <;> rfl

end

theorem typBinds_erase : ∀ (ρ : VarEnv) (bs : List TypBind) (vs : List Value),
    typBinds (eraseScope ρ) bs (vs.map eraseV) = eraseScope (typBinds ρ bs vs)
  | ρ, .mk x _ :: bs, v :: vs => by
    simp only [List.map_cons, typBinds]
    rw [← EraseAll.eraseScope_bindVal]
    exact typBinds_erase _ bs vs
  | _, [], _ => by simp [typBinds]
  | _, _ :: _, [] => by simp [typBinds]

theorem caseScope_erase (ρ : VarEnv) (t : Typ) (w : Value) :
    caseScope (eraseScope ρ) t (eraseV w) = eraseScope (caseScope ρ t w) := by
  cases t with
  | tupT bs =>
    rcases w with _ | _ | _ | vs | _ | _ | _ | (_ | _) <;> simp only [caseScope, eraseV_tuple'] <;>
      first | rfl | exact typBinds_erase ρ bs vs
  | _ => cases w <;> rfl

theorem sg_typBinds : ∀ {ρ : VarEnv} {bs : List TypBind} {vs : List Value}, SG Q gdE ρ →
    (∀ v ∈ vs, AllIn Q v) → SG Q gdE (typBinds ρ bs vs)
  | ρ, .mk x _ :: bs, v :: vs, h, hv => by
    simp only [typBinds]
    exact sg_typBinds (h.bindVal (hv v List.mem_cons_self)) fun w hw =>
      hv w (List.mem_cons_of_mem _ hw)
  | _, [], _, h, _ => by simpa [typBinds] using h
  | _, _ :: _, [], h, _ => by simpa [typBinds] using h

theorem sg_caseScope {ρ : VarEnv} (h : SG Q gdE ρ) (t : Typ) {w : Value} (hw : AllIn Q w) :
    SG Q gdE (caseScope ρ t w) := by
  cases t with
  | tupT bs =>
    cases w with
    | tuple vs => exact sg_typBinds h fun v hv => EraseAll.allIn_tuple_mem hw v hv
    | _ => exact h
  | _ => exact h

/-! ## Defining conjuncts -/

theorem xExp_cmp {op : CmpOp} {t : OpTyp} {a b : Exp} (h : xExp grE gdE (.cmpE op t a b) = true) :
    xExp grE gdE a = true ∧ xExp grE gdE b = true := by
  simpa [EraseAll.xExp] using h

theorem xExp_bin {op : BinOp} {t : OpTyp} {a b : Exp} (h : xExp grE gdE (.binE op t a b) = true) :
    xExp grE gdE a = true ∧ xExp grE gdE b = true := by
  simpa [EraseAll.xExp] using h

theorem quantEqs_x {qs : List Param} {e : Exp} (hG : xExp grE gdE e = true) :
    ∀ d ∈ quantEqs qs e, xExp grE gdE d.2.2 = true ∧ Param.expP d.1 d.2.1 ∈ qs := by
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
    exact ⟨(xExp_cmp hG).1, TypAgree.quantOf_mem hq⟩
  | case3 τ a b _ x t hq =>
    intro d hd
    have hd' : d = (x, t, b) := List.mem_singleton.1 hd
    rw [hd']
    exact ⟨(xExp_cmp hG).2, TypAgree.quantOf_mem hq⟩
  | case4 => intro d hd; simp at hd
  | case5 => intro d hd; simp at hd

theorem quantDefs_x {qs : List Param} {prems : List Prem} (hG : xPrems grE gdE prems = true)
    (hq : qs.all (fun q => match q with | .expP _ t => xTy tyB t | _ => true) = true) :
    ∀ d ∈ quantDefs qs prems, xExp grE gdE d.2.2 = true ∧ xTy tyB d.2.1 = true := by
  intro d hd
  simp only [quantDefs, List.mem_flatMap] at hd
  obtain ⟨pr, hpr, hd⟩ := hd
  have hGpr := EraseAll.xPrems_mem hG pr hpr
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

/-! ## Types found under a checked name -/

theorem xInsts_of_find {B : Builtins} {x : IL.Id} {v : TypDef}
    (h : (utf8Env B).findTyp? x = some v) (hS : tyB.contains x = true) : xInsts tyB v.2 = true := by
  rw [findTyp?_utf8Env] at h
  have hm := TypAgree.mem_typs_of_findTyp h
  have := List.all_eq_true.1 xTypMap_fixed _ hm
  simp only [hS, Bool.not_true, Bool.false_or] at this
  exact this

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
