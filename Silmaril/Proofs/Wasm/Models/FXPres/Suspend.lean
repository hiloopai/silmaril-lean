module

public import Silmaril.Proofs.Wasm.Models.FXPres.RedexFX

/-!
# Preservation at `suspend`, `switch` and calls of FX functions

* `pres_suspend`: the context captured by `suspend` is a typed continuation (by `TL.plug_inv`),
  from the tag's results to the handler's results; the values and the new continuation fit the
  clause's label. This uses the typed arity of `StepFXS.suspend`.
* `pres_switch`: `switch` is not typed, so no typed configuration takes this step.
* `pres_invoke`: by `CoreHyp.invoke`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXPres

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXBindT Silmaril.Wasm.Models.FXResume
open Silmaril.Wasm.Models.FXResumeT Silmaril.Wasm.Models.FXPres
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {E : TyEnv H} {P : Profile} {host : HostSemantics H}
  {fx : H → Option FuncFX} {s : Store H} {Γ : List TypeIdx} {K : List (Option ContFX)}
  {f : Frame} {Ls : List (List FTy)} {R : Option (List FTy)} {i o : List FTy}

/-- The hole of a `suspend`: the values have the tag's parameter types, the hole's output is
the tag's results. -/
theorem suspend_hole (hyp : CoreHyp E P host fx) {Ls' : List (List FTy)}
    {R' : Option (List FTy)} {vs : List FVal} {x : TagIdx} {ta : Nat} {ti : TagInst}
    {i' o' : List FTy} (hx : E.m₀.tags[x.toNat]? = some ta) (ht : s.tags[ta]? = some ti)
    (ha : TagArity ti vs.length) (h : TL E s Γ Ls' R' (fvals vs ++ [.fx (.suspend x)]) i' o') :
    ∃ tp tr, ti.type.funcType? = some (tp, tr) ∧ ValsTy E s Γ vs (E.tys tp) ∧
      o' = i' ++ E.tys tr := by
  obtain ⟨m, hv, hb⟩ := TL.split h
  obtain ⟨T, hmT, hT⟩ := TL.vals_inv hyp.val hv
  cases hb with
  | @suspend _ _ _ tp tr ta' ti' _ pre _ hx' ht' htt hr =>
    cases hr
    rw [hx] at hx'
    have hta : ta = ta' := Option.some.inj hx'
    subst hta
    rw [ht] at ht'
    have hti : ti = ti' := Option.some.inj ht'
    subst hti
    obtain ⟨tp', tr', htt', hlen⟩ := ha
    rw [htt] at htt'
    obtain ⟨htp, -⟩ := Prod.mk.inj (Option.some.inj htt')
    subst htp
    obtain ⟨rfl, rfl⟩ := stack_split hmT (by simp [tys_length, ← hT.length_eq, hlen])
    exact ⟨tp, tr, htt, hT, rfl⟩

/-- The clause found by `suspend` fits. -/
theorem suspend_clause {hs : List HClause} {ts : List FTy} {ta : Nat} {l : LabelIdx}
    (hh : ∀ c ∈ hs, HClauseOk E s Ls ts c)
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) :
    HClauseOk E s Ls ts (.onLabel ta l) :=
  hh _ (List.mem_of_find?_eq_some hc)

/-- The clause of a `suspend` at a tag `[tp] → [tr]`: the label takes `tp` and a continuation
from `tr` to the handler's results. -/
theorem clause_fit {ta : Nat} {ti : TagInst} {tp tr : List CValType} {l : LabelIdx}
    {ts : List FTy} (h : HClauseOk E s Ls ts (.onLabel ta l)) (hti : s.tags[ta]? = some ti)
    (htt : ti.type.funcType? = some (tp, tr)) :
    ∃ ct' rs, contType? E.m₀ ct' = some (tr, rs) ∧ E.tys rs = ts ∧
      Ls[l.toNat]? = some (E.tys tp ++ [.cont ct']) := by
  obtain ⟨ti₂, tp₂, tr₂, ct', rs, hti₂, htt₂, hct', hrs, hl⟩ := h
  have hti' : ti₂ = ti := Option.some.inj (hti₂.symm.trans hti)
  subst hti'
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj (Option.some.inj (htt₂.symm.trans htt))
  subst h₁ h₂
  exact ⟨ct', rs, hct', hrs, hl⟩

/-- The context captured by `suspend` is a typed continuation. -/
theorem contTy_suspend (hyp : CoreHyp E P host fx) {Ec : CtxV} {ct' : TypeIdx}
    {tr rs : List CValType} {Ls' : List (List FTy)} {R' : Option (List FTy)} {i' : List FTy}
    (hct' : contType? E.m₀ ct' = some (tr, rs))
    (hctx : CtxTy E s Γ Ec [] none [] (E.tys rs) Ls' R' i' (i' ++ E.tys tr)) :
    ContTy E s (Γ ++ [ct']) ⟨Ec.plug⟩ ct' := by
  refine ⟨tr, rs, hct', fun s' Γ' c hs' hΓ hc' => ?_⟩
  have hc'' : TL E s' Γ' Ls' R' c i' (i' ++ E.tys tr) := by
    simpa using TL.weaken i' (TL.lift0 Ls' R' hc')
  exact hctx s' Γ' c (CoreHyp.le hyp hs') ((List.prefix_append _ _).trans hΓ) hc''

/-- The code after `suspend`: the values, the new continuation, the branch. -/
theorem suspend_code {vs : List FVal} {tp : List CValType} {ct' : TypeIdx} {l : LabelIdx}
    {n : Nat} {ts : List FTy} (hT : ValsTy E s (Γ ++ [ct']) vs (E.tys tp))
    (hk : (Γ ++ [ct'])[n]? = some ct') (hl : Ls[l.toNat]? = some (E.tys tp ++ [.cont ct'])) :
    TL E s (Γ ++ [ct']) Ls R (fvals vs ++ [.contRef n, .core (.plain (.br l))]) i (i ++ ts) := by
  have hbr : TL E s (Γ ++ [ct']) Ls R [.core (.plain (.br l))]
      (i ++ (E.tys tp ++ [.cont ct'])) (i ++ ts) := .br hl .nil
  have hk' : TL E s (Γ ++ [ct']) Ls R (.contRef n :: [.core (.plain (.br l))])
      (i ++ E.tys tp) (i ++ ts) := .contRef hk (by simpa using hbr)
  exact TL.append (TL.vals hT i) hk'

theorem pres_suspend_body (hyp : CoreHyp E P host fx) (hf : f.module = E.m₀)
    (hK : KOk E s Γ K) {hs : List HClause} {Ec : CtxV} {vs : List FVal} {x : TagIdx}
    {ta : Nat} {ti : TagInst} {l : LabelIdx} {ts : List FTy}
    (ht : s.tag? (Ec.frameAt f) x = some (ta, ti))
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) (ha : TagArity ti vs.length)
    (hh : ∀ c ∈ hs, HClauseOk E s Ls ts c)
    (hb : TL E s Γ [] none (Ec.plug (fvals vs ++ [.fx (.suspend x)])) [] ts) :
    PresC E s Γ Ls R i (i ++ ts) s (K ++ [some ⟨Ec.plug⟩]) f
      (fvals vs ++ [.contRef K.length, .core (.plain (.br l))]) := by
  obtain ⟨Ls', R', i', o', hc0, hfr, hctx⟩ := TL.plug_inv hb
  obtain ⟨hx, hti⟩ := tag?_eq (hfr f hf) ht
  obtain ⟨tp, tr, htt, hT, rfl⟩ := suspend_hole hyp hx hti ha hc0
  obtain ⟨ct', rs, hct', hrs, hl⟩ := clause_fit (suspend_clause hh hc) hti htt
  have hC : ContTy E s (Γ ++ [ct']) ⟨Ec.plug⟩ ct' := contTy_suspend hyp hct' (hrs ▸ hctx)
  have hk : (Γ ++ [ct'])[K.length]? = some ct' := by simp [← hK.1]
  have hT' : ValsTy E s (Γ ++ [ct']) vs (E.tys tp) :=
    ValsTy.mono (CoreHyp.le hyp (hyp.ext_refl s)) (List.prefix_append Γ [ct']) hT
  exact ⟨Γ ++ [ct'], List.prefix_append _ _, hyp.ext_refl s, hf, KOk.push hyp hK hC,
    suspend_code hT' hk hl⟩

theorem pres_suspend (hyp : CoreHyp E P host fx) (hf : f.module = E.m₀) (hK : KOk E s Γ K)
    {hs : List HClause} {Ec : CtxV} {vs : List FVal} {x : TagIdx} {ta : Nat} {ti : TagInst}
    {l : LabelIdx} (ht : s.tag? (Ec.frameAt f) x = some (ta, ti))
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l))
    (ha : TagArity ti vs.length)
    (h : TL E s Γ Ls R [.handler hs (Ec.plug (fvals vs ++ [.fx (.suspend x)]))] i o) :
    PresC E s Γ Ls R i o s (K ++ [some ⟨Ec.plug⟩]) f
      (fvals vs ++ [.contRef K.length, .core (.plain (.br l))]) := by
  cases h with
  | handler hh hb hr =>
    cases hr
    exact pres_suspend_body hyp hf hK ht hc ha hh hb

theorem pres_switch {hs : List HClause} {Ec : CtxV} {vs : List FVal} {k : Nat}
    {ct : TypeIdx} {x : TagIdx} {P' : Prop}
    (h : TL E s Γ Ls R [.handler hs (Ec.plug (fvals vs ++ [.contRef k, .fx (.switch ct x)]))]
      i o) : P' := by
  cases h with
  | handler _ hb _ =>
    obtain ⟨_, _, _, _, hc0, -, -⟩ := TL.plug_inv hb
    obtain ⟨m, -, hb'⟩ := TL.split hc0
    cases hb' with
    | contRef _ hr => cases hr

theorem callRef_not_ctl {c : Admin} (hc : c.IsCallRef) : ¬ IsCtl c := by
  intro h
  unfold IsCtl at h
  split at h <;> simp_all [Admin.IsCallRef]

theorem pres_invoke (hyp : CoreHyp E P host fx) (hf : f.module = E.m₀) (hK : KOk E s Γ K)
    {c : Admin} {vs : List Val} {a : Nat} {fi : FuncInst H} {h : H} {F : FuncFX}
    (hc : c.IsCallRef) (hfa : s.funcs[a]? = some fi) (hcode : fi.code = .host h)
    (hfx : fx h = some F) (hn : vs.length = F.nparams)
    (ht : TL E s Γ Ls R (cvals vs ++ [.core (.ref (.func a)), .core c]) i o) :
    PresC E s Γ Ls R i o s K f [.frame F.nresults (Frame.forCall F.module vs F.locals)
      [.label F.nresults [] (F.body.map InstrFX.toAdmin)]] := by
  rw [← fvals_liftV] at ht
  obtain ⟨m, hv, hb⟩ := TL.split ht
  obtain ⟨T, hmT, hT⟩ := TL.vals_inv hyp.val hv
  obtain ⟨pre, i₀, o₀, hcr, hpre, hr⟩ := TL.core_inv (a := .ref (.func a)) (by simp [IsCtl]) hb
  obtain ⟨rfl, t, rfl⟩ := hyp.val (v := .ref (.func a)) hcr
  obtain ⟨pre₂, i₁, o₁, hcc, hpre₂, hr₂⟩ := TL.core_inv (callRef_not_ctl hc) hr
  cases hr₂
  obtain ⟨ps, rs, rfl, rfl, hps, hmod, hres, hbody⟩ :=
    hyp.invoke (Γ := Γ) hc hfa hcode hfx hcr hcc
  rw [List.append_nil] at hpre
  subst hpre
  rw [hmT] at hpre₂
  have hpre₃ : (i ++ T) ++ [t] = (pre₂ ++ ps) ++ [t] := by rw [hpre₂, List.append_assoc]
  obtain ⟨hpre₄, -⟩ := List.append_inj' hpre₃ rfl
  obtain ⟨rfl, -⟩ := stack_split hpre₄ (by rw [hps, ← hn, ← hT.length_eq, liftV, List.length_map])
  refine presC_same hyp hf hK (.frame (pre := i) hmod hres ?_ .nil)
  exact .label (pre := []) hres .nil (by simpa using hbody) (by simpa using TL.nil)

end Silmaril.Proofs.Wasm.Models.FXPres
