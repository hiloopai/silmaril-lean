module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxFlow.Exp

/-!
# Round 7, REH route 2: `evalExp`, one step, every constructor (unrefined)
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB nxBs nxBf)

variable {env : Env} {n : Nat}

set_option maxHeartbeats 1000000 in
/-- **`evalExp`, one step.** -/
theorem step_exp (ih : ExpAt env n) (S : Sig) (T : TSig) (Γ : List (String × AT))
    (tps : AuxCtx) (ρ : VarEnv) (e : Exp) (v : Value) (hρ : ScopeVT S Γ ρ)
    (hc : CallH S T tps env ρ (n + 1)) (ht : tyOk S T Γ e = true) (ha : auxE tps e = true)
    (hv : evalExp (n + 1) env ρ e = .ok v) : EOk S T Γ e v := by
  have hc' := hc.mono (Nat.le_succ n)
  cases e with
  | varE x =>
    simp only [evalExp, Res.ofOption_eq_ok] at hv
    have hty : vtB S (tyOf S Γ (.varE x)) v = true := by
      rw [tyOf_varE]
      cases hx : Γ.lookup x with
      | none => exact vtB_unk S v
      | some a => exact hρ.val x a v hx hv
    refine EOk.of_ty_nx hty (fun h => ?_) (fun a h => by simpa only [ckE] using h)
    simp only [nxD, nxE] at h
    exact nxB_of_vtB h hty
  | boolE b => simp only [evalExp, Except.ok.injEq] at hv; subst hv; exact EOk.of_nxB (nxB_bool _)
  | numE m => simp only [evalExp, Except.ok.injEq] at hv; subst hv; exact EOk.of_nxB (nxB_num _)
  | textE t => simp only [evalExp, Except.ok.injEq] at hv; subst hv; exact EOk.of_nxB (by simp [nxB])
  | unE op t e =>
    simp only [evalExp, Res.bind_eq_ok] at hv
    obtain ⟨w, _, hw⟩ := hv
    exact EOk.of_nxB (unValue_nx hw)
  | binE op t e₁ e₂ =>
    simp only [evalExp, Res.bind_eq_ok] at hv
    obtain ⟨v₁, _, hv⟩ := hv
    cases hb : boolShort op v₁ with
    | some u =>
      rw [hb] at hv; cases hv; exact EOk.of_nxB (boolShort_nx hb)
    | none =>
      rw [hb] at hv
      simp only [Res.bind_eq_ok] at hv
      obtain ⟨v₂, _, hw⟩ := hv
      exact EOk.of_nxB (binValues_nx hw)
  | cmpE op t e₁ e₂ =>
    simp only [evalExp, Res.bind_eq_ok] at hv
    obtain ⟨v₁, _, v₂, _, hw⟩ := hv
    exact EOk.of_nxB (cmpValues_nx hw)
  | tupE es =>
    simp only [tyOk] at ht; simp only [auxE] at ha
    simp only [evalExp, Res.map_eq_ok] at hv
    obtain ⟨vs, hvs, rfl⟩ := hv
    have h2 := ih.exps S T Γ tps ρ es vs hρ hc' ht ha hvs
    have hnx : nxD S Γ (.tupE es) = true → nxB (.tuple vs) = true := by
      intro h
      simp only [nxD, nxE, Bool.or_eq_true] at h
      simp only [nxB]
      rcases h with h | h
      · exact nxEs_sound h2 h
      · exact nxDs_sound h2 h
    refine ⟨by simp only [tyOf]; exact vtB_unk S _, hnx, fun a h => ?_⟩
    simp only [ckE, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases h with (⟨_, hl⟩ | ht') | ⟨hn, hm⟩
    · refine vtB_of_nxB' ?_
      simp only [nxB]
      exact nxBs_of_forall fun w hw => nxB_of_base (ckL_sound h2 hl w hw)
    · exact vtB_of_triv ht' _
    · split at hm
      · rename_i xs hu
        rw [vtB_tup hn hu]
        exact ckT_sound h2 hm
      · cases hm
  | projE e i =>
    simp only [tyOk] at ht; simp only [auxE] at ha
    simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at hv
    obtain ⟨v', hv', vs, hvs, hi⟩ := hv
    have h1 := ih.exp S T Γ tps ρ e v' hρ hc' ht ha hv'
    rw [Value.asTuple?_eq_some] at hvs
    subst hvs
    split at hi
    · rename_i h0
      have hty : vtB S (tyOf S Γ (.projE e i)) v = true := by
        rw [tyOf_projE e h0]; exact vtB_proj h1.ty hi
      refine EOk.of_ty_nx hty (fun h => ?_) (fun a h => by simpa only [ckE] using h)
      simp only [nxD, Bool.or_eq_true] at h
      rcases h with h | h
      · simp only [nxE] at h; exact nxB_of_vtB h hty
      · have := h1.nx h
        simp only [nxB] at this
        exact (nxBs_iff vs).1 this v (List.mem_of_getElem? hi)
    · cases hi
  | caseE op e =>
    simp only [tyOk] at ht; simp only [auxE] at ha
    simp only [evalExp, Res.map_eq_ok] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    have h1 := ih.exp S T Γ tps ρ e w hρ hc' ht ha hw
    have hnx : nxD S Γ (.caseE op e) = true → nxB (.case op w) = true := by
      intro h
      simp only [nxD, nxE, Bool.or_eq_true] at h
      simp only [nxB]
      rcases h with h | h
      · exact h1.nx (nxD_of_nxE e h)
      · exact h1.nx h
    refine ⟨by simp only [tyOf]; exact vtB_unk S _, hnx, fun a h => ?_⟩
    simp only [ckE, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases h with (⟨_, hl⟩ | ht') | ⟨hn, hm⟩
    · refine vtB_of_nxB' ?_
      simp only [nxB]
      exact nxB_of_base (h1.ck _ hl)
    · exact vtB_of_triv ht' _
    · split at hm
      · rename_i m xs hu
        rw [vtB_case_name hn hu]
        exact h1.ck _ hm
      · cases hm
  | uncaseE e op =>
    simp only [tyOk] at ht; simp only [auxE] at ha
    simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at hv
    obtain ⟨v', hv', ⟨op', w⟩, hcase, hass⟩ := hv
    simp only [Res.assert_eq_ok, Except.ok.injEq] at hass
    obtain ⟨rfl, rfl⟩ := hass
    rw [Value.asCase?_eq_some] at hcase
    subst hcase
    have h1 := ih.exp S T Γ tps ρ e _ hρ hc' ht ha hv'
    have hty : vtB S (tyOf S Γ (.uncaseE e op')) w = true := by
      rw [tyOf_uncaseE]; exact vtB_payload h1.ty
    refine EOk.of_ty_nx hty (fun h => ?_) (fun a h => by simpa only [ckE] using h)
    simp only [nxD, Bool.or_eq_true] at h
    rcases h with h | h
    · simp only [nxE] at h; exact nxB_of_vtB h hty
    · have := h1.nx h
      simpa only [nxB] using this
  | optE eo =>
    cases eo with
    | none =>
      simp only [evalExp, Except.ok.injEq] at hv; subst hv; exact EOk.of_nxB (by simp [nxB])
    | some e =>
      simp only [tyOk] at ht; simp only [auxE] at ha
      simp only [evalExp, Res.map_eq_ok] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      have h1 := ih.exp S T Γ tps ρ e w hρ hc' ht ha hw
      have hty : vtB S (tyOf S Γ (.optE (some e))) (.opt (some w)) = true := by
        rw [tyOf_optSome]; exact vtB_iter_some h1.ty
      refine ⟨hty, fun h => ?_, fun a h => ?_⟩
      · simp only [nxD, nxE, Bool.or_eq_true] at h
        simp only [nxB]
        rcases h with h | h
        · exact h1.nx (nxD_of_nxE e h)
        · exact h1.nx h
      · simp only [ckE, Bool.or_eq_true] at h
        rcases h with h | h
        · exact vtB_of_atLe S _ _ _ h _ hty
        · exact vtB_optSome_of (h1.ck _ h)
  | theE e =>
    simp only [tyOk] at ht; simp only [auxE] at ha
    simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at hv
    obtain ⟨v', hv', o, ho, hw⟩ := hv
    rw [Value.asOpt?_eq_some] at ho
    subst ho; subst hw
    have h1 := ih.exp S T Γ tps ρ e _ hρ hc' ht ha hv'
    have hty : vtB S (tyOf S Γ (.theE e)) v = true := by
      rw [tyOf_theE]; exact vtB_elemAT_of_elemOf (vtB_elemOpt h1.ty)
    refine EOk.of_ty_nx hty (fun h => ?_) (fun a h => by simpa only [ckE] using h)
    simp only [nxD, Bool.or_eq_true] at h
    rcases h with h | h
    · simp only [nxE] at h; exact nxB_of_vtB h hty
    · have := h1.nx h
      simpa only [nxB] using this
  | strE fs =>
    simp only [tyOk] at ht; simp only [auxE] at ha
    simp only [evalExp, Res.map_eq_ok] at hv
    obtain ⟨gs, hgs, rfl⟩ := hv
    have h2 := ih.fields S T Γ tps ρ fs gs hρ hc' ht ha hgs
    have h2' : List.Forall₂ (FOk S T Γ) fs gs := h2
    have hnx : nxD S Γ (.strE fs) = true → nxB (.struct gs) = true := by
      intro h
      simp only [nxD, nxE] at h
      simp only [nxB]
      exact nxFs_sound h2' h
    refine ⟨by simp only [tyOf]; exact vtB_unk S _, hnx, fun a h => ?_⟩
    simp only [ckE, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases h with (⟨_, hl⟩ | ht') | ⟨hn, hm⟩
    · refine vtB_of_nxB' ?_
      simp only [nxB]
      exact ckFsN_sound h2' hl
    · exact vtB_of_triv ht' _
    · split at hm
      · rename_i m xs hu
        rw [vtB_struct_name hn hu]
        exact ckFs_sound h2' hm
      · cases hm
  | dotE e k =>
    simp only [tyOk] at ht; simp only [auxE] at ha
    simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at hv
    obtain ⟨v', hv', hf⟩ := hv
    have h1 := ih.exp S T Γ tps ρ e v' hρ hc' ht ha hv'
    have hty : vtB S (tyOf S Γ (.dotE e k)) v = true := by
      rw [tyOf_dotE]; exact vtB_field? h1.ty hf
    refine EOk.of_ty_nx hty (fun h => ?_) (fun a h => by simpa only [ckE] using h)
    simp only [nxD, Bool.or_eq_true] at h
    rcases h with h | h
    · simp only [nxE] at h; exact nxB_of_vtB h hty
    · exact nxB_field? (h1.nx h) hf
  | compE e₁ e₂ =>
    simp only [tyOk, Bool.and_eq_true] at ht; simp only [auxE, Bool.and_eq_true] at ha
    simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at hv
    obtain ⟨v₁, hv₁, v₂, hv₂, hcomp⟩ := hv
    have h1 := ih.exp S T Γ tps ρ e₁ v₁ hρ hc' ht.1 ha.1 hv₁
    have h2 := ih.exp S T Γ tps ρ e₂ v₂ hρ hc' ht.2 ha.2 hv₂
    refine ⟨by simp only [tyOf]; exact vtB_unk S _, fun h => ?_, fun a h => ?_⟩
    · simp [nxD, nxE, tyOf, nxAT] at h
    · simp only [ckE, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with h | ⟨ha₁, ha₂⟩
      · exact vtB_of_triv h _
      · exact vtB_comp? a v₁ v₂ v (h1.ck a ha₁) (h2.ck a ha₂) hcomp
  | listE es =>
    simp only [tyOk, Bool.and_eq_true] at ht; simp only [auxE] at ha
    simp only [evalExp, Res.map_eq_ok] at hv
    obtain ⟨vs, hvs, rfl⟩ := hv
    have h2 := ih.exps S T Γ tps ρ es vs hρ hc' ht.1 ha hvs
    have hty : vtB S (tyOf S Γ (.listE es)) (.list vs) = true := by
      have hc2 := ht.2
      cases h2 with
      | nil => rw [tyOf_listE_nil]; exact vtB_unk S _
      | @cons e w es' vs' he hs =>
        rw [tyOf_listE_cons]
        refine vtB_iter_list fun u hu => ?_
        rcases List.mem_cons.1 hu with rfl | hu
        · exact he.ty
        · exact ckL_sound hs hc2 u hu
    refine ⟨hty, fun h => ?_, fun a h => ?_⟩
    · simp only [nxD, nxE, Bool.or_eq_true] at h
      simp only [nxB]
      rcases h with h | h
      · exact nxEs_sound h2 h
      · exact nxDs_sound h2 h
    · simp only [ckE, Bool.or_eq_true] at h
      rcases h with h | h
      · exact vtB_of_atLe S _ _ _ h _ hty
      · exact vtB_list_of (ckL_sound h2 h)
  | liftE e =>
    simp only [tyOk] at ht; simp only [auxE] at ha
    simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok, Except.ok.injEq] at hv
    obtain ⟨v', hv', o, ho, rfl⟩ := hv
    rw [Value.asOpt?_eq_some] at ho
    subst ho
    have h1 := ih.exp S T Γ tps ρ e _ hρ hc' ht ha hv'
    refine ⟨by simp only [tyOf]; exact vtB_unk S _, fun h => ?_, fun a h => ?_⟩
    · simp only [nxD, nxE, Bool.or_eq_true] at h
      have hn : nxB (.opt o) = true := by
        rcases h with h | h
        · exact h1.nx (nxD_of_nxE e h)
        · exact h1.nx h
      cases o <;> simp_all [nxB, nxBs]
    · simp only [ckE, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with h | ⟨_, h⟩
      · exact vtB_of_triv h _
      · exact vtB_lift (h1.ck a h)
  | memE e₁ e₂ =>
    simp only [evalExp, Res.bind_eq_ok] at hv
    obtain ⟨v₁, _, v₂, _, hw⟩ := hv
    exact EOk.of_nxB (memValue_nx hw)
  | lenE e =>
    simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok, Option.map_eq_some_iff] at hv
    obtain ⟨_, _, k, _, rfl⟩ := hv
    exact EOk.of_nxB (nxB_num _)
  | catE e₁ e₂ =>
    simp only [tyOk, Bool.and_eq_true] at ht; simp only [auxE, Bool.and_eq_true] at ha
    simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at hv
    obtain ⟨v₁, hv₁, v₂, hv₂, hcat⟩ := hv
    have h1 := ih.exp S T Γ tps ρ e₁ v₁ hρ hc' ht.1.1 ha.1 hv₁
    have h2 := ih.exp S T Γ tps ρ e₂ v₂ hρ hc' ht.1.2 ha.2 hv₂
    have hty : vtB S (tyOf S Γ (.catE e₁ e₂)) v = true := by
      rw [tyOf_catE]; exact vtB_cat? h1.ty (h2.ck _ ht.2) hcat
    refine ⟨hty, fun h => ?_, fun a h => ?_⟩
    · simp only [nxD, nxE, Bool.or_eq_true, Bool.and_eq_true] at h
      have hb : nxB v₁ = true ∧ nxB v₂ = true := by
        rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact ⟨h1.nx (nxD_of_nxE e₁ h₁), h2.nx (nxD_of_nxE e₂ h₂)⟩
        · exact ⟨h1.nx h₁, h2.nx h₂⟩
      exact nxB_of_base (S := S) (vtB_cat? (base_of_nxB hb.1) (base_of_nxB hb.2) hcat)
    · simp only [ckE, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with h | ⟨⟨_, ha₁⟩, ha₂⟩
      · exact vtB_of_atLe S _ _ _ h _ hty
      · exact vtB_cat? (h1.ck a ha₁) (h2.ck a ha₂) hcat
  | idxE e₁ e₂ =>
    simp only [tyOk, Bool.and_eq_true] at ht; simp only [auxE, Bool.and_eq_true] at ha
    simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at hv
    obtain ⟨v₁, hv₁, v₂, _, i, _, hi⟩ := hv
    have h1 := ih.exp S T Γ tps ρ e₁ v₁ hρ hc' ht.1 ha.1 hv₁
    have hty : vtB S (tyOf S Γ (.idxE e₁ e₂)) v = true := by
      rw [tyOf_idxE]; exact vtB_elemAT_of_elemOf (vtB_idx? h1.ty hi)
    refine EOk.of_ty_nx hty (fun h => ?_) (fun a h => by simpa only [ckE] using h)
    simp only [nxD, Bool.or_eq_true] at h
    rcases h with h | h
    · simp only [nxE] at h; exact nxB_of_vtB h hty
    · have := vtB_idx? (base_of_nxB (S := S) (h1.nx h)) hi
      rw [elemOf_of_nx (by simp [nxAT])] at this
      exact nxB_of_base this
  | sliceE e₁ e₂ e₃ =>
    simp only [tyOk, Bool.and_eq_true] at ht; simp only [auxE, Bool.and_eq_true] at ha
    simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at hv
    obtain ⟨v₁, hv₁, v₂, _, v₃, _, i, _, k, _, hs⟩ := hv
    have h1 := ih.exp S T Γ tps ρ e₁ v₁ hρ hc' ht.1.1 ha.1.1 hv₁
    have hty : vtB S (tyOf S Γ (.sliceE e₁ e₂ e₃)) v = true := by
      rw [tyOf_sliceE]; exact vtB_slice? h1.ty hs
    refine EOk.of_ty_nx hty (fun h => ?_) (fun a h => by simpa only [ckE] using h)
    simp only [nxD, Bool.or_eq_true] at h
    rcases h with h | h
    · simp only [nxE] at h; exact nxB_of_vtB h hty
    · exact nxB_of_base (vtB_slice? (base_of_nxB (S := S) (h1.nx h)) hs)
  | updE e₁ p e₂ =>
    simp only [tyOk, Bool.and_eq_true] at ht; simp only [auxE, Bool.and_eq_true] at ha
    simp only [evalExp, Res.bind_eq_ok] at hv
    obtain ⟨v₁, hv₁, v₂, hv₂, hset⟩ := hv
    have h1 := ih.exp S T Γ tps ρ e₁ v₁ hρ hc' ht.1.1 ha.1 hv₁
    have h2 := ih.exp S T Γ tps ρ e₂ v₂ hρ hc' ht.2 ha.2 hv₂
    refine ⟨by simp only [tyOf]; exact vtB_unk S _, fun h => ?_, fun a h => ?_⟩
    · simp [nxD, nxE, tyOf, nxAT] at h
    · simp only [ckE, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with h | ⟨ha₁, ha₂⟩
      · exact vtB_of_triv h _
      · exact ih.pathSet S ρ a v₁ p v₂ v (h1.ck a ha₁) (h2.ck _ ha₂) hset
  | extE e₁ p e₂ =>
    simp only [tyOk, Bool.and_eq_true] at ht; simp only [auxE, Bool.and_eq_true] at ha
    simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] at hv
    obtain ⟨v₁, hv₁, v₂, hv₂, u, hu, u', hu', hset⟩ := hv
    have h1 := ih.exp S T Γ tps ρ e₁ v₁ hρ hc' ht.1.1 ha.1 hv₁
    have h2 := ih.exp S T Γ tps ρ e₂ v₂ hρ hc' ht.2 ha.2 hv₂
    refine ⟨by simp only [tyOf]; exact vtB_unk S _, fun h => ?_, fun a h => ?_⟩
    · simp [nxD, nxE, tyOf, nxAT] at h
    · simp only [ckE, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with h | ⟨⟨ha₁, _⟩, ha₂⟩
      · exact vtB_of_triv h _
      · have hg := ih.pathGet S ρ a v₁ p u (h1.ck a ha₁) hu
        exact ih.pathSet S ρ a v₁ p u' v (h1.ck a ha₁) (vtB_cat? hg (h2.ck _ ha₂) hu') hset
  | callE f xs =>
    simp only [evalExp] at hv
    exact ih.call S T Γ tps ρ f xs v hρ hc' ht ha hv
  | iterE e ie =>
    obtain ⟨it, ds⟩ := ie
    simp only [tyOk, Bool.and_eq_true] at ht; simp only [auxE, Bool.and_eq_true] at ha
    simp only [evalExp] at hv
    exact EOk.iter (ih.iter S T Γ tps ρ e it ds v hρ hc' ht.1.1 ht.1.2 ht.2 ha.1.1.1
      ha.1.1.2 ha.1.2 ha.2 hv)
  | cvtE e t₁ t₂ =>
    simp only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok, Option.map_eq_some_iff] at hv
    obtain ⟨_, _, m, _, m', _, rfl⟩ := hv
    exact EOk.of_nxB (nxB_num _)
  | subE e t₁ t₂ =>
    simp only [tyOk, Bool.and_eq_true] at ht; simp only [auxE] at ha
    simp only [evalExp] at hv
    have h1 := ih.exp S T Γ tps ρ e v hρ hc' ht.1 ha hv
    have hty : vtB S (tyOf S Γ (.subE e t₁ t₂)) v = true := by
      rw [tyOf_subE]; exact h1.ck _ ht.2
    refine ⟨hty, fun h => ?_, fun a h => ?_⟩
    · simp only [nxD, nxE, Bool.or_eq_true] at h
      rcases h with (h | h) | h
      · exact h1.nx (nxD_of_nxE e h)
      · rw [tyOf_subE] at hty; exact nxB_of_vtB h hty
      · exact h1.nx h
    · simp only [ckE] at h
      exact h1.ck a h

end Silmaril.Wasm.SpecTec.Sim.Round7.NxFlow
