module

public import Silmaril.Net.Http1.Institution.Defs
public import Silmaril.Net.Http1.Request.Thms
public import Silmaril.Net.Http1.Profile.Thms
public import Silmaril.Net.Http1.Framing.Thms

/-! Proofs for `Silmaril.Net.Http1.Institution.Thms`. -/

@[expose] public section

namespace Silmaril.Net.Http1.Proofs.Institution

open CategoryTheory
open Silmaril.Net.Http1 Silmaril.Net.Http1.Inst
open Silmaril.Parse.ByteParse (Bytes)

theorem sat_map_iff {A B : Sig} (σ : A ⟶ B) (M : Model B) (φ : Sen A) :
    Sat M (φ.map σ) ↔ Sat (M.reduct σ) φ := by
  induction φ with
  | status m r cs => rfl
  | notStatus m r cs => rfl
  | respField m r f => rfl
  | noRespField f => rfl
  | implements c => rfl
  | unknownMethods ks cs =>
    simp only [Sen.map, Sat, Model.reduct, List.map_map]
  | framesSafely => rfl
  | closesOnClTe => rfl
  | headNoContent => rfl
  | wellFramed => rfl
  | neg φ ih => simp only [Sen.map, Sat, ih]
  | conj φ ψ ih₁ ih₂ => simp only [Sen.map, Sat, ih₁, ih₂]

theorem map_id {A : Sig} (φ : Sen A) : φ.map (𝟙 A) = φ := by
  induction φ with
  | unknownMethods ks cs =>
    show Sen.unknownMethods (ks.map id) cs = _
    rw [List.map_id]
  | neg φ ih => simp only [Sen.map, ih]
  | conj φ ψ ih₁ ih₂ => simp only [Sen.map, ih₁, ih₂]
  | _ => rfl

theorem map_comp {A B C : Sig} (σ : A ⟶ B) (τ : B ⟶ C) (φ : Sen A) :
    φ.map (σ ≫ τ) = (φ.map σ).map τ := by
  induction φ with
  | unknownMethods ks cs =>
    show Sen.unknownMethods (ks.map (τ.meth ∘ σ.meth)) cs = _
    simp [Sen.map, List.map_map]
  | neg φ ih => simp only [Sen.map, ih]
  | conj φ ψ ih₁ ih₂ => simp only [Sen.map, ih₁, ih₂]
  | _ => rfl

/-! ## The reference server -/

theorem errorResponse_valid (s : Nat) (hs : s ∈ [400, 501, 505]) : (errorResponse s).1.Valid := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl <;> decide

theorem errorResponse_fits (s : Nat) (hs : s ∈ [400, 501, 505]) (m : Bytes) (hm : m ≠ methodHEAD) :
    (errorResponse s).2.Fits (responseBodyLength m s (errorResponse s).1.fields) := by
  have hb : bodyLengthOfFields (errorResponse 0).1.fields .close .close = .length 0 := by decide
  have h₁ : ¬ (m = methodHEAD ∨ s / 100 = 1 ∨ s = 204 ∨ s = 304) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> simp [hm]
  have h₂ : ¬ (m = methodCONNECT ∧ s / 100 = 2) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> simp
  unfold responseBodyLength
  simp only [h₁, h₂, ↓reduceIte]
  change Body.Fits (bodyLengthOfFields (errorResponse 0).1.fields .close .close) (Body.content [])
  rw [hb]; rfl

theorem stripHead_fits {h : RequestHead} {r : ResponseHead × Body}
    (hf : h.line.method ≠ methodHEAD → r.2.Fits (responseBodyLength h.line.method r.1.line.code r.1.fields)) :
    (stripHead h r).2.Fits (responseBodyLength h.line.method (stripHead h r).1.line.code
      (stripHead h r).1.fields) := by
  unfold stripHead
  split
  · next hm => rw [hm, responseBodyLength_HEAD]; trivial
  · next hm => exact hf hm

theorem refModel_vanilla {cfg : ServerConfig} {H : Handler} (hp : cfg.profile.Compliant)
    (hH : Handler.WellFramed H) : Vanilla (refModel cfg H) := by
  refine ⟨⟨rfl, rfl, rfl⟩, ?_⟩
  intro φ hφ
  simp only [rfcCore, List.mem_cons, List.not_mem_nil, or_false] at hφ
  rcases hφ with rfl | rfl | rfl | rfl | rfl
  · exact fun v fs => frame_compliant hp v fs
  · intro h rh hte hcl
    show (match checkRequest cfg h with
      | .ok c => c.persistent && keepOpen cfg.keepAlive h rh
      | .error _ => false) = false
    split
    · next c hc => rw [checkRequest_clte hc hte hcl]; rfl
    · rfl
  · intro h b rh rb hm hr
    change (match checkRequest cfg h with
      | .ok c => (rh, rb) = stripHead h (H h b c)
      | .error e => (rh, rb) = stripHead h (errorResponse e.status)) at hr
    split at hr <;>
    · simp only [stripHead, hm, ite_true, Prod.mk.injEq] at hr
      rw [hr.2]; rfl
  · intro h b rh rb hr
    change (match checkRequest cfg h with
      | .ok c => (rh, rb) = stripHead h (H h b c)
      | .error e => (rh, rb) = stripHead h (errorResponse e.status)) at hr
    split at hr
    · next c _ =>
      have e₁ : rh = (stripHead h (H h b c)).1 := congrArg Prod.fst hr
      have e₂ : rb = (stripHead h (H h b c)).2 := congrArg Prod.snd hr
      subst e₁ e₂
      refine ⟨?_, stripHead_fits (hH h b c).2⟩
      unfold stripHead; split <;> exact (hH h b c).1
    · next e _ =>
      have e₁ : rh = (stripHead h (errorResponse e.status)).1 := congrArg Prod.fst hr
      have e₂ : rb = (stripHead h (errorResponse e.status)).2 := congrArg Prod.snd hr
      subst e₁ e₂
      refine ⟨?_, stripHead_fits (errorResponse_fits _ e.status_mem _)⟩
      unfold stripHead; split <;> exact errorResponse_valid _ e.status_mem
  · show chunkedName = chunkedName || cfg.implements chunkedName
    simp

theorem clWins_violates (cfg : ServerConfig) (H : Handler) :
    Violates (refModel { cfg with profile := Profile.clWins } H) .framesSafely := fun h =>
  clWins_not_compliant ((compliant_iff_safe _).1 h)

theorem keepAlways_violates (cfg : ServerConfig) (H : Handler) :
    Violates (⟨StdMethod.token, StdField.name, StdCoding.name, keepAlwaysImpl cfg H⟩ : Model Std)
      .closesOnClTe := fun h =>
  absurd (h clteHead (errorResponse 400).1 (by decide) (by decide)) (by simp [keepAlwaysImpl])

theorem patchHandler_wellFramed : Handler.WellFramed patchHandler := by
  intro h b c
  unfold patchHandler
  split
  · refine ⟨by decide, fun _ => ?_⟩
    rw [responseBodyLength_noContent _ (Or.inr (Or.inl rfl))]; trivial
  · refine ⟨by decide, fun hm => ?_⟩
    have hb : bodyLengthOfFields [⟨ascii "Allow", methodPATCH⟩, ⟨ascii "Content-Length", ascii "0"⟩]
        .close .close = .length 0 := by decide
    have h₁ : ¬ (h.line.method = methodHEAD ∨ 405 / 100 = 1 ∨ 405 = 204 ∨ 405 = 304) := by simp [hm]
    have h₂ : ¬ (h.line.method = methodCONNECT ∧ 405 / 100 = 2) := by simp
    unfold responseBodyLength
    simp only [h₁, h₂, ↓reduceIte, hb]
    rfl

theorem patchModel_reduct : patchModel.reduct (Std.incl Unit Empty Empty) = refModel {} patchHandler :=
  rfl

theorem patchModel_extensionCompliant : ExtensionCompliant patchTheory patchModel := by
  have hv := refModel_vanilla (cfg := {}) (H := patchHandler) (by decide) patchHandler_wellFramed
  refine ⟨by rw [patchModel_reduct]; exact hv.1, ?_, ?_⟩
  · intro φ hφ
    obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.1 hφ
    rw [sat_map_iff, patchModel_reduct]
    exact hv.2 ψ hψ
  · intro φ hφ
    simp only [patchTheory, List.mem_cons, List.not_mem_nil, or_false] at hφ
    subst hφ
    intro h b rh rb _ hm _ hr
    change (match checkRequest {} h with
      | .ok c => (rh, rb) = stripHead h (patchHandler h b c)
      | .error e => (rh, rb) = stripHead h (errorResponse e.status)) at hr
    have hm' : h.line.method = methodPATCH := hm
    have hnh : h.line.method ≠ methodHEAD := by rw [hm']; decide
    split at hr
    · next c _ =>
      have e₁ : rh = (stripHead h (patchHandler h b c)).1 := congrArg Prod.fst hr
      rw [e₁]
      simp [stripHead, patchHandler, hm']
    · next e _ =>
      have e₁ : rh = (stripHead h (errorResponse e.status)).1 := congrArg Prod.fst hr
      rw [e₁]
      have := e.status_mem
      simp only [stripHead, hnh, ↓reduceIte, errorResponse]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
      omega

end Silmaril.Net.Http1.Proofs.Institution
