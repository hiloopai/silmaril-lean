module

public import Silmaril.Proofs.Wasm.LimeCompile.HandleTr.Equiv
public import Silmaril.Proofs.Wasm.LimeCompile.HandleTr.Api

/-!
# The handle compiler is correct on the forwarder fragment

* `compile0_fwd`: on a forwarder module, a successful `compile0` returns `tgtM M`
  (the bodies are unchanged; only the types are rewritten);
* `scriptRelT_lime`, `equivUpToT_self`: at a Lime API a typed-handle-related script is the
  source script, so every module is `EquivUpToT` itself;
* **`fwd_handleCorrect`**: `HandleCorrectOnT FwdFrag compile`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.HandleTr

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen (SessionRel moduleObs)
open Silmaril.Wasm.LimeCompile Silmaril.Wasm.LimeCompile.HandleTr
open Silmaril.Wasm.LimeCompile.Handle (handleRef BehRel ArgRel ArgsRel CallRel ScriptRel)
open Silmaril.Wasm.LimeCompile.Preserve (ApiLime)
open Silmaril.Wasm.LimeCompile.Preserve.Module (exportApi)

variable {H : Type}

theorem hL_localGets : ∀ js : List LocalIdx, hL (js.map .localGet) = js.map .localGet
  | [] => by rw [List.map_nil, hL]
  | j :: js => by rw [List.map_cons, hL, hL_localGets js, hI] <;> simp

theorem lowerL_localGets :
    ∀ js : List LocalIdx, Direct.lowerL (js.map .localGet) = js.map .localGet
  | [] => by rw [List.map_nil, Direct.lowerL]
  | j :: js => by rw [List.map_cons, Direct.lowerL, lowerL_localGets js, Direct.lowerI] <;> simp

theorem lowerModule_hModule {M : Module} (hM : onlyFuncs M = true)
    (hfwd : ∀ f ∈ M.funcs, fwdFunc f = true) : Direct.lowerModule (hModule M) = tgtM M := by
  have hg : M.globals = [] := (onlyFuncs_fields hM).2.2.1
  have hf : M.funcs.map (Direct.lowerFunc ∘ hFunc) = M.funcs := by
    conv => rhs; rw [← List.map_id M.funcs]
    apply List.map_congr_left
    intro f hfm
    obtain ⟨hloc, js, hbody⟩ := fwd_body (hfwd f hfm)
    obtain ⟨ty, locals, body⟩ := f
    subst hloc hbody
    simp [Direct.lowerFunc, hFunc, hL_localGets, lowerL_localGets]
  simp only [Direct.lowerModule, hModule, tgtM, hg, List.map_nil, List.map_map, hf]

/-- On a forwarder module, the non-Lime branch of the compiler returns the type rewrite. -/
theorem compile0_fwd {M : Module} {l : Lime1.Module} (hM : onlyFuncs M = true)
    (hfwd : ∀ f ∈ M.funcs, fwdFunc f = true) (h : compile0 M = some l) : l.toCore = tgtM M := by
  unfold compile0 at h
  split at h
  · rw [Silmaril.Wasm.LimeCompile.Direct.compile_toCore h, lowerModule_hModule hM hfwd]
  · cases h

theorem argRelT_argRel {σ : List Val} {t : ValType} {w v : Val} (h : ArgRelT σ t w v) :
    ArgRel σ t w v := by
  rcases h with h | ⟨ht, k, hw, hk, hok⟩
  · exact .inl h
  · obtain ⟨r, rfl⟩ := handleOk_ref hok
    exact .inr ⟨ht, k, r, rfl, hw, hk⟩

theorem scriptRelT_scriptRel {σ : List Val} {A : List (String × Option Preserve.ApiTy)}
    {sc' sc : List Binaryen.Call} (h : ScriptRelT σ A sc' sc) : ScriptRel σ A sc' sc := by
  refine h.imp fun c' c hc => ⟨hc.1, ?_⟩
  have h2 := hc.2
  cases hp : Silmaril.Wasm.LimeCompile.Handle.paramsOf A c.1 with
  | none =>
    simp only [hp] at h2 ⊢
    exact h2
  | some ps =>
    simp only [hp] at h2 ⊢
    unfold ArgsRelT at h2
    unfold ArgsRel
    by_cases hl : c.2.length = ps.length
    · simp only [hl, ↓reduceIte] at h2 ⊢
      exact h2.imp fun _ _ h => argRelT_argRel h
    · simp only [hl, ↓reduceIte] at h2 ⊢
      exact h2

/-- **Every module is equivalent to itself up to typed handles at a Lime API.** -/
theorem equivUpToT_self {M : Module} (hA : ApiLime (exportApi M)) (σ : List Val) (P : Profile)
    (host : HostSemantics H) : EquivUpToT σ P host M M := by
  have hsc : ∀ {sc' sc}, ScriptRelT σ (exportApi M) sc' sc → sc' = sc := fun h =>
    Silmaril.Proofs.Wasm.LimeCompile.Handle.scriptRel_eq hA (scriptRelT_scriptRel h)
  refine ⟨⟨fun _ _ c _ hc => ⟨c, hc⟩, ?_⟩, ⟨fun _ _ c _ hc => ⟨c, hc⟩, ?_⟩⟩
  · intro s xas sc' sc _ h bs hbs
    obtain rfl := hsc h
    exact ⟨bs, hbs, SessionRel.refl (fun _ => .inl rfl) bs⟩
  · intro s xas sc' sc _ h bs hbs
    obtain rfl := hsc h
    exact ⟨bs, hbs, SessionRel.refl (fun _ => .inl rfl) bs⟩

/-- **The handle compiler is correct on the forwarder fragment.** -/
theorem fwd_handleCorrect : HandleCorrectOnT FwdFrag compile := by
  intro M l hF hl
  obtain ⟨hM, hfwd, ⟨ts, hts⟩, hvM, hvT⟩ := hF
  refine ⟨compile_api hl, fun H σ P host _ _ => ?_⟩
  have hvT' := hvT l hl
  unfold compile Preserve.limePres at hl
  cases hv : Preserve.limeView M with
  | some l' =>
    rw [hv] at hl
    cases hl
    have hM' : l.toCore = M := Preserve.limeView_eq_some_iff.mp hv
    rw [hM']
    exact equivUpToT_self (hM' ▸ Preserve.apiLime_toCore l) σ P host
  | none =>
    rw [hv] at hl
    rw [compile0_fwd hM hfwd hl] at hvT' ⊢
    exact fwd_equiv hM hfwd hts hvM hvT' σ P host

end Silmaril.Proofs.Wasm.LimeCompile.HandleTr
