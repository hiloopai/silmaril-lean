module

public import Silmaril.Wasm.Models.FXLower.Defs
public import Silmaril.Wasm.Models.FX.Thms

/-!
# Conservativity with live continuations

`stepFX_conservative` (track H) is stated at `ofCore c`, whose continuation store is empty. A
Core configuration reached inside an FX program can have live continuations. Here the store is
any `K`:

* `ofCoreK K c`: the Core configuration `c` with continuation store `K`;
* `step_ofCoreK`: an FX step from `ofCoreK K c` (store without FX functions) is the image of a
  Core step, and keeps `K`;
* `ofCoreK_step`: every Core step lifts.

New proofs, following the structure of track H's `step_ofCore`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXLower

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX
open Silmaril.Proofs.Wasm.Models.FX (isCore map_core_inj split3 hne_map all_isCore_map)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

/-- A Core configuration with continuation store `K`. -/
def ofCoreK (K : List (Option ContFX)) (c : Config H) : ConfigFX H :=
  ⟨c.store, K, c.frame, c.code.map .core⟩

theorem ofCoreK_eq {K : List (Option ContFX)} {c : Config H} {s : Store H}
    {K' : List (Option ContFX)} {f : Frame} {L : List AdminFX}
    (h : (⟨s, K', f, L⟩ : ConfigFX H) = ofCoreK K c) :
    s = c.store ∧ K' = K ∧ f = c.frame ∧ L = c.code.map AdminFX.core := by
  simp only [ofCoreK, ConfigFX.mk.injEq] at h
  exact h

theorem ofCoreK_mk (K : List (Option ContFX)) (s : Store H) (f : Frame) (cs : List Admin) :
    ofCoreK K (⟨s, f, cs⟩ : Config H) = ⟨s, K, f, cs.map AdminFX.core⟩ := rfl

theorem config_mk_of {c : Config H} {s : Store H} {f : Frame} {cs : List Admin}
    (hs : s = c.store) (hf : f = c.frame) (hc : cs = c.code) : c = ⟨s, f, cs⟩ := by
  cases c
  simp only at hs hf hc
  rw [hs, hf, hc]

/-- The `seq` case. -/
theorem caseK_seq {s s' : Store H} {K₀ K₀' : List (Option ContFX)} {f f' : Frame}
    {vs : List Val} {es es' rest : List AdminFX} (hne : vs ≠ [] ∨ rest ≠ [])
    (ih : ∀ K (c : Config H), (⟨s, K₀, f, es⟩ : ConfigFX H) = ofCoreK K c → NoFX fx c.store →
      ∃ c', Step P (blockFX host fx) c c' ∧ (⟨s', K₀', f', es'⟩ : ConfigFX H) = ofCoreK K c')
    (K : List (Option ContFX)) (c : Config H)
    (hx : (⟨s, K₀, f, cvals vs ++ es ++ rest⟩ : ConfigFX H) = ofCoreK K c)
    (hno : NoFX fx c.store) :
    ∃ c', Step P (blockFX host fx) c c' ∧
      (⟨s', K₀', f', cvals vs ++ es' ++ rest⟩ : ConfigFX H) = ofCoreK K c' := by
  obtain ⟨hs, hK, hf, hL⟩ := ofCoreK_eq hx
  obtain ⟨A, B, C, hc, hA, hB, hC⟩ := split3 hL
  have hA' : A = vals vs := map_core_inj hA
  have hin : (⟨s, K₀, f, es⟩ : ConfigFX H) = ofCoreK K ⟨s, f, B⟩ := by
    rw [ofCoreK_mk, hB, hK]
  obtain ⟨c₁, hstep, hy⟩ := ih K ⟨s, f, B⟩ hin (hs ▸ hno)
  obtain ⟨hs₁, hK₁, hf₁, hes'⟩ := ofCoreK_eq hy
  have hcc : c = ⟨s, f, vals vs ++ B ++ C⟩ := config_mk_of hs hf (by rw [hc, hA'])
  have hstep' : Step P (blockFX host fx) ⟨s, f, B⟩ ⟨c₁.store, c₁.frame, c₁.code⟩ := by
    cases c₁
    exact hstep
  refine ⟨⟨c₁.store, c₁.frame, vals vs ++ c₁.code ++ C⟩, hcc ▸ Step.ctxtInstrs hstep'
    (hne_map hC hne), ?_⟩
  show (⟨s', K₀', f', cvals vs ++ es' ++ rest⟩ : ConfigFX H) =
    ⟨c₁.store, K, c₁.frame, (vals vs ++ c₁.code ++ C).map .core⟩
  rw [hs₁, hK₁, hf₁, hes', ← hC]
  simp only [cvals, List.map_append]

/-- A configuration with a non-Core instruction is not a Core configuration. -/
theorem not_ofCoreK {x : ConfigFX H} (hx : x.code.all isCore = false)
    (K : List (Option ContFX)) (c : Config H) : x ≠ ofCoreK K c := by
  intro h
  have h2 : (ofCoreK K c).code.all isCore = true := all_isCore_map _
  rw [← h, hx] at h2
  exact Bool.false_ne_true h2

/-- **An FX step from a Core configuration with live continuations is a Core step.** -/
theorem step_ofCoreK {x y : ConfigFX H} (h : StepFX P host fx x y) :
    ∀ K (c : Config H), x = ofCoreK K c → NoFX fx c.store →
      ∃ c', Step P (blockFX host fx) c c' ∧ y = ofCoreK K c' := by
  induction h with
  | @core s s' K₀ f f' cs cs' h =>
    intro K c hx _
    obtain ⟨hs, hK, hf, hL⟩ := ofCoreK_eq hx
    have hcc : c = ⟨s, f, cs⟩ := config_mk_of hs hf (map_core_inj hL)
    exact ⟨⟨s', f', cs'⟩, hcc ▸ h, by rw [ofCoreK_mk, hK]⟩
  | seq _ hne ih => exact caseK_seq hne ih
  | @trapSeq s K₀ f vs rest hne =>
    intro K c hx _
    obtain ⟨hs, hK, hf, hL⟩ := ofCoreK_eq hx
    obtain ⟨A, B, C, hc, hA, hB, hC⟩ := split3 hL
    have hcc : c = ⟨s, f, vals vs ++ [.trap] ++ C⟩ :=
      config_mk_of hs hf (by rw [hc, map_core_inj hA, map_core_inj (l' := [.trap]) hB])
    exact ⟨⟨s, f, [.trap]⟩, hcc ▸ Step.trapInstrs (hne_map hC hne), by rw [ofCoreK_mk, hK]; rfl⟩
  | @throwSeq s K₀ f vs a rest hne =>
    intro K c hx _
    obtain ⟨hs, hK, hf, hL⟩ := ofCoreK_eq hx
    obtain ⟨A, B, C, hc, hA, hB, hC⟩ := split3 hL
    have hcc : c = ⟨s, f, vals vs ++ throwing a ++ C⟩ :=
      config_mk_of hs hf (by rw [hc, map_core_inj hA, map_core_inj (l' := throwing a) hB])
    exact ⟨⟨s, f, throwing a⟩, hcc ▸ Step.throwRefInstrs (hne_map hC hne),
      by rw [ofCoreK_mk, hK]; rfl⟩
  | @invoke s K₀ f c₀ vs a fi h₀ F hc hf hcode hfx hn =>
    intro K c hx hno
    have hs : s = c.store := (ofCoreK_eq hx).1
    have hnone : (none : Option FuncFX) = some F := (hno a fi h₀ (hs ▸ hf) hcode).symm.trans hfx
    exact absurd hnone (by simp)
  | _ => exact fun K c hx _ => absurd hx (not_ofCoreK (by simp [isCore, cvals]) K c)

/-- **Every Core step lifts, with any continuation store.** -/
theorem ofCoreK_step {K : List (Option ContFX)} {c c' : Config H}
    (h : Step P (blockFX host fx) c c') : StepFX P host fx (ofCoreK K c) (ofCoreK K c') := by
  cases c
  cases c'
  exact StepFX.core h

end Silmaril.Proofs.Wasm.Models.FXLower
