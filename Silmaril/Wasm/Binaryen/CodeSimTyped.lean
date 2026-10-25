module

public import Silmaril.Wasm.Binaryen.CodeSimModule
public import Silmaril.Wasm.Binaryen.InlUnwrapClosed
public import Silmaril.Wasm.Execution.Core.Sim.TypedClosure

@[expose] public section

/-! # Closed-host module/session refinement from a typed reverse closure

Typing is required only of the right configuration. Invocation typing and
closed-host preservation supply that guard and preserve valid stores between
successive exported calls, at the same arbitrary numerical profile.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Validation Numerics

theorem typed_session_transport {H : Type} {P : Profile}
    {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}
    {rank : List Admin → Nat} [Sim.LawfulCodeRank rank]
    (hhost : Sim.HostRespects (Sim.FuncRel (H := H) BI) closedHost)
    (hB : Sim.TypedBaseSim P (Sim.FuncRel (H := H) BI) BI B rank) {mi : ModuleInst} {s : Store H}
    {script : List Call} {bs : List (Behaviour Val)} (hs : Session P closedHost mi s script bs) :
    ∀ {t : Store H}, StoreOk t → Sim.StoreRel (Sim.FuncRel (H := H) BI) s t → Session P closedHost mi t script bs := by
  have hcfg : ∀ {s t : Store H} (a : Nat) (vs : List Val), Sim.StoreRel (Sim.FuncRel (H := H) BI) s t →
      Sim.CfgRel (Sim.FuncRel (H := H) BI) (Sim.AdminsRel BI B) (invoke s a vs) (invoke t a vs) := by
    intro s t a vs hst
    refine ⟨hst, rfl, ?_⟩
    have hcode : (invoke s a vs).code = (invoke t a vs).code := by
      simp only [invoke, ← List.getElem?_map, hst.types]
    rw [hcode]
    exact Sim.AdminsRel.refl _
  induction hs with
  | nil => intro _ _ _; exact .nil
  | stop h =>
    intro t ht hst
    exact .stop fun a ha hok => h a ha (invokeOk_of_storeRel hst.symm hok)
  | done ha hok run hr _ ih =>
    intro t ht hst
    have hokT := invokeOk_of_storeRel hst hok
    obtain ⟨_, _, _, _, _, hcT⟩ := invoke_ok ht hokT
    obtain ⟨d, hd, hdc, hst'⟩ :=
      Sim.typed_closure_run_transport (fun _ _ h => h) hhost hB (hcfg _ _ hst)
        (Sim.ContextTyped.of_configOk hcT) run hr
    exact .done ha (invokeOk_of_storeRel hst hok) hd hdc (ih (SingleThreaded.ConfigOk.storeOk (Unwrap.preserves_closed hcT hd)) hst')
  | diverge ha hok hd =>
    intro t ht hst
    have hokT := invokeOk_of_storeRel hst hok
    obtain ⟨_, _, _, _, _, hcT⟩ := invoke_ok ht hokT
    exact .diverge ha hokT
      (Sim.typed_closure_diverges_transport (fun _ _ h => h) hhost hB (hcfg _ _ hst)
        (Sim.ContextTyped.of_configOk hcT) hd)

theorem exportRefines_of_typedBodiesRel {H : Type} {P : Profile}
    {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}
    {rank : List Admin → Nat} [Sim.LawfulCodeRank rank]
    (hB : Sim.TypedBaseSim P (Sim.FuncRel (H := H) BI) BI B rank)
    (hhost : Sim.HostRespects (Sim.FuncRel (H := H) BI) closedHost)
    {m m' : Module} (hrel : ModuleBodiesRel BI m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportRefines (· = ·) P (closedHost (H := H)) m m' := by
  refine ⟨fun s xas c' _ hI' => ?_, fun s xas script hs bs hbs => ?_⟩
  · obtain ⟨c, hc, -⟩ := instantiate_bodiesRel hrel.flip hm hI'
    exact ⟨c, hc⟩
  · obtain ⟨c, hI, hcase⟩ := hbs
    obtain ⟨c', hI', hfr, hco, hst⟩ := instantiate_bodiesRel hrel hm' hI
    have hcT : ConfigOk c' [] := Instantiate.ok SingleThreaded.divHost_ok hs
      (Unwrap.instantiate_of_closed_unwrap SingleThreaded.divHost hI')
    have hcfg : Sim.CfgRel (Sim.FuncRel (H := H) BI) (Sim.AdminsRel BI B) c c' :=
      ⟨hst, hfr.symm, by rw [hco]; exact Sim.AdminsRel.refl _⟩
    refine ⟨bs, ⟨c', hI', ?_⟩, SessionRel.refl (fun _ => rfl) bs⟩
    rcases hcase with ⟨c₁, bs', hS, hcode, hsess, rfl⟩ | ⟨c₁, r, hS, hcode, hr, rfl⟩ | ⟨hd, rfl⟩
    · obtain ⟨d, hd, hdc, hst'⟩ := Sim.typed_closure_run_transport (r := .values [])
        (fun _ _ h => h) hhost hB hcfg (Sim.ContextTyped.of_configOk hcT) hS (by simp [hcode, Result.toAdmin, vals])
      refine Or.inl ⟨d, bs', hd, by simpa [Result.toAdmin, vals] using hdc, ?_, rfl⟩
      rw [hfr]
      exact typed_session_transport hhost hB hsess
        (SingleThreaded.ConfigOk.storeOk (Unwrap.preserves_closed hcT hd)) hst'
    · obtain ⟨d, hd, hdc, -⟩ := Sim.typed_closure_run_transport (fun _ _ h => h) hhost hB hcfg (Sim.ContextTyped.of_configOk hcT) hS hcode
      exact Or.inr (Or.inl ⟨d, r, hd, hdc, hr, rfl⟩)
    · exact Or.inr (Or.inr ⟨Sim.typed_closure_diverges_transport (fun _ _ h => h) hhost hB hcfg
        (Sim.ContextTyped.of_configOk hcT) hd, rfl⟩)


end Silmaril.Wasm.Binaryen
