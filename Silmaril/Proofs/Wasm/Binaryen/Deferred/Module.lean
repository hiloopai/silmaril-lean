module

public import Silmaril.Proofs.Wasm.Binaryen.Deferred.Closure

@[expose] public section

/-! # Export refinement from a deferred base simulation

Silmaril's `deferred_session_transport` and `deferred_exportRefines_of_bodiesRel`
(`Silmaril.Wasm.Binaryen.CoalesceLocalsProfile`, pinned silmaril-lean), restated for
`Silmaril.Wasm.Binaryen.Deferred.DeferredBaseSim`: modules whose bodies are related by
the base pairs refine each other's exports at every numerical profile under the
closed host, through instantiation, completed runs, subsequent calls and divergence.
-/

namespace Silmaril.Wasm.Binaryen.Deferred

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {BI : List Instr → List Instr → Prop}
  {B : List Admin → List Admin → Prop}

/-- Invocations in related stores start related. -/
theorem _root_.Silmaril.Proofs.Wasm.Binaryen.Deferred.invoke_cfgRel {s t : Store H} (a : Nat) (vs : List Val)
    (hst : StoreRel (FuncRel (H := H) BI) s t) :
    CfgRel (FuncRel (H := H) BI) (AdminsRel BI B) (invoke s a vs) (invoke t a vs) := by
  have hcode : (invoke s a vs).code = (invoke t a vs).code := by
    simp only [invoke, ← List.getElem?_map, hst.types]
  exact ⟨hst, rfl, hcode ▸ AdminsRel.refl _⟩

/-- **Sessions transport** from the left store to a related right store. -/
theorem deferred_session_transport (hB : DeferredBaseSim P (FuncRel (H := H) BI) BI B)
    {mi : ModuleInst} {s : Store H} {script : List Call} {bs : List (Behaviour Val)}
    (hs : Session P closedHost mi s script bs) :
    ∀ {t : Store H}, StoreRel (FuncRel (H := H) BI) s t → Session P closedHost mi t script bs := by
  have hhost : HostRespects (FuncRel (H := H) BI) closedHost :=
    CoalesceLocalsLite.closedHost_respects _
  induction hs with
  | nil => exact fun _ => .nil
  | stop h => exact fun hst => .stop fun a ha hok => h a ha (invokeOk_of_storeRel hst.symm hok)
  | done ha hok run hr _ ih =>
    intro t hst
    obtain ⟨d, hd, hdc, hst'⟩ :=
      Silmaril.Proofs.Wasm.Binaryen.Deferred.deferred_closure_run_transport (fun _ _ h => h) hhost hB
        (Silmaril.Proofs.Wasm.Binaryen.Deferred.invoke_cfgRel _ _ hst) run hr
    exact .done ha (invokeOk_of_storeRel hst hok) hd hdc (ih hst')
  | diverge ha hok hd =>
    intro t hst
    exact .diverge ha (invokeOk_of_storeRel hst hok)
      (Silmaril.Proofs.Wasm.Binaryen.Deferred.deferred_closure_diverges_transport (fun _ _ h => h)
        hhost hB (Silmaril.Proofs.Wasm.Binaryen.Deferred.invoke_cfgRel _ _ hst) hd)

/-- **Export refinement from a deferred base simulation**, at every numerical profile:
the left module's behaviours are behaviours of the right module. -/
theorem _root_.Silmaril.Proofs.Wasm.Binaryen.Deferred.deferred_exportRefines_of_bodiesRel (hB : DeferredBaseSim P (FuncRel (H := H) BI) BI B)
    {m m' : Module} (hrel : ModuleBodiesRel BI m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportRefines (· = ·) P (closedHost (H := H)) m m' := by
  have hhost : HostRespects (FuncRel (H := H) BI) closedHost :=
    CoalesceLocalsLite.closedHost_respects _
  refine ⟨fun s xas c' _ hI' => ?_, fun s xas script _ bs hbs => ?_⟩
  · obtain ⟨c, hc, -⟩ := instantiate_bodiesRel hrel.flip hm hI'
    exact ⟨c, hc⟩
  · obtain ⟨c, hI, hcase⟩ := hbs
    obtain ⟨c', hI', hfr, hco, hst⟩ := instantiate_bodiesRel hrel hm' hI
    have hcfg : CfgRel (FuncRel (H := H) BI) (AdminsRel BI B) c c' :=
      ⟨hst, hfr.symm, hco ▸ AdminsRel.refl _⟩
    refine ⟨bs, ⟨c', hI', ?_⟩, SessionRel.refl (fun _ => rfl) bs⟩
    rcases hcase with ⟨c₁, bs', hS, hcode, hsess, rfl⟩ |
      ⟨c₁, r, hS, hcode, hr, rfl⟩ | ⟨hd, rfl⟩
    · obtain ⟨d, hd, hdc, hst'⟩ :=
        Silmaril.Proofs.Wasm.Binaryen.Deferred.deferred_closure_run_transport (r := .values [])
        (fun _ _ h => h) hhost hB hcfg hS (by simp [hcode, Result.toAdmin, vals])
      have hsess' : Session P closedHost c'.frame.module d.store script bs' :=
        hfr ▸ deferred_session_transport hB hsess hst'
      exact Or.inl ⟨d, bs', hd, by simpa [Result.toAdmin, vals] using hdc, hsess', rfl⟩
    · obtain ⟨d, hd, hdc, -⟩ :=
        Silmaril.Proofs.Wasm.Binaryen.Deferred.deferred_closure_run_transport (fun _ _ h => h) hhost hB
          hcfg hS hcode
      exact Or.inr (Or.inl ⟨d, r, hd, hdc, hr, rfl⟩)
    · exact Or.inr (Or.inr
        ⟨Silmaril.Proofs.Wasm.Binaryen.Deferred.deferred_closure_diverges_transport (fun _ _ h => h)
          hhost hB hcfg hd, rfl⟩)

end Silmaril.Wasm.Binaryen.Deferred
