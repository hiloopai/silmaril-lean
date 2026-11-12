module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HostMods.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.Unstrip.Thms

/-!
# Core's `Step` commutes with export-only rewritings, store-local host (unrefined)

`step_mapConfigAt` is `Round7.step_mapConfig` (`Raw/…/Round7/Unstrip/Step.lean`) with the host
hypothesis `HostModMap host μ` (at every store) weakened to `HostModMapAt host μ c.store` (at the
store of the source). A step calls the host only at the store of its source, and the context
rules keep the store of the inner step, so the copy changes only the host-call cases and the
induction hypotheses of the context cases. One case per rule, kept unrefined.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HostMods

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- **Core's `Step` commutes with an export-only rewriting**, for a host invariant under it at
the store of the source only. -/
theorem step_mapConfigAt {P : Profile} {host : HostSemantics H} {μ : ModuleInst → ModuleInst}
    (hμ : ExportOnly μ) {c c' : Config H} (h : Step P host c c')
    (hh : HostModMapAt host μ c.store) :
    Step P host (mapConfig μ c) (mapConfig μ c') := by
  induction h with
  | parametric h =>
      simp only [mapConfig, mapAdmins_atomic μ (parametricStep_atomic h),
        mapAdmins_atomic μ (parametricStep_atomic' h)]
      exact .parametric h
  | numeric h =>
      simp only [mapConfig, mapAdmins_atomic μ (numericStep_atomic h),
        mapAdmins_atomic μ (numericStep_atomic' h)]
      exact .numeric h
  | vector h =>
      simp only [mapConfig, mapAdmins_atomic μ (vectorStep_atomic h),
        mapAdmins_atomic μ (vectorStep_atomic' h)]
      exact .vector h
  | «variable» h =>
      obtain ⟨hF, hM⟩ := variableStep_funcs h
      rw [mapConfig_eq_setEx hμ (variableStep_atomic h),
        mapConfig_eq_setEx hμ (variableStep_atomic' h), hF, hM]
      exact .variable (variableStep_setEx h _ _)
  | table h =>
      obtain ⟨hF, hM⟩ := tableStep_funcs h
      rw [mapConfig_eq_setEx hμ (tableStep_atomic h),
        mapConfig_eq_setEx hμ (tableStep_atomic' h), hF, hM]
      exact .table (tableStep_setEx h _ _)
  | memory h =>
      obtain ⟨hF, hM⟩ := memoryStep_funcs h
      rw [mapConfig_eq_setEx hμ (memoryStep_atomic h),
        mapConfig_eq_setEx hμ (memoryStep_atomic' h), hF, hM]
      exact .memory (memoryStep_setEx h _ _)
  | reference h =>
      obtain ⟨hF, hM⟩ := refStep_funcs h
      rw [mapConfig_eq_setEx hμ (refStep_atomic h),
        mapConfig_eq_setEx hμ (refStep_atomic' h), hF, hM]
      exact .reference (refStep_setEx h _ (map_mapFI_strip hμ _) _)
  | aggregate h =>
      obtain ⟨hF, hM⟩ := aggregateStep_funcs h
      rw [mapConfig_eq_setEx hμ (aggregateStep_atomic h),
        mapConfig_eq_setEx hμ (aggregateStep_atomic' h), hF, hM]
      exact .aggregate (aggregateStep_setEx h _ _)
  | ctxtInstrs h hne ih =>
      simp only [mapConfig, mapAdmins_append, mapAdmins_vals] at ih ⊢
      exact .ctxtInstrs (ih hh) (hne.imp id (mapAdmins_ne_nil μ))
  | ctxtLabel h ih =>
      simp only [mapConfig] at ih
      map_nf
      exact .ctxtLabel (ih hh)
  | ctxtHandler h ih =>
      simp only [mapConfig] at ih
      map_nf
      exact .ctxtHandler (ih hh)
  | ctxtFrame h ih =>
      simp only [mapConfig] at ih
      map_nf
      exact .ctxtFrame (ih hh)
  | block hbt hm =>
      map_nf
      exact .block (by simpa [mapFrame, blockType?_exportOnly hμ] using hbt) hm
  | loop hbt hm =>
      map_nf
      exact .loop (by simpa [mapFrame, blockType?_exportOnly hμ] using hbt) hm
  | ifTrue hc => map_nf; exact .ifTrue hc
  | ifFalse => map_nf; exact .ifFalse
  | labelVals => map_nf; exact .labelVals
  | brLabelZero hl hn => map_nf; exact .brLabelZero hl hn
  | brLabelSucc hl => map_nf; exact .brLabelSucc hl
  | brHandler => map_nf; exact .brHandler
  | brIfTrue hc => map_nf; exact .brIfTrue hc
  | brIfFalse => map_nf; exact .brIfFalse
  | brTableLt hi => map_nf; exact .brTableLt hi
  | brTableGe hi => map_nf; exact .brTableGe hi
  | brOnNullNull => map_nf; exact .brOnNullNull
  | brOnNullAddr hv => map_nf; exact .brOnNullAddr hv
  | brOnNonNullNull => map_nf; exact .brOnNonNullNull
  | brOnNonNullAddr hv => map_nf; exact .brOnNonNullAddr hv
  | brOnCastSucceed h =>
      map_nf
      exact .brOnCastSucceed (by simpa [mapFrame, refOk_map hμ, instRef_exportOnly hμ] using h)
  | brOnCastFail h =>
      map_nf
      exact .brOnCastFail (by simpa [mapFrame, refOk_map hμ, instRef_exportOnly hμ] using h)
  | brOnCastFailSucceed h =>
      map_nf
      exact .brOnCastFailSucceed
        (by simpa [mapFrame, refOk_map hμ, instRef_exportOnly hμ] using h)
  | brOnCastFailFail h =>
      map_nf
      exact .brOnCastFailFail (by simpa [mapFrame, refOk_map hμ, instRef_exportOnly hμ] using h)
  | call hx hf =>
      map_nf
      exact .call (fi := mapFI μ _) (by simpa [mapFrame, exportOnly_funcs hμ] using hx)
        (funcs_map_get hf)
  | callRefNull hc =>
      map_nf
      rw [mapAdmin_callRef μ hc]
      exact .callRefNull hc
  | callRefFunc hc hf he hn hcode =>
      map_nf
      rw [mapAdmin_callRef μ hc, ← forCall_exportOnly hμ]
      exact .callRefFunc (fi := mapFI μ _) hc (funcs_map_get hf) he hn hcode
  | callRefHost hc hf he hn hcode hhost =>
      map_nf
      rw [mapAdmin_callRef μ hc]
      exact .callRefHost (fi := mapFI μ _) hc (funcs_map_get hf) he hn hcode (hh _ _ _ hhost)
  | callRefHostDiv hc hf he hn hcode hhost =>
      map_nf
      rw [mapAdmin_callRef μ hc]
      exact .callRefHostDiv (fi := mapFI μ _) hc (funcs_map_get hf) he hn hcode
        (hh _ _ _ hhost)
  | returnCall hx hf =>
      map_nf
      exact .returnCall (fi := mapFI μ _) (by simpa [mapFrame, exportOnly_funcs hμ] using hx)
        (funcs_map_get hf)
  | returnCallRefLabel hc =>
      map_nf
      rw [mapAdmin_atomic μ (atomic_of_isReturnCallRef hc)]
      exact .returnCallRefLabel hc
  | returnCallRefHandler hc =>
      map_nf
      rw [mapAdmin_atomic μ (atomic_of_isReturnCallRef hc)]
      exact .returnCallRefHandler hc
  | returnCallRefFrameNull hc =>
      map_nf
      rw [mapAdmin_atomic μ (atomic_of_isReturnCallRef hc)]
      exact .returnCallRefFrameNull hc
  | returnCallRefFrameAddr hc hf he hn =>
      map_nf
      rw [mapAdmin_atomic μ (atomic_of_isReturnCallRef hc),
        mapAdmin_atomic μ (atomic_retToCallIn (atomic_of_isReturnCallRef hc) _),
        ← retToCallIn_exportOnly hμ]
      exact .returnCallRefFrameAddr (fn := mapFI μ _) hc (funcs_map_get hf) he hn
  | callIndirect => map_nf; exact .callIndirect
  | returnCallIndirect => map_nf; exact .returnCallIndirect
  | frameVals hn => map_nf; exact .frameVals hn
  | returnFrame hn => map_nf; exact .returnFrame hn
  | returnLabel => map_nf; exact .returnLabel
  | returnHandler => map_nf; exact .returnHandler
  | throw ht he hn =>
      map_nf
      rw [mapStore_addExn]
      have := Step.throw (P := P) (host := host) (s := mapStore μ _) (f := mapFrame μ _)
        (by rw [tag?_map hμ]; exact ht) he hn
      simpa using this
  | throwRefNull => map_nf; exact .throwRefNull
  | throwRefInstrs hne => map_nf; exact .throwRefInstrs (hne.imp id (mapAdmins_ne_nil μ))
  | throwRefLabel => map_nf; exact .throwRefLabel
  | throwRefFrame => map_nf; exact .throwRefFrame
  | throwRefHandlerEmpty => map_nf; exact .throwRefHandlerEmpty
  | throwRefHandlerCatch he ht =>
      map_nf
      exact .throwRefHandlerCatch he (by simpa [mapFrame, exportOnly_tags hμ] using ht)
  | throwRefHandlerCatchRef he ht =>
      map_nf
      exact .throwRefHandlerCatchRef he (by simpa [mapFrame, exportOnly_tags hμ] using ht)
  | throwRefHandlerCatchAll => map_nf; exact .throwRefHandlerCatchAll
  | throwRefHandlerCatchAllRef => map_nf; exact .throwRefHandlerCatchAllRef
  | throwRefHandlerNext h =>
      map_nf
      exact .throwRefHandlerNext (by rwa [catchMatches_map hμ])
  | tryTable hbt hm =>
      map_nf
      exact .tryTable (by simpa [mapFrame, blockType?_exportOnly hμ] using hbt) hm
  | handlerVals => map_nf; exact .handlerVals
  | trapInstrs hne => map_nf; exact .trapInstrs (hne.imp id (mapAdmins_ne_nil μ))
  | trapLabel => map_nf; exact .trapLabel
  | trapHandler => map_nf; exact .trapHandler
  | trapFrame => map_nf; exact .trapFrame

end Silmaril.Wasm.SpecTec.Sim.Round7.HostMods
