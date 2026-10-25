module

public import Silmaril.Wasm.Binaryen.CoalesceLocalsClosure
public import Silmaril.Wasm.Binaryen.CoalesceLocalsReverseBase

@[expose] public section

/-! # CoalesceLocals equivalence at every numerical profile

The reverse direction uses the real transient source-frame simulation, including
recursive runtime contexts, final-store transport, subsequent export calls and
divergence. It imposes no determinism assumption on the profile.
-/

namespace Silmaril.Wasm.Binaryen.CoalesceLocalsLite

open Execution.Core Execution.Core.Sim Validation Numerics

variable {H : Type} {P : Profile}

theorem deferred_session_transport
    {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}
    (hB : DeferredBaseSim P (FuncRel (H := H) BI) BI B) {mi : ModuleInst} {s : Store H}
    {script : List Call} {bs : List (Behaviour Val)} (hs : Session P closedHost mi s script bs) :
    ∀ {t : Store H}, StoreRel (FuncRel (H := H) BI) s t → Session P closedHost mi t script bs := by
  have hhost := closedHost_respects (FuncRel (H := H) BI)
  have hcfg : ∀ {s t : Store H} (a : Nat) (vs : List Val), StoreRel (FuncRel (H := H) BI) s t →
      CfgRel (FuncRel (H := H) BI) (AdminsRel BI B) (invoke s a vs) (invoke t a vs) := by
    intro s t a vs hst
    refine ⟨hst, rfl, ?_⟩
    have hcode : (invoke s a vs).code = (invoke t a vs).code := by
      simp only [invoke, ← List.getElem?_map, hst.types]
    rw [hcode]
    exact AdminsRel.refl _
  induction hs with
  | nil => intro _ _; exact .nil
  | stop h =>
    intro t hst
    exact .stop fun a ha hok => h a ha (invokeOk_of_storeRel hst.symm hok)
  | done ha hok run hr _ ih =>
    intro t hst
    obtain ⟨d, hd, hdc, hst'⟩ :=
      deferred_closure_run_transport (fun _ _ h => h) hhost hB (hcfg _ _ hst) run hr
    exact .done ha (invokeOk_of_storeRel hst hok) hd hdc (ih hst')
  | diverge ha hok hd =>
    intro t hst
    exact .diverge ha (invokeOk_of_storeRel hst hok)
      (deferred_closure_diverges_transport (fun _ _ h => h) hhost hB (hcfg _ _ hst) hd)

theorem deferred_exportRefines_of_bodiesRel
    {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}
    (hB : DeferredBaseSim P (FuncRel (H := H) BI) BI B)
    {m m' : Module} (hrel : ModuleBodiesRel BI m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportRefines (· = ·) P (closedHost (H := H)) m m' := by
  have hhost := closedHost_respects (FuncRel (H := H) BI)
  refine ⟨fun s xas c' _ hI' => ?_, fun s xas script _ bs hbs => ?_⟩
  · obtain ⟨c, hc, -⟩ := instantiate_bodiesRel hrel.flip hm hI'
    exact ⟨c, hc⟩
  · obtain ⟨c, hI, hcase⟩ := hbs
    obtain ⟨c', hI', hfr, hco, hst⟩ := instantiate_bodiesRel hrel hm' hI
    have hcfg : CfgRel (FuncRel (H := H) BI) (AdminsRel BI B) c c' :=
      ⟨hst, hfr.symm, by rw [hco]; exact AdminsRel.refl _⟩
    refine ⟨bs, ⟨c', hI', ?_⟩, SessionRel.refl (fun _ => rfl) bs⟩
    rcases hcase with ⟨c₁, bs', hS, hcode, hsess, rfl⟩ |
      ⟨c₁, r, hS, hcode, hr, rfl⟩ | ⟨hd, rfl⟩
    · obtain ⟨d, hd, hdc, hst'⟩ := deferred_closure_run_transport (r := .values [])
        (fun _ _ h => h) hhost hB hcfg hS (by simp [hcode, Result.toAdmin, vals])
      refine Or.inl ⟨d, bs', hd, by simpa [Result.toAdmin, vals] using hdc, ?_, rfl⟩
      rw [hfr]
      exact deferred_session_transport hB hsess hst'
    · obtain ⟨d, hd, hdc, -⟩ :=
        deferred_closure_run_transport (fun _ _ h => h) hhost hB hcfg hS hcode
      exact Or.inr (Or.inl ⟨d, r, hd, hdc, hr, rfl⟩)
    · exact Or.inr (Or.inr
        ⟨deferred_closure_diverges_transport (fun _ _ h => h) hhost hB hcfg hd, rfl⟩)

/-- Original-to-rewritten refinement, including arbitrary numerical and growth choices. -/
theorem deadSetLite_refines_reverse {m : BModule} (hm : m.Ok) :
    ExportRefines (· = ·) P (closedHost (H := H)) m.lower (deadSetLite m).lower :=
  deferred_exportRefines_of_bodiesRel reverseBaseSim (deadSetLite_bodiesRel m).flip
    hm (deadSetLite_ok hm)

/-- The unchanged overwrite-anchored transform preserves exports at every profile. -/
theorem deadSetLite_sound_profile {m : BModule} (hm : m.Ok) :
    ExportEquiv (· = ·) P (closedHost (H := H)) (deadSetLite m).lower m.lower :=
  ⟨deadSetLite_refines hm _ (closedHost_respects _),
    (deadSetLite_refines_reverse hm).mono fun _ _ h => h.symm⟩

end Silmaril.Wasm.Binaryen.CoalesceLocalsLite
