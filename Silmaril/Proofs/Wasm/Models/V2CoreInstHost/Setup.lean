module

public import Silmaril.Wasm.Models.V2CoreInstDet.Thms
public import Silmaril.Wasm.Models.V2Core.Thms
public import Silmaril.Wasm.Execution.Core.Exec.Instantiate
public import Silmaril.Wasm.Validation.Check.Validate

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreInstHost

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core
open Silmaril.Wasm.Numerics (Profile)

/-- `ref.null extern`. -/
abbrev rExt : Silmaril.Wasm.V2.Execution.Ref := .null .externref

/-- The host function: type `[] → []`, host code `0`. -/
def fiH : Silmaril.Wasm.V2.Execution.FuncInst Nat :=
  { type := ⟨[], []⟩, module := {}, code := .host 0 }

/-- A `funcref` table with one null entry. -/
def tabF : Silmaril.Wasm.V2.Execution.TableInst :=
  { type := ⟨⟨1, some 1⟩, .funcref⟩, refs := [.null .funcref] }

/-- The point's store: the host function at address `0`, the table at address `0`. -/
def st : VStore Nat := { funcs := [fiH], tables := [tabF] }

/-- The same store with the table entry read as `ref.null extern`: an ill-typed 2.0 store with
the same Core image. -/
def stX : VStore Nat := { funcs := [fiH], tables := [{ tabF with refs := [rExt] }] }

/-- Some table of `s` holds `ref.null extern`. -/
def HasExtNull (s : VStore Nat) : Prop := ∃ ti ∈ s.tables, rExt ∈ ti.refs

/-- The host: a call may always diverge; it returns nothing, leaving the store, when some
table holds `ref.null extern`. -/
def src : VHost Nat := fun _ s _ out =>
  out = .diverged ∨ (HasExtNull s ∧ out = .returned s (.values []))

/-- The module: import a function of type `[] → []` and start with it. -/
def mI : Silmaril.Wasm.V2.Module :=
  { types := [⟨[], []⟩], imports := [⟨"env", "f", .func ⟨0⟩⟩], start := some ⟨0⟩ }

theorem stX_toCore : Silmaril.Wasm.V2.Execution.Store.toCore stX =
    Silmaril.Wasm.V2.Execution.Store.toCore st := rfl

theorem st_noExt : ¬ HasExtNull st := by
  rintro ⟨ti, hti, hr⟩
  simp [st, tabF] at hti
  subst hti
  simp [rExt] at hr

theorem stX_ext : HasExtNull stX := ⟨_, List.mem_singleton_self _, List.mem_singleton_self _⟩

/-- `mI` is 2.0-valid, importing one function of type `[] → []`. -/
theorem mI_ok : Silmaril.Wasm.V2.Validation.ModuleOk mI [.func ⟨[], []⟩] [] :=
  .mk (ft' := [⟨[], []⟩]) (ft := []) (gt := []) (tt := []) (mt := [])
    (rt := []) (.cons (by decide) .nil) (.cons (by decide) .nil) .nil .nil .nil .nil
    (by simp [mI]) .nil (by intro x hx; simp [mI] at hx; subst hx; decide) .nil (by decide)
    (by decide) rfl rfl

theorem mI_valid : Silmaril.Wasm.V2.Validation.ModuleValid mI := ⟨_, _, mI_ok⟩

/-- Both stores are well formed: `StoreWF` does not type table entries. -/
theorem wf_of {s : VStore Nat} (hf : s.funcs = [fiH]) (hm : s.mems = [])
    (ht : ∀ ti ∈ s.tables, ti.refs.length = 1) : Silmaril.Wasm.V2.Execution.StoreWF s := by
  refine ⟨fun i x h => ?_, fun i x h => by simp [hm] at h, fun i x h => by simp [hm] at h,
    fun i x h => ?_⟩
  · rw [hf] at h
    rcases i with _ | i <;> simp at h
    subst h
    intro a ha
    simp [fiH] at ha
  · rw [ht x (List.mem_of_getElem? h)]
    decide

theorem st_wf : Silmaril.Wasm.V2.Execution.StoreWF st :=
  wf_of rfl rfl (by simp [st, tabF])

theorem stX_wf : Silmaril.Wasm.V2.Execution.StoreWF stX :=
  wf_of rfl rfl (by simp [stX, tabF])

theorem src_preserves : Silmaril.Wasm.V2.Execution.HostPreserves src := by
  rintro _ s _ s' _ (h | ⟨-, h⟩) hwf
  · cases h
  · cases h
    exact ⟨hwf, Silmaril.ListExt.refl _ _⟩

theorem src_keeps : HostKeepsV src := by
  rintro _ s _ s' _ (h | ⟨-, h⟩)
  · cases h
  · cases h
    rfl

theorem src_embV : Silmaril.Wasm.Models.V2CoreSpec.HostEmbV src := by
  refine ⟨fun {ρ D s t s' h vs r} he hr => ?_, fun _ _ => Or.inl rfl⟩
  rcases hr with hr | ⟨hx, hr⟩
  · cases hr
  · cases hr
    obtain ⟨ti, hti, hmem⟩ := hx
    exact ⟨t, Or.inr ⟨⟨ti, he.tables ▸ hti, hmem⟩, rfl⟩, he⟩

/-- The point: `st` with the host `src`. -/
def pt : Pt Nat := (st, src)

/-- The ill-typed point: `stX` with the host `src`. Its Core image is `pt`'s. -/
def ptX : Pt Nat := (stX, src)

theorem ptCore_ptX : ptCore ptX = ptCore pt := by
  simp only [ptCore, ptX, pt, stX_toCore]

/-- The domain of `v20instHT` at a store with `st`'s Core image. -/
theorem dom_of (P : Profile) {s : VStore Nat} (hwf : Silmaril.Wasm.V2.Execution.StoreWF s)
    (hc : Silmaril.Wasm.V2.Execution.Store.toCore s = Silmaril.Wasm.V2.Execution.Store.toCore st) :
    (Silmaril.Wasm.Models.V2CoreSpec.v20instHT P).dom (s, src) := by
  refine ⟨⟨hwf, by rw [hc]; rfl, src_preserves, src_keeps⟩, src_embV, ?_⟩
  intro fi hfi
  have e : (ptCore (s, src)).1.funcs = (ptCore pt).1.funcs := by
    simp only [ptCore, pt, hc]
  have e' : (ptCore pt).1.funcs = [⟨fiH.type.toDefType, fiH.module.toCore, .host 0⟩] := rfl
  rw [e, e'] at hfi
  simp only [List.mem_singleton] at hfi
  subst hfi
  refine ⟨fun a ha => ?_, fun e he => ?_⟩
  · change a ∈ ([] : List Nat) at ha
    cases ha
  · change e ∈ ([] : List Silmaril.Wasm.Execution.Core.ExportInst) at he
    cases he

theorem pt_dom (P : Profile) : (Silmaril.Wasm.Models.V2CoreSpec.v20instHT P).dom pt :=
  dom_of P st_wf rfl

theorem ptX_dom (P : Profile) : (Silmaril.Wasm.Models.V2CoreSpec.v20instHT P).dom ptX :=
  dom_of P stX_wf stX_toCore

end Silmaril.Proofs.Wasm.Models.V2CoreInstHost
