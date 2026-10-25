module

public import Silmaril.Wasm.Execution.Core.Exec.InstantiateComplete
public import Silmaril.Wasm.Execution.Core.Exec.ConstEvalComplete
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateInit

@[expose] public section

/-! # `instantiate? evalConst?` decides `Instantiate`

Combining soundness (`instantiate?_sound`, `evalConst?_evalSound`) and completeness
(`instantiate?_complete`, `evalConst?_complete`), the concrete instantiator computes
exactly the configurations related by `Instantiate` (for valid modules/imports).
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem evalConst?_evalComplete : EvalComplete P host (evalConst? (H := H)) :=
  fun _ _ _ _ _ _ hc h => evalConst?_complete hc h

theorem instantiate?_evalConst_complete {s : Store H} {m : Module} {xas : List ExternAddr}
    {c : Config H} (h : Instantiate P host s m xas c) :
    instantiate? evalConst? s m xas = some c :=
  instantiate?_complete evalConst?_evalComplete h

theorem instantiate?_iff {s : Store H} {m : Module} {xas : List ExternAddr} {c : Config H}
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI) :
    instantiate? evalConst? s m xas = some c ↔ Instantiate P host s m xas c :=
  ⟨fun h => instantiate?_sound evalConst?_evalSound h hvalid,
   instantiate?_evalConst_complete⟩

theorem exists_instantiate_iff_isSome {s : Store H} {m : Module} {xas : List ExternAddr}
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI) :
    (∃ c, Instantiate P host s m xas c) ↔ (instantiate? evalConst? s m xas).isSome := by
  constructor
  · rintro ⟨c, hc⟩
    rw [instantiate?_evalConst_complete hc]; rfl
  · intro h
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 h
    exact ⟨c, (instantiate?_iff hvalid).1 hc⟩

/-- Computable decision procedure for instantiability of a valid module. -/
def decInstantiate (s : Store H) (m : Module) (xas : List ExternAddr)
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI) :
    Decidable (∃ c, Instantiate P host s m xas c) :=
  decidable_of_iff _ (exists_instantiate_iff_isSome hvalid).symm

/-- `prepare?` analogue, stated via `instantiate?`. -/
theorem prepare?_iff {s : Store H} {m : Module} {xas : List ExternAddr} {c : Config H}
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI) :
    ((prepare? evalConst? s m xas).map fun p => p.1.withStart p.2) = some c ↔
      Instantiate P host s m xas c := by
  rw [← prepare?_instantiate?]; exact instantiate?_iff hvalid

theorem exists_instantiate_iff_prepare?_isSome {s : Store H} {m : Module}
    {xas : List ExternAddr}
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI) :
    (∃ c, Instantiate P host s m xas c) ↔ (prepare? evalConst? s m xas).isSome := by
  rw [exists_instantiate_iff_isSome hvalid, prepare?_instantiate?, Option.isSome_map]

end Silmaril.Wasm.Execution.Core
