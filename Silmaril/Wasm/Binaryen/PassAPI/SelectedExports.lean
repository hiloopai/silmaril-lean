module

public import Silmaril.Wasm.Binaryen.PassAPI.ModuleModes
public import Silmaril.Wasm.Binaryen.Pass.RUMESim.ObsOn

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Modes

open Execution.Core Numerics Validation RUMESim

variable {H : Type}

/-- Source-first exact correctness on an explicit export interface. Admission
and initialization remain actual module observations; arbitrary shared-store
scripts are restricted only by their requested names. -/
structure ExportCorrectOn (allowed : String → Prop) (P : Profile) (host : HostSemantics H)
    (source target : Module) : Prop where
  admission : ∀ s imports, StoreOk s →
    (Instantiates P host s imports source ↔ Instantiates P host s imports target)
  observations : ∀ s imports script, StoreOk s → ScriptOn allowed script →
    moduleObs P host s imports source script = moduleObs P host s imports target script

namespace ExportCorrectOn

theorem refl (allowed : String → Prop) (P : Profile) (host : HostSemantics H) (m : Module) :
    ExportCorrectOn allowed P host m m := ⟨fun _ _ _ => Iff.rfl, fun _ _ _ _ _ => rfl⟩

theorem trans {allowed : String → Prop} {P : Profile} {host : HostSemantics H}
    {a b c : Module} (h : ExportCorrectOn allowed P host a b)
    (h' : ExportCorrectOn allowed P host b c) : ExportCorrectOn allowed P host a c :=
  ⟨fun s imports hs => (h.admission s imports hs).trans (h'.admission s imports hs),
    fun s imports script hs on =>
      (h.observations s imports script hs on).trans (h'.observations s imports script hs on)⟩

theorem of_equivalence {allowed : String → Prop} {P : Profile} {host : HostSemantics H}
    {source target : Module} (h : ExportCorrect .equivalence P host source target) :
    ExportCorrectOn allowed P host source target :=
  ⟨h.admission, fun s imports script hs _ => h.observations s imports script hs⟩

end ExportCorrectOn

/-- Selected-interface equivalence uses the same shared Pass API. Fixing the
allowed interface makes composition explicit and transitive. -/
def moduleContractOn (allowed : String → Prop) (P : Profile) (host : HostSemantics H) :
    Silmaril.Compile.PassAPI.Contract Module where
  Rel := ExportCorrectOn allowed P host
  refl := ExportCorrectOn.refl allowed P host
  trans := ExportCorrectOn.trans
  Inv := ModuleValid

end Silmaril.Wasm.Binaryen.Modes
