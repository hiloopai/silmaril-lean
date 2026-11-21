module

public import Silmaril.Semantics.Operational.Program.Defs
public import Silmaril.Wasm.Execution.Core.Entry.Defs
public import Silmaril.Wasm.Validation.Intrinsic.Thms

@[expose] public section

namespace Silmaril.Wasm.Execution.Core.Entry

open Validation Numerics Semantics.Operational

variable {H : Type} {interface : CModuleType}

/-- Checked raw syntax at a resolved import interface, not binary encodability,
feature admission, or a proof that instantiation succeeds. -/
def ModuleInput.CheckedAt (input : ModuleInput H) (interface : CModuleType) : Prop :=
  ModuleOk input.module_ interface ∧ StoreOk input.store ∧
    List.Forall₂ (ExternAddrOk input.store) input.imports interface.imports

def TypedModuleInput.checked (input : TypedModuleInput H interface) :
    { raw : ModuleInput H // raw.CheckedAt interface } :=
  ⟨input.erase, input.module_.sound, input.storeOk, input.importsOk⟩

/-- Checking changes the program domain; execution still uses actual Core. -/
def checkedModule (P : Profile) (host : HostSemantics H) (interface : CModuleType) :=
  (rawModule P host).restrictPrograms (·.CheckedAt interface)

end Silmaril.Wasm.Execution.Core.Entry
