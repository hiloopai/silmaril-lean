module

public import Silmaril.Wasm.Component.Reference.Validation.Defs
public import Silmaril.Wasm.Lime1.ToCore

@[expose] public section

namespace Silmaril.Wasm.Component.Validation

/-- Scope restriction on the module's exposed ports, not on its internal
declarations or bodies. In particular a function export may reexport an import. -/
structure LimeFunctionPorts (mod : Lime1.Module) : Prop where
  imports : ∀ entry ∈ mod.imports, ∃ index, entry.desc = .func index
  exports : ∀ entry ∈ mod.exports, ∃ index, entry.index = .func index

end Silmaril.Wasm.Component.Validation
