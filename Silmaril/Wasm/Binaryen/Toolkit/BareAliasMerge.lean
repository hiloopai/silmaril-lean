module

public import Silmaril.Wasm.Binaryen.MergeExportNames
public import Silmaril.Wasm.Binaryen.Exe.CoreInputCheck
public import Silmaril.Wasm.Binaryen.Toolkit.MetaDCERuntime

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

/-- Compare complete canonical encodings instead of assuming decidable
syntactic equality for the recursive Core instruction datatype. -/
def identityFunctionB (types : List RecType) (f : Func) : Bool :=
  match Link.GC.func? Link.GC.Recipe.identity f with
  | none => false
  | some shifted => Exe.canonicalModuleEq {types, funcs := [f]} {types, funcs := [shifted]}

/-- Narrow executable scope for certified observation-name transport. The
broader experimental alias endpoint retains all of its existing functionality. -/
def bareAliasTransportB (aliases : List MergeExportNames.Alias) (ns : String) (m : Module) : Bool :=
  m.imports.isEmpty && m.tags.isEmpty && m.globals.isEmpty && m.memories.isEmpty &&
  m.tables.isEmpty && m.data.isEmpty && m.elems.isEmpty && m.start.isNone &&
  (MetaDCE.tree m).inProfileBase &&
  m.funcs.all (identityFunctionB m.types) &&
  (Validation.validate? m).isSome &&
  (Validation.validate? (MergeExportNames.rewrite aliases ns m)).isSome &&
  MergeExportNames.aliasInjectiveB aliases ns m

end Silmaril.Wasm.Binaryen.Toolkit
