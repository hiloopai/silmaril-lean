module

public import Silmaril.Wasm.Sublanguages.Strict.Defs

/-! Native static linking for function-only declarations. Core validation
supplies the closed interfaces; the Core linker is not used to assemble the result. -/

@[expose] public section

namespace Silmaril.Wasm.Sublanguages.StrictLink

open Link

/-- Match in declaration order using the validated closed types, not source
type indices. The first matching export has the same priority as in Core. -/
def resolve? (namespaceName : String) (exports : List FunctionExport)
    (imports : List FunctionImport) (providerType consumerType : Validation.CModuleType) :
    Option (List FuncIdx) :=
  (imports.zip consumerType.imports).mapM fun (entry, expected) => do
    if entry.moduleName != namespaceName then none else do
      let .func expected := expected | none
      let (actualExport, actualType) ← (exports.zip providerType.exports).find?
        (fun (entry', _) => entry'.name == entry.name)
      let .func actual := actualType | none
      if actual = expected then some actualExport.index else
        if Validation.Sub.check {} actual expected then some actualExport.index else none

def relocateExport? (relocation : GC.Relocation) (entry : FunctionExport) : Option FunctionExport :=
  (FunctionExport.mk entry.name) <$> GC.function? relocation entry.index

/-- The closed provider's definitions come first. A consumer import is
replaced by its provider index; a consumer definition moves past the provider
definitions after dropping the import prefix. Type groups are shifted, not
deduplicated. Starts are outside the shared linker domain. -/
def assemble? (namespaceName : String) (provider : LocalSections) (consumer : FunctionModule) :
    Option LocalSections := do
  if !(provider.start.isNone && consumer.sections.start.isNone) then none else do
    let providerType ← Validation.validate? (provider.assemble [])
    let consumerType ← Validation.validate? consumer.toCore
    let providerTypes := (provider.types.flatMap RecType.types).length
    let consumerTypes := (consumer.sections.types.flatMap RecType.types).length
    if providerTypes + consumerTypes ≥ 2^32 ||
        provider.funcs.length + consumer.sections.funcs.length ≥ 2^32 then none else do
      let imports ← resolve? namespaceName provider.exports consumer.imports providerType consumerType
      let relocation : GC.Relocation := ⟨providerTypes, provider.funcs.length, 0, imports⟩
      let types ← consumer.sections.types.mapM (GC.recType? relocation.types)
      let funcs ← consumer.sections.funcs.mapM (GC.func? relocation)
      let exports ← consumer.sections.exports.mapM (relocateExport? relocation)
      let providerFuncs ← provider.funcs.mapM (GC.func? ⟨0, 0, 0, []⟩)
      pure {
        types := provider.types ++ types
        funcs := providerFuncs ++ funcs
        exports := provider.exports ++ exports }

/-- Native linking on function-only module shapes. Recheck the complete
linked module just as the Core linker does. -/
def linkSections? (namespaceName : String) (provider : LocalSections) (consumer : FunctionModule) :
    Option LocalSections := do
  let result ← assemble? namespaceName provider consumer
  if (Validation.validate? (result.assemble [])).isSome then some result else none

/-- Link a strict consumer against a closed strict provider. No syntax is read
back from Core: admission is checked on the natively assembled sections. -/
def link? (namespaceName : String) (provider : Ultrastrict) (consumer : Strict) : Option Ultrastrict := do
  let result ← linkSections? namespaceName provider.val consumer.val
  if admitted : Models.Module.InFeat strictCaps (result.assemble []) then
    some ⟨result, admitted⟩
  else none

end Silmaril.Wasm.Sublanguages.StrictLink
