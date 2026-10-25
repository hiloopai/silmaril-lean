module

public import Silmaril.Wasm.Link.GC
public import Silmaril.Wasm.Validation.Check.ModuleComplete

@[expose] public section

namespace Silmaril.Wasm.Link.GC

open Validation

/-- Every legacy exact-resolution success retains the exact resolved index
list. No module validity or subtype-checker completeness premise is needed. -/
theorem resolveImports?_of_exact {namespaceName : String} {provider consumer : Module}
    {providerType consumerType : CModuleType} {resolved : List FuncIdx}
    (accepted : resolveImportsExact? namespaceName provider consumer providerType consumerType = some resolved) :
    resolveImports? namespaceName provider consumer providerType consumerType = some resolved := by
  let exactEntry : Import × CExternType → Option FuncIdx := fun (entry, expected) => do
    if entry.moduleName != namespaceName then none else do
      let .func _ := entry.type | none
      let .func expected := expected | none
      let (actualExport, actualType) ← (provider.exports.zip providerType.exports).find?
        (fun (e, _) => e.name == entry.name)
      let .func f := actualExport.index | none
      let .func actual := actualType | none
      if actual = expected then some f else none
  change (consumer.imports.zip consumerType.imports).mapM exactEntry = some resolved at accepted
  unfold resolveImports?
  apply List.mapM_some_of_forall₂ (R := fun entry f => exactEntry entry = some f) ?_
    (List.mapM_some_forall₂ (fun h => h) accepted)
  intro pair f entryAccepted
  rcases pair with ⟨entry, expected⟩
  dsimp only [exactEntry] at entryAccepted ⊢
  split at entryAccepted
  · cases entryAccepted
  · rename_i name
    cases entryType : entry.type <;> simp only [entryType] at entryAccepted
    all_goals try contradiction
    cases expectedType : expected <;> simp only [expectedType] at entryAccepted
    all_goals try contradiction
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at entryAccepted
    obtain ⟨⟨exported, actualType⟩, found, entryAccepted⟩ := entryAccepted
    cases indexType : exported.index <;> simp only [indexType] at entryAccepted
    all_goals try contradiction
    cases actualTypeEq : actualType <;> simp only [actualTypeEq] at entryAccepted
    all_goals try contradiction
    split at entryAccepted
    · rename_i exactType
      cases entryAccepted
      simp [name, found, indexType, actualTypeEq, exactType]
    · cases entryAccepted

end Silmaril.Wasm.Link.GC
