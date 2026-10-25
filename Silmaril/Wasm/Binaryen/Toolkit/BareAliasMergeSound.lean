module

public import Silmaril.Wasm.Binaryen.Toolkit.BareAliasMerge
public import Silmaril.Wasm.Binaryen.Exe.CoreInputCheckSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

theorem identityFunctionB_sound {types : List RecType} {f : Func}
    (checked : identityFunctionB types f = true) :
    Link.GC.func? Link.GC.Recipe.identity f = some f := by
  unfold identityFunctionB at checked
  cases relocated : Link.GC.func? Link.GC.Recipe.identity f with
  | none => simp [relocated] at checked
  | some shifted =>
      simp only [relocated] at checked
      have same := Exe.canonicalModuleEq_sound checked
      have funcs := congrArg Module.funcs same
      simp only [List.cons.injEq, and_true] at funcs
      simp only [funcs]

theorem bareAliasTransportB_sound {aliases : List MergeExportNames.Alias}
    {ns : String} {m : Module} (checked : bareAliasTransportB aliases ns m = true) :
    (m.imports = [] ∧ m.tags = [] ∧ m.globals = [] ∧ m.memories = [] ∧
      m.tables = [] ∧ m.data = [] ∧ m.elems = [] ∧ m.start = none) ∧
    (MetaDCE.tree m).inProfileBase = true ∧
    (∀ f ∈ m.funcs, Link.GC.func? Link.GC.Recipe.identity f = some f) ∧
    Validation.ModuleValid m ∧ Validation.ModuleValid (MergeExportNames.rewrite aliases ns m) ∧
    MergeExportNames.AliasInjectiveOn aliases ns m := by
  simp only [bareAliasTransportB, Bool.and_eq_true, List.isEmpty_iff,
    Option.isNone_iff_eq_none] at checked
  rcases checked with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hi, ht⟩, hg⟩, hm⟩, hta⟩, hd⟩, he⟩, hs⟩,
    profile⟩, functions⟩, sourceValid⟩, targetValid⟩, injection⟩
  exact ⟨⟨hi, ht, hg, hm, hta, hd, he, hs⟩, profile,
    fun f hf => identityFunctionB_sound (List.all_eq_true.mp functions f hf),
    Validation.validate?_isSome_iff.mp sourceValid,
    Validation.validate?_isSome_iff.mp targetValid,
    MergeExportNames.aliasInjectiveB_sound injection⟩

end Silmaril.Wasm.Binaryen.Toolkit
