module

public import Silmaril.Wasm.Sublanguages.Strict.Link.Defs
import Silmaril.Proofs.Wasm.Sublanguages.Strict.Link.Features

public section

namespace Silmaril.Proofs.Wasm.Sublanguages.StrictLink

open Silmaril.Wasm Silmaril.Wasm.Sublanguages Silmaril.Wasm.Link

private theorem resolve_eq (namespaceName : String) (provider : LocalSections)
    (consumer : FunctionModule) (providerType consumerType : Validation.CModuleType) :
    StrictLink.resolve? namespaceName provider.exports consumer.imports providerType consumerType =
      GC.resolveImports? namespaceName (provider.assemble []) consumer.toCore providerType consumerType := by
  unfold StrictLink.resolve? GC.resolveImports?
  simp only [FunctionModule.toCore, LocalSections.assemble, List.zip_map_left, List.mapM_map]
  congr 1
  funext entry
  rcases entry with ⟨entry, expected⟩
  simp only [Prod.map_fst, Prod.map_snd, id_eq, FunctionImport.toCore, List.find?_map,
    Function.comp_def, FunctionExport.toCore]
  cases provider.exports.zip providerType.exports |>.find? (fun x => x.1.name == entry.name) <;> rfl

private theorem exports_eq (relocation : GC.Relocation) (exports : List FunctionExport) :
    (exports.mapM (StrictLink.relocateExport? relocation)).map (List.map FunctionExport.toCore) =
      (exports.map FunctionExport.toCore).mapM (GC.export? relocation) := by
  induction exports with
  | nil => rfl
  | cons entry rest ih =>
    simp only [List.map_cons, List.mapM_cons, StrictLink.relocateExport?, GC.export?,
      FunctionExport.toCore, ← ih]
    cases GC.function? relocation entry.index <;>
      cases rest.mapM (StrictLink.relocateExport? relocation) <;> rfl

theorem assemble?_toCore (namespaceName : String) (provider : LocalSections) (consumer : FunctionModule) :
    (StrictLink.assemble? namespaceName provider consumer).map (LocalSections.assemble · []) =
      GC.assemble? namespaceName (provider.assemble []) consumer.toCore := by
  unfold StrictLink.assemble? GC.assemble?
  have providerProfile : GC.inProfile (provider.assemble []) = provider.start.isNone := by
    simp [GC.inProfile, LocalSections.assemble]
  have consumerProfile : GC.inProfile consumer.toCore = consumer.sections.start.isNone := by
    simp [GC.inProfile, FunctionModule.toCore, LocalSections.assemble, FunctionImport.toCore]
  simp only [providerProfile, consumerProfile, ← resolve_eq]
  have bound : decide ((2 : Nat)^32 ≤ 0) = false := by decide
  simp only [FunctionModule.toCore, LocalSections.assemble, Module.typeDefinitions,
    List.map_nil, List.isEmpty_nil, Bool.and_true, List.length_nil, Nat.zero_add,
    bound, Bool.or_false, List.mapM_nil, Option.bind_eq_bind, Option.pure_def, Option.bind_some]
  simp only [← exports_eq, Option.bind_map]
  split
  · rfl
  · simp only [Option.map_bind, Function.comp_def]
    congr 1
    funext providerType
    congr 1
    funext consumerType
    split
    · rfl
    · simp only [Option.map_bind, Function.comp_def, Option.map_some, List.map_append, List.nil_append]

theorem linkSections?_toCore (namespaceName : String) (provider : LocalSections)
    (consumer : FunctionModule) :
    (StrictLink.linkSections? namespaceName provider consumer).map (LocalSections.assemble · []) =
      GC.link? namespaceName (provider.assemble []) consumer.toCore := by
  rw [GC.link?, ← assemble?_toCore]
  simp [StrictLink.linkSections?, GC.validated?, Option.bind_map, apply_ite]

private theorem linkSections_features {namespaceName : String} {provider : Ultrastrict} {consumer : Strict}
    {result : LocalSections} (h : StrictLink.linkSections? namespaceName provider.val consumer.val = some result) :
    Models.Module.InFeat strictCaps (result.assemble []) := by
  obtain ⟨assembled, eq, valid⟩ := Option.bind_eq_some_iff.mp h
  split at valid
  · cases valid
    exact assemble_features strictCaps provider.property consumer.property eq
  · contradiction

theorem link?_toCore (namespaceName : String) (provider : Ultrastrict) (consumer : Strict) :
    (StrictLink.link? namespaceName provider consumer).map Ultrastrict.toCore =
      GC.link? namespaceName provider.toCore consumer.toCore := by
  change _ = GC.link? namespaceName (provider.val.assemble []) consumer.val.toCore
  rw [← linkSections?_toCore]
  cases h : StrictLink.linkSections? namespaceName provider.val consumer.val with
  | none => simp [StrictLink.link?, h]
  | some result =>
    have admitted := linkSections_features h
    simp [StrictLink.link?, h, admitted]
    rfl

end Silmaril.Proofs.Wasm.Sublanguages.StrictLink
