module

public import Silmaril.Wasm.Component.Reference.Validation.FunctionPorts.Defs
import Silmaril.Wasm.Component.Reference.Validation.Defs.Thms
import Silmaril.Wasm.Validation.Check.ValidateFinal
import Silmaril.Wasm.Versions.Thms

public section

namespace Silmaril.Proofs.Wasm.Component.Reference.Validation.FunctionPorts

open Silmaril.Wasm
open Wasm.Component.Validation Wasm.Component.Types
open Wasm.Component.Engine (CoreExternType)
open Wasm.Validation (CExternType DefType)

private theorem allFlat (sig : V1.FuncType) : core3Ext? (.func sig.toDefType) = some (core3OfFlat sig) := by
  have ok := Wasm.Validation.ExternTypeOk.check_complete
    (Wasm.Validation.tyOk_check_complete_all {} Wasm.Validation.TypeCtx.ok_empty rfl) (externTypeOk_toDefType sig)
  simp [core3Ext?, ok, core3OfFlat]

private theorem getElem_filterMap {α β : Type} (resolve : α → Option β) :
    ∀ (entries : List α), (∀ item ∈ entries, (resolve item).isSome = true) →
    ∀ index : Nat, (entries.filterMap resolve)[index]? = (entries[index]?).bind resolve
  | [], _, _ => by simp
  | item :: rest, total, index => by
    obtain ⟨_, found⟩ := Option.isSome_iff_exists.mp (total item List.mem_cons_self)
    have tail := getElem_filterMap resolve rest (fun entry mem => total entry (List.mem_cons_of_mem _ mem))
    cases index <;> simp [found, tail]

private theorem functionLookup {mod : Lime1.Module} (valid : Lime1.Validation.ModuleValid mod) (index : FuncIdx) :
    (Lime1.Validation.moduleContext mod).funcs[index.toNat]? = mod.functionType? index := by
  have funcs : (Lime1.Validation.moduleContext mod).funcs =
      mod.functionTypes.filterMap (fun ty => mod.types[ty.toNat]?) := by
    simp only [Lime1.Validation.moduleContext, Scalar.Module.functionTypes, Scalar.Module.importedFunctions,
      List.filterMap_append, List.filterMap_filterMap, List.filterMap_map]
    congr 1
    apply List.filterMap_congr
    intro entry _
    cases entry.desc <;> rfl
  have total : FuncTypesResolve mod := by
    intro ty mem
    simp only [Scalar.Module.functionTypes, Scalar.Module.importedFunctions, List.mem_append,
      List.mem_filterMap, List.mem_map] at mem
    rcases mem with ⟨entry, present, found⟩ | ⟨fn, present, rfl⟩
    · obtain ⟨_, resolved, _⟩ := valid.imports entry present
      cases desc : entry.desc <;> simp_all [Lime1.Validation.importType?]
      obtain ⟨_, foundType, _⟩ := resolved
      exact (List.getElem?_eq_some_iff.mp foundType).1
    · obtain ⟨_, found⟩ := valid.function_type_exists present
      simp [found]
  rw [funcs, getElem_filterMap _ _ total]
  rfl

private def PortMatch {Key : Type} (native : Option (Key × CoreExternType)) (key : Key)
    (core : CExternType) : Prop :=
  ∃ sig : V1.FuncType, native = some (key, .func sig) ∧ core = .func sig.toDefType

private theorem resolveBoth {Decl Image Key : Type} (resolve : Decl → Option (Key × CoreExternType))
    (lift : Decl → Image) (key : Image → Key) : ∀ {entries types},
    List.Forall₂ (fun entry ty => PortMatch (resolve entry) (key (lift entry)) ty) entries types →
    ∃ ports : List (Key × V1.FuncType),
      entries.mapM resolve = some (ports.map (fun entry => (entry.1, .func entry.2))) ∧
      ((entries.map lift).zip types).mapM (fun entry => (core3Ext? entry.2).map (entry.1 |> key, ·)) =
        some (ports.map (fun entry => (entry.1, core3OfFlat entry.2)))
  | _, _, .nil => ⟨[], rfl, rfl⟩
  | _, _, .cons (a := entry) ⟨sig, found, rfl⟩ rest => by
    obtain ⟨ports, native, core⟩ := resolveBoth resolve lift key rest
    exact ⟨(key (lift entry), sig) :: ports,
      by simp [found, native], by simp [allFlat, core]⟩

private theorem importMatch {mod : Lime1.Module} (valid : Lime1.Validation.ModuleValid mod)
    (ports : LimeFunctionPorts mod) : List.Forall₂
      (fun entry ty => PortMatch (scalarImportEntry? mod entry) (entry.moduleName, entry.name) ty)
      mod.imports (mod.imports.map fun entry => Lime1.Validation.importC mod.types entry.desc) := by
  simpa only [List.map_id] using Lime1.Validation.forall₂_map_of id
    (fun entry => Lime1.Validation.importC mod.types entry.desc) mod.imports (fun entry mem => by
      obtain ⟨index, desc⟩ := ports.imports entry mem
      obtain ⟨_, resolved, _⟩ := valid.imports entry mem
      rw [desc] at resolved
      obtain ⟨sig, found, _⟩ := Option.map_eq_some_iff.mp resolved
      exact ⟨sig, by simp [scalarImportEntry?, scalarImportType?, desc, found],
        by simp [Lime1.Validation.importC, desc, found]⟩)

private theorem pairedImp {α β : Type} {Before After : α → β → Prop} {entries : List α} {types : List β}
    (paired : List.Forall₂ Before entries types)
    (convert : ∀ left right, left ∈ entries → Before left right → After left right) :
    List.Forall₂ After entries types := by
  induction paired with
  | nil => exact .nil
  | cons pair _ ih =>
    exact .cons (convert _ _ List.mem_cons_self pair) (ih (fun left right mem =>
      convert left right (List.mem_cons_of_mem _ mem)))

private theorem exportMatch {mod : Lime1.Module} (valid : Lime1.Validation.ModuleValid mod)
    (ports : LimeFunctionPorts mod) {types : List CExternType}
    (paired : List.Forall₂ (fun entry ty => match entry.index with
      | .func index => ((Lime1.Validation.moduleContext mod).funcs[index.toNat]?).map
          (fun sig => CExternType.func sig.toDefType) = some ty
      | _ => True) mod.exports types) : List.Forall₂
    (fun entry ty => PortMatch (scalarExportEntry? mod entry) entry.name ty) mod.exports types := by
  apply pairedImp paired
  intro entry ty present found
  obtain ⟨index, desc⟩ := ports.exports entry present
  rw [desc] at found
  obtain ⟨sig, lookup, typeEq⟩ := Option.map_eq_some_iff.mp found
  exact ⟨sig, by simp [scalarExportEntry?, scalarExportType?, desc, ← functionLookup valid index, lookup], typeEq.symm⟩

theorem resolves {mod : Lime1.Module} (valid : Lime1.Validation.ModuleValid mod) (ports : LimeFunctionPorts mod) :
    ∃ signature : CoreModuleType V1.FuncType,
      lime1ModuleType mod = some (signature.mapX CoreExternType.func) ∧
      core3ModuleType? mod.toCore = some (signature.mapX core3OfFlat) := by
  obtain ⟨exportTypes, validated, matched⟩ := valid.toCore_ok_functionPorts
  obtain ⟨imports, nativeImports, coreImports⟩ := resolveBoth (scalarImportEntry? mod)
    V1.Import.toCore (fun entry : Wasm.Import => (entry.moduleName, entry.name)) (importMatch valid ports)
  obtain ⟨exports, nativeExports, coreExports⟩ := resolveBoth (scalarExportEntry? mod)
    V1.Export.toCore Wasm.Export.name (exportMatch valid ports matched)
  refine ⟨⟨imports, exports⟩, ?_, ?_⟩
  · simp [lime1ModuleType, scalarModuleType, CoreModuleType.mapX, nativeImports, nativeExports]
  · unfold core3ModuleType?
    rw [Wasm.Validation.validate?_complete validated]
    change (((mod.imports.map V1.Import.toCore).zip
      (mod.imports.map fun entry => Lime1.Validation.importC mod.types entry.desc)).mapM
        (fun entry => (core3Ext? entry.2).map ((entry.1.moduleName, entry.1.name), ·))).bind
      (fun resolvedImports => (((mod.exports.map V1.Export.toCore).zip exportTypes).mapM
        (fun entry => (core3Ext? entry.2).map (entry.1.name, ·))).bind
        (fun resolvedExports => some (⟨resolvedImports, resolvedExports⟩ : CoreModuleType Core3Extern))) = _
    rw [coreImports, Option.bind_some, coreExports]
    rfl

end Silmaril.Proofs.Wasm.Component.Reference.Validation.FunctionPorts
