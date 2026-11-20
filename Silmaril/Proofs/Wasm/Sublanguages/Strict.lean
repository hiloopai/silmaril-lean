module

public import Silmaril.Wasm.Sublanguages.Strict.Defs

public section

namespace Silmaril.Wasm.Sublanguages.Proofs

private theorem imports_sound {entry : Import} {decoded : FunctionImport}
    (read : FunctionImport.ofCore? entry = some decoded) : decoded.toCore = entry := by
  rcases entry with ⟨_, _, type⟩
  cases type <;> cases read
  rfl

private theorem exports_sound {entry : Export} {decoded : FunctionExport}
    (read : FunctionExport.ofCore? entry = some decoded) : decoded.toCore = entry := by
  rcases entry with ⟨_, index⟩
  cases index <;> cases read
  rfl

private theorem mapM_sound {Core Small : Type} {read : Core → Option Small} {embed : Small → Core}
    (sound : ∀ {entry decoded}, read entry = some decoded → embed decoded = entry)
    {entries : List Core} {decoded : List Small} (found : entries.mapM read = some decoded) :
    decoded.map embed = entries := by
  have aligned := Validation.List.mapM_some_forall₂ (R := fun entry result => entry = embed result)
    (fun eq => (sound eq).symm) found
  have mapped := List.forall₂_map_right_iff.mpr aligned
  exact (by simpa only [List.forall₂_eq_eq_eq] using mapped : entries = decoded.map embed).symm

theorem functionModule_complete (mod : FunctionModule) : FunctionModule.ofCore? mod.toCore = some mod := by
  have imports (entries : List FunctionImport) :
      (entries.map FunctionImport.toCore).mapM FunctionImport.ofCore? = some entries := by
    induction entries with
    | nil => rfl
    | cons entry tail ih => simp [List.mapM_cons, FunctionImport.ofCore?, FunctionImport.toCore, ih]
  have exports (entries : List FunctionExport) :
      (entries.map FunctionExport.toCore).mapM FunctionExport.ofCore? = some entries := by
    induction entries with
    | nil => rfl
    | cons entry tail ih => simp [List.mapM_cons, FunctionExport.ofCore?, FunctionExport.toCore, ih]
  simp [FunctionModule.ofCore?, FunctionModule.toCore, LocalSections.assemble,
    FunctionModule.noResourceSections, imports, exports]

theorem functionModule_sound {source : Wasm.Module} {mod : FunctionModule}
    (found : FunctionModule.ofCore? source = some mod) : mod.toCore = source := by
  by_cases shape : FunctionModule.noResourceSections source = true
  · simp only [FunctionModule.ofCore?, shape, Bool.not_true, Bool.false_eq_true, ite_false] at found
    obtain ⟨imports, readImports, rest⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨exports, readExports, assembled⟩ := Option.bind_eq_some_iff.mp rest
    cases assembled
    have importsEq := mapM_sound (fun eq => imports_sound eq) readImports
    have exportsEq := mapM_sound (fun eq => exports_sound eq) readExports
    cases source
    simp_all [FunctionModule.noResourceSections, Bool.and_eq_true, FunctionModule.toCore,
      LocalSections.assemble]
  · simp [FunctionModule.ofCore?, Bool.eq_false_of_not_eq_true shape] at found

theorem strict_sound {source : Wasm.Module} {mod : Strict}
    (found : Strict.ofCore? source = some mod) : mod.toCore = source := by
  obtain ⟨candidate, read, admitted⟩ := Option.bind_eq_some_iff.mp found
  split at admitted
  · cases admitted; exact functionModule_sound read
  · cases admitted

theorem ultrastrict_sound {source : Wasm.Module} {mod : Ultrastrict}
    (found : Ultrastrict.ofCore? source = some mod) : mod.toCore = source := by
  obtain ⟨candidate, read, admitted⟩ := Option.bind_eq_some_iff.mp found
  split at admitted
  · rename_i closed
    cases admitted
    change candidate.val.sections.assemble [] = source
    rw [← closed]
    exact strict_sound read
  · cases admitted

theorem functionModule_types (mod : FunctionModule) : mod.toCore.functionTypes = mod.functionTypes := by
  unfold Module.functionTypes Module.importedFunctions FunctionModule.functionTypes
  change List.filterMap _ (mod.imports.map FunctionImport.toCore) ++ _ = _
  rw [List.filterMap_map]
  simp [Function.comp_def, FunctionImport.toCore, FunctionModule.toCore, LocalSections.assemble]

theorem functionModule_signature (mod : FunctionModule) (index : FuncIdx) :
    mod.toCore.functionSignature? index = mod.functionSignature? index := by
  have types : mod.toCore.split.functionTypes = mod.functionTypes := functionModule_types mod
  unfold Module.functionSignature? ModuleParts.functionSignature? FunctionModule.functionSignature?
  rw [types]; rfl

theorem strict_imports {iface : Validation.CModuleType} (mod : Strict.Checked iface) :
    ∃ types, Validation.TypesOk {} mod.val.val.sections.types types ∧
      List.Forall₂ (fun entry port => Validation.ImportOk { types := types } entry.toCore port)
        mod.val.val.imports iface.imports := by
  rcases mod with ⟨mod, valid⟩
  cases valid with
  | mk typesValid importsValid =>
    exact ⟨_, typesValid, List.forall₂_map_left_iff.mp importsValid⟩

theorem import_type {context : Validation.Context} {entry : FunctionImport} {port : Validation.CExternType}
    (valid : Validation.ImportOk context entry.toCore port) :
    ∃ type, context.type? entry.type = some type ∧ port = .func type := by
  have resolved : (context.type? entry.type).map Validation.CExternType.func = some port := valid.1
  obtain ⟨type, found, equal⟩ := Option.map_eq_some_iff.mp resolved
  exact ⟨type, found, equal.symm⟩

theorem ultrastrict_legacy (mod : Ultrastrict) :
    Profiles.FunctionalCore.accepts .immutable .disabled mod.toCore := by
  refine ⟨mod.property, ?_⟩
  simp [Profiles.FunctionalCore.closedShape, Ultrastrict.toCore, Ultrastrict.toStrict,
    Strict.toCore, FunctionModule.toCore, LocalSections.assemble, List.all_map, FunctionExport.toCore]

private theorem exports_read (entries : List Export)
    (allowed : entries.all (fun entry => match entry.index with | .func _ => true | _ => false) = true) :
    ∃ decoded, entries.mapM FunctionExport.ofCore? = some decoded := by
  induction entries with
  | nil => exact ⟨[], rfl⟩
  | cons entry tail ih =>
    simp only [List.all_cons, Bool.and_eq_true] at allowed
    obtain ⟨decoded, read⟩ := ih allowed.2
    rcases entry with ⟨name, index⟩
    cases index <;> cases allowed.1
    rename_i index
    exact ⟨⟨name, index⟩ :: decoded, by simp [List.mapM_cons, FunctionExport.ofCore?, read]⟩

theorem legacy_read (mod : Profiles.Module Profiles.Strict) :
    ∃ closed, Ultrastrict.ofCore? mod.val = some closed := by
  have shape := mod.property.2
  simp only [Profiles.FunctionalCore.closedShape, Bool.and_eq_true, List.isEmpty_iff] at shape
  rcases shape with ⟨⟨⟨⟨⟨⟨hi, hm⟩, ht⟩, hg⟩, he⟩, hd⟩, hx⟩
  obtain ⟨exports, read⟩ := exports_read _ hx
  let output : FunctionModule := ⟨⟨mod.val.types, mod.val.funcs, mod.val.start, exports⟩, []⟩
  have found : FunctionModule.ofCore? mod.val = some output := by
    simp [FunctionModule.ofCore?, FunctionModule.noResourceSections, Profiles.FunctionalCore.tags_empty mod,
      hi, hm, ht, hg, he, hd, read, output]
  have admitted : Models.Module.InFeat strictCaps output.toCore := functionModule_sound found ▸ mod.property.1
  have strict : Strict.ofCore? mod.val = some (⟨output, admitted⟩ : Strict) := by
    simp [Strict.ofCore?, found, admitted]
  refine ⟨⟨output.sections, admitted⟩, ?_⟩
  unfold Ultrastrict.ofCore?
  rw [strict]; rfl

theorem validate_checked {iface : Validation.CModuleType} (mod : Strict.Checked iface) :
    Strict.validate? mod.val = some ⟨iface, mod⟩ := by
  have computed : Validation.validate? mod.val.toCore = some iface := Validation.validate?_complete mod.property
  unfold Strict.validate?
  split
  · rename_i absent
    rw [computed] at absent
    contradiction
  · rename_i actual selected
    have equal := Option.some.inj (selected.symm.trans computed)
    subst actual
    rfl

end Silmaril.Wasm.Sublanguages.Proofs
