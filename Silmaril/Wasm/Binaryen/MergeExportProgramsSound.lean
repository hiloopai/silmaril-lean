module

public import Silmaril.Wasm.Binaryen.MergeExportNamesSound
public import Silmaril.Wasm.Binaryen.MergeProfileEquivalence

@[expose] public section

namespace Silmaril.Wasm.Binaryen.MergeExportNames

open Execution.Core Validation Numerics RUMESim Link.GC
open Silmaril.Wasm.SingleThreaded.Det

variable {H : Type} {P : Profile}

private theorem bare_views {s t : Store H} (counts : s.funcs.length = t.funcs.length)
    (types : List RecType) (functions : List Func) (exportsA exportsB : List ExportInst) :
    Views.Successful Recipe.identity
      (Toolkit.MetaDCE.instanceOf s types functions exportsA)
      (Toolkit.MetaDCE.instanceOf t types functions exportsB) := by
  constructor
  · intro x y address shifted lookup
    simp only [Identity.function_identity, Option.some.injEq] at shifted
    subst y
    simpa only [Toolkit.MetaDCE.instanceOf, counts] using lookup
  · intro x y address shifted lookup
    simp [Toolkit.MetaDCE.instanceOf] at lookup
  · intro x y tag shifted lookup
    simp only [Recipe.identity, Identity.shift_zero, Option.some.injEq] at shifted
    subst y
    exact lookup

/-- Export-name changes are stable under an already related ambient store.
All old functions retain their existing relation, and newly installed functions
use the checked identity relocation with the actual differently named views. -/
theorem installed_names_related {s t : Store H} (ambient : StoreRelation.Related s t)
    (types : List RecType) (functions : List Func) (tags : List DefType)
    (exportsA exportsB : List ExportInst)
    (supported : ∀ fn ∈ functions, func? Recipe.identity fn = some fn) :
    StoreRelation.Related
      (Toolkit.MetaDCE.installed s functions tags (Toolkit.MetaDCE.instanceOf s types functions exportsA))
      (Toolkit.MetaDCE.installed t functions tags (Toolkit.MetaDCE.instanceOf t types functions exportsB)) := by
  have views := bare_views ambient.functions.length_eq types functions exportsA exportsB
  have own : List.Forall₂ (StoreRelation.Function (H := H))
      ((tags.zip functions).map fun p => ⟨p.1,
        Toolkit.MetaDCE.instanceOf s types functions exportsA, .wasm p.2⟩)
      ((tags.zip functions).map fun p => ⟨p.1,
        Toolkit.MetaDCE.instanceOf t types functions exportsB, .wasm p.2⟩) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro pair member
    exact .relocated Recipe.identity views
      (Functions.rewrite (supported pair.2 (List.of_mem_zip member).2))
  exact ⟨⟨ambient.tags, ambient.globals, ambient.mems, ambient.tables, ambient.datas,
    ambient.elems, ambient.structs, ambient.arrays, ambient.exns⟩,
    List.rel_append ambient.functions own⟩

/-- Actual export-list recipes preserve preparation and retain the existing
runtime store relation. Renaming and public export filtering instantiate this
one allocation theorem. -/
theorem bare_exports_ready_restore {s t targetFinal : Store H} {targetInstance : ModuleInst}
    (ambient : StoreRelation.Related s t) (storeValid : StoreOk s)
    (types : List RecType) (functions : List Func) (exports targetExports : List Export)
    (transform : List ExportInst → List ExportInst)
    (transport : ∀ E xi, exports.mapM (allocExport? E) = some xi →
      targetExports.mapM (allocExport? E) = some (transform xi))
    (profile : (Toolkit.MetaDCE.tree (Toolkit.MetaDCE.bare types functions exports)).inProfileBase = true)
    (sourceValid : ModuleValid (Toolkit.MetaDCE.bare types functions exports))
    (targetValid : ModuleValid (Toolkit.MetaDCE.bare types functions targetExports))
    (supported : ∀ fn ∈ functions, func? Recipe.identity fn = some fn)
    (ready : Ready P closedHost t (Toolkit.MetaDCE.bare types functions targetExports) [] targetFinal targetInstance) :
    ∃ sourceFinal sourceInstance,
      Ready P closedHost s (Toolkit.MetaDCE.bare types functions exports) [] sourceFinal sourceInstance ∧
      StoreOk sourceFinal ∧ StoreRelation.Related sourceFinal targetFinal ∧
      targetInstance = {sourceInstance with exports := transform sourceInstance.exports} ∧
      sourceInstance.exports.map ExportInst.name = exports.map Export.name := by
  obtain ⟨xtE, sourceType⟩ := Toolkit.MetaDCE.valid_closed rfl sourceValid
  obtain ⟨xtE', targetType⟩ := Toolkit.MetaDCE.valid_closed rfl targetValid
  have lifted : ModuleOk (Toolkit.MetaDCE.tree (Toolkit.MetaDCE.bare types functions exports)).lower
      ⟨[], xtE⟩ := by
    rw [Toolkit.MetaDCE.tree_lower]
    exact sourceType
  obtain ⟨values, tags, allocatedExports, globals, functionTypes, exportAllocation⟩ :=
    src_data profile rfl (s := s) lifted .nil
  rw [Toolkit.MetaDCE.tree_lower] at globals functionTypes exportAllocation
  have noValues : values = [] := by
    simpa only [Toolkit.MetaDCE.bare, List.map_nil, gv] using Option.some.inj globals.symm
  subst values
  let renamedAllocated := transform allocatedExports
  have counts := ambient.functions.length_eq
  have exportViews : EIrec s (Toolkit.MetaDCE.bare types functions exports) [] [] =
      EIrec t (Toolkit.MetaDCE.bare types functions targetExports) [] [] := by
    simp [EIrec, Toolkit.MetaDCE.bare, tmpStore, gtys, ExternAddr.funcs,
      ExternAddr.tags, ExternAddr.globals, ExternAddr.mems, ExternAddr.tables, counts]
  have renamedAllocation :
      (Toolkit.MetaDCE.bare types functions targetExports).exports.mapM
        (allocExport? (EIrec t (Toolkit.MetaDCE.bare types functions targetExports) [] [])) =
        some renamedAllocated := by
    have mapped := transport _ _ exportAllocation
    rw [exportViews] at mapped
    exact mapped
  have sourceInst := inst_of_closed (P := P) (host := closedHost)
    (Toolkit.MetaDCE.bare_profiled types functions exports) rfl
    ⟨xtE, [], sourceType, .nil⟩ rfl functionTypes exportAllocation
  have targetInst := inst_of_closed (P := P) (host := closedHost)
    (Toolkit.MetaDCE.bare_profiled types functions targetExports) rfl
    ⟨xtE', [], targetType, .nil⟩ rfl functionTypes renamedAllocation
  let c : Config H := ⟨Toolkit.MetaDCE.installed s functions tags
    (Toolkit.MetaDCE.instanceOf s types functions allocatedExports),
    {module := Toolkit.MetaDCE.instanceOf s types functions allocatedExports}, []⟩
  let d : Config H := ⟨Toolkit.MetaDCE.installed t functions tags
    (Toolkit.MetaDCE.instanceOf t types functions renamedAllocated),
    {module := Toolkit.MetaDCE.instanceOf t types functions renamedAllocated}, []⟩
  have sourceInstantiation : Instantiate P closedHost s (Toolkit.MetaDCE.bare types functions exports) [] c := by
    simpa only [Toolkit.MetaDCE.MIrec_bare, Toolkit.MetaDCE.STrec_bare,
      Toolkit.MetaDCE.startCode_bare] using sourceInst
  have targetInstantiation : Instantiate P closedHost t
      (Toolkit.MetaDCE.bare types functions targetExports) [] d := by
    simpa only [Toolkit.MetaDCE.MIrec_bare, Toolkit.MetaDCE.STrec_bare,
      Toolkit.MetaDCE.startCode_bare] using targetInst
  have sourceReady : Ready P closedHost s (Toolkit.MetaDCE.bare types functions exports) [] c.store c.frame.module :=
    ⟨c, c, sourceInstantiation, .refl, rfl, rfl, rfl⟩
  have sourceStoreValid : StoreOk c.store := by
    have preparation := MergeChain.prepare_of_ready (as := []) (by rfl) sourceReady
    exact MergeChain.prepare_storeOk storeValid ⟨xtE, [], sourceType, .nil⟩ preparation
  obtain ⟨initial, final, instantiated, run, _, finalStore, initialModule⟩ := ready
  obtain rfl := inst_det instantiated targetInstantiation
  rcases Relation.ReflTransGen.cases_head run with rfl | ⟨next, step, _⟩
  · change d.store = targetFinal at finalStore
    change d.frame.module = targetInstance at initialModule
    refine ⟨c.store, c.frame.module, sourceReady, sourceStoreValid, ?_, ?_, ?_⟩
    · rw [← finalStore]
      exact installed_names_related ambient types functions tags allocatedExports renamedAllocated supported
    · rw [← initialModule]
      simp only [c, d, Toolkit.MetaDCE.instanceOf, counts, renamedAllocated]
    · exact allocExports_names _ exportAllocation
  · exact (not_step_vals (W := []) step).elim

/-- A renamed closed module is prepared alongside its original in related
ambient stores. The resulting stores retain the real linker simulation and
the returned instance exposes exactly the renamed original exports. -/
theorem bare_ready_restore {s t targetFinal : Store H} {targetInstance : ModuleInst}
    (ambient : StoreRelation.Related s t) (storeValid : StoreOk s)
    (rename : String → String) (types : List RecType) (functions : List Func) (exports : List Export)
    (profile : (Toolkit.MetaDCE.tree (Toolkit.MetaDCE.bare types functions exports)).inProfileBase = true)
    (sourceValid : ModuleValid (Toolkit.MetaDCE.bare types functions exports))
    (targetValid : ModuleValid (renameExports rename (Toolkit.MetaDCE.bare types functions exports)))
    (supported : ∀ fn ∈ functions, func? Recipe.identity fn = some fn)
    (ready : Ready P closedHost t
      (renameExports rename (Toolkit.MetaDCE.bare types functions exports)) [] targetFinal targetInstance) :
    ∃ sourceFinal sourceInstance,
      Ready P closedHost s (Toolkit.MetaDCE.bare types functions exports) [] sourceFinal sourceInstance ∧
      StoreOk sourceFinal ∧ StoreRelation.Related sourceFinal targetFinal ∧
      targetInstance = {sourceInstance with exports := sourceInstance.exports.map (fun e => {e with name := rename e.name})} ∧
      sourceInstance.exports.map ExportInst.name = exports.map Export.name := by
  exact bare_exports_ready_restore ambient storeValid types functions exports
    (exports.map fun (e : Export) => {e with name := rename e.name})
    (fun xi => xi.map fun (e : ExportInst) => {e with name := rename e.name})
    (fun E _ allocated => allocExports_rename rename E allocated)
    profile sourceValid targetValid supported ready

/-- The executable narrow alias guard supplies these nonsemantic facts.
No execution-preservation assumption is included. -/
structure ClosedFacts (aliases : List Alias) (namespaceName : String) (m : Module) : Prop where
  bare : m = Toolkit.MetaDCE.bare m.types m.funcs m.exports
  profile : (Toolkit.MetaDCE.tree m).inProfileBase = true
  valid : ModuleValid m
  rewrittenValid : ModuleValid (rewrite aliases namespaceName m)
  identity : ∀ fn ∈ m.funcs, func? Recipe.identity fn = some fn
  injective : AliasInjectiveOn aliases namespaceName m

/-- Actual named instances retain their original declaration's export-name
domain, and the prepared instance carries exactly the declared alias map. -/
def InstanceFrom (aliases : List Alias) (whole : List (String × Module))
    (source target : String × ModuleInst) : Prop :=
  source.1 = target.1 ∧ ∃ m, (source.1, m) ∈ whole ∧
    source.2.exports.map ExportInst.name = m.exports.map Export.name ∧
    target.2 = {source.2 with exports := source.2.exports.map (fun e =>
      {e with name := lookup aliases source.1 e.name})}

/-- Restore the original in-order program while carrying its actual store
relation and the explicit per-namespace observation-name map. -/
theorem separateReady_names {aliases : List Alias} {whole program : List (String × Module)}
    (members : ∀ p ∈ program, p ∈ whole)
    (facts : ∀ p ∈ program, ClosedFacts aliases p.1 p.2)
    {s t targetFinal : Store H} {sourceInstances targetInstances finalTargets : List (String × ModuleInst)}
    (ambient : StoreRelation.Related s t) (storeValid : StoreOk s)
    (instances : List.Forall₂ (InstanceFrom aliases whole) sourceInstances targetInstances)
    (ready : SeparateReady P closedHost t targetInstances (rewriteProgram aliases program) targetFinal finalTargets) :
    ∃ sourceFinal finalSources, SeparateReady P closedHost s sourceInstances program sourceFinal finalSources ∧
      StoreOk sourceFinal ∧ StoreRelation.Related sourceFinal targetFinal ∧
      List.Forall₂ (InstanceFrom aliases whole) finalSources finalTargets := by
  induction program generalizing s t sourceInstances targetInstances with
  | nil =>
    cases ready
    exact ⟨s, sourceInstances, .nil, storeValid, ambient, instances⟩
  | cons pair rest ih =>
    rcases pair with ⟨namespaceName, m⟩
    have moduleFacts : ClosedFacts aliases namespaceName m := facts (namespaceName, m) (by simp)
    have noImports : m.imports = [] := by rw [moduleFacts.bare]; rfl
    have rewritten := rewrite_closed aliases namespaceName noImports
    change SeparateReady P closedHost t targetInstances
      ((namespaceName, rewrite aliases namespaceName m) :: rewriteProgram aliases rest) targetFinal finalTargets at ready
    cases ready with
    | @cons _ intermediate _ _ _ _ _ _ xas targetInstance imports headReady tailReady =>
      have noTargetImports : (rewrite aliases namespaceName m).imports = [] := by
        simp [rewrite, noImports]
      have noAddresses : xas = [] := by
        simpa [resolveImportsBy, noTargetImports] using imports.symm
      subst xas
      have originalValid := moduleFacts.valid
      have renamedValid := moduleFacts.rewrittenValid
      have profile := moduleFacts.profile
      rw [moduleFacts.bare] at originalValid profile
      rw [rewritten, moduleFacts.bare] at renamedValid headReady
      obtain ⟨sourceIntermediate, sourceInstance, sourceReady, sourceStoreValid,
        related, names, declaredNames⟩ := bare_ready_restore ambient storeValid
          (lookup aliases namespaceName) m.types m.funcs m.exports profile originalValid
          renamedValid moduleFacts.identity headReady
      rw [← moduleFacts.bare] at sourceReady
      have fresh : InstanceFrom aliases whole (namespaceName, sourceInstance) (namespaceName, targetInstance) :=
        ⟨rfl, m, members (namespaceName, m) (by simp), declaredNames, names⟩
      obtain ⟨sourceFinal, finalSources, sourceTail, finalValid, finalRelated, finalInstances⟩ :=
        ih (fun p member => members p (by simp [member]))
          (fun p member => facts p (by simp [member])) related sourceStoreValid
          (.cons fresh instances) tailReady
      refine ⟨sourceFinal, finalSources, .cons ?_ sourceReady sourceTail,
        finalValid, finalRelated, finalInstances⟩
      simp [resolveImportsBy, noImports]

private theorem instance_lookup {aliases : List Alias} {whole : List (String × Module)}
    {source target : List (String × ModuleInst)}
    (instances : List.Forall₂ (InstanceFrom aliases whole) source target)
    {name : String} {targetInstance : ModuleInst} (found : target.lookup name = some targetInstance) :
    ∃ sourceInstance, source.lookup name = some sourceInstance ∧
      InstanceFrom aliases whole (name, sourceInstance) (name, targetInstance) := by
  induction instances with
  | nil => simp at found
  | @cons sourceHead targetHead sourceTail targetTail head rest ih =>
    rcases sourceHead with ⟨sourceName, sourceInstance⟩
    rcases targetHead with ⟨targetName, targetHeadInstance⟩
    obtain ⟨sameName, declaration, member, declaredNames, renamed⟩ := head
    change sourceName = targetName at sameName
    subst targetName
    by_cases same : name = sourceName
    · subst name
      simp only [List.lookup, beq_self_eq_true] at found
      cases found
      exact ⟨sourceInstance, by simp [List.lookup], rfl, declaration, member, declaredNames, renamed⟩
    · have different : (name == sourceName) = false := by simp [same]
      simp only [List.lookup, different] at found ⊢
      exact ih found

private theorem alias_names {aliases : List Alias} {namespaceName : String} {m : Module}
    (injective : AliasInjectiveOn aliases namespaceName m) :
    ∀ x ∈ m.exports.map Export.name, ∀ y ∈ m.exports.map Export.name,
      lookup aliases namespaceName x = lookup aliases namespaceName y → x = y := by
  intro x hx y hy same
  obtain ⟨a, memberA, rfl⟩ := List.mem_map.mp hx
  obtain ⟨b, memberB, rfl⟩ := List.mem_map.mp hy
  exact injective a memberA b memberB same

/-- Every actual renamed-program behavior is an original-program behavior
under its explicit namespace-qualified export query. The theorem includes
arbitrary argument lists and every numerical profile. -/
theorem program_beh_names {aliases : List Alias} {program : List (String × Module)}
    (facts : ∀ p ∈ program, ClosedFacts aliases p.1 p.2)
    (names : (program.map Prod.fst).Nodup) {namespaceName query : String} {args : List Val}
    (declared : ∃ m, (namespaceName, m) ∈ program ∧ query ∈ m.exports.map Export.name) :
    Program.beh P (closedHost (H := H)) (rewriteProgram aliases program)
        namespaceName (lookup aliases namespaceName query) args ⊆
      Program.beh P (closedHost (H := H)) program namespaceName query args := by
  rintro behavior ⟨targetStore, targetInstances, targetInstance, address,
    targetReady, targetLookup, exported, observed⟩
  obtain ⟨sourceStore, sourceInstances, sourceReady, sourceValid, stores, instances⟩ :=
    separateReady_names (whole := program) (fun _ member => member) facts
      (StoreRelation.Related.refl {}) MergeChain.storeOk_empty .nil targetReady
  obtain ⟨sourceInstance, sourceLookup, _, m, member, declaredNames, renamed⟩ :=
    instance_lookup instances targetLookup
  obtain ⟨original, originalMember, queryDeclared⟩ := declared
  have same : (namespaceName, m) = (namespaceName, original) :=
    List.inj_on_of_nodup_map names member originalMember rfl
  have sameModule := congrArg Prod.snd same
  change m = original at sameModule
  subst m
  have moduleFacts : ClosedFacts aliases namespaceName original := facts _ originalMember
  change sourceInstance.exports.map ExportInst.name = original.exports.map Export.name at declaredNames
  change targetInstance = {sourceInstance with exports := sourceInstance.exports.map (fun e => {e with name := lookup aliases namespaceName e.name})} at renamed
  have queries : exportFunc? targetInstance (lookup aliases namespaceName query) =
      exportFunc? sourceInstance query := by
    rw [renamed]
    apply exportFunc_rename (lookup aliases namespaceName) sourceInstance query
    intro e member
    have eDeclared : e.name ∈ original.exports.map Export.name := by
      rw [← declaredNames]
      exact List.mem_map.mpr ⟨e, member, rfl⟩
    exact ⟨alias_names moduleFacts.injective e.name eDeclared query queryDeclared,
      congrArg (lookup aliases namespaceName)⟩
  have observations : behaviours P closedHost targetStore address args =
      behaviours P closedHost sourceStore address args :=
    MergeUntyped.related_behaviours_profile stores
      (MergeUntyped.storeSc_of_ok sourceValid) address args
  rw [observations] at observed
  exact ⟨sourceStore, sourceInstances, sourceInstance, address, sourceReady, sourceLookup,
    queries.symm.trans exported, observed⟩

/-- Compose the actual checked merger with original-interface name transport.
The output is the pre-filter linked module; skip-policy export filtering is a
separate public-interface projection step. -/
theorem checkedMerge_names_refines_original {aliases : List Alias}
    {program : List (String × Module)} {linked : Module}
    (facts : ∀ p ∈ program, ClosedFacts aliases p.1 p.2)
    (merged : checkedMerge? (rewriteProgram aliases program) = some linked)
    (P : Profile) {namespaceName query : String} {args : List Val}
    (declared : ∃ m, (namespaceName, m) ∈ program ∧ query ∈ m.exports.map Export.name) :
    (moduleEntryPoints P (closedHost (H := H)) closedEnv).beh linked
        (lookup aliases namespaceName query) args ⊆
      Program.beh P (closedHost (H := H)) program namespaceName query args := by
  have exported : ∃ p ∈ rewriteProgram aliases program,
      p.1 = namespaceName ∧ ∃ e ∈ p.2.exports, e.name = lookup aliases namespaceName query := by
    obtain ⟨m, member, queryDeclared⟩ := declared
    obtain ⟨e, exportMember, exportName⟩ := List.mem_map.mp queryDeclared
    refine ⟨(namespaceName, rewrite aliases namespaceName m), ?_, rfl,
      {e with name := lookup aliases namespaceName e.name}, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨(namespaceName, m), member, rfl⟩
    · exact List.mem_map.mpr ⟨e, exportMember, rfl⟩
    · simp only [exportName]
  have agreement : Program.beh P (closedHost (H := H)) (rewriteProgram aliases program)
      namespaceName (lookup aliases namespaceName query) args =
      (moduleEntryPoints P (closedHost (H := H)) closedEnv).beh linked
        (lookup aliases namespaceName query) args := checkedMerge?_sound_profile merged P exported
  rw [← agreement]
  obtain ⟨_, _, _, _, _, names, _⟩ := checkedMerge?_conditions merged
  have originalNames : (program.map Prod.fst).Nodup := by
    simpa [rewriteProgram, List.map_map, Function.comp_def] using names
  exact program_beh_names facts originalNames declared

end Silmaril.Wasm.Binaryen.MergeExportNames
