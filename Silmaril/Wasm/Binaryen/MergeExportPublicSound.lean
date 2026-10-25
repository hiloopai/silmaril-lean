module

public import Silmaril.Wasm.Binaryen.MergeExportProgramsSound

@[expose] public section

namespace Silmaril.Wasm.Binaryen.MergeExportNames

open Execution.Core Validation Numerics RUMESim Link.GC

variable {H : Type} {P : Profile}

/-- Filtering actual source exports filters precisely their allocated names;
all retained external addresses and their order are unchanged. -/
theorem allocExports_filter (keep : String → Bool) (E : ModuleInst) :
    ∀ {exports : List Export} {allocated : List ExportInst},
      exports.mapM (allocExport? E) = some allocated →
      (exports.filter fun e => keep e.name).mapM (allocExport? E) =
        some (allocated.filter fun e => keep e.name)
  | [], allocated, accepted => by
    have empty : allocated = [] := by simpa using accepted.symm
    subst allocated
    rfl
  | e :: exports, allocated, accepted => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at accepted
    obtain ⟨ei, head, rest, tail, rfl⟩ := accepted
    have name := Toolkit.MetaDCE.allocExport_name head
    have ih := allocExports_filter keep E tail
    cases selected : keep e.name <;> simp [name, selected, head, ih]

/-- Every retained name resolves to its exact pre-filter address. -/
theorem exportFunc_filter (keep : String → Bool) (mi : ModuleInst) {query : String}
    (retained : keep query = true) :
    exportFunc? {mi with exports := mi.exports.filter fun e => keep e.name} query =
      exportFunc? mi query := by
  unfold exportFunc?
  congr 1
  rw [List.find?_filter]
  congr 1
  funext e
  by_cases same : e.name = query
  · simp [same, retained]
  · simp [same]

/-- The public export projection cannot add a behavior at a retained name.
The theorem uses actual related allocations and covers arbitrary argument
lists at every numerical profile. -/
theorem bare_filter_beh_refines (keep : String → Bool) (types : List RecType)
    (functions : List Func) (exports : List Export)
    (profile : (Toolkit.MetaDCE.tree (Toolkit.MetaDCE.bare types functions exports)).inProfileBase = true)
    (sourceValid : ModuleValid (Toolkit.MetaDCE.bare types functions exports))
    (targetValid : ModuleValid (Toolkit.MetaDCE.bare types functions
      (exports.filter fun e => keep e.name)))
    (supported : ∀ fn ∈ functions, func? Recipe.identity fn = some fn)
    {query : String} {args : List Val} (retained : keep query = true) :
    (moduleEntryPoints P (closedHost (H := H)) closedEnv).beh
        (Toolkit.MetaDCE.bare types functions (exports.filter fun e => keep e.name)) query args ⊆
      (moduleEntryPoints P (closedHost (H := H)) closedEnv).beh
        (Toolkit.MetaDCE.bare types functions exports) query args := by
  rintro behavior ⟨s, imports, targetStore, targetInstance, address,
    ⟨rfl, rfl⟩, targetReady, exported, observed⟩
  obtain ⟨sourceStore, sourceInstance, sourceReady, storeValid, related, filtered, _⟩ :=
    bare_exports_ready_restore (StoreRelation.Related.refl {}) MergeChain.storeOk_empty
      types functions exports (exports.filter fun e => keep e.name)
      (fun xi => xi.filter fun e => keep e.name)
      (fun E _ allocation => allocExports_filter keep E allocation)
      profile sourceValid targetValid supported targetReady
  have queryEq : exportFunc? targetInstance query = exportFunc? sourceInstance query := by
    rw [filtered]
    exact exportFunc_filter keep sourceInstance retained
  have observations : behaviours P closedHost targetStore address args =
      behaviours P closedHost sourceStore address args :=
    MergeUntyped.related_behaviours_profile related (MergeUntyped.storeSc_of_ok storeValid) address args
  rw [observations] at observed
  exact ⟨{}, [], sourceStore, sourceInstance, address, ⟨rfl, rfl⟩, sourceReady,
    queryEq.symm.trans exported, observed⟩

/-- Binaryen-style skip policy is an explicit public-interface projection.
Renamed aliases remain available during linking; only visible public queries
are compared with the original pre-filter linked program. -/
theorem publicModule_beh_refines {policy : Policy} {aliases : List Alias} {linked : Module}
    (facts : ClosedFacts [] "" linked)
    (publicValid : ModuleValid (publicModule policy aliases linked))
    {query : String} {args : List Val} (retained : visible policy aliases query = true) :
    (moduleEntryPoints P (closedHost (H := H)) closedEnv).beh
        (publicModule policy aliases linked) query args ⊆
      (moduleEntryPoints P (closedHost (H := H)) closedEnv).beh linked query args := by
  have sourceValid := facts.valid
  have profile := facts.profile
  rw [facts.bare] at sourceValid profile publicValid ⊢
  exact bare_filter_beh_refines (visible policy aliases) linked.types linked.funcs linked.exports
    profile sourceValid publicValid facts.identity retained

/-- Actual checked alias linking followed by public-interface filtering refines
the original program under the explicit namespace-qualified query map. -/
theorem checkedMerge_public_refines_original {policy : Policy} {aliases : List Alias}
    {program : List (String × Module)} {linked : Module}
    (facts : ∀ p ∈ program, ClosedFacts aliases p.1 p.2)
    (merged : checkedMerge? (rewriteProgram aliases program) = some linked)
    (outputFacts : ClosedFacts [] "" linked)
    (publicValid : ModuleValid (publicModule policy aliases linked))
    (P : Profile) {namespaceName query : String} {args : List Val}
    (declared : ∃ m, (namespaceName, m) ∈ program ∧ query ∈ m.exports.map Export.name)
    (retained : visible policy aliases (lookup aliases namespaceName query) = true) :
    (moduleEntryPoints P (closedHost (H := H)) closedEnv).beh
        (publicModule policy aliases linked) (lookup aliases namespaceName query) args ⊆
      Program.beh P (closedHost (H := H)) program namespaceName query args :=
  (publicModule_beh_refines outputFacts publicValid retained).trans
    (checkedMerge_names_refines_original facts merged P declared)

end Silmaril.Wasm.Binaryen.MergeExportNames
