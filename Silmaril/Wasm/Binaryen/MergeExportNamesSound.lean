module

public import Silmaril.Wasm.Binaryen.MergeExportNames
public import Mathlib.Data.List.Find
public import Silmaril.Wasm.Binaryen.Toolkit.MetaDCEProjection

@[expose] public section

namespace Silmaril.Wasm.Binaryen.MergeExportNames

open Execution.Core Validation Numerics RUMESim
open Silmaril.Wasm.SingleThreaded.Det

variable {H : Type} {P : Profile}

/-- Export queries follow the explicit name map; runtime function addresses are
related by the existing function-store simulation, rather than presumed equal. -/
structure ExportsAlong (allowed : String → Prop) (rename : String → String) (X : SimCtx) : Prop where
  fwd : ∀ x, allowed x → ∀ a, exportFunc? X.MA x = some a →
    ∃ b, exportFunc? X.MB (rename x) = some b ∧ X.F a b
  bwd : ∀ x, allowed x → ∀ b, exportFunc? X.MB (rename x) = some b →
    ∃ a, exportFunc? X.MA x = some a

/-- Renaming queries preserves complete persistent sessions, including stopping,
traps and divergence, at the same arbitrary numerical profile. -/
theorem session_rename {allowed : String → Prop} {rename : String → String} {X : SimCtx} (context : X.WF)
    (exports : ExportsAlong allowed rename X) {s t : Store H} (stores : StoreRel X s t)
    {script : List Call} {observations : List (Behaviour Val)}
    (on : ScriptOn allowed script)
    (session : Session P closedHost X.MA s script observations) :
    Session P closedHost X.MB t (script.map fun call => (rename call.1, call.2)) observations := by
  induction session generalizing t with
  | nil => exact .nil
  | @stop s x vs rest unavailable =>
    refine .stop fun b exported valid => ?_
    have permitted := on (x, vs) (by simp)
    obtain ⟨a, sourceExport⟩ := exports.bwd _ permitted _ exported
    obtain ⟨b', targetExport, related⟩ := exports.fwd _ (on (x, vs) (by simp)) _ sourceExport
    rw [exported] at targetExport
    cases targetExport
    exact unavailable a sourceExport (invokeOk_bwd stores related valid)
  | @done s x vs rest a c r bs sourceExport valid run result tail ih =>
    obtain ⟨b, targetExport, related⟩ := exports.fwd _ (on (x, vs) (by simp)) _ sourceExport
    obtain ⟨targetValid, values⟩ := invokeOk_fwd stores related valid
    obtain ⟨targetFinal, targetRun, finalRelated⟩ :=
      sim_steps context run (invoke_rel stores related values)
    exact .done targetExport targetValid targetRun (finalRelated.result result)
      (ih finalRelated.1 (fun call member => on call (by simp [member])))
  | @diverge s x vs rest a sourceExport valid diverges =>
    obtain ⟨b, targetExport, related⟩ := exports.fwd _ (on (x, vs) (by simp)) _ sourceExport
    obtain ⟨targetValid, values⟩ := invokeOk_fwd stores related valid
    exact .diverge targetExport targetValid
      (sim_diverges context diverges (invoke_rel stores related values))

/-- The inverse query transport uses the declared source-name domain, avoiding
any false claim that the lookup map is injective on all strings. -/
structure ExportsBackAlong (allowed : String → Prop) (rename : String → String)
    (X : SimCtx) : Prop where
  fwd : ∀ x, allowed x → ∀ a, exportFunc? X.MA (rename x) = some a →
    ∃ b, exportFunc? X.MB x = some b ∧ X.F a b
  bwd : ∀ x, allowed x → ∀ b, exportFunc? X.MB x = some b →
    ∃ a, exportFunc? X.MA (rename x) = some a

theorem session_unrename {allowed : String → Prop} {rename : String → String}
    {X : SimCtx} (context : X.WF) (exports : ExportsBackAlong allowed rename X)
    {s t : Store H} (stores : StoreRel X s t) {script : List Call}
    {observations : List (Behaviour Val)} (on : ScriptOn allowed script)
    (session : Session P closedHost X.MA s
      (script.map fun call => (rename call.1, call.2)) observations) :
    Session P closedHost X.MB t script observations := by
  induction script generalizing observations s t with
  | nil => cases session; exact .nil
  | cons call script ih =>
    rcases call with ⟨x, vs⟩
    have permitted := on (x, vs) (by simp)
    have tailOn : ScriptOn allowed script := fun call member => on call (by simp [member])
    cases session with
    | stop unavailable =>
      refine .stop fun b exported valid => ?_
      obtain ⟨a, sourceExport⟩ := exports.bwd _ permitted _ exported
      obtain ⟨b', targetExport, related⟩ := exports.fwd _ permitted _ sourceExport
      rw [exported] at targetExport
      cases targetExport
      exact unavailable a sourceExport (invokeOk_bwd stores related valid)
    | done sourceExport valid run result tail =>
      obtain ⟨b, targetExport, related⟩ := exports.fwd _ permitted _ sourceExport
      obtain ⟨targetValid, values⟩ := invokeOk_fwd stores related valid
      obtain ⟨targetFinal, targetRun, finalRelated⟩ :=
        sim_steps context run (invoke_rel stores related values)
      exact .done targetExport targetValid targetRun (finalRelated.result result)
        (ih finalRelated.1 tailOn tail)
    | diverge sourceExport valid diverges =>
      obtain ⟨b, targetExport, related⟩ := exports.fwd _ permitted _ sourceExport
      obtain ⟨targetValid, values⟩ := invokeOk_fwd stores related valid
      exact .diverge targetExport targetValid
        (sim_diverges context diverges (invoke_rel stores related values))

/-- The actual allocation of a renamed export preserves its external address. -/
theorem allocExport_rename (rename : String → String) (mi : ModuleInst) (e : Export) :
    allocExport? mi {e with name := rename e.name} =
      (allocExport? mi e).map (fun ei => {ei with name := rename ei.name}) := by
  rcases e with ⟨name, index⟩
  cases index <;> simp [allocExport?, Option.map_map, Function.comp_def]

/-- Actual allocated export lists, including order and repeated addresses,
follow the source name map exactly. -/
theorem allocExports_rename (rename : String → String) (mi : ModuleInst) :
    ∀ {es : List Export} {xi : List ExportInst}, es.mapM (allocExport? mi) = some xi →
    (es.map fun e => {e with name := rename e.name}).mapM (allocExport? mi) =
      some (xi.map fun ei => {ei with name := rename ei.name})
  | [], xi, accepted => by
    have empty : xi = [] := by simpa using accepted.symm
    subst xi
    rfl
  | e :: es, xi, accepted => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at accepted
    obtain ⟨ei, head, rest, tail, rfl⟩ := accepted
    simp only [List.map_cons, List.mapM_cons, allocExport_rename, head,
      Option.map_some, allocExports_rename rename mi tail, Option.pure_def]
    rfl

/-- Injectivity is only required on the actual exported-name domain. -/
theorem exportFunc_rename (rename : String → String) (mi : ModuleInst) (query : String)
    (injective : ∀ e ∈ mi.exports, rename e.name = rename query ↔ e.name = query) :
    exportFunc? {mi with exports := mi.exports.map fun e => {e with name := rename e.name}}
      (rename query) = exportFunc? mi query := by
  unfold exportFunc?
  have found :
      (mi.exports.map fun e => {e with name := rename e.name}).find?
          (fun e => e.name == rename query) =
        (mi.exports.find? fun e => e.name == query).map
          (fun e => {e with name := rename e.name}) := by
    rw [List.find?_map]
    congr 1
    apply List.find?_congr
    intro e member
    apply Bool.eq_iff_iff.mpr
    simpa only [Function.comp_apply, beq_iff_eq] using injective e member
  rw [found]
  cases mi.exports.find? (fun e => e.name == query) with
  | none => rfl
  | some e => rcases e with ⟨name, address⟩; cases address <;> rfl

/-- Module observations include initialization and all subsequent renamed
queries; the exact function-store simulation is supplied by actual allocation. -/
theorem obs_rename {allowed : String → Prop} {rename : String → String}
    {s : Store H} {imports : List ExternAddr} {source target : Module} {script : List Call}
    (on : ScriptOn allowed script)
    (allocation : ∀ c, Instantiate P closedHost s source imports c →
      ∃ (X : SimCtx) (d : Config H), X.WF ∧ ExportsAlong allowed rename X ∧
        Instantiate P closedHost s target imports d ∧ ConfRel X .ours c d ∧
        c.frame.module = X.MA ∧ d.frame.module = X.MB) :
    ∀ observations ∈ moduleObs P closedHost s imports source script,
      observations ∈ moduleObs P closedHost s imports target
        (script.map fun call => (rename call.1, call.2)) := by
  rintro observations ⟨c, instantiated, observed⟩
  obtain ⟨X, d, context, exports, targetInstantiation, related, sourceModule, targetModule⟩ :=
    allocation c instantiated
  refine ⟨d, targetInstantiation, ?_⟩
  rcases observed with ⟨c₁, tail, run, result, session, rfl⟩ |
    ⟨c₁, r, run, result, nonempty, rfl⟩ | ⟨diverges, rfl⟩
  · obtain ⟨d₁, targetRun, finalRelated⟩ := sim_steps context run related
    refine .inl ⟨d₁, tail, targetRun, finalRelated.result (r := .values []) result, ?_, rfl⟩
    rw [targetModule]
    rw [sourceModule] at session
    exact session_rename context exports finalRelated.1 on session
  · obtain ⟨d₁, targetRun, finalRelated⟩ := sim_steps context run related
    exact .inr (.inl ⟨d₁, r, targetRun, finalRelated.result result, nonempty, rfl⟩)
  · exact .inr (.inr ⟨sim_diverges context diverges related, rfl⟩)

theorem obs_unrename {allowed : String → Prop} {rename : String → String}
    {s : Store H} {imports : List ExternAddr} {source target : Module} {script : List Call}
    (on : ScriptOn allowed script)
    (allocation : ∀ c, Instantiate P closedHost s source imports c →
      ∃ (X : SimCtx) (d : Config H), X.WF ∧ ExportsBackAlong allowed rename X ∧
        Instantiate P closedHost s target imports d ∧ ConfRel X .ours c d ∧
        c.frame.module = X.MA ∧ d.frame.module = X.MB) :
    ∀ observations ∈ moduleObs P closedHost s imports source
        (script.map fun call => (rename call.1, call.2)),
      observations ∈ moduleObs P closedHost s imports target script := by
  rintro observations ⟨c, instantiated, observed⟩
  obtain ⟨X, d, context, exports, targetInstantiation, related, sourceModule, targetModule⟩ :=
    allocation c instantiated
  refine ⟨d, targetInstantiation, ?_⟩
  rcases observed with ⟨c₁, tail, run, result, session, rfl⟩ |
    ⟨c₁, r, run, result, nonempty, rfl⟩ | ⟨diverges, rfl⟩
  · obtain ⟨d₁, targetRun, finalRelated⟩ := sim_steps context run related
    refine .inl ⟨d₁, tail, targetRun, finalRelated.result (r := .values []) result, ?_, rfl⟩
    rw [targetModule]
    rw [sourceModule] at session
    exact session_unrename context exports finalRelated.1 on session
  · obtain ⟨d₁, targetRun, finalRelated⟩ := sim_steps context run related
    exact .inr (.inl ⟨d₁, r, targetRun, finalRelated.result result, nonempty, rfl⟩)
  · exact .inr (.inr ⟨sim_diverges context diverges related, rfl⟩)

/-- Export-only renaming is the concrete fragment used by import-free alias
preparation. It changes no executable field. -/
def renameExports (rename : String → String) (m : Module) : Module :=
  {m with exports := m.exports.map fun e => {e with name := rename e.name}}

theorem rewrite_closed (aliases : List Alias) (namespaceName : String) {m : Module}
    (closed : m.imports = []) :
    rewrite aliases namespaceName m = renameExports (lookup aliases namespaceName) m := by
  cases m
  simp_all [rewrite, renameExports]

theorem allocExports_names (mi : ModuleInst) :
    ∀ {es : List Export} {xi : List ExportInst}, es.mapM (allocExport? mi) = some xi →
      xi.map ExportInst.name = es.map Export.name
  | [], xi, accepted => by
    have empty : xi = [] := by simpa using accepted.symm
    subst xi
    rfl
  | e :: es, xi, accepted => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at accepted
    obtain ⟨ei, head, rest, tail, rfl⟩ := accepted
    simp only [List.map_cons, Toolkit.MetaDCE.allocExport_name head,
      allocExports_names mi tail]

/-- Actual closed numeric-signature function-module allocation realizes the
query map. Stored functions capture different export tables; the established
RUME store relation, rather than store equality, relates their executions. -/
theorem bare_rename_pair (rename : String → String) (types : List RecType)
    (functions : List Func) (exports : List Export)
    (profile : (Toolkit.MetaDCE.tree (Toolkit.MetaDCE.bare types functions exports)).inProfileBase = true)
    (signatures : numSigs (Toolkit.MetaDCE.tree (Toolkit.MetaDCE.bare types functions exports)) = true)
    (sourceValid : ModuleValid (Toolkit.MetaDCE.bare types functions exports))
    (targetValid : ModuleValid (renameExports rename (Toolkit.MetaDCE.bare types functions exports)))
    (injective : ∀ x ∈ exports.map Export.name, ∀ y ∈ exports.map Export.name,
      rename x = rename y → x = y)
    (s : Store H) (storeValid : StoreOk s) :
    ∃ (c d : Config H) (X Y : SimCtx),
      Instantiate P closedHost s (Toolkit.MetaDCE.bare types functions exports) [] c ∧
      Instantiate P closedHost s (renameExports rename (Toolkit.MetaDCE.bare types functions exports)) [] d ∧
      X.WF ∧ Y.WF ∧ ExportsAlong (· ∈ exports.map Export.name) rename X ∧
      ExportsBackAlong (· ∈ exports.map Export.name) rename Y ∧
      ConfRel X .ours c d ∧ ConfRel Y .ours d c ∧
      c.frame.module = X.MA ∧ d.frame.module = X.MB ∧
      d.frame.module = Y.MA ∧ c.frame.module = Y.MB := by
  let renamedExports := exports.map fun e => {e with name := rename e.name}
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
  let renamedAllocated := allocatedExports.map fun e => {e with name := rename e.name}
  have renamedAllocation :
      (Toolkit.MetaDCE.bare types functions renamedExports).exports.mapM
        (allocExport? (EIrec s (Toolkit.MetaDCE.bare types functions renamedExports) [] [])) =
        some renamedAllocated := allocExports_rename rename _ exportAllocation
  have sourceInst := inst_of_closed (P := P) (host := closedHost)
    (Toolkit.MetaDCE.bare_profiled types functions exports) rfl
    ⟨xtE, [], sourceType, .nil⟩ rfl functionTypes exportAllocation
  have targetInst := inst_of_closed (P := P) (host := closedHost)
    (Toolkit.MetaDCE.bare_profiled types functions renamedExports) rfl
    ⟨xtE', [], targetType, .nil⟩ rfl functionTypes renamedAllocation
  let c : Config H := ⟨Toolkit.MetaDCE.installed s functions tags
    (Toolkit.MetaDCE.instanceOf s types functions allocatedExports),
    {module := Toolkit.MetaDCE.instanceOf s types functions allocatedExports}, []⟩
  let d : Config H := ⟨Toolkit.MetaDCE.installed s functions tags
    (Toolkit.MetaDCE.instanceOf s types functions renamedAllocated),
    {module := Toolkit.MetaDCE.instanceOf s types functions renamedAllocated}, []⟩
  let X := Toolkit.MetaDCE.projectionCtx s types functions allocatedExports renamedAllocated
  let Y := Toolkit.MetaDCE.projectionCtx s types functions renamedAllocated allocatedExports
  have numeric := numParams_types (m := Toolkit.MetaDCE.tree (Toolkit.MetaDCE.bare types functions exports))
    (numSigs_sound signatures)
  have bodies := (BModule.inProfileBase_sound profile).code
  rw [Toolkit.MetaDCE.tree_lower] at bodies
  have stores := Toolkit.MetaDCE.installed_related storeValid functionTypes numeric bodies
    allocatedExports renamedAllocated
  have storesBack := Toolkit.MetaDCE.installed_related storeValid functionTypes numeric bodies
    renamedAllocated allocatedExports
  have names := allocExports_names _ exportAllocation
  change allocatedExports.map ExportInst.name = exports.map Export.name at names
  have queries : ∀ x ∈ exports.map Export.name,
      exportFunc? (Toolkit.MetaDCE.instanceOf s types functions renamedAllocated) (rename x) =
        exportFunc? (Toolkit.MetaDCE.instanceOf s types functions allocatedExports) x := by
    intro x allowed
    apply exportFunc_rename rename (Toolkit.MetaDCE.instanceOf s types functions allocatedExports) x
    intro e member
    have eAllowed : e.name ∈ exports.map Export.name := by
      rw [← names]
      exact List.mem_map.mpr ⟨e, member, rfl⟩
    exact ⟨injective e.name eAllowed x allowed, congrArg rename⟩
  have self : ∀ x a,
      exportFunc? (Toolkit.MetaDCE.instanceOf s types functions allocatedExports) x = some a → X.F a a := by
    intro x a exported
    have related := Toolkit.MetaDCE.allocated_exports_self (F := X.F)
      (fun idx address lookup => ⟨idx.toNat, idx.toNat, rfl, lookup, lookup⟩) exportAllocation
    obtain ⟨b, lookup, relation⟩ := (exportFunc?_rel related x).1 a exported
    change exportFunc? (Toolkit.MetaDCE.instanceOf s types functions allocatedExports) x = some b at lookup
    rw [exported] at lookup
    cases lookup
    exact relation
  have selfBack : ∀ x a,
      exportFunc? (Toolkit.MetaDCE.instanceOf s types functions allocatedExports) x = some a → Y.F a a := by
    intro x a exported
    have related := Toolkit.MetaDCE.allocated_exports_self (F := Y.F)
      (fun idx address lookup => ⟨idx.toNat, idx.toNat, rfl, lookup, lookup⟩) exportAllocation
    obtain ⟨b, lookup, relation⟩ := (exportFunc?_rel related x).1 a exported
    change exportFunc? (Toolkit.MetaDCE.instanceOf s types functions allocatedExports) x = some b at lookup
    rw [exported] at lookup
    cases lookup
    exact relation
  refine ⟨c, d, X, Y, ?_, ?_, Toolkit.MetaDCE.projectionCtx_wf _ _ _ _ _,
    Toolkit.MetaDCE.projectionCtx_wf _ _ _ _ _, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simpa only [Toolkit.MetaDCE.MIrec_bare, Toolkit.MetaDCE.STrec_bare,
      Toolkit.MetaDCE.startCode_bare] using sourceInst
  · change Instantiate P closedHost s (Toolkit.MetaDCE.bare types functions renamedExports) [] d
    simpa only [Toolkit.MetaDCE.MIrec_bare, Toolkit.MetaDCE.STrec_bare,
      Toolkit.MetaDCE.startCode_bare] using targetInst
  · constructor
    · intro x allowed a exported
      exact ⟨a, (queries x allowed).trans exported, self x a exported⟩
    · intro x allowed a exported
      exact ⟨a, (queries x allowed).symm.trans exported⟩
  · constructor
    · intro x allowed a exported
      have original := (queries x allowed).symm.trans exported
      exact ⟨a, original, selfBack x a original⟩
    · intro x allowed a exported
      exact ⟨a, (queries x allowed).trans exported⟩
  · exact ⟨stores, ⟨rfl, rfl, rfl, by simp [localsF, c]⟩, .nil⟩
  · exact ⟨storesBack, ⟨rfl, rfl, rfl, by simp [localsF, d]⟩, .nil⟩

/-- Exact named observations for an actual renamed closed function module.
The name map need only be injective on declared exports; scripts follow that
original interface explicitly. Arbitrary base-profile bodies, traps, divergence
and persistent state within the supported instruction family use the existing
execution simulation. -/
theorem bare_observations_rename (rename : String → String) (types : List RecType)
    (functions : List Func) (exports : List Export)
    (profile : (Toolkit.MetaDCE.tree (Toolkit.MetaDCE.bare types functions exports)).inProfileBase = true)
    (signatures : numSigs (Toolkit.MetaDCE.tree (Toolkit.MetaDCE.bare types functions exports)) = true)
    (sourceValid : ModuleValid (Toolkit.MetaDCE.bare types functions exports))
    (targetValid : ModuleValid (renameExports rename (Toolkit.MetaDCE.bare types functions exports)))
    (injective : ∀ x ∈ exports.map Export.name, ∀ y ∈ exports.map Export.name,
      rename x = rename y → x = y)
    (s : Store H) (imports : List ExternAddr) (storeValid : StoreOk s)
    (script : List Call) (on : ScriptOn (· ∈ exports.map Export.name) script) :
    moduleObs P closedHost s imports (Toolkit.MetaDCE.bare types functions exports) script =
      moduleObs P closedHost s imports
        (renameExports rename (Toolkit.MetaDCE.bare types functions exports))
        (script.map fun call => (rename call.1, call.2)) := by
  obtain ⟨c, d, X, Y, instantiated, renamedInstantiation, context, reverseContext,
    queries, reverseQueries, related, reverseRelated, sourceModule, targetModule,
    reverseSourceModule, reverseTargetModule⟩ :=
    bare_rename_pair rename types functions exports profile signatures sourceValid targetValid
      injective s storeValid
  ext observations
  constructor
  · intro observed
    obtain rfl := Toolkit.MetaDCE.no_imports
      (m := Toolkit.MetaDCE.bare types functions exports) rfl observed.choose_spec.1
    exact obs_rename on (fun c' h => by
      obtain rfl := inst_det h instantiated
      exact ⟨X, d, context, queries, renamedInstantiation, related, sourceModule, targetModule⟩)
      observations observed
  · intro observed
    obtain rfl := Toolkit.MetaDCE.no_imports
      (m := renameExports rename (Toolkit.MetaDCE.bare types functions exports)) rfl observed.choose_spec.1
    exact obs_unrename on (fun d' h => by
      obtain rfl := inst_det h renamedInstantiation
      exact ⟨Y, c, reverseContext, reverseQueries, instantiated, reverseRelated,
        reverseSourceModule, reverseTargetModule⟩) observations observed

end Silmaril.Wasm.Binaryen.MergeExportNames
