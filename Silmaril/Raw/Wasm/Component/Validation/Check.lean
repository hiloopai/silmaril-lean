module

public import Silmaril.Wasm.Component.Reference.Validation.Check.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Check.Defs

public import Silmaril.Raw.Wasm.Component.Validation.Defs
public import Silmaril.Raw.Wasm.Component.Types.Subtype.Check
public import Silmaril.Raw.Wasm.Component.Syntax.Builder

/-!
# Executable component validator and its soundness

The executable half of definition validation: `checkDef?` / `checkDefs?` decide, for every
`Syntax.Definition`, the relational rule `ValidDef` of `Validation/Defs.lean`, and
`check? feat P validCore c : Except ValidationError (ComponentType Nat X)` folds them from the
empty component state and closes the component (`ComponentDone`, `componentTypeOfDefs`),
following wasmparser's `ComponentState` (`validator/component.rs`: `instantiate_core_module`,
`instantiate_component`, `alias_*`, `add_import`, `add_export`, `add_start`, `add_value`), following
`Explainer.md` at component-model `a25fc0b`
(https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/Explainer.md).

## Structure

The checker reuses the executable leaves of the other validation modules, each with its
soundness lemma: `coreTypeDecl?` / `checkDefType?` / `importDecl?` / `resolveDesc?`
(`DefTypes.lean`), `checkLiftLower?`, `checkBuiltin?`, `Ctx.aliasInstanceExport?`, `Scopes.outer?`,
`Entity.sub?` and `openInstanceType?` (wasmparser `SubtypeCx`, `Types/Subtype/Check.lean`). New
here: 🪙 value consumption `consumeValues?`, the export ascription `ascribe?`, the core-instance
import check `coreImportOk?`, and the per-definition checkers `checkCoreModule?`,
`checkCoreInstance?`, `checkInstantiate?`, `checkInstanceExports?`, `checkAlias?`, `checkCanon?`,
`checkStart?`, `checkExport?`, `checkValue?`.

* **Component instantiation.** The relation quantifies over the import substitution `f`; the
  checker infers it with wasmparser's `open_instance_type` (`openInstanceType?`: resources
  matched by name/path) and uses `f = m.apply ct.imported`.
* **Core extern subtyping** is the profile's Boolean `DefProfile.extSub`, lifted to the
  `Except String Unit` interface of `Entity.sub?` by `extSub?`.

## Theorems

* `check?_sound : check? feat P validCore c = .ok ct → ValidComponent feat P validCore c ct`
  (from `checkDef?_sound` / `checkDefs?_sound`, proved by mutual structural recursion).
* Profile instances: `checkLime1?` / `checkV1?` run `check?` with `lime1ModuleType` /
  `v1ModuleType`. **The repository has no decidable checker for Lime1/V1 `ModuleValid`**, so
  these do not validate core module bodies: `checkLime1?_sound` / `checkV1?_sound` take the
  core validity of every (nested) core module as a hypothesis and conclude
  `ValidComponentLime1` / `ValidComponentV1`; without it they conclude the core-type-level
  `ValidComponent` (`checkLime1?_valid`, `checkV1?_valid`). `checkCore3?` runs `check?` with
  the Core 3.0 profile `core3Profile` (closed extern types, `ExternSub.check {}`) and the Core
  3.0 validator `validate?` as core validator (`core3ModuleType?`), so `checkCore3?_sound`
  concludes `ValidComponentCore3` outright: every core module of an accepted component is
  `ModuleValid`.

Completeness is NOT claimed. Known sources of incompleteness: the inferred
instantiation substitution (the relation's `f` is existential; `openInstanceType?` is
incomplete on non-hoisted types, see `Types/Subtype/Check.lean`) and `Entity.sub?`'s fuel.

## Error messages

Messages carry wasmparser substrings where one is known (the `test/validation/*.wast` corpus and
wasm-tools `validator/component.rs`): "missing import named `a`", "missing module instantiation
argument named `m`", "module instantiation argument `m` does not export an item named `n`", "type
mismatch for export `n` of module instantiation argument `m`", "export name `A` conflicts with
previous name `a`" (names compared up to strong uniqueness, first clash in insertion order),
"duplicate module instantiation argument named `m`", "instantiation argument `a` conflicts with
previous argument `a`", "duplicate instantiation export name `f` already defined", "is not a valid
extern name", "cannot alias outer type which transitively refers to resources not defined in the
current component", "invalid outer alias count", "index out of bounds", "not valid to be used as
export", "was not used as part of an instantiation, start function, or export", "ascribed type of
export is not compatible with item's type", "support for component model `value`s is not enabled",
the three `start` mismatch messages of wasmparser's `add_start` (arity, result count, argument
type), and the messages of the reused leaves. Others are descriptive and not verified against
wasmparser. Wasmparser's restriction to one `start` function is not modelled (`Validation/Defs.lean`
follows the Explainer).

## Tests (kernel-checked, `decide +kernel`)

Built inline from `Syntax/Builder.lean`'s transcriptions of the `Explainer.md` examples over
small Lime1 core modules (whose bodies are placeholders: only their import/export types
matter to `lime1ModuleType`; no core `ModuleValid` is claimed for them):
the adder (`adder_check`, with its exact type `DefsTests.adderType` and the relational
corollary `adder_valid_lime1`, plus the V1 adder of `DefsTests`, `adderV1_check`), the linked
parent `$P` (`linkP_check`, exporting `bar`), and the async-callback component (`asyncRun_check`,
under `Features.p3`; rejected under `Features.p2`). Invalid examples with their wasmparser
substrings (`errHas`): instantiating `$B` without its import `a`
(the message shape of resources.wast:673 and attributes.wast:234/243, "missing import named
`a`"), an outer alias of a resource type across a component boundary (outer-alias.wast:39-44,
"transitively refers to resources"), a duplicate export name ("conflicts with previous name"),
a case-only clash of inline instance export names (`a` then `A`), a core instantiation without
its argument ("missing module instantiation argument named"), and the three duplicate-argument
and core-export messages of wasmparser (`duplicate_*_rejected`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Validation

open Silmaril.Wasm.Component.Types
open Silmaril.Wasm.Component.Engine (CoreExternType)

/-! ## Generic helpers -/

section Helpers

variable {X : Type}

/-! ### 🪙 value consumption -/

/-! ### Core extern subtyping of a profile -/

end Helpers

/-! ## Per-definition checkers -/

section Leaves

variable {X : Type} {M : Type} {feat : Features} {P : DefProfile X}
  {validCore : M → Option (CoreModuleType X)} {sc : Scopes X}

end Leaves

/-! ## The checker -/

section Checker

variable {X : Type} {M : Type}

variable {feat : Features} {P : DefProfile X} {validCore : M → Option (CoreModuleType X)}

end Checker

/-! ## Profile instances -/

theorem checkLime1?_valid {feat : Features} {c : Syntax.Component Lime1.Module}
    {ct : ComponentType Nat CoreExternType} (h : checkLime1? feat c = .ok ct) :
    ValidComponent feat lime1Profile lime1ModuleType c ct := check?_sound h

/-- Soundness of `checkLime1?`, given core validity of every core module (taken as input:
the repository has no decidable Lime1 `ModuleValid` checker). -/
theorem checkLime1?_sound {feat : Features} {c : Syntax.Component Lime1.Module}
    {ct : ComponentType Nat CoreExternType} (h : checkLime1? feat c = .ok ct)
    (hm : ∀ m ∈ c.coreModules, Lime1.Validation.ModuleValid m) :
    ValidComponentLime1 feat c ct := ⟨check?_sound h, hm⟩

theorem checkV1?_valid {feat : Features} {c : Syntax.Component V1.Module}
    {ct : ComponentType Nat CoreExternType} (h : checkV1? feat c = .ok ct) :
    ValidComponent feat lime1Profile v1ModuleType c ct := check?_sound h

/-- Soundness of `checkV1?`, given core validity of every core module (taken as input). -/
theorem checkV1?_sound {feat : Features} {c : Syntax.Component V1.Module}
    {ct : ComponentType Nat CoreExternType} (h : checkV1? feat c = .ok ct)
    (hm : ∀ m ∈ c.coreModules, V1.Validation.ModuleValid m) :
    ValidComponentV1 feat c ct := ⟨check?_sound h, hm⟩

-- FLAG(statement-change): `Core3Extern` is now the closed extern type
-- `{τ : CExternType // ExternTypeOk {} τ}` and `ValidComponentCore3` types core modules with
-- `validate?` (conjoining `ModuleValid`) instead of the structural module types.
/-! ## Tests -/

namespace CheckTests

open Syntax.BuilderExamples

/-! ### The adder -/

theorem isAdderType_eq {r : Except ValidationError (ComponentType Nat CoreExternType)}
    (h : isAdderType r = true) : r = .ok DefsTests.adderType := by
  unfold isAdderType at h
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · cases h

/-- The Explainer adder (`Explainer.md` §Canonical ABI) over the Lime1 core module `adderCore`
checks with exactly the type `DefsTests.adderType` (`add : func(a: u32, b: u32) -> u32`). -/
theorem adder_check : checkLime1? Features.p2 adderLime1 = .ok DefsTests.adderType :=
  isAdderType_eq (by decide +kernel)

/-- The relational corollary of `adder_check`. -/
theorem adder_valid_lime1 :
    ValidComponent Features.p2 lime1Profile lime1ModuleType adderLime1 DefsTests.adderType :=
  checkLime1?_valid adder_check

/-- The V1 adder of `DefsTests` (over `CoreModules.addModule`) checks too. -/
theorem adderV1_check : exportNames (checkV1? Features.p2 DefsTests.adder) = some ["add"] := by
  decide +kernel

/-! ### The linked parent `$P` -/

/-- The parent `$P` of the linking example (`Explainer.md` §Instance Definitions, `Linking.md`): it
instantiates `$A`, feeds the instance to `$B` and re-exports `bar`. -/
theorem linkP_check :
    exportNames (checkLime1? Features.p2 (linkP linkACore linkBCore)) = some ["bar"] := by
  decide +kernel

/-! ### The async-callback component -/

/-- The async-callback component of `Explainer.md` §Canonical ABI checks under `Features.p3`. -/
theorem asyncRun_check :
    exportNames (checkLime1? Features.p3 (asyncRun asyncCore)) = some ["run"] := by
  decide +kernel

/-- ... and is rejected without the 🔀 async feature. -/
theorem asyncRun_p2_rejected : okB (checkLime1? Features.p2 (asyncRun asyncCore)) = false := by
  decide +kernel

/-! ### Invalid components -/

/-- Instantiating `$B` without an argument for its import `a` (the message shape of
resources.wast:673 and attributes.wast:234/243). -/
theorem missing_import_rejected :
    errHas "missing import named `a`"
      (checkLime1? Features.p2 [.component (linkB linkBCore), Syntax.instantiate 0]) = true := by
  decide +kernel

/-- outer-alias.wast:39-44: an outer alias of a resource type across a component
boundary. -/
theorem outer_alias_resource_rejected :
    errHas "transitively refers to resources"
      (checkLime1? Features.p2
        [Syntax.resourceT, .component [Syntax.aliasOuter 1 0 .type]]) = true := by
  decide +kernel

/-- A second export named `add` (wasmparser "export name `add` conflicts with previous name
`add`"). -/
theorem duplicate_export_rejected :
    errHas "conflicts with previous name"
      (checkLime1? Features.p2 (adderLime1 ++ [Syntax.exportFunc "add" 0])) = true := by
  decide +kernel

/-- A core instantiation of the async core module without the argument `""` that provides
`task.return` (wasmparser "missing module instantiation argument named ``"). -/
theorem missing_core_argument_rejected :
    errHas "missing module instantiation argument named"
      (checkLime1? Features.p3 [.coreModule asyncCore, Syntax.coreInst 0]) = true := by
  decide +kernel

open Syntax.SortIdx in
/-- Inline instance export names clashing only up to case (strong uniqueness). -/
theorem case_clash_export_rejected :
    errHas "export name `A` conflicts with previous name `a`"
      (checkLime1? Features.p2 (adderLime1 ++
        [Syntax.synthInstance [("a", func 0), ("A", func 0)]])) = true := by
  decide +kernel

open Syntax.SortIdx in
/-- A duplicate core `instantiate` argument (validation/instantiation.wast:507). -/
theorem duplicate_core_argument_rejected :
    errHas "duplicate module instantiation argument named ``"
      (checkLime1? Features.p3 [.coreModule asyncCore, Syntax.coreInst 0 [("", 0), ("", 0)]])
      = true := by
  decide +kernel

open Syntax.SortIdx in
/-- A duplicate component `instantiate` argument. -/
theorem duplicate_argument_rejected :
    errHas "instantiation argument `a` conflicts with previous argument `a`"
      (checkLime1? Features.p2 [.component (linkB linkBCore),
        Syntax.instantiate 0 [("a", instance_ 0), ("a", instance_ 0)]]) = true := by
  decide +kernel

open Syntax.SortIdx in
/-- A duplicate core inline export; the first repeat in insertion order (`x`) is reported. -/
theorem duplicate_core_export_rejected :
    errHas "duplicate instantiation export name `x` already defined"
      (checkLime1? Features.p2 [Syntax.synthCoreInstance
        [("x", coreFunc 0), ("y", coreFunc 0), ("x", coreFunc 0),
          ("y", coreFunc 0)]]) = true := by
  decide +kernel

end CheckTests

end Silmaril.Wasm.Component.Validation
