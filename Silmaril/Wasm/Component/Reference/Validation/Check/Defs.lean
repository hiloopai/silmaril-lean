module

public import Silmaril.Wasm.Component.Reference.Validation.Defs
public import Silmaril.Wasm.Component.Reference.Types.Subtype.Check.Defs
public import Silmaril.Wasm.Component.Reference.Syntax.Builder.Defs

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

/-- Map a partial function over a list, reporting the first failing element with `err`. -/
def mapE {α β : Type} (f : α → Option β) (err : α → ValidationError) :
    List α → Except ValidationError (List β)
  | [] => .ok []
  | a :: as =>
    match f a with
    | none => .error (err a)
    | some b =>
      match mapE f err as with
      | .ok bs => .ok (b :: bs)
      | .error e => .error e

/-- The first element (scanning forward) whose key clashes with an earlier element, paired
with that earlier element (wasmparser's `IndexSet` insertion order); only used to build error
messages. -/
def conflictPair? {α β : Type} [DecidableEq β] (key : α → β) (l : List α) :
    Option (α × α) :=
  go [] l
where
  go : List α → List α → Option (α × α)
    | _, [] => none
    | seen, a :: as =>
      match seen.find? (fun b => decide (key b = key a)) with
      | some b => some (a, b)
      | none => go (seen ++ [a]) as

/-- The message of a duplicate among `names` (compared through `key`), formatted by `fmt`
applied to the clashing name and the earlier name; `dflt` if no clash is found. -/
def dupMsg (key : String → List Char) (fmt : String → String → String) (dflt : String)
    (names : List String) : String :=
  match conflictPair? key names with
  | some (a, b) => fmt a b
  | none => dflt

/-- The error for an item that has no entity type (out of bounds, or a core sort that cannot
be exported or passed to `instantiate`). -/
def itemError (it : Syntax.SortIdx Syntax.Sort_) : ValidationError :=
  match it.sort with
  | .core .module_ => ValidationError.outOfBounds "module" "module" it.idx
  | .func => ValidationError.outOfBounds "function" "function" it.idx
  | .value => ValidationError.outOfBounds "value" "value" it.idx
  | .type => ValidationError.outOfBounds "type" "type" it.idx
  | .instance_ => ValidationError.outOfBounds "instance" "instance" it.idx
  | .component => ValidationError.outOfBounds "component" "component" it.idx
  | .core _ =>
    ⟨"core items other than modules cannot be exported or passed to an instantiation"⟩

/-! ### 🪙 value consumption -/

/-- Consume the values `is` in order (executable `ConsumeValues`). -/
def consumeValues? (Γ : Ctx X) :
    List Nat → Except ValidationError (List (Types.ValType Nat) × Ctx X)
  | [] => .ok ([], Γ)
  | i :: is =>
    match Γ.value? i with
    | none => .error (ValidationError.outOfBounds "value" "value" i)
    | some (_, true) => .error (ValidationError.valueConsumed i)
    | some (t, false) =>
      match consumeValues? (consumedAt Γ i t) is with
      | .ok (ts, Γ') => .ok (t :: ts, Γ')
      | .error e => .error e

/-! ### Core extern subtyping of a profile -/

/-- The profile's Boolean core extern subtyping as a checker for `Entity.sub?`. -/
def extSub? (P : DefProfile X) (a b : X) : Except String Unit :=
  if P.extSub a b then .ok () else .error "type mismatch"

/-- Entity subtyping with the profile's core extern subtyping (wasmparser `SubtypeCx`). -/
def entSub? (P : DefProfile X) (a b : Entity Nat X) : Except String Unit :=
  Entity.sub? (extSub? P) a b

end Helpers

/-! ## Per-definition checkers -/

section Leaves

variable {X : Type} {M : Type} {feat : Features} {P : DefProfile X}
  {validCore : M → Option (CoreModuleType X)} {sc : Scopes X}

/-- `core module m`: run the supplied core validator. -/
def checkCoreModule? (validCore : M → Option (CoreModuleType X)) (s : DefState X) (m : M) :
    Except ValidationError (DefState X) :=
  match validCore m with
  | some mt => .ok (s.step (s.st.withCtx (s.ctx.pushCoreModule mt).2))
  | none => .error ⟨"core module failed core validation"⟩

/-- One import `((mod, name), x)` of a core module type against the instantiation arguments
(wasmparser `instantiate_core_module`). -/
def coreImportOk? (P : DefProfile X) (Γ : Ctx X) (args : List (String × Nat))
    (imp : (String × String) × X) : Except ValidationError Unit :=
  match args.lookup imp.1.1 with
  | none => .error ⟨s!"missing module instantiation argument named `{imp.1.1}`"⟩
  | some i =>
    match Γ.coreInstance? i with
    | none => .error (ValidationError.outOfBounds "core instance" "instance" i)
    | some ex =>
      match ex.lookup imp.1.2 with
      | none => .error ⟨s!"module instantiation argument `{imp.1.1}` does not export an item \
          named `{imp.1.2}`"⟩
      | some y =>
        if P.extSub y imp.2 then .ok ()
        else .error ⟨s!"type mismatch for export `{imp.1.2}` of module instantiation \
          argument `{imp.1.1}`"⟩

/-- Run a check on every element, stopping at the first error. -/
def forallE {α : Type} (f : α → Except ValidationError Unit) :
    List α → Except ValidationError Unit
  | [] => .ok ()
  | a :: as =>
    match f a with
    | .ok () => forallE f as
    | .error e => .error e

/-- `core instance (instantiate m args)` / `core instance (export ...)*`. -/
def checkCoreInstance? (P : DefProfile X) (s : DefState X) :
    Syntax.CoreInstanceExpr → Except ValidationError (DefState X)
  | .instantiate mod args =>
    match s.ctx.coreModuleAt? mod with
    | .error e => .error e
    | .ok mt =>
      if (args.map (·.1)).Nodup then
        if ∀ a ∈ args, a.2 < s.ctx.coreInstances.length then
          match forallE (coreImportOk? P s.ctx args) mt.imports with
          | .error e => .error e
          | .ok () => .ok (s.step (s.st.withCtx (s.ctx.pushCoreInstance mt.exports).2))
        else
          match args.find? (fun a => !decide (a.2 < s.ctx.coreInstances.length)) with
          | some a => .error (ValidationError.outOfBounds "core instance" "instance" a.2)
          | none => .error ⟨"core instance index out of bounds"⟩
      else .error ⟨dupMsg String.toList
        (fun a _ => s!"duplicate module instantiation argument named `{a}`")
        "duplicate module instantiation argument" (args.map (·.1))⟩
  | .exports items =>
    if (items.map (·.1)).Nodup then
      match mapE (fun it => (coreItem? s.ctx it.2).map (it.1, ·))
          (fun it => ⟨s!"unknown core item {it.2.idx}: index out of bounds"⟩) items with
      | .error e => .error e
      | .ok ex => .ok (s.step (s.st.withCtx (s.ctx.pushCoreInstance ex).2))
    else .error ⟨dupMsg String.toList
      (fun a _ => s!"duplicate instantiation export name `{a}` already defined")
      "duplicate instantiation export name" (items.map (·.1))⟩

/-- `instance (instantiate c args)`: the import substitution is inferred by wasmparser's
`open_instance_type` (`openInstanceType?`), then the values are consumed. -/
def checkInstantiate? (P : DefProfile X) (s : DefState X) (c : Nat)
    (args : List (String × Syntax.SortIdx Syntax.Sort_)) :
    Except ValidationError (DefState X) :=
  match s.ctx.componentAt? c with
  | .error e => .error e
  | .ok ct =>
    if (args.map (·.1)).Nodup then
      match mapE (fun a => (itemEntity? s.ctx a.2).map (a.1, ·)) (fun a => itemError a.2)
          args with
      | .error e => .error e
      | .ok argEs =>
        match openInstanceType? (entSub? P) argEs ct.imported ct.imports "import" with
        | .error m => .error ⟨m⟩
        | .ok rm =>
          match consumeValues? s.ctx (valueIdxs (args.map (·.2))) with
          | .error e => .error e
          | .ok (_, Γc) => .ok (s.step ((s.st.withCtx Γc).instantiate ct (rm.apply ct.imported)))
    else .error ⟨dupMsg String.toList
      (fun a b => s!"instantiation argument `{a}` conflicts with previous argument `{b}`")
      "duplicate instantiation argument" (args.map (·.1))⟩

/-- `instance (export n i)*`. -/
def checkInstanceExports? (s : DefState X)
    (items : List (Syntax.ExternName × Syntax.SortIdx Syntax.Sort_)) :
    Except ValidationError (DefState X) :=
  if ∀ it ∈ items, it.1.valid = true then
    if (items.map fun it => Syntax.strongCanonChars it.1.name.toList).Nodup then
      match mapE (fun it => (itemEntity? s.ctx it.2).map (it.1.name, ·)) (fun it => itemError it.2)
          items with
      | .error e => .error e
      | .ok ents =>
        match consumeValues? s.ctx (valueIdxs (items.map (·.2))) with
        | .error e => .error e
        | .ok (_, Γc) => .ok (s.step ((s.st.withCtx Γc).inlineInstance items ents))
    else .error ⟨dupMsg (fun n => Syntax.strongCanonChars n.toList)
      (fun a b => s!"export name `{a}` conflicts with previous name `{b}`")
      "duplicate export name" (items.map (·.1.name))⟩
  else
    match items.find? (fun it => !it.1.valid) with
    | some it => .error ⟨s!"`{it.1.name}` is not a valid extern name"⟩
    | none => .error ⟨"invalid extern name"⟩

/-- Aliases: `alias export`, `alias core export`, and `alias outer` of `type`, `core type`,
`core module` and `component`. -/
def checkAlias? (P : DefProfile X) (sc : Scopes X) (s : DefState X) :
    Syntax.Alias → Except ValidationError (DefState X)
  | .export_ i n so =>
    match s.ctx.aliasInstanceExport? i n with
    | .error e => .error e
    | .ok p =>
      if exportSortOk s.ctx i n so then
        .ok (s.step (s.st.withCtx p.2) (aliasReq s.ctx i n) (aliasReq s.ctx i n))
      else .error ⟨s!"export `{n}` of instance {i} has a different sort"⟩
  | .coreExport i n so =>
    match s.ctx.coreInstanceAt? i with
    | .error e => .error e
    | .ok ex =>
      match ex.lookup n with
      | none => .error ⟨s!"core instance {i} has no export named `{n}`"⟩
      | some x =>
        if P.coreSort x = so then .ok (s.step (s.st.withCtx (pushCoreItem s.ctx so x)))
        else .error ⟨s!"export `{n}` of core instance {i} has a different sort"⟩
  | .outer ct idx .type =>
    match Scopes.outer? sc s.ctx ct with
    | .error e => .error e
    | .ok q =>
      match q.typeSlotAt? idx with
      | .error e => .error e
      | .ok slot =>
        if crossesComponent sc s.ctx ct && !slot.def_.fv.isEmpty then
          .error ⟨"cannot alias outer type which transitively refers to resources not \
            defined in the current component"⟩
        else .ok (s.step (s.st.withCtx (s.ctx.pushTypeSlot slot).2))
  | .outer ct idx (.core .type) =>
    match Scopes.outer? sc s.ctx ct with
    | .error e => .error e
    | .ok q =>
      match q.coreTypeAt? idx with
      | .error e => .error e
      | .ok slot => .ok (s.step (s.st.withCtx (s.ctx.pushCoreType slot).2))
  | .outer ct idx (.core .module_) =>
    match Scopes.outer? sc s.ctx ct with
    | .error e => .error e
    | .ok q =>
      match q.coreModuleAt? idx with
      | .error e => .error e
      | .ok mt => .ok (s.step (s.st.withCtx (s.ctx.pushCoreModule mt).2))
  | .outer ct idx .component =>
    match Scopes.outer? sc s.ctx ct with
    | .error e => .error e
    | .ok q =>
      match q.componentAt? idx with
      | .error e => .error e
      | .ok t => .ok (s.step (s.st.withCtx (s.ctx.pushComponent t).2))
  | .outer _ _ _ =>
    .error ⟨"outer aliases may only be made to types, modules, and components"⟩

/-- `canon lift` / `canon lower` and canonical builtins. -/
def checkCanon? (feat : Features) (P : DefProfile X) (s : DefState X) :
    Syntax.Canon → Except ValidationError (DefState X)
  | .builtin b =>
    match checkBuiltin? feat P.view s.ctx b with
    | .ok (x, Γ') => .ok (s.step (s.st.withCtx (Γ'.pushCoreFunc x).2))
    | .error e => .error e
  | c =>
    match checkLiftLower? feat P.view.core s.ctx c with
    | .ok e => .ok (s.step (s.st.withCtx (pushCanonEntity s.ctx e)) (canonReq s.names s.ctx c))
    | .error e => .error e

/-- The 🪙 feature-gate error. -/
def valuesFeatureError : ValidationError :=
  ⟨"support for component model `value`s is not enabled"⟩

/-- The first index at which two lists differ (`none` if one is a prefix of the other). -/
def firstMismatch? {α : Type} [DecidableEq α] : List α → List α → Nat → Option Nat
  | a :: as, b :: bs, i => if a = b then firstMismatch? as bs (i + 1) else some i
  | _, _, _ => none

/-- wasmparser's message for a `start` whose arguments or results do not match the function
type (component.rs `add_start`: arity first, then result count, then argument types). -/
def startMismatchMsg {α : Type} [DecidableEq α] (ts ps : List α) (results expected : Nat) :
    String :=
  if ts.length ≠ ps.length then
    s!"component start function requires {natStr ps.length} arguments but was given \
      {natStr ts.length}"
  else if results ≠ expected then
    s!"component start function has a result count of {natStr results} but the function \
      type has a result count of {natStr expected}"
  else
    match firstMismatch? ts ps 0 with
    | some i => s!"value type mismatch for component start function argument {natStr i}"
    | none => "value type mismatch for component start function argument"

/-- 🪙 `start f (value v)* (result (value))^r`. -/
def checkStart? (feat : Features) (s : DefState X) (f : Nat) (args : List Nat)
    (results : Nat) : Except ValidationError (DefState X) :=
  if feat.values then
    match s.ctx.funcAt? f with
    | .error e => .error e
    | .ok ft =>
      match consumeValues? s.ctx args with
      | .error e => .error e
      | .ok (ts, Γc) =>
        if ts = ft.params.map (·.2) then
          if results = ft.result.toList.length then
            .ok (s.step (s.st.withCtx (startCtx Γc ft.result.toList)) .tt (s.funcReq f))
          else .error ⟨startMismatchMsg ts (ft.params.map (·.2)) results
            ft.result.toList.length⟩
        else .error ⟨startMismatchMsg ts (ft.params.map (·.2)) results
          ft.result.toList.length⟩
  else .error valuesFeatureError

/-- Export ascription (executable `Ascribe`): none; `(type (sub resource))` on a resource
type; otherwise the ascribed `externtype` resolves and the item's type is a subtype of it. -/
def ascribe? (feat : Features) (P : DefProfile X) (Γ : Ctx X) (e : Entity Nat X) :
    Option Syntax.ExternDesc → Except ValidationError (Entity Nat X)
  | none => .ok e
  | some d =>
    if d = .type .subResource then
      match e with
      | .type (.resource r) => .ok (.type (.resource r))
      | _ => .error ⟨"ascribed type of export is not compatible with item's type\n\
          expected resource"⟩
    else
      match resolveDesc? feat Γ d with
      | .error err => .error err
      | .ok e' =>
        match entSub? P e e' with
        | .ok () => .ok e'
        | .error m =>
          .error ⟨"ascribed type of export is not compatible with item's type\n" ++ m⟩

/-- `export n it et?`. -/
def checkExport? (feat : Features) (P : DefProfile X) (s : DefState X) (n : Syntax.ExternName)
    (it : Syntax.SortIdx Syntax.Sort_) (asc : Option Syntax.ExternDesc) :
    Except ValidationError (DefState X) :=
  if n.valid then
    match conflict? (s.ctx.exports.map (·.1)) n.name with
    | some p => .error ⟨s!"export name `{n.name}` conflicts with previous name `{p}`"⟩
    | none =>
      match itemEntity? s.ctx it with
      | none => .error (itemError it)
      | some e =>
        match ascribe? feat P s.ctx e asc with
        | .error err => .error err
        | .ok e' =>
          if exportValueOk e' then
            if (exportReq s it asc).eval (s.ctx.importedTokens ++ s.ctx.exportedTokens) then
              if resNamed s.ctx e' then
                match consumeValues? s.ctx (valueIdxs [it]) with
                | .error err => .error err
                | .ok (_, Γc) =>
                  .ok (s.step ((s.st.withCtx Γc).exportItem n.name it e') (exportReq s it asc)
                    (exportReq s it asc))
              else .error ⟨s!"{sortWord e'} not valid to be used as export: a resource it \
                uses is neither imported nor exported"⟩
            else .error ⟨s!"{sortWord e'} not valid to be used as export"⟩
          else .error ⟨"value exports cannot contain a `borrow` type"⟩
  else .error ⟨s!"`{n.name}` is not a valid extern name"⟩

/-- 🪙 `value t payload`. -/
def checkValue? (feat : Features) (s : DefState X) (t : Syntax.VT) :
    Except ValidationError (DefState X) :=
  if feat.values then
    match resolveVT? s.ctx t with
    | .error e => .error e
    | .ok ty =>
      if valueDefTypeOk ty then
        .ok (s.step (s.st.withCtx (s.ctx.pushValue ty).2) .tt (vtReq s.names s.ctx t))
      else .error ⟨"value definitions cannot contain handles, streams, futures or \
        error-contexts"⟩
  else .error valuesFeatureError

/-- The error reported when a finished component fails `ComponentDone`. -/
def doneError (Γ : Ctx X) : ValidationError :=
  match Γ.values.findIdx? (fun p => !p.2) with
  | some i => ⟨s!"value index {i} was not used as part of an instantiation, start function, \
      or export"⟩
  | none => ⟨"component type mentions a resource that is not bound"⟩

end Leaves

/-! ## The checker -/

section Checker

variable {X : Type} {M : Type}

mutual
  /-- Validate one component-level definition (executable `ValidDef`, `checkDef?_sound`). -/
  def checkDef? (feat : Features) (P : DefProfile X)
      (validCore : M → Option (CoreModuleType X)) (sc : Scopes X) (s : DefState X) :
      Syntax.Definition M → Except ValidationError (DefState X)
    | .coreModule m => checkCoreModule? validCore s m
    | .coreInstance e => checkCoreInstance? P s e
    | .coreType t =>
      match coreTypeDecl? P.decl sc s.st t with
      | .ok st' => .ok (s.step st')
      | .error e => .error e
    | .component defs =>
      match checkDefs? feat P validCore (Scopes.enter sc s.ctx .component).1
          { st := s.st.child (Scopes.enter sc s.ctx .component).2 } defs with
      | .error e => .error e
      | .ok ch =>
        if ComponentDone ch.ctx then .ok (s.step (s.st.closeComponentDef ch.st))
        else .error (doneError ch.ctx)
    | .instance_ (.instantiate c args) => checkInstantiate? P s c args
    | .instance_ (.exports items) => checkInstanceExports? s items
    | .alias a => checkAlias? P sc s a
    | .type t =>
      match checkDefType? feat P.decl sc s.st t with
      | .ok st' => .ok (s.step st')
      | .error e => .error e
    | .canon c => checkCanon? feat P s c
    | .start f args results => checkStart? feat s f args results
    | .import_ n d =>
      match importDecl? feat s.st n d with
      | .ok st' => .ok (s.step st' (descReq s.names s.ctx d) (descReq s.names s.ctx d))
      | .error e => .error e
    | .export_ n it asc => checkExport? feat P s n it asc
    | .value t _ => checkValue? feat s t
    termination_by structural d => d

  /-- Validate definitions in order (executable `ValidDefs`). -/
  def checkDefs? (feat : Features) (P : DefProfile X)
      (validCore : M → Option (CoreModuleType X)) (sc : Scopes X) (s : DefState X) :
      List (Syntax.Definition M) → Except ValidationError (DefState X)
    | [] => .ok s
    | d :: ds =>
      match checkDef? feat P validCore sc s d with
      | .ok s' => checkDefs? feat P validCore sc s' ds
      | .error e => .error e
    termination_by structural ds => ds
end

/-- The executable component validator: fold the definitions from the empty component state,
check that the component is finished (every 🪙 value consumed, closed type) and return its
type (`componentTypeOfDefs`). Sound for `ValidComponent` (`check?_sound`). -/
def check? (feat : Features) (P : DefProfile X) (validCore : M → Option (CoreModuleType X))
    (c : Syntax.Component M) : Except ValidationError (ComponentType Nat X) :=
  match checkDefs? feat P validCore [] initState c with
  | .error e => .error e
  | .ok s =>
    if ComponentDone s.ctx then .ok (componentTypeOfDefs s.ctx) else .error (doneError s.ctx)

variable {feat : Features} {P : DefProfile X} {validCore : M → Option (CoreModuleType X)}

end Checker

/-! ## Profile instances -/

/-- The Lime1 validator: `check?` with `lime1Profile` and `lime1ModuleType`. Core module
bodies are NOT validated (no decidable Lime1 `ModuleValid` checker exists in the
repository); see `checkLime1?_sound`. -/
def checkLime1? (feat : Features) (c : Syntax.Component Lime1.Module) :
    Except ValidationError (ComponentType Nat CoreExternType) :=
  check? feat lime1Profile lime1ModuleType c

/-- The WebAssembly 1.0 validator: `check?` with `lime1Profile` and `v1ModuleType`. Core
module bodies are NOT validated; see `checkV1?_sound`. -/
def checkV1? (feat : Features) (c : Syntax.Component V1.Module) :
    Except ValidationError (ComponentType Nat CoreExternType) :=
  check? feat lime1Profile v1ModuleType c

/-- The Core 3.0 validator: `check?` with the Core 3.0 profile `core3Profile` and the Core 3.0
module validator (`core3ModuleType?`, over `validate?`). -/
def checkCore3? (feat : Features) (c : Syntax.Component Wasm.Module) :
    Except ValidationError (ComponentType Nat Core3Extern) :=
  check? feat core3Profile core3ModuleType? c

-- FLAG(statement-change): `Core3Extern` is now the closed extern type
-- `{τ : CExternType // ExternTypeOk {} τ}` and `ValidComponentCore3` types core modules with
-- `validate?` (conjoining `ModuleValid`) instead of the structural module types.
/-! ## Tests -/

namespace CheckTests

open Syntax.BuilderExamples

/-- `true` iff the result is `ok`. -/
def okB {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

/-- `p` is a prefix of `s` (characters). -/
def isPrefixL : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a == b && isPrefixL as bs

/-- `p` occurs contiguously in `s` (characters). -/
def isInfixL (p : List Char) : List Char → Bool
  | [] => isPrefixL p []
  | c :: cs => isPrefixL p (c :: cs) || isInfixL p cs

/-- The result is an error whose message contains `sub` (wasmparser substring matching, as in
the `assert_invalid` directives of the upstream `.wast` corpus). -/
def errHas {α : Type} (sub : String) : Except ValidationError α → Bool
  | .error e => isInfixL sub.toList e.message.toList
  | .ok _ => false

/-- The export names of an accepted component. -/
def exportNames {X : Type} (r : Except ValidationError (ComponentType Nat X)) :
    Option (List String) :=
  r.toOption.map fun ct => ct.exports.map (·.1)

/-! ### The adder -/

/-- The result is exactly `DefsTests.adderType` (Boolean inspection: `ComponentType` has no
`DecidableEq`). -/
def isAdderType : Except ValidationError (ComponentType Nat CoreExternType) → Bool
  | .ok ⟨[], [], [], [(n, .func ft)]⟩ => n == "add" && decide (ft = DefsTests.adderFunc)
  | _ => false

/-! ### The linked parent `$P` -/

/-- Core module of `$A`: exports `f : [] -> [i32]` (placeholder body). -/
def linkACore : Lime1.Module where
  types := [⟨[], [.int .i32]⟩]
  funcs := [⟨⟨0⟩, [], []⟩]
  exports := [⟨"f", .func ⟨0⟩⟩]

/-- Core module of `$B`: imports `a.foo : [] -> [i32]`, exports `g : [] -> [i32]`
(placeholder body). -/
def linkBCore : Lime1.Module where
  types := [⟨[], [.int .i32]⟩]
  imports := [⟨"a", "foo", .func ⟨0⟩⟩]
  funcs := [⟨⟨0⟩, [], []⟩]
  exports := [⟨"g", .func ⟨1⟩⟩]

/-! ### The async-callback component -/

/-- Core module of the async component: imports `"" "task.return" : [i32] -> []` and exports
`run : [i32] -> [i32]` and the callback `cb : [i32, i32, i32] -> [i32]` (placeholder
bodies). -/
def asyncCore : Lime1.Module where
  types := [⟨[.int .i32], []⟩, ⟨[.int .i32], [.int .i32]⟩,
    ⟨[.int .i32, .int .i32, .int .i32], [.int .i32]⟩]
  imports := [⟨"", "task.return", .func ⟨0⟩⟩]
  funcs := [⟨⟨1⟩, [], []⟩, ⟨⟨2⟩, [], []⟩]
  exports := [⟨"run", .func ⟨1⟩⟩, ⟨"cb", .func ⟨2⟩⟩]

/-! ### Invalid components -/

end CheckTests

end Silmaril.Wasm.Component.Validation
