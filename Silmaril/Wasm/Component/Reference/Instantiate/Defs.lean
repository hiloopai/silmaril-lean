module

public import Silmaril.Wasm.Component.Reference.Instantiate.Runtime.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Defs
public import Silmaril.Wasm.Component.Reference.Syntax.Builder.Defs
public import Silmaril.Wasm.Component.Reference.Types.Subtype.Check.Defs

/-!
# Instantiation as a specification program

Component instantiation (Explainer.md, "Instance Definitions") as a program of the specification
carrier `Canon.P E σ` (`Canon/Effects.lean`), run by the component machine like every other
REF function. There is no upstream function for the whole: the Python reference
(`design/mvp/canonical-abi/definitions.py` at component-model `a25fc0b`,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>)
only has `Store.lift` (L539-543) and `Store.lower` (L545-548), which are the `canon lift` and
`canon lower` rows below. The per-definition table follows the Explainer's definition forms, and
the order of side effects is definition order, as in wasmtime's inliner
(`crates/environ/src/component/translate/inline.rs` at wasmtime `a7b4f29`, whose
`GlobalInitializer` list, `crates/environ/src/component/info.rs`, keeps instantiations and
resource definitions in definition order).

Per definition (`instantiateDef`):
* `core module m`: push `m`. `core type t`: push the core type slot (static).
* `component c`: push the closure `⟨c, f :: outer⟩`.
* `import n d`: push `args[n]` into `sort(d)`; a missing argument traps
  `hostTrap "missing import"`.
* `core instance (instantiate m args)`: `coreImportsFor?`, `E.prepare?` on the core store
  (failure traps `coreTrap`), then the start function as a synchronous task of `inst`
  (`runStart`), then push the export map.
* `core instance (exports ...)` and `instance (exports ...)`: push the synthetic bag.
* `instance (instantiate c args)`: evaluate the arguments, `recurse` (a fresh instance), push
  the child's exports.
* `alias export` / `alias core export` / `alias outer`: push the aliased entry.
* `type (resource rep dtor)`: allocate a fresh `RtId` with `impl = inst`
  (`allocResourceType`), push it. Other `type`s: resolve (`resolveDefValType?`,
  `resolveFuncType?`) and push (static).
* `canon lift`: `Store.lift`, allocate `CFuncInst.lifted core ft opts inst`, push its `FuncId`.
* `canon lower`: `Store.lower`, `E.allocHost` of `CanonHost.lowered callee ft opts inst`, push
  the address. `canon <builtin>`: `E.allocHost` of `CanonHost.builtin b inst`, push it.
* `export n si`: record `(n, E[si])` and push it again.

**Start functions** (Concurrency.md "Interaction with the start function"): a core start function
returned by `E.prepare?` is registered as a lifted `CFuncInst`
with the implicit type `func()` and empty (default) options in instance `inst`, and called with
`call (.funcInst f caller)` where `caller` is a fresh `Caller.sub .start` record. It therefore
runs as a *synchronous task* of `inst` through `canon_lift`'s synchronous loop (REF L2140-2144,
handled by `canon_lift`, not here): while the task is not resolved, a ready thread of `inst` is
resumed, and the start function traps only if it blocks while *no* thread of `inst` is ready
(`trap_if(not candidates)`; test/async/dont-block-start.wast). It may block while another
thread of `inst` is ready (test/async/during-sync-call-may-block-if-other-ready-threads.wast),
e.g. a thread spawned by the start function of an earlier core instance of `inst`.

**Nested instantiation.** `instance (instantiate c args)` instantiates the closure `c`, which
comes from the frame, not from a syntactic subterm of the current definition list, so the
recursion is not structural. The programs here take the nested instantiation as a parameter
`recurse : Recurse E σ` (instantiate a closure with arguments in a *fresh* component instance
and return its exports). Two ties are provided:
* the specification tie `callRecurse c args := callItems (.instantiate c args)`: a late-bound
  call, which the dispatcher (`Canon.dispatch`) resolves to `instantiateClosure callRecurse c
  args`, so nesting depth is bounded only by the machine's fuel. Core instantiation goes
  through `coreImportsFor?`, so this needs the instance `[∀ a b, Decidable (E.ExternSub a b)]`
  (an instance argument of `Canon.dispatch`; `lime1`, `v1` and `mock` have one, and for a
  `Core3Engine` it is `Core3Engine.decExternSub`, from `externSub_iff` and
  `ExternSub.decideEmpty`);
* `instantiateFuel n`, by recursion on fuel, for store-only tests without a machine
  (exhaustion traps `TrapReason.exhausted`, not a REF trap).

**Import type checking** (Explainer.md, "Instance Definitions" and "Type Checking"): the `import
n d` row checks the supplied value against the descriptor `d` resolved in the current frame
(`importTypeCheck`, wasmparser's `open_instance_type(args, component, Import)` over
`Types.Entity.sub?`), for root and nested instantiation alike; a mismatch traps
`hostTrap "import type mismatch: ..."` (for nested instantiation of a valid component this is
unreachable: validation performs the same check statically; for root instantiation
`instantiateRoot` also runs the check before any side effect as far as it can, see
`Instantiate/Root.lean`). Functions, types and instances of them are checked by type; core
modules and components by sort only (their module and component types are not compared);
🪙 values are not typed at run time (`itemEntity?`, `pruneEntity`), so a 🪙 value or an
unallocated function supplied where a typed entity is expected is rejected
(`untypedImportMsg`). Soundness: `importTypeCheck_sound`, `importTypeCheck_typable`,
`importTypeCheck_sound_typed`. The type check of wasmtime's `Linker` against a validated
component type, including core module types, is `linkCheck` (`Instantiate/Link.lean`).

Design notes:
* `instantiateDef` takes the scope state `Scope E` (the frame *and* the exports recorded so
  far), the enclosing frames `outer` and the argument map `args`, besides `inst`; it returns the
  new `Scope E`. It takes no `Limits` (nothing here depends on them).
* Core type definitions push one slot per member of a recursion group (`coreTypeSlots`), like
  the validation context (`Validation.Ctx.pushCoreRec`), and one per core module type.
* Instance and component *type* definitions are resolved into semantic types over `RtId`
  (`staticType?`, `resolveDefType?` of `Instantiate/Runtime.lean`): binders are reserved
  identities (`binderVar`), instance types in import/export position are freshened and hoisted
  (`freshenInstance`). Declarators outside the supported fragment (`alias export` inside a type,
  🪙 value descriptors) fall back to the empty placeholder types. Core module *type* definitions
  remain the placeholder `.module_ ⟨[], []⟩` (the engine interface has no translation of Core
  3.0 extern types into `E.ExternType`); only the sort of a core module argument is checked
  (`pruneEntity`).
* 🪙 `start` and `value` definitions are NOT modelled: they trap `internal` (no profile enables
  🪙 values, so this is unreachable for components validated under any profile).
* Every resolution failure other than a missing import (unknown index, sort mismatch, a core
  import that does not match, a type index of the wrong kind) is an `internal` trap: validation
  rules it out.

Provided theorems (the generativity requirement):
* `ArenasExtend s₀ s`: every arena of `s₀` is a prefix of the same arena of `s` (hence
  `ArenasExtend.length_le`: arena lengths are monotone); reflexive and transitive.
* `instantiateDef_inv`, `instantiateComponent_inv`, `instantiateClosure_inv`,
  `instantiateFuel_inv`: `P.Inv (ArenasExtend s₀)` for every `s₀`, i.e. every store update the
  instantiation programs issue only appends to arenas (for `recurse`, under the hypothesis that
  it does so too; the `call`-based tie satisfies it trivially since `P.Inv` only constrains
  `modify`).
* `resource_fresh`: under any handler that implements `get`/`modify` as reading/updating the
  store (`StoreHandler`), `allocResourceType` returns an `RtId` that was not allocated before and
  is allocated afterwards with `impl = some inst`; `instantiateDef_resource` shows that the
  `type (resource rep dtor)` row is exactly `allocResourceType` followed by a push.

NOT claimed: instantiation typing, completeness of the import check, agreement with wasmtime's
inliner or with wasmtime's `Linker` (`linkCheck`), termination of
nested instantiation, or anything about the machine's treatment of `call`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Instantiate

open Engine Canon _root_.Silmaril.Wasm.Component.Runtime

variable {E : CoreEngine} {σ : Type}

/-- An export map (and an argument map) of a component instance. -/
abbrev Exports (E : CoreEngine) := List (String × ItemVal E)

/-- Nested instantiation: instantiate a closure with arguments in a fresh component instance
and return its exports (see the module docstring for the ties). -/
abbrev Recurse (E : CoreEngine) (σ : Type) := Closure E → Exports E → P E σ (Exports E)

/-- The state threaded through the definitions of one component: its index spaces and the
exports recorded so far (in definition order). -/
structure Scope (E : CoreEngine) where
  frame : Frame E := Frame.empty
  exports : Exports E := []

/-! ## Named store updates -/

/-- Replace the core store (after core instantiation). -/
def setCoreSt (c : E.Store (CanonHost E)) (s : CStore E) : CStore E := { s with core := c }

/-- Allocate a canon host function of flat type `ty` with host code `h` in the core store. -/
def allocHostSt (ty : V1.FuncType) (h : CanonHost E) (s : CStore E) : CStore E :=
  { s with core := (E.allocHost s.core ty h).1 }

/-- The address types of memories and tables in the core store (`.i32` for unknown
addresses, deviation D-g). -/
def addrTypesOf (s : CStore E) : AddrTypes E where
  mem m := (E.memAddrType? s.core m).getD .i32
  table t := (E.tableAddrType? s.core t).getD .i32

/-! ## Helpers -/

/-- An `Option` that validation guarantees to be `some`. -/
def need {α : Type} (what : String) (o : Option α) : P E σ α :=
  orTrap (.internal ("instantiation: " ++ what)) o

/-- Push an entry onto the index space of sort `s` (a sort mismatch is internal). -/
def pushEntry (f : Frame E) (s : Syntax.Sort_) (e : Entry E) : P E σ (Frame E) :=
  need "index-space sort mismatch" (f.push s e)

/-- The component-level value of an entry (core modules included). -/
def Entry.toItem? : Entry E → Option (ItemVal E)
  | .item v => some v
  | _ => none

/-- The core extern value of a core entry. -/
def Entry.toExtern? : Entry E → Option E.ExternVal
  | .coreFunc a => some (E.ofFunc a)
  | .coreExtern x => some x
  | _ => none

/-- The item value at sort index `si`. -/
def itemAt? (f : Frame E) (si : Syntax.SortIdx Syntax.Sort_) : Option (ItemVal E) :=
  (f.get? si.sort si.idx).bind Entry.toItem?

/-- The core extern value at core sort index `si`. -/
def externAt? (f : Frame E) (si : Syntax.SortIdx Syntax.CoreSort) : Option E.ExternVal :=
  (f.get? (.core si.sort) si.idx).bind Entry.toExtern?

/-- The frame `ct` scopes outward (`0`: the current frame). -/
def outerFrame? (f : Frame E) (outer : List (Frame E)) (ct : Nat) : Option (Frame E) :=
  (f :: outer)[ct]?

/-- Allocate a fresh component instance (REF `ComponentInstance()`: empty tables,
`may_leave`, no backpressure). -/
def allocInst : P E σ InstId := allocObj ArenaField.insts {}

/-- Allocate a fresh resource type `ResourceType{impl = inst, rep, dtor}` (generative: a new
identity per evaluation, `type (resource ...)`). -/
def allocResourceType (inst : InstId) (rep : AddrType) (dtor : Option E.FuncAddr) :
    P E σ RtId :=
  allocObj ArenaField.resourceTypes { impl := some inst, rep, dtor }

/-- The destructor of a resource type definition: core function index `dtor`. -/
def resolveDtor (f : Frame E) : Option Nat → P E σ (Option E.FuncAddr)
  | none => pure none
  | some i => some <$> need "destructor index" (f.coreFunc? i)

/-- Allocate a component function value (REF `Store.lift`, L539-543). -/
def allocFunc (fi : CFuncInst E) : P E σ FuncId := allocObj ArenaField.funcs fi

/-- Allocate a canon host function in the core store and return its address (REF
`Store.lower`, L545-548, for `lowered`; the canon built-ins likewise). Its flat core type is
`CanonHost.coreType` at the current memory/table address types. -/
def allocCoreHost (h : CanonHost E) : P E σ E.FuncAddr := do
  let s ← getStore
  let ty := h.coreType (addrTypesOf s)
  modifyStore (allocHostSt ty h)
  return (E.allocHost s.core ty h).2

/-- The implicit component-level type `func()` of start functions. -/
def startType : WIT.FuncType Empty RtId := ⟨[], none, false⟩

/-- Run a core start function as a synchronous task of `inst` (Concurrency.md "Interaction
with the start function"): register it as a lifted function of type `func()` with default
options, and call it with a fresh `Caller.sub .start` record. -/
def runStart (inst : InstId) (sf : E.FuncAddr) : P E σ Unit := do
  let fid ← allocFunc (.lifted sf startType {} inst)
  let caller ← allocObj ArenaField.callers (Caller.sub .start)
  let _ ← callCancel (.funcInst fid caller)
  pure ()

/-- The specification tie of nested instantiation: a late-bound call `Call.instantiate`,
which the dispatcher (`Canon.dispatch`) resolves to `instantiateClosure callRecurse`; nesting
is bounded only by the machine's fuel. -/
def callRecurse : Recurse E σ := fun c args => callItems (.instantiate c args)

/-- Trap `hostTrap "import type mismatch: ..."` on a failed import type check. -/
def checkImport : Except String Unit → P E σ Unit
  | .ok () => pure ()
  | .error e => trap (.hostTrap ("import type mismatch: " ++ e))

section Core

variable [∀ a b, Decidable (E.ExternSub a b)]

/-- `core instance (instantiate m args)`: the import vector, core instantiation on the core
store (failure traps), the start function (as a synchronous task), and the export map. -/
def instantiateCore (inst : InstId) (f : Frame E) (m : Nat) (args : List (String × Nat)) :
    P E σ (List (String × E.ExternVal)) := do
  let md ← need "core module index" (f.coreModule? m)
  let s ← getStore
  let imports ← need "core instantiation arguments" (coreImportsFor? s.core md args f)
  match E.prepare? s.core md imports with
  | none => trap .coreTrap
  | some (core', ci, start) =>
    modifyStore (setCoreSt core')
    match start with
    | none => pure ()
    | some sf => runStart inst sf
    pure (E.exports ci)

/-- A syntactic type definition as a run-time type (resources excluded), in frame `f` with
enclosing frames `outer`. Instance and component types are resolved with their binders
(`resolveDefType?`); if their declarators use a construct the resolution does not support
(see `resolveDefType?`), they fall back to the empty placeholders `instance ⟨[], []⟩` /
`component ⟨[], [], [], []⟩` (as an expected import type, the empty instance type accepts
every instance). -/
def staticType? (f : Frame E) (outer : List (Frame E)) :
    Syntax.DefType → Option (Types.TypeDef RtId E.ExternType)
  | .val d => (resolveDefValType? f d).map .val
  | .func ft => (resolveFuncType? f ft).map .func
  | t@(.component _) =>
    some (((resolveDefType? outer f 0 t).map Prod.fst).getD (.component ⟨[], [], [], []⟩))
  | t@(.instance_ _) =>
    some (((resolveDefType? outer f 0 t).map Prod.fst).getD (.instance ⟨[], []⟩))
  | .resource _ _ => none

/-! ### Import type checking -/

/-- The core extern subtyping of the engine as a checker for `Types.Entity.sub?`. -/
def xsubCheck (a b : E.ExternType) : Except String Unit :=
  if E.ExternSub a b then .ok () else .error "core extern type mismatch"

/-- Erase from an expected entity type what `itemEntity?` types by sort only (core modules and
components become the placeholders `module ⟨[], []⟩` and `component ⟨[], [], [], []⟩`, so only
their sort is checked) and drop what it cannot type (🪙 values), recursively through instance
exports; `none` if the entity itself is a 🪙 value. Fuel: one unit per instance layer
(`pruneEntity` passes `Entity.depth + 1`). -/
def pruneFuel : Nat → EntityT E → Option (EntityT E)
  | 0, _ => none
  | n + 1, .instance it =>
    some (.instance
      ⟨it.defined, it.exports.filterMap fun (k, e) => (pruneFuel n e).map (k, ·)⟩)
  | _ + 1, .func t => some (.func t)
  | _ + 1, .type t => some (.type t)
  | _ + 1, .module _ => some (.module ⟨[], []⟩)
  | _ + 1, .value _ => none
  | _ + 1, .component _ => some (.component ⟨[], [], [], []⟩)

/-- `pruneFuel` with enough fuel. -/
def pruneEntity (e : EntityT E) : Option (EntityT E) := pruneFuel (e.depth + 1) e

/-- The message of `importTypeCheck` for a supplied item without a run-time type
(`itemEntity? s v = none`) where an entity of sort `srt` is expected: an unallocated function
(where a function is expected, the wording of wasmtime's linker, `TypeChecker::definition` in
`crates/wasmtime/src/runtime/component/matching.rs`: `function implementation is missing`;
otherwise wasmparser's sort mismatch `expected instance, found func`) or a 🪙 value
(wasmparser's `expected func, found value`). -/
def untypedImportMsg (n : String) (srt : Types.EntitySort) : ItemVal E → String
  | .func _ =>
    if srt = .func then s!"type mismatch for import `{n}`\nfunction implementation is missing"
    else s!"type mismatch for import `{n}`\nexpected {srt.desc}, found func"
  | _ => s!"type mismatch for import `{n}`\nexpected {srt.desc}, found value"

/-- The run-time type check of an import `n` with descriptor `d` (resolved in the frame `f` of
the component being instantiated) against the supplied item value `v` (Explainer.md,
"Instance Definitions" and "Type Checking": the arguments of `instantiate` must match the
component's imports;
wasmparser `open_instance_type(args, component, Import)`): the binders of the descriptor are
inferred from the supplied value by resource path (`Types.openInstanceType?`) and the
supplied type must be a subtype (`Types.Entity.sub?` over `E.ExternSub`). Core modules and
components are checked by sort only (`itemEntity?`, `pruneEntity`): a supplied value of another
sort is rejected with wasmparser's `expected module, found instance` (wasmtime's linker,
`TypeChecker::definition`: `expected module found instance`, `linking.wast` 10-12), but their
module and component types are not compared (wasmtime's `Linker` compares module types and
rejects every root component import: `linkCheck`, `Instantiate/Link.lean`). A supplied item
without a run-time type (a 🪙 value, or a function id that is not allocated) is rejected when
the descriptor resolves to an entity that is not erased (`untypedImportMsg`). Not checked
(always `ok`): descriptors that cannot be resolved (🪙 values) and expected 🪙 value entities
(`pruneEntity`, also inside instance types). Inside a supplied instance, untypable exports are
dropped (`itemEntities`), so a missing typed export is reported as missing, and of several
exports with the same name the first typable one is checked (`alias export` reads the first,
`lookupExport?`). -/
def importTypeCheck (s : CStore E) (f : Frame E) (n : String) (d : Syntax.ExternDesc)
    (v : ItemVal E) : Except String Unit :=
  match descEntity? f 0 d, itemEntity? s v with
  | some (exp, bs, _), some act =>
    match pruneEntity exp with
    | none => .ok ()
    | some exp' =>
      match Types.openInstanceType? (Types.Entity.sub? xsubCheck) [(n, act)] bs [(n, exp')]
          "import" with
      | .ok _ => .ok ()
      | .error e => .error e
  | some (exp, _, _), none =>
    match pruneEntity exp with
    | none => .ok ()
    | some exp' => .error (untypedImportMsg n exp'.sort v)
  | none, _ => .ok ()

/-- One definition of a component being instantiated in instance `inst`, with enclosing
frames `outer` and argument map `args` (see the table in the module docstring). -/
def instantiateDef (recurse : Recurse E σ) (inst : InstId) (outer : List (Frame E))
    (args : Exports E) (sc : Scope E) : Syntax.Definition E.Module → P E σ (Scope E)
  | .coreModule m => do
    let f ← pushEntry sc.frame (.core .module_) (.item (.coreModule m))
    pure { sc with frame := f }
  | .coreType t => do
    pure { sc with frame := { sc.frame with
      coreTypes := sc.frame.coreTypes ++ coreTypeSlots sc.frame.coreTypes t } }
  | .component defs => do
    let f ← pushEntry sc.frame .component (.item (.component ⟨defs, sc.frame :: outer⟩))
    pure { sc with frame := f }
  | .import_ n d => do
    let v ← orTrap (.hostTrap "missing import") (args.lookup n.name)
    let s ← getStore
    checkImport (importTypeCheck s sc.frame n.name d v)
    let f ← pushEntry sc.frame d.sort (.item v)
    pure { sc with frame := f }
  | .coreInstance (.instantiate m cargs) => do
    let es ← instantiateCore inst sc.frame m cargs
    let f ← pushEntry sc.frame (.core .instance_) (.coreInstance es)
    pure { sc with frame := f }
  | .coreInstance (.exports items) => do
    let es ← need "core export item" (items.mapM fun (n, si) => (n, ·) <$> externAt? sc.frame si)
    let f ← pushEntry sc.frame (.core .instance_) (.coreInstance es)
    pure { sc with frame := f }
  | .instance_ (.instantiate c iargs) => do
    let cl ← need "component index" (sc.frame.component? c)
    let vs ← need "instantiation argument"
      (iargs.mapM fun (n, si) => (n, ·) <$> itemAt? sc.frame si)
    let es ← recurse cl vs
    let f ← pushEntry sc.frame .instance_ (.item (.instance es))
    pure { sc with frame := f }
  | .instance_ (.exports items) => do
    let es ← need "instance export item"
      (items.mapM fun (n, si) => (n.name, ·) <$> itemAt? sc.frame si)
    let f ← pushEntry sc.frame .instance_ (.item (.instance es))
    pure { sc with frame := f }
  | .alias (.export_ i name s) => do
    let es ← need "instance index" (sc.frame.instance? i)
    let v ← need "instance export" (lookupExport? es name)
    let f ← pushEntry sc.frame s (.item v)
    pure { sc with frame := f }
  | .alias (.coreExport i name s) => do
    let es ← need "core instance index" (sc.frame.coreInstance? i)
    let x ← need "core instance export" (lookupExport? es name)
    let e ← need "core export sort" (Entry.ofExtern? s x)
    let f ← pushEntry sc.frame (.core s) e
    pure { sc with frame := f }
  | .alias (.outer ct idx s) => do
    let g ← need "outer alias count" (outerFrame? sc.frame outer ct)
    let e ← need "outer alias index" (g.get? s idx)
    let f ← pushEntry sc.frame s e
    pure { sc with frame := f }
  | .type (.resource rep dtor) => do
    let d ← resolveDtor sc.frame dtor
    let r ← allocResourceType inst rep d
    let f ← pushEntry sc.frame .type (.item (.type (.resource r)))
    pure { sc with frame := f }
  | .type t => do
    let ty ← need "type definition" (staticType? sc.frame outer t)
    let f ← pushEntry sc.frame .type (.item (.type ty))
    pure { sc with frame := f }
  | .canon (.lift cf opts ft) => do
    let (a, t, o) ← need "canon lift" (resolveLift? sc.frame cf opts ft)
    let fid ← allocFunc (.lifted a t o inst)
    let f ← pushEntry sc.frame .func (.item (.func fid))
    pure { sc with frame := f }
  | .canon (.lower g opts) => do
    let (callee, o) ← need "canon lower" (resolveLower? sc.frame g opts)
    let fi ← getObj ArenaField.funcs callee
    let a ← allocCoreHost (.lowered callee fi.ft o inst)
    let f ← pushEntry sc.frame (.core .func) (.coreFunc a)
    pure { sc with frame := f }
  | .canon (.builtin b) => do
    let s ← getStore
    let rb ← need "canon built-in" (resolveBuiltin? s.resourceRep? sc.frame b)
    let a ← allocCoreHost (.builtin rb inst)
    let f ← pushEntry sc.frame (.core .func) (.coreFunc a)
    pure { sc with frame := f }
  | .start _ _ _ => internal "instantiation: start definitions (values) are not modelled"
  | .value _ _ => internal "instantiation: value definitions (values) are not modelled"
  | .export_ n si _ => do
    let e ← need "export index" (sc.frame.get? si.sort si.idx)
    let v ← need "export sort" (Entry.toItem? e)
    let f ← pushEntry sc.frame si.sort e
    pure { frame := f, exports := sc.exports ++ [(n.name, v)] }

/-- Instantiate the closure `c` with arguments `args` in the (already allocated) instance
`inst`: fold `instantiateDef` over the body from the empty frame (Step 1) and return the
exports (Step 2). Structural over the definition list. -/
def instantiateComponent (recurse : Recurse E σ) (c : Closure E) (args : Exports E)
    (inst : InstId) : P E σ (Exports E) := do
  let sc ← c.body.foldlM (instantiateDef recurse inst c.outer args) {}
  pure sc.exports

/-- Instantiate a closure in a fresh component instance (Step 0 then `instantiateComponent`):
the body of the nested-instantiation tie. -/
def instantiateClosure (recurse : Recurse E σ) (c : Closure E) (args : Exports E) :
    P E σ (Exports E) := do
  let inst ← allocInst
  instantiateComponent recurse c args inst

/-- The fuel tie of nested instantiation (store-only tests without a machine): depth `n` of
nested `instance (instantiate ...)`; exhaustion traps `exhausted`. -/
def instantiateFuel : Nat → Recurse E σ
  | 0 => fun _ _ => trap .exhausted
  | n + 1 => fun c args => instantiateClosure (instantiateFuel n) c args

end Core

/-! ## Generativity: instantiation only appends to arenas -/

/-- Every arena of `s₀` is a prefix of the same arena of `s`. -/
def ArenasExtend (s₀ s : CStore E) : Prop :=
  s₀.insts <+: s.insts ∧ s₀.resourceTypes <+: s.resourceTypes ∧ s₀.funcs <+: s.funcs ∧
  s₀.tasks <+: s.tasks ∧ s₀.threads <+: s.threads ∧ s₀.subtasks <+: s.subtasks ∧
  s₀.resHandles <+: s.resHandles ∧ s₀.ends <+: s.ends ∧ s₀.wsets <+: s.wsets ∧
  s₀.errCtxs <+: s.errCtxs ∧ s₀.callers <+: s.callers

namespace ArenasExtend

variable {s₀ : CStore E}

end ArenasExtend

section Inv

variable {s₀ : CStore E}

local notation "I" => ArenasExtend s₀

variable [∀ a b, Decidable (E.ExternSub a b)]

end Inv

/-! ## Freshness of resource types -/

/-- A handler (over the component store) that implements `get` and `modify` as reading and
updating the store; every other operation is unconstrained. -/
def StoreHandler (H : (o : Op E σ) → CStore E → o.Resp → CStore E → Prop) : Prop :=
  (∀ s (r : CStore E) s', H .get s r s' → r = s ∧ s' = s) ∧
  (∀ f s (r : Unit) s', H (.modify f) s r s' → s' = f s)

end Silmaril.Wasm.Component.Instantiate
