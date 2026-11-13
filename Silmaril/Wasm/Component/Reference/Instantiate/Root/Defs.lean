module

import all Batteries.Data.Except
public import Silmaril.Wasm.Component.Reference.Instantiate.Defs

/-!
# Root (host) instantiation

The host instantiates a root component with an argument map for its imports (Explainer.md,
"Instance Definitions"): `instantiateRoot recurse c args`
allocates the root component instance and runs `instantiateComponent` on the closure `⟨c, []⟩`
(a root component has no enclosing frames), returning the root instance and its exports. It is
a program of the specification carrier `Canon.P E σ`, run by the component machine; nested
instantiation goes through `recurse` (`Instantiate/Defs.lean`): the specification tie is
`instantiateRootCall` (`recurse := callRecurse`, a late-bound `Call.instantiate` resolved by
the dispatcher, so arbitrary nesting depth is bounded only by the machine's fuel); the fuel tie
`instantiateRootFuel` serves store-only tests without a machine.

The relaxations of wasmtime's root instantiation are NOT applied: every import must be
supplied. `instantiateRoot` checks `argsComplete` FIRST, before allocating the root instance
or running any definition (core instantiation, start function, resource allocation), and traps
`hostTrap "missing import"` otherwise, as wasmtime rejects a missing import at link /
instantiate-pre time before any core instantiation.

The supplied arguments are type-checked against the import descriptors (`importTypeCheck`:
functions, types and instances of them by type, core modules and components by sort; a
mismatch traps `hostTrap "import type mismatch: ..."`) also BEFORE any side effect, like
wasmtime, which type-checks every import (`crates/wasmtime/src/runtime/component/matching.rs`)
at link / instantiate-pre time before any core instantiation: `precheckImports` walks the
definitions of the root without running them,
building only the index spaces that import descriptors can read (types, instances and core
types, `typeRelevant`), and checks each `import` it reaches. The walk stops (without an error)
at the first definition whose type-relevant entry is only known by running it: a resource
type definition, an `alias export` of a type or instance out of an instance produced by
`instance (instantiate ...)` (which the walk records as an empty placeholder instance), an
outer alias past the root, a type whose resolution fails, or a 🪙 `start`/`value` definition.
Imports after that point are checked in definition order only, by the `import` row of
`instantiateDef` (which re-checks every import, for root and nested instantiation alike), so a
mismatch there traps after the side effects of the preceding definitions (start functions,
nested instantiations), unlike wasmtime. The walk reproduces the frame of `instantiateDef` on
the type-relevant index spaces only for valid components (validation restricts outer aliases
in type declarators to types, so resolving a type never reads the skipped index spaces).
`instantiateRoot_prechecked`: a root instantiation that returns (under a store handler) passed
the pre-check on its initial store. Core modules and components supplied as arguments are
checked by sort only (`expected module found instance` in `matching.rs`; their module and
component types are not computed), and a 🪙 value or an unallocated function supplied where a
typed entity is expected is rejected (`untypedImportMsg`), so the check is weaker than
wasmtime's `matching.rs`. wasmtime's `Linker` check against the validated component type
(module types compared, root component imports rejected, the arguments projected onto the
import types) is `linkCheck` / `instantiateLinkedTop` (`Instantiate/Link.lean`).

Deviation from wasmtime: a missing or ill-typed root argument is modelled as a trap (the
`hostTrap`s above), and the machine's trap rule locks the store down, so no later embedder
action is possible on that store. wasmtime instead reports a link error before any side effect
(`Linker::instantiate` / `instantiate_pre` return `Err`) and leaves the store usable for other
instantiations and calls. The host Embedding-API
assertion that the store is not locked down is a side condition of the machine rule that
starts a root instantiation, not part of this program (deviation D-f).

Theorems: `instantiateRoot_inv` / `instantiateRootFuel_inv` / `instantiateRootCall_inv` (the
store updates of root instantiation only append to arenas, `ArenasExtend`; for
`instantiateRootFuel` this covers the nested bodies, which run inline; for
`instantiateRootCall` it covers the root body's own `modify`s only, since nested bodies run as
separately dispatched programs: their dispatcher arm is covered by
`Canon.instantiateCallProg_inv`, and the composition across the machine is not proved here),
`instantiateRoot_prechecked` (see
above), `instantiateRoot_inst_fresh` (under a store handler, the returned
instance id was not allocated in the initial store; that it is allocated afterwards is proved
only for `allocInst` itself, `allocInst_fresh`, since later operations such as `call` are
unconstrained by a store handler), and kernel-checked runs of
small components on the Mock engine with a store-only interpreter (`Tests`), including the
import check with an inferred resource binder (`importCheck_resource_ok`/`_bad`,
`rtImporter_run_ok`/`_bad`), the rejection of untypable arguments (`precheck_value_for_func`,
`precheck_unallocated_func`, `precheck_unallocated_func_for_instance`,
`precheck_value_export_for_func`, `precheck_unallocated_func_run`) and the reach of the
pre-check (`precheck_after_instantiate`, `precheck_stops_at_resource`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Instantiate

open Engine Canon _root_.Silmaril.Wasm.Component.Runtime

variable {E : CoreEngine} {σ : Type} [∀ a b, Decidable (E.ExternSub a b)]

/-- The import names of a component, in definition order. -/
def importNames {M : Type} (c : Syntax.Component M) : List String :=
  c.filterMap fun
    | .import_ n _ => some n.name
    | _ => none

/-- Every import of the root is supplied (the spec requires all imports; no wasmtime
relaxation). -/
def argsComplete {M : Type} (c : Syntax.Component M) (args : Exports E) : Bool :=
  (importNames c).all fun n => (args.lookup n).isSome

/-! ## Import type pre-check -/

/-- The index spaces that import descriptors and type resolution read (`descEntity?`,
`staticType?`, `resolveDefType?`): types, instances (through `alias export`) and core types. -/
def typeRelevant : Syntax.Sort_ → Bool
  | .type | .instance_ | .core .type => true
  | _ => false

/-- One definition of the root in the import pre-check, over the frame `f` of its
type-relevant index spaces (entries of the other index spaces are not pushed). `.ok (some f')`:
continue with `f'`; `.ok none`: stop pre-checking (the next entry is only known by running the
definition, or the definition is invalid); `.error e`: an import does not match. An
`instance (instantiate ...)` pushes an empty placeholder instance, so an `alias export` out of
it stops the walk. -/
def precheckDef (s : CStore E) (args : Exports E) (f : Frame E) :
    Syntax.Definition E.Module → Except String (Option (Frame E))
  | .coreType t => .ok (some { f with coreTypes := f.coreTypes ++ coreTypeSlots f.coreTypes t })
  | .import_ n d =>
    match args.lookup n.name with
    | none => .ok none
    | some v =>
      match importTypeCheck s f n.name d v with
      | .error e => .error e
      | .ok () => .ok (if typeRelevant d.sort then f.push d.sort (.item v) else some f)
  | .type t =>
    .ok (match t with
      | .instance_ _ | .component _ =>
        (resolveDefType? [] f 0 t).bind fun (ty, _) => f.push .type (.item (.type ty))
      | _ => (staticType? f [] t).bind fun ty => f.push .type (.item (.type ty)))
  | .instance_ (.instantiate _ _) => .ok (f.push .instance_ (.item (.instance [])))
  | .instance_ (.exports items) =>
    .ok (f.push .instance_ (.item (.instance (items.filterMap fun (n, si) =>
      if typeRelevant si.sort then (itemAt? f si).map (n.name, ·) else none))))
  | .alias (.export_ i name st) =>
    if typeRelevant st then
      .ok ((f.instance? i).bind fun es =>
        (lookupExport? es name).bind fun v => f.push st (.item v))
    else .ok (some f)
  | .alias (.outer ct idx st) =>
    if typeRelevant st then
      .ok (if ct = 0 then (f.get? st idx).bind (f.push st) else none)
    else .ok (some f)
  | .export_ _ si _ =>
    if typeRelevant si.sort then .ok ((f.get? si.sort si.idx).bind (f.push si.sort))
    else .ok (some f)
  | .start _ _ _ => .ok none
  | .value _ _ => .ok none
  | .coreModule _ => .ok (some f)
  | .component _ => .ok (some f)
  | .coreInstance _ => .ok (some f)
  | .alias (.coreExport _ _ _) => .ok (some f)
  | .canon _ => .ok (some f)

/-- The import pre-check of a root component (see the module docstring): fold `precheckDef`
from frame `f`, stopping at the first mismatch (`.error`) or at the first definition the walk
cannot follow (`.ok ()`). Structural over the definition list. -/
def precheckImports (s : CStore E) (args : Exports E) :
    Frame E → Syntax.Component E.Module → Except String Unit
  | _, [] => .ok ()
  | f, d :: ds =>
    match precheckDef s args f d with
    | .error e => .error e
    | .ok none => .ok ()
    | .ok (some f') => precheckImports s args f' ds

/-- Root instantiation: check that every import is supplied and pre-check the import types
(`precheckImports`), both before any side effect; then a fresh root instance, then the
definitions of `c` with the host's arguments `args`; returns the root instance and its
exports. -/
def instantiateRoot (recurse : Recurse E σ) (c : Syntax.Component E.Module) (args : Exports E) :
    P E σ (InstId × Exports E) := do
  trapIf (!argsComplete c args) (.hostTrap "missing import")
  let s ← getStore
  checkImport (precheckImports s args Frame.empty c)
  let inst ← allocInst
  let es ← instantiateComponent recurse ⟨c, []⟩ args inst
  pure (inst, es)

/-- Root instantiation with the specification tie of nested instantiation (`callRecurse`). -/
def instantiateRootCall (c : Syntax.Component E.Module) (args : Exports E) :
    P E σ (InstId × Exports E) :=
  instantiateRoot callRecurse c args

/-- Root instantiation with nested instantiations tied by fuel (`instantiateFuel`). -/
def instantiateRootFuel (fuel : Nat) (c : Syntax.Component E.Module) (args : Exports E) :
    P E σ (InstId × Exports E) :=
  instantiateRoot (instantiateFuel fuel) c args

/-! ## Tests (Mock engine, store-only interpreter) -/

namespace Tests

open Engine.Mock

/-- A store-only interpreter: `get`/`modify` act on the store; every other operation (traps,
calls, choices, ...) aborts. Enough for components without core instances or nested calls. -/
def storeOnly : (o : Op mock Unit) → StateT (CStore mock) Option o.Resp
  | .get => (get : StateT (CStore mock) Option (CStore mock))
  | .modify f => (modify f : StateT (CStore mock) Option Unit)
  | _ => fun _ => none

/-- Run a root instantiation with the store-only interpreter from the empty store. -/
def runRoot (c : Syntax.Component mock.Module) (args : Exports mock) :
    Option ((InstId × Exports mock) × CStore mock) :=
  (Prog.run storeOnly (instantiateRootFuel (σ := Unit) 4 c args)).run CStore.empty

/-- Two resource type definitions (generative: two identities) and an export of the second. -/
def twoResources : Syntax.Component mock.Module :=
  [.type (.resource .i32 none), .type (.resource .i64 none),
    .export_ { name := "r" } ⟨.type, 1⟩ none]

/-- The observable summary of a run: root instance, export names, the exported resource
identity (if a resource type) and the number of resource types. -/
def summary : Option ((InstId × Exports mock) × CStore mock) →
    Option (InstId × List String × Option RtId × Nat)
  | none => none
  | some ((inst, es), s) =>
    some (inst, es.map (·.1),
      (match es with
        | [(_, .type (.resource r))] => some r
        | _ => none),
      s.resourceTypes.length)

/-- A nested component instantiated twice yields two distinct resource types (generativity
across instances), each defined by its own fresh instance. -/
def nestedTwice : Syntax.Component mock.Module :=
  [.component [.type (.resource .i32 none), .export_ { name := "r" } ⟨.type, 0⟩ none],
    .instance_ (.instantiate 0 []), .instance_ (.instantiate 0 []),
    .alias (.export_ 0 "r" .type), .alias (.export_ 1 "r" .type),
    .export_ { name := "a" } ⟨.type, 0⟩ none, .export_ { name := "b" } ⟨.type, 1⟩ none]

/-! ### Import type checks with resource binders -/

/-- `(instance (export "t" (type (sub resource))) (export "u" (type (eq 0))))`: `u` must be the
same resource as the abstract `t`. -/
def rtInstType : Syntax.DefType :=
  .instance_ [.export_ { name := "t" } (.type .subResource),
    .export_ { name := "u" } (.type (.eq 0))]

/-- A root importing an instance `"x"` of `rtInstType`, after the definitions `pre`, which
define `k` types (so `rtInstType` is type `k`). -/
def rtImporter (pre : Syntax.Component mock.Module) (k : Nat := 0) :
    Syntax.Component mock.Module :=
  pre ++ [.type rtInstType, .import_ { name := "x" } (.instance_ k)]

/-- An argument instance exporting `t = resource t` and `u = resource u`. -/
def rtArg (t u : Nat) : Exports mock :=
  [("x", .instance [("t", .type (.resource ⟨t⟩)), ("u", .type (.resource ⟨u⟩))])]

/-- The expected rejection message (wasmparser's, with the context of the export `u` of the
import `x`). -/
def rtMismatch : String :=
  "type mismatch for import `x`\ntype mismatch in instance export `u`\n" ++
    "resource types are not the same"

/-- The result class of a check: `some true` accepted, `some false` rejected with exactly
`rtMismatch`, `none` rejected for another reason. -/
def checkClass : Except String Unit → Option Bool
  | .ok _ => some true
  | .error e => if e == rtMismatch then some false else none

/-- A root importing a function `"f"` of type `func()`. -/
def funcImporter : Syntax.Component mock.Module := [Syntax.funcT [] none, Syntax.importFunc "f" 0]

end Tests

end Silmaril.Wasm.Component.Instantiate
