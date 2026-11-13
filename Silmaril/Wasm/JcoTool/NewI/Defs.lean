module

public import Silmaril.Wasm.JcoTool.New.Defs
public import Silmaril.Wasm.JcoTool.AbiR.Defs
public import Silmaril.Wasm.Wit.Binary.DecodeLax.Defs
public import Silmaril.Wasm.JcoTool.WorldMerge.Defs
public import Silmaril.Wasm.Perf.CoreMod.Defs

/-!
# `wasm-jco new` for worlds with interfaces, named types and resources

`Silmaril.Wasm.JcoTool.New` covers worlds of freestanding functions over anonymous types. This
module covers the rest of the fragment wit-component handles with legacy core names:

* **interface imports** (`import ns:pkg/iface;`, `import x: interface { … }`): the component
  imports the instance (its instance type copied from the world), aliases its functions and
  types, and `canon lower`s the functions the module imports from the module named after the
  interface (`ns:pkg/iface`), sync (`f`) or async (`[async-lower]f`);
* **interface exports**: the module exports `ns:pkg/iface#f` (or `[async-lift]…`,
  `[async-lift-stackful]…`, with `cabi_post_…`); each function is lifted at the function type
  of the world's instance type, replayed at the top level, and the component exports an
  instance of the lifted functions and the interface's types;
* **named types** (records, variants, enums, flags, aliases), in interfaces and as world
  type imports: flattened by `AbiR` with the resolver `rho`, and referred to through the
  top-level type indices of the world's declarations and of the aliases of imported
  interfaces' types;
* **resources**: an exported interface's resource is defined (`(resource (rep i32))`, with
  the destructor `ns:pkg/iface#[dtor]r` when the module exports one, called through the shim
  table since the destructor is a core export of the module the resource's built-ins are
  imported into); `[resource-new]r`, `[resource-rep]r`, `[resource-drop]r` from
  `[export]ns:pkg/iface`; `[resource-drop]r` of an imported resource from `ns:pkg/iface`;
  `own<r>`/`borrow<r>` flatten to handles;
* every built-in of `New` (task.return of interface functions from `[export]ns:pkg/iface`,
  streams and futures `[stream-new-N]f` of interface functions, waitable sets, …).

**How the component is laid out.** The world's component type (`WorldFull.decls`, as
decoded from the `component-type` section or encoded from WIT text) is copied, declaration by
declaration, to the top level of the component (minus its exports), so that the world's type,
instance and function indices are the component's. Async function names are written in the
plain form (`f`, the asyncness in the type), as wit-component 0.262 writes them.

The plan (`planI`) checks every core import and export against its canonical type, like
`New.plan`; the theorems are in `Silmaril.Wasm.JcoTool.NewI.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.NewI

open Silmaril.Wasm.Wit.Binary (Ty Func TyRef TyDefKind TypeDef Interface IfaceName DItem WorldFull
  pAsync pAsyncMethod pAsyncStatic pMethod pStatic dropPrefix?)
open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component (CoreFuncTy)
open Silmaril.Wasm.JcoTool.New (TS TyM intern Lift ChanOp coreExport? expectExport require strip?
  indexBracket chanOps generalReq moduleNames shimMod fixupMod mustEncode ES EM addSec coreFunc
  coreInst aliasCoreFunc)

/-! ## Names -/

/-- The plain form of a function name: `[async]f ↦ f`, `[async method]r.f ↦ [method]r.f`,
`[async static]r.f ↦ [static]r.f`. -/
def plainName (n : String) : String :=
  let cs := n.toList
  match dropPrefix? pAsync cs with
  | some r => String.ofList r
  | none => match dropPrefix? pAsyncMethod cs with
    | some r => String.ofList (pMethod ++ r)
    | none => match dropPrefix? pAsyncStatic cs with
      | some r => String.ofList (pStatic ++ r)
      | none => n

/-- A function's name in the plain form. -/
def fname (f : Silmaril.Wasm.Wit.Binary.Func) : String := plainName f.mangled

def plainExt (e : ExternName) : ExternName := { e with name := plainName e.name }

mutual
def plainDef : DefType → DefType
  | .component ds => .component (plainComp ds)
  | .instance ds => .instance (plainInst ds)
  | t => t
def plainInst : List InstanceDecl → List InstanceDecl
  | [] => []
  | .type t :: ds => .type (plainDef t) :: plainInst ds
  | .export n (.func k) :: ds => .export (plainExt n) (.func k) :: plainInst ds
  | d :: ds => d :: plainInst ds
def plainComp : List ComponentDecl → List ComponentDecl
  | [] => []
  | .inst (.type t) :: ds => .inst (.type (plainDef t)) :: plainComp ds
  | .import n (.func k) :: ds => .import (plainExt n) (.func k) :: plainComp ds
  | .inst (.export n (.func k)) :: ds => .inst (.export (plainExt n) (.func k)) :: plainComp ds
  | d :: ds => d :: plainComp ds
end

/-- The name of an interface key. -/
def keyName : IfaceName ⊕ String → String
  | .inl i => i.id
  | .inr n => n

/-! ## The world -/

/-- An interface of the world: its key, body, and whether it is imported. -/
structure Iface where
  key : IfaceName ⊕ String
  body : Interface
  imported : Bool

/-- The interfaces of a world. -/
def ifaces (wf : WorldFull) : List Iface :=
  (wf.imports.filterMap fun
    | .iface k b => some ⟨k, b, true⟩
    | _ => none) ++
  (wf.exports.filterMap fun
    | .iface k b => some ⟨k, b, false⟩
    | _ => none)

/-- The world-level named types (type imports). -/
def worldTypes (wf : WorldFull) : List TypeDef :=
  wf.imports.filterMap fun
    | .type t => some t
    | _ => none

/-- The world-level functions (imported or exported). -/
def worldFuncs (items : List DItem) : List Silmaril.Wasm.Wit.Binary.Func :=
  items.filterMap fun
    | .func f => some f
    | _ => none

/-- The body of the interface of scope `sc` (imports first). -/
def bodyOf (wf : WorldFull) (k : IfaceName ⊕ String) : Option Interface :=
  ((ifaces wf).find? (·.key == k)).map (·.body)

/-- **The resolver** of a world: a local reference is to the scope's own types, a reference
`⟨.iface i, n⟩` to type `n` of interface `i`. -/
def rho (wf : WorldFull) : Resolver := fun sc r => do
  let (sc', tys) ← match r.owner, sc with
    | .local, .world => pure (Scope.world, worldTypes wf)
    | .local, .iface k => match bodyOf wf k with
      | some b => pure (Scope.iface k, b.types)
      | none => throw s!"type {r.name}: no interface {keyName k}"
    | .iface i, _ => match bodyOf wf (.inl i) with
      | some b => pure (Scope.iface (.inl i), b.types)
      | none => throw s!"type {r.name}: interface {i.id} is not in the world"
  match tys.find? (·.name == r.name) with
  | some t => pure (sc', t.kind)
  | none => throw s!"no type {r.name} in its interface"

/-- The scope and name a reference resolves to (for the type index tables). -/
def refKey (sc : Scope) (r : TyRef) : Scope × String :=
  match r.owner with
  | .local => (sc, r.name)
  | .iface i => (.iface (.inl i), r.name)

/-! ## Requests -/

/-- An exported or imported function of a scope. -/
structure Fn where
  sc : Scope
  f : Silmaril.Wasm.Wit.Binary.Func

/-- What a core import of the module asks for. -/
inductive IReq where
  /-- `canon lower` of the component function `fidx` (`async`: `[async-lower]`). -/
  | lower (fidx : Nat) (sc : Scope) (f : Silmaril.Wasm.Wit.Binary.Func) (async : Bool)
  | taskReturn (sc : Scope) (f : Silmaril.Wasm.Wit.Binary.Func)
  /-- A resource built-in of the resource `(scope, name)`. -/
  | resNew (r : Scope × String)
  | resRep (r : Scope × String)
  /-- `exported`: requested by an exported interface (`[export]…`); else by an import, whose
  resource is the imported one even when the interface is also exported. -/
  | resDrop (r : Scope × String) (exported : Bool)
  /-- A stream or future built-in of a function of scope `sc`. -/
  | chan (op : ChanOp) (async : Bool) (sc : Scope) (c : Chan) (f : Silmaril.Wasm.Wit.Binary.Func)
  /-- A scope-free built-in of `New` (task.cancel, waitable sets, context, error-context, …). -/
  | gen (r : New.Req)

instance : Inhabited IReq := ⟨.gen .taskCancel⟩

/-- A stream or future operation `[stream-<op>-N]f` of a function in `fs`. -/
def chanReq (async : Bool) (sc : Scope) (fs : List Silmaril.Wasm.Wit.Binary.Func) (s : String) :
    Except String (Option IReq) := do
  let named := fs.map fun f => { f with name := fname f }
  match ← New.chanReq async named s with
  | some (.chan op a c f) => pure (some (.chan op a sc c f))
  | _ => pure none

/-- The index tables of classification: the component function index of every imported
function (`(scope, plain name)`), the resources of every scope. -/
structure Tables where
  funcIdx : List ((Scope × String) × Nat)
  resources : List (Scope × String)

def lookupIdx {α : Type} [BEq α] (k : α) (xs : List (α × Nat)) : Option Nat :=
  (xs.find? (·.1 == k)).map (·.2)

/-- The last entry of `k`. -/
def lookupLastIdx {α : Type} [BEq α] (k : α) (xs : List (α × Nat)) : Option Nat :=
  lookupIdx k xs.reverse

/-- The resources defined by interfaces, then the world's own (`resource a;` in the world). -/
def resourcesOf (wf : WorldFull) : List (Scope × String) :=
  (ifaces wf).flatMap (fun i =>
    i.body.types.filterMap fun t => if t.kind = .resource then some (.iface i.key, t.name) else none) ++
  (worldTypes wf).filterMap fun t => if t.kind = .resource then some (.world, t.name) else none

/-- The interface a core import module name `key` refers to: the one of that name, else (as
wit-component merges imports by semantic version) the one whose name is semver-compatible
(`WorldMerge.compatible`), e.g. `wasi:io/poll@0.2.0` for `wasi:io/poll@0.2.12`. -/
def findIface (wf : WorldFull) (key : String) (exported : Bool) : Option Iface :=
  match (ifaces wf).find? (fun i => keyName i.key == key && i.imported == !exported) with
  | some i => some i
  | none => match WorldMerge.ifaceOfModule key with
    | some j => (ifaces wf).find? fun i => i.imported == !exported && match i.key with
      | .inl k => WorldMerge.compatible k j
      | .inr _ => false
    | none => none

/-- Classify a core import `(module, name)`. -/
def classify (wf : WorldFull) (tb : Tables) (modName name : String) : Except String IReq := do
  let (async, base) := match strip? "[async-lower]" name with
    | some b => (true, b)
    | none => (false, name)
  let imps := worldFuncs wf.imports
  let exps := worldFuncs wf.exports
  let lowerIn (sc : Scope) (fs : List Silmaril.Wasm.Wit.Binary.Func) (n : String) : Option IReq :=
    match fs.find? (fname · == n), lookupIdx (sc, n) tb.funcIdx with
    | some f, some i => some (.lower i sc f async)
    | _, _ => none
  match modName with
  | "$root" =>
    if !async then
      if let some r := generalReq name then return .gen r
      -- a resource of the world (`resource a;` at the world level)
      if let some r := strip? "[resource-drop]" name then
        if tb.resources.contains (.world, r) then return .resDrop (.world, r) false
    if let some r := lowerIn .world imps base then return r
    match ← chanReq async .world imps base with
    | some r => pure r
    | none => throw s!"core import $root {name}: neither a world import nor a built-in"
  | "[export]$root" =>
    if name == "[task-cancel]" then return .gen .taskCancel
    if let some n := strip? "[task-return]" name then
      match exps.find? (fname · == n) with
      | some f => return .taskReturn .world f
      | none => throw s!"core import [export]$root {name}: no exported function {n}"
    match ← chanReq async .world exps base with
    | some r => pure r
    | none => throw s!"core import [export]$root {name}: not a built-in"
  | m =>
    let (exported, key) := match strip? "[export]" m with
      | some k => (true, k)
      | none => (false, m)
    let some i := findIface wf key exported
      | throw s!"core import {m} {name}: the world has no {if exported then "exported" else "imported"} interface {key}"
    let sc := Scope.iface i.key
    let res (pre : String) : Option (Scope × String) :=
      (strip? pre name).bind fun r => if tb.resources.contains (sc, r) then some (sc, r) else none
    if exported then
      if name == "[task-cancel]" then return .gen .taskCancel
      if let some r := res "[resource-new]" then return .resNew r
      if let some r := res "[resource-rep]" then return .resRep r
      if let some r := res "[resource-drop]" then return .resDrop r true
      if let some n := strip? "[task-return]" name then
        match i.body.funcs.find? (fname · == n) with
        | some f => return .taskReturn sc f
        | none => throw s!"core import {m} {name}: no function {n} in {key}"
    else
      if let some r := res "[resource-drop]" then return .resDrop r false
      if let some r := lowerIn sc i.body.funcs base then return r
    match ← chanReq async sc i.body.funcs base with
    | some r => pure r
    | none => throw s!"core import {m} {name}: not a function of {key} nor a built-in"

section
variable (wf : WorldFull)

/-- The canonical core type of a request. -/
def IReq.coreTy : IReq → Except String CoreFuncTy
  | .lower _ sc f false => lowerCoreR (rho wf) sc f
  | .lower _ sc f true => lowerAsyncCoreR (rho wf) sc f
  | .taskReturn sc f => taskReturnCoreR (rho wf) sc f
  | .resNew _ | .resRep _ => pure ⟨[ti32], [ti32]⟩
  | .resDrop _ _ => pure ⟨[ti32], []⟩
  | .chan op a _ c f => (New.Req.chan op a c f).coreTy
  | .gen r => r.coreTy

/-- Whether the request's core function needs the module's memory. -/
def IReq.usesMem : IReq → Except String Bool
  | .lower _ sc f false => usesMemoryR (rho wf) sc f
  | .lower _ sc f true => lowerAsyncUsesMemoryR (rho wf) sc f
  | .taskReturn sc f => taskReturnUsesMemoryR (rho wf) sc f
  | .resNew _ | .resRep _ | .resDrop _ _ => pure false
  | .chan op _ _ _ _ => pure (decide (op = .read) || decide (op = .write))
  | .gen r => r.usesMem

/-- Whether the request's core function needs the allocator. -/
def IReq.usesRealloc : IReq → Except String Bool
  | .lower _ sc f _ => resultMemR (rho wf) sc f
  | .chan .read _ sc (.stream (some t)) _ | .chan .read _ sc (.future (some t)) _ =>
    usesMemR (rho wf) flatFuel sc t
  | .gen (.errorContextDebugMessage _) => pure true
  | _ => pure false

end

/-! ## Plans -/

/-- A world export implemented by the module: its scope, core base name and function. -/
structure XFn where
  sc : Scope
  core : String
  f : Silmaril.Wasm.Wit.Binary.Func

/-- The exported functions: world-level (`f`), then each exported interface's (`key#f`). -/
def exportFns (wf : WorldFull) : List XFn :=
  (worldFuncs wf.exports).map (fun f => ⟨.world, fname f, f⟩) ++
  (ifaces wf).flatMap fun i =>
    if i.imported then [] else i.body.funcs.map fun f => ⟨.iface i.key, keyName i.key ++ "#" ++ fname f, f⟩

/-- A sync export: the core export `x.core` at `liftCoreR`, with an optional post-return. -/
def liftSync (wf : WorldFull) (m : CoreMod) (x : XFn) : Except String Lift := do
  let t ← liftCoreR (rho wf) x.sc x.f
  expectExport m x.core t
  match coreExport? m ("cabi_post_" ++ x.core) with
  | some t' =>
    if t' = ⟨t.results, []⟩ then pure (.sync x.core (some ("cabi_post_" ++ x.core)))
    else throw s!"core export cabi_post_{x.core}: not a post-return function of {x.core}"
  | none => pure (.sync x.core none)

/-- An async export with a callback. -/
def liftCallback (wf : WorldFull) (m : CoreMod) (x : XFn) : Except String Lift := do
  let t ← liftAsyncCoreR (rho wf) x.sc x.f true
  expectExport m ("[async-lift]" ++ x.core) t
  expectExport m ("[callback][async-lift]" ++ x.core) callbackCore
  pure (.callback ("[async-lift]" ++ x.core) ("[callback][async-lift]" ++ x.core))

/-- A stackful async export. -/
def liftStackful (wf : WorldFull) (m : CoreMod) (x : XFn) : Except String Lift := do
  let t ← liftAsyncCoreR (rho wf) x.sc x.f false
  expectExport m ("[async-lift-stackful]" ++ x.core) t
  pure (.stackful ("[async-lift-stackful]" ++ x.core))

/-- How export `x` is implemented by the module, at its canonical type. -/
def liftOf (wf : WorldFull) (m : CoreMod) (x : XFn) : Except String Lift :=
  if x.f.async then
    if (coreExport? m ("[async-lift]" ++ x.core)).isSome then liftCallback wf m x
    else liftStackful wf m x
  else liftSync wf m x

/-- The destructor of an exported resource, if the module exports one (at `[i32] → []`). -/
def dtorOf (m : CoreMod) (r : Scope × String) : Except String (Option String) :=
  match r.1 with
  | .iface k =>
    let n := keyName k ++ "#[dtor]" ++ r.2
    match coreExport? m n with
    | some t => if t = ⟨[ti32], []⟩ then pure (some n)
        else throw s!"core export {n}: a destructor has type (i32) -> ()"
    | none => pure none
  | .world => pure none

/-- A plan. -/
structure Plan where
  core : ByteArray
  mod : CoreMod
  wf : WorldFull
  tables : Tables
  reqs : List ((String × String) × IReq)
  fns : List XFn
  lifts : List Lift
  /-- The exported resources and their destructors. -/
  dtors : List ((Scope × String) × Option String)
  memory : Option String
  realloc : Option String

/-- The component function indices of imported functions: the world's function imports in
order, then, per imported interface, its functions (aliased in that order by `emit`). -/
def funcTable (wf : WorldFull) : List ((Scope × String) × Nat) :=
  let w := (worldFuncs wf.imports).map fun f => ((Scope.world, fname f))
  let i := (ifaces wf).flatMap fun i =>
    if i.imported then i.body.funcs.map fun f => (Scope.iface i.key, fname f) else []
  (w ++ i).zipIdx

/-- A core import: its request at the canonical type. -/
def reqOf (wf : WorldFull) (tb : Tables) (x : (String × String) × (String × CoreFuncTy)) :
    Except String ((String × String) × IReq) := do
  let r ← classify wf tb x.1.1 x.1.2
  let t' ← r.coreTy wf
  require (decide (x.2.2 = t'))
    s!"core import {x.1.1} {x.1.2}: type {repr x.2.2}, the canonical ABI expects {repr t'}"
  pure (x.1, r)

/-- Whether the exports or requests need the memory or the allocator. -/
def needs (wf : WorldFull) (fns : List XFn) (reqs : List IReq) : Except String (Bool × Bool) := do
  let mut mem := false
  let mut ra := false
  for x in fns do
    if ← liftUsesMemoryR (rho wf) x.sc x.f then mem := true
    if ← needsReallocR (rho wf) x.sc x.f then ra := true
  for r in reqs do
    if ← r.usesMem wf then mem := true
    if ← r.usesRealloc wf then ra := true
  pure (mem, ra)

/-- **The plan** of a core module against a full world. -/
def plan (core : ByteArray) (wf : WorldFull) : Except String Plan := do
  let m ← Silmaril.Wasm.Perf.CoreMod.coreModF core
  let tb : Tables := ⟨funcTable wf, resourcesOf wf⟩
  let reqs ← (m.importNames.zip m.imports).mapM (reqOf wf tb)
  let fns := exportFns wf
  let lifts ← fns.mapM (liftOf wf m)
  let exported := tb.resources.filter fun r => match r.1 with
    | .iface k => (ifaces wf).any fun i => i.key == k && !i.imported
    | .world => false
  let dtors ← exported.mapM fun r => do pure (r, ← dtorOf m r)
  let (mem, ra) ← needs wf fns (reqs.map (·.2))
  require (!mem || New.hasMemory core) "the world needs linear memory: export it as `memory`"
  New.reallocOk m ra
  pure ⟨core, m, wf, tb, reqs, fns, lifts, dtors, if mem then some "memory" else none,
    if ra then some "cabi_realloc" else none⟩

/-! ## Emission -/

/-- What emission knows about the top-level index spaces. -/
structure Idx where
  types : Nat := 0
  funcs : Nat := 0
  insts : Nat := 0
  /-- The top-level type definitions (for replaying exported instance types). -/
  defs : List (Nat × DefType) := []
  /-- Named types: `(scope, name)` to type index. -/
  names : List ((Scope × String) × Nat) := []
  /-- Imported interfaces: instance index. -/
  instOf : List (String × Nat) := []
  /-- World-level exports: function type index by plain name, instance type index by name. -/
  expFunc : List (String × Nat) := []
  expInst : List (String × Nat) := []
  comps : Nat := 0

/-- One declaration of the world's component type, as a top-level section (exports are
recorded, not emitted). -/
def copyDecl (x : Idx) : ComponentDecl → Except String (Option Section × Idx)
  | .inst (.type t) => pure (some (.types [t]),
      { x with types := x.types + 1, defs := (x.types, t) :: x.defs })
  | .inst (.coreType t) => pure (some (.coreTypes [t]), x)
  | .inst (.alias a) => do
    let x' ← match a.sort, a.target with
      | .type, .export i n =>
        let key := (x.instOf.find? (·.2 == i)).map (·.1)
        let names := match key with
          | some k => match Silmaril.Wasm.Wit.Binary.parseIfaceName k.toList with
            | some ifn => ((Scope.iface (.inl ifn), n), x.types) :: x.names
            | none => ((Scope.iface (.inr k), n), x.types) :: x.names
          | none => x.names
        pure { x with types := x.types + 1, names := names }
      | .type, _ => pure { x with types := x.types + 1 }
      | .func, _ => pure { x with funcs := x.funcs + 1 }
      | .instance, _ => pure { x with insts := x.insts + 1 }
      | _, _ => throw "unsupported alias in the world's type"
    pure (some (.aliases [a]), x')
  | .import n d => do
    let x' ← match d with
      | .func _ => pure { x with funcs := x.funcs + 1 }
      | .instance _ => pure { x with insts := x.insts + 1, instOf := (n.name, x.insts) :: x.instOf }
      | .type _ => pure { x with types := x.types + 1, names := ((.world, n.name), x.types) :: x.names }
      | _ => throw s!"world import {n.name}: unsupported kind"
    pure (some (.imports [⟨n, d⟩]), x')
  | .inst (.export n d) => match d with
    | .func k => pure (none, { x with expFunc := (n.name, k) :: x.expFunc })
    | .instance k => pure (none, { x with expInst := (n.name, k) :: x.expInst })
    | _ => throw s!"world export {n.name}: unsupported kind"

def copyDecls (x : Idx) : List ComponentDecl → Except String (List Section × Idx)
  | [] => pure ([], x)
  | d :: ds => do
    let (s, x) ← copyDecl x d
    let (ss, x) ← copyDecls x ds
    pure (s.toList ++ ss, x)

/-- A local type index of an instance type, at the top level. -/
def at? (lm : List Nat) (i : Nat) : Except String Nat :=
  match lm[i]? with
  | some j => pure j
  | none => throw s!"instance type: type index {i} out of bounds"

def remapV (lm : List Nat) : Silmaril.Wasm.Component.Binary.ValType → Except String Silmaril.Wasm.Component.Binary.ValType
  | .prim p => pure (.prim p)
  | .idx i => .idx <$> at? lm i

def remapO (lm : List Nat) : Option Silmaril.Wasm.Component.Binary.ValType → Except String (Option Silmaril.Wasm.Component.Binary.ValType)
  | none => pure none
  | some v => some <$> remapV lm v

/-- A value type definition of an instance type, at the top level. -/
def remapDV (lm : List Nat) : DefValType → Except String DefValType
  | .prim p => pure (.prim p)
  | .record fs => .record <$> fs.mapM fun (n, v) => do pure (n, ← remapV lm v)
  | .variant cs => .variant <$> cs.mapM fun (n, v) => do pure (n, ← remapO lm v)
  | .list t => .list <$> remapV lm t
  | .tuple ts => .tuple <$> ts.mapM (remapV lm)
  | .flags ls => pure (.flags ls)
  | .enum ls => pure (.enum ls)
  | .option t => .option <$> remapV lm t
  | .result a b => do pure (.result (← remapO lm a) (← remapO lm b))
  | .own i => .own <$> at? lm i
  | .borrow i => .borrow <$> at? lm i
  | .fixedList t n => do pure (.fixedList (← remapV lm t) n)
  | .stream t => .stream <$> remapO lm t
  | .future t => .future <$> remapO lm t
  | .map k v => do pure (.map (← remapV lm k) (← remapV lm v))

def remapD (lm : List Nat) : DefType → Except String DefType
  | .val d => .val <$> remapDV lm d
  | .func f => do
    let ps ← f.params.mapM fun (n, v) => do pure (n, ← remapV lm v)
    pure (.func ⟨ps, ← remapO lm f.result, f.async⟩)
  | _ => throw "nested component or instance types in an exported interface are not supported"

/-- An exported interface, replayed: the sections, the top-level indices of its named
types (in order) and the function type of each function. -/
structure Replay where
  secs : List Section := []
  types : List (String × Nat) := []
  funcs : List (String × Nat) := []

/-- Replay the instance type of an exported interface at the top level; a resource export
defines a resource with the destructor of `dtor` (a core function index). -/
def replay (sc : Scope) (dtor : String → Option Nat) :
    Idx → List Nat → Replay → List InstanceDecl → Except String (Idx × Replay)
  | x, _, r, [] => pure (x, r)
  | x, lm, r, d :: ds => do
    match d with
    | .type t =>
      let t' ← remapD lm t
      replay sc dtor { x with types := x.types + 1 } (lm ++ [x.types])
        { r with secs := r.secs ++ [.types [t']] } ds
    | .alias ⟨.type, .outer 1 j⟩ => replay sc dtor x (lm ++ [j]) r ds
    | .export n (.type (.eq k)) => do
      let j ← at? lm k
      replay sc dtor { x with names := ((sc, n.name), j) :: x.names } (lm ++ [j])
        { r with types := r.types ++ [(n.name, j)] } ds
    | .export n (.type .subResource) =>
      replay sc dtor { x with types := x.types + 1, names := ((sc, n.name), x.types) :: x.names }
        (lm ++ [x.types])
        { r with secs := r.secs ++ [.types [.resource .i32 (dtor n.name)]],
                 types := r.types ++ [(n.name, x.types)] } ds
    | .export n (.func k) => do
      let j ← at? lm k
      replay sc dtor x lm { r with funcs := r.funcs ++ [(n.name, j)] } ds
    | .coreType _ => replay sc dtor x lm r ds
    | _ => throw "unsupported declaration in an exported interface's type"

/-- The kebab-case import name of function `n` in a shim component (wit-component's names):
`import-func-f`, `import-constructor-r`, `import-method-r-f`, `import-static-r-f`. -/
def funcImportName (n : String) : String :=
  let dot (r : String) := String.ofList ((r.toList.map fun c => if c = '.' then '-' else c))
  match strip? "[constructor]" n with
  | some r => "import-constructor-" ++ r
  | none => match strip? "[method]" n with
    | some r => "import-method-" ++ dot r
    | none => match strip? "[static]" n with
      | some r => "import-static-" ++ dot r
      | none => "import-func-" ++ n

/-- The shim component being built: its sections, its type count and the indices of the named
types defined or imported in it. -/
structure CB where
  secs : Array Section := #[]
  cT : Nat := 0
  cnames : List ((Scope × String) × Nat) := []

abbrev CBM := StateT CB (Except String)

/-- Define a type in the shim component; its index. -/
def cbDef (d : DefType) : CBM Nat := do
  let s ← get
  set { s with secs := s.secs.push (.types [d]), cT := s.cT + 1 }
  pure s.cT

mutual
/-- A WIT type in the shim component: a named type by its index there, or defined
structurally (with the definitions it needs) when the shim has none for it yet. -/
def cbTy (wf : WorldFull) : Nat → Scope → Ty → CBM Silmaril.Wasm.Component.Binary.ValType
  | 0, _, _ => throw "type nesting too deep"
  | fuel + 1, sc, t => match t with
    | .prim p => pure (.prim p)
    | .ref r => do
      match lookupIdx (refKey sc r) (← get).cnames with
      | some i => pure (.idx i)
      | none =>
        let (sc', k) ← (rho wf sc r : Except String _)
        let i ← cbKind wf fuel sc' k
        modify fun s => { s with cnames := (refKey sc r, i) :: s.cnames }
        pure (.idx i)
    | .own r | .borrow r => do
      match lookupIdx (refKey sc r) (← get).cnames with
      | some i => .idx <$> cbDef (.val (match t with
        | .own _ => .own i
        | _ => .borrow i))
      | none => throw s!"resource {r.name}: used by an exported interface without being imported into its shim"
    | .list t => do .idx <$> cbDef (.val (.list (← cbTy wf fuel sc t)))
    | .option t => do .idx <$> cbDef (.val (.option (← cbTy wf fuel sc t)))
    | .result a b => do
      let a' ← cbOpt wf fuel sc a
      let b' ← cbOpt wf fuel sc b
      .idx <$> cbDef (.val (.result a' b'))
    | .tuple ts => do .idx <$> cbDef (.val (.tuple (← ts.mapM (cbTy wf fuel sc))))
    | .stream t => do .idx <$> cbDef (.val (.stream (← cbOpt wf fuel sc t)))
    | .future t => do .idx <$> cbDef (.val (.future (← cbOpt wf fuel sc t)))
    | .map k v => do
      let k' ← cbTy wf fuel sc k
      let v' ← cbTy wf fuel sc v
      .idx <$> cbDef (.val (.map k' v'))
    | .fixedList t n => do .idx <$> cbDef (.val (.fixedList (← cbTy wf fuel sc t) n))
def cbOpt (wf : WorldFull) : Nat → Scope → Option Ty → CBM (Option Silmaril.Wasm.Component.Binary.ValType)
  | _, _, none => pure none
  | fuel, sc, some t => some <$> cbTy wf fuel sc t
/-- The structural definition of a named type's kind in the shim component. -/
def cbKind (wf : WorldFull) : Nat → Scope → TyDefKind → CBM Nat
  | 0, _, _ => throw "type nesting too deep"
  | fuel + 1, sc, k => match k with
    | .record fs => do
      let fs' ← fs.mapM fun f => do pure (f.name, ← cbTy wf fuel sc f.ty)
      cbDef (.val (.record fs'))
    | .variant cs => do
      let cs' ← cs.mapM fun c => do pure (c.name, ← cbOpt wf fuel sc c.ty)
      cbDef (.val (.variant cs'))
    | .enum cs => cbDef (.val (.enum (cs.map (·.name))))
    | .flags fs => cbDef (.val (.flags (fs.map (·.name))))
    | .resource => throw "a resource used (not defined) by an exported interface is not supported"
    | .type t => do
      match ← cbTy wf fuel sc t with
      | .idx i => pure i
      | .prim p => cbDef (.val (.prim p))
end

/-- Whether the type `n` of scope `sc` is, through `type`/`use` aliases, a resource of another
scope: that resource. -/
def resourceThrough (wf : WorldFull) (sc : Scope) (n : String) : Option (Scope × String) :=
  let rec go : Nat → Scope → TyRef → Option (Scope × String)
    | 0, _, _ => none
    | fuel + 1, sc, r =>
      match (rho wf sc r : Except String _) with
      | .ok (sc', .resource) => if sc' == sc && r.owner == .local then none else some (sc', r.name)
      | .ok (sc', .type (.ref r')) => go fuel sc' r'
      | _ => none
  go 16 sc ⟨.local, n⟩

/-- The shim component of an exported interface (wit-component's pattern), from the
interface's instance type `ds`: it imports each of the interface's types (`import-type-n`,
with the bound of the instance type; a type the interface uses from another interface is
imported at its structural definition) and functions (`funcImportName`), then exports the
types and the functions, the functions ascribed with function types over the exported
types. Its instance is the exported interface. The result: the sections, and the names of
the type and function imports in order. -/
def shimComp (wf : WorldFull) (sc : Scope) (ds : List InstanceDecl) :
    Except String (List Section × List String × List String) := do
  let go : CBM (List String × List String) := do
    -- `none`: an outer alias, defined structurally when it is exported
    let mut m1 : Array (Option Nat) := #[]
    -- the instance type's own definitions, by instance type index
    let mut defs : Array (Option DefType) := #[]
    let mut cF := 0
    -- exported types: name, import index, instance type index of the export, and the
    -- instance type index of its definition (`none`: a resource)
    let mut tyImps : Array (String × Nat × Nat × Option Nat) := #[]
    let mut fnImps : Array (String × Nat × Nat) := #[]
    let idx (m : Array (Option Nat)) (k : Nat) : Except String Nat := match m[k]? with
      | some (some c) => pure c
      | _ => throw s!"shim: type index {k} has no definition"
    for d in ds do
      match d with
      | .type t =>
        let t' ← (remapD (m1.toList.map (·.getD 0)) t : Except String _)
        let c ← cbDef t'
        m1 := m1.push (some c)
        defs := defs.push (some t)
      | .alias ⟨.type, .outer 1 _⟩ => m1 := m1.push none; defs := defs.push none
      | .export n (.type (.eq k)) =>
        if m1[k]? == some none && (match resourceThrough wf sc n.name with
            | some (.iface key, _) => (ifaces wf).any fun i => i.key == key && i.imported
            | _ => false) then
          -- a resource of another interface (`use i.{r}`): imported as a resource, the
          -- instantiation supplying the world's resource
          let s ← get
          set { s with secs := s.secs.push (.imports [⟨⟨"import-type-" ++ n.name, .plain0⟩, .type .subResource⟩]),
                       cT := s.cT + 1, cnames := ((sc, n.name), s.cT) :: s.cnames }
          tyImps := tyImps.push (n.name, s.cT, m1.size, none)
          m1 := m1.push (some s.cT)
          defs := defs.push none
          continue
        let c ← match m1[k]? with
          | some (some c) => pure c
          | some none => do
            let (sc', kind) ← (rho wf sc ⟨.local, n.name⟩ : Except String _)
            cbKind wf flatFuel sc' kind
          | none => throw s!"shim: type index {k} out of bounds"
        let s ← get
        -- every name of the definition `c` now denotes the import
        let cn := s.cnames.map fun (k, v) => (k, if v = c then s.cT else v)
        set { s with secs := s.secs.push (.imports [⟨⟨"import-type-" ++ n.name, .plain0⟩, .type (.eq c)⟩]),
                     cT := s.cT + 1, cnames := ((sc, n.name), s.cT) :: cn }
        tyImps := tyImps.push (n.name, s.cT, m1.size, some k)
        m1 := m1.push (some s.cT)
        defs := defs.push none
      | .export n (.type .subResource) =>
        let s ← get
        set { s with secs := s.secs.push (.imports [⟨⟨"import-type-" ++ n.name, .plain0⟩, .type .subResource⟩]),
                     cT := s.cT + 1, cnames := ((sc, n.name), s.cT) :: s.cnames }
        tyImps := tyImps.push (n.name, s.cT, m1.size, none)
        m1 := m1.push (some s.cT)
        defs := defs.push none
      | .export n (.func k) =>
        let c ← (idx m1 k : Except String _)
        modify fun s => { s with secs := s.secs.push (.imports [⟨⟨funcImportName n.name, .plain0⟩, .func c⟩]) }
        fnImps := fnImps.push (n.name, cF, k)
        cF := cF + 1
      | .coreType _ => pure ()
      | _ => throw "unsupported declaration in an exported interface's type"
    -- Each exported type is defined again over the types exported before it (as
    -- wit-component's shim does): a definition referring to an imported type could not be
    -- exported (the exported instance would mention a type it does not export).
    let mut m2 := m1
    for (n, c, l, kdef) in tyImps do
      let c' ← match kdef with
        | none => pure c
        | some k => match defs[k]? with
          | some (some t) => do
            let t' ← (remapD (m2.toList.map (·.getD 0)) t : Except String _)
            cbDef t'
          | _ => match m1[k]? with
            -- `type b = a` of an earlier exported type: the export of `a`
            | some (some _) => pure ((m2[k]?).bind id |>.getD c)
            -- an alias of another interface's type is exported as imported
            | _ => pure c
      let s ← get
      set { s with secs := s.secs.push (.exports [⟨⟨n, .plain0⟩, ⟨.type, c'⟩, none⟩]), cT := s.cT + 1,
                   cnames := ((sc, n), s.cT) :: s.cnames }
      m2 := m2.set! l (some s.cT)
    let mut l := 0
    for d in ds do
      match d with
      | .type t =>
        let t' ← (remapD (m2.toList.map (·.getD 0)) t : Except String _)
        let c ← cbDef t'
        m2 := m2.set! l (some c)
        l := l + 1
      | .alias _ | .export _ (.type _) => l := l + 1
      | _ => pure ()
    for (n, f, k) in fnImps do
      let t ← (idx m2 k : Except String _)
      modify fun s => { s with secs := s.secs.push (.exports [⟨⟨n, .plain0⟩, ⟨.func, f⟩, some (.func t)⟩]) }
    pure (tyImps.toList.map (·.1), fnImps.toList.map (·.1))
  let ((tns, fns), st) ← go.run {}
  pure (st.secs.toList, tns, fns)

mutual
/-- A resolved WIT type as a top-level value type: named types through `names`. -/
def valType (names : List ((Scope × String) × Nat)) (sc : Scope) : Ty → TyM Silmaril.Wasm.Component.Binary.ValType
  | .prim p => pure (.prim p)
  | .ref r => match lookupIdx (refKey sc r) names with
    | some i => pure (.idx i)
    | none => throw s!"named type {r.name} has no type index"
  | .own r => match lookupIdx (refKey sc r) names with
    | some i => intern (.own i)
    | none => throw s!"resource {r.name} has no type index"
  | .borrow r => match lookupIdx (refKey sc r) names with
    | some i => intern (.borrow i)
    | none => throw s!"resource {r.name} has no type index"
  | .list t => do intern (.list (← valType names sc t))
  | .option t => do intern (.option (← valType names sc t))
  | .result ok err => do intern (.result (← optType names sc ok) (← optType names sc err))
  | .tuple ts => do intern (.tuple (← valTypes names sc ts))
  | .stream t => do intern (.stream (← optType names sc t))
  | .future t => do intern (.future (← optType names sc t))
  | .map k v => do intern (.map (← valType names sc k) (← valType names sc v))
  | .fixedList t n => do intern (.fixedList (← valType names sc t) n)
def optType (names : List ((Scope × String) × Nat)) (sc : Scope) : Option Ty → TyM (Option Silmaril.Wasm.Component.Binary.ValType)
  | none => pure none
  | some t => some <$> valType names sc t
def valTypes (names : List ((Scope × String) × Nat)) (sc : Scope) : List Ty → TyM (List Silmaril.Wasm.Component.Binary.ValType)
  | [] => pure []
  | t :: ts => do
    let a ← valType names sc t
    let b ← valTypes names sc ts
    pure (a :: b)
end

/-- The type of a stream or future. -/
def chanTy : Chan → Ty
  | .stream t => .stream t
  | .future t => .future t

/-- Run a type computation against the final type state (whose memo already holds it). -/
def tyIdx (ts : TS) (m : TyM Silmaril.Wasm.Component.Binary.ValType) : Except String Nat :=
  match m.run ts with
  | .ok (.idx i, _) => pure i
  | .ok _ => throw "internal: not a defined type"
  | .error e => throw e

def tyOpt (ts : TS) (m : TyM (Option Silmaril.Wasm.Component.Binary.ValType)) : Except String (Option Silmaril.Wasm.Component.Binary.ValType) :=
  match m.run ts with
  | .ok (r, _) => pure r
  | .error e => throw e

/-- The core function of a request (memory `mem`, allocator `ra`). -/
def reqFunc (wf : WorldFull) (names : List ((Scope × String) × Nat)) (ts : TS)
    (mem ra : Option Nat) : IReq → Except String XSection
  | .lower i sc f async => do
    let mo := (mem.map CanonOpt.memory).toList
    let ro := if ← resultMemR (rho wf) sc f then (ra.map CanonOpt.realloc).toList else []
    pure (.sec (.canons [.lower i (mo ++ ro ++ (if async then [.async] else []))]))
  | .taskReturn sc f => do
    let r ← tyOpt ts (optType names sc f.result)
    pure (.builtins [.taskReturn r (mem.map CanonOpt.memory).toList])
  | .resNew r => do
    let some t := lookupIdx r names | throw s!"resource {r.2} has no type index"
    pure (.sec (.canons [.resourceNew t]))
  | .resRep r => do
    let some t := lookupIdx r names | throw s!"resource {r.2} has no type index"
    pure (.sec (.canons [.resourceRep t]))
  | .resDrop r ex => do
    -- the names table lists the latest definitions first: an exported interface's resource
    -- (its replay) before the imported interface's of the same name (aliased earlier)
    let some t := (if ex then lookupIdx r names else lookupLastIdx r names)
      | throw s!"resource {r.2} has no type index"
    pure (.sec (.canons [.resourceDrop t]))
  | .chan op async sc c _ => do
    let t ← tyIdx ts (valType names sc (chanTy c))
    let payloadMem ← match c with
      | .stream (some p) | .future (some p) => usesMemR (rho wf) flatFuel sc p
      | _ => pure false
    let opts := (mem.map CanonOpt.memory).toList ++
      (if payloadMem then (ra.map CanonOpt.realloc).toList else []) ++
      (if async then [CanonOpt.async] else [])
    let b : Builtin := match op, c with
      | .new, .stream _ => .streamNew t
      | .read, .stream _ => .streamRead t opts
      | .write, .stream _ => .streamWrite t opts
      | .cancelRead, .stream _ => .streamCancelRead t async
      | .cancelWrite, .stream _ => .streamCancelWrite t async
      | .dropReadable, .stream _ => .streamDropReadable t
      | .dropWritable, .stream _ => .streamDropWritable t
      | .new, .future _ => .futureNew t
      | .read, .future _ => .futureRead t opts
      | .write, .future _ => .futureWrite t opts
      | .cancelRead, .future _ => .futureCancelRead t async
      | .cancelWrite, .future _ => .futureCancelWrite t async
      | .dropReadable, .future _ => .futureDropReadable t
      | .dropWritable, .future _ => .futureDropWritable t
    pure (.builtins [b])
  | .gen r => New.reqFunc ts mem ra r

/-- The options of `canon lift` of export `x`. -/
def liftOpts (wf : WorldFull) (mem ra : Option Nat) (x : XFn) (postRet callback : Option Nat) :
    Except String (List CanonOpt) := do
  let um ← liftUsesMemoryR (rho wf) x.sc x.f
  let nr ← needsReallocR (rho wf) x.sc x.f
  let mo := if um then (mem.map CanonOpt.memory).toList else []
  let ro := if nr then (ra.map CanonOpt.realloc).toList else []
  let po := (postRet.map CanonOpt.postReturn).toList
  let ao := if x.f.async then CanonOpt.async :: (callback.map CanonOpt.callback).toList else []
  pure (mo ++ ro ++ po ++ ao)

/-- A shim slot: a request needing memory, or the destructor of an exported resource. -/
inductive Slot where
  | req (r : IReq)
  | dtor (r : Scope × String) (core : String)

/-- The core type of a slot. -/
def Slot.coreTy (wf : WorldFull) : Slot → Except String CoreFuncTy
  | .req r => r.coreTy wf
  | .dtor _ _ => pure ⟨[ti32], []⟩

/-- **The component** of a plan. -/
def emit (p : Plan) : Except String XAst := do
  let wf := p.wf
  let viaShim ← p.reqs.mapM fun (_, r) => r.usesMem wf
  let reqSlots : List Slot := ((p.reqs.map (·.2)).zip viaShim).filterMap fun (r, b) =>
    if b then some (.req r) else none
  let dtorSlots : List Slot := p.dtors.filterMap fun (r, d) => d.map (.dtor r)
  let slots := reqSlots ++ dtorSlots
  let slotTys ← slots.mapM (·.coreTy wf)
  let shim := !slots.isEmpty
  -- the world's declarations at the top level
  let (declSecs, x0) ← copyDecls {} (plainComp wf.decls)
  let go : StateT Idx EM Unit := do
    addSec (.sec (.coreModule p.core))
    if shim then
      addSec (.sec (.coreModule (← (mustEncode "shim" (shimMod slotTys).encode))))
      let _ ← coreInst (.instantiate 1 [])
    for s in declSecs do addSec (.sec s)
    set x0
    -- aliases of the imported interfaces' types and functions
    for i in ifaces wf do
      if i.imported then
        let some j := lookupIdx (keyName i.key) (← get).instOf
          | (throw s!"imported interface {keyName i.key} has no instance")
        for t in i.body.types do
          if (lookupIdx (Scope.iface i.key, t.name) (← get).names).isNone then
            addSec (.sec (.aliases [⟨.type, .export j t.name⟩]))
            modify fun x =>
              { x with types := x.types + 1, names := ((Scope.iface i.key, t.name), x.types) :: x.names }
        for f in i.body.funcs do
          addSec (.sec (.aliases [⟨.func, .export j (fname f)⟩]))
          modify fun x => { x with funcs := x.funcs + 1 }
    -- the destructors, through the shim
    let mut dtorIdx : List ((Scope × String) × Nat) := []
    let mut dk := reqSlots.length
    for s in dtorSlots do
      match s with
      | .dtor r _ =>
        let c ← aliasCoreFunc 0 (toString dk)
        dtorIdx := dtorIdx ++ [(r, c)]
        dk := dk + 1
      | .req _ => pure ()
    -- the exported interfaces' types and function types
    let mut replays : List (Iface × Replay × List InstanceDecl) := []
    for i in ifaces wf do
      if !i.imported then
        let some ti := lookupIdx (keyName i.key) (← get).expInst
          | (throw s!"exported interface {keyName i.key} has no instance type")
        let some (DefType.instance ds) := ((← get).defs.find? (·.1 == ti)).map (·.2)
          | (throw s!"exported interface {keyName i.key}: type {ti} is not an instance type")
        let dt : String → Option Nat := fun n => lookupIdx (Scope.iface i.key, n) dtorIdx
        let (x', r) ← (replay (.iface i.key) dt (← get) [] {} ds)
        set x'
        for s in r.secs do addSec (.sec s)
        replays := replays ++ [(i, r, ds)]
    -- types for task.return and the streams and futures
    let x ← get
    let names := x.names
    let ts0 : TS := { types := Array.replicate x.types (.val (.prim .bool)) }
    let ((), ts) ← ((do
      for (_, r) in p.reqs do
        match r with
        | .taskReturn sc f => do let _ ← optType names sc f.result
        | .chan _ _ sc c _ => do let _ ← valType names sc (chanTy c)
        | _ => pure ()
      : TyM Unit).run ts0)
    let fresh := ts.types.toList.drop x.types
    if !fresh.isEmpty then
      addSec (.sec (.types fresh))
      modify fun x => { x with types := x.types + fresh.length }
    -- one core function per core import
    let mut fs : Array Nat := #[]
    let mut slot := 0
    for k in List.range p.reqs.length do
      let r := (p.reqs[k]!).2
      if viaShim[k]! then
        fs := fs.push (← aliasCoreFunc 0 (toString slot))
        slot := slot + 1
      else
        fs := fs.push (← coreFunc (← (reqFunc wf names ts none none r)))
    -- inline instances per module name, then the main instance
    let mnames := moduleNames (p.reqs.map (·.1))
    let mut args : List (String × Nat) := []
    for mn in mnames do
      let es := ((List.range p.reqs.length).filter fun k => (p.reqs[k]!).1.1 == mn).map fun k =>
        ((p.reqs[k]!).1.2, (⟨.func, fs[k]!⟩ : CoreSortIdx))
      args := args ++ [(mn, ← coreInst (.exports es))]
    let main ← coreInst (.instantiate 0 args)
    let mem : Option Nat := p.memory.map fun _ => 0
    if let some mname := p.memory then
      addSec (.sec (.aliases [⟨.core .memory, .coreExport main mname⟩]))
    let ra ← match p.realloc with
      | some n => some <$> aliasCoreFunc main n
      | none => pure none
    -- the indirect pattern: the real functions, then the fixup instance
    if shim then
      let mut real : List (String × CoreSortIdx) := []
      let mut i := 0
      for s in slots do
        let f ← match s with
          | .req r => coreFunc (← (reqFunc wf names ts mem ra r))
          | .dtor _ c => aliasCoreFunc main c
        real := real ++ [(toString i, ⟨.func, f⟩)]
        i := i + 1
      let actual ← coreInst (.exports real)
      addSec (.sec (.coreModule (← (mustEncode "fixup" (fixupMod slotTys).encode))))
      let _ ← coreInst (.instantiate 2 [("actual", actual), ("shim", 0)])
    -- lifts
    let liftOne (x : XFn) (l : Lift) (ty : Nat) : StateT Idx EM Nat := do
      let (cf, pr, cb) ← match l with
        | .sync c pr => do
          let a ← aliasCoreFunc main c
          let b ← match pr with
            | some n => some <$> aliasCoreFunc main n
            | none => pure none
          pure (a, b, none)
        | .stackful c => do pure (← aliasCoreFunc main c, none, none)
        | .callback c cbn => do
          let a ← aliasCoreFunc main c
          let b ← aliasCoreFunc main cbn
          pure (a, none, some b)
      let opts ← (liftOpts wf mem ra x pr cb)
      addSec (.sec (.canons [.lift cf opts ty]))
      let s ← get
      set { s with funcs := s.funcs + 1 }
      pure s.funcs
    let pairs := p.fns.zip p.lifts
    for (x, l) in pairs do
      if x.sc = .world then
        let some ty := lookupIdx x.core (← get).expFunc
          | (throw s!"world export {x.core} has no function type")
        let fi ← liftOne x l ty
        addSec (.sec (.exports [⟨⟨x.core, .plain0⟩, ⟨.func, fi⟩, none⟩]))
        modify fun s => { s with funcs := s.funcs + 1 }
    for (i, r, ds) in replays do
      let mut fargs : List (String × SortIdx) := []
      for (x, l) in pairs do
        if x.sc = .iface i.key then
          let some ty := lookupIdx (fname x.f) r.funcs
            | (throw s!"{keyName i.key}: no function type for {fname x.f}")
          let fi ← liftOne x l ty
          fargs := fargs ++ [(funcImportName (fname x.f), ⟨.func, fi⟩)]
      let (csecs, tns, _) ← (shimComp wf (.iface i.key) ds : Except String _)
      let targs ← tns.mapM fun n => match lookupIdx n r.types with
        | some t => pure ("import-type-" ++ n, (⟨.type, t⟩ : SortIdx))
        | none => (throw s!"{keyName i.key}: no type index for {n}" : Except String _)
      addSec (.sec (.component ⟨csecs⟩))
      let s ← get
      set { s with comps := s.comps + 1 }
      addSec (.sec (.instances [.instantiate s.comps (targs ++ fargs)]))
      let s ← get
      set { s with insts := s.insts + 1 }
      addSec (.sec (.exports [⟨⟨keyName i.key, .plain0⟩, ⟨.instance, s.insts⟩, none⟩]))
      modify fun s => { s with insts := s.insts + 1 }
  let (((), _), e) ← (go.run {}).run {}
  pure ⟨e.secs.toList⟩

/-- The bytes of the component of a plan. -/
def new (core : ByteArray) (wf : WorldFull) : Except String ByteArray := do
  let p ← plan core wf
  let c ← emit p
  mustEncode "the component" c.encode

end Silmaril.Wasm.JcoTool.NewI
