module

public import Silmaril.Wasm.Component.Reference.Instantiate.Items.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Builtin.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Defs
public import Silmaril.Wasm.Component.Reference.Types.Basic.Defs
public import Silmaril.Wasm.Component.Reference.Value.Basic.Defs
public import Silmaril.Wasm.Component.Reference.Validation.Context.Defs
public import Silmaril.Wasm.Component.Reference.Engine.Mock.Defs
public import Silmaril.Wasm.V1.ToCore.Types

/-!
# Instantiation-time runtime values and resolution of canonical immediates

The run-time index spaces of component instantiation (Explainer.md, "Index
Spaces" and "Instance Definitions") and the resolution of the index immediates of `canon`
definitions against them. There is no upstream function for this: the Python reference
(`design/mvp/canonical-abi/definitions.py` at component-model `a25fc0b`,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>)
receives already-resolved `CanonicalOptions` (L608-613), `ResourceType`s and core functions
in `canon_*`, `Store.lift` and `Store.lower`; the resolution step corresponds to wasmtime's
inliner (`crates/environ/src/component/translate/inline.rs` at wasmtime `a7b4f29`: the
`*Def` item values, `ExtractMemory`/`ExtractRealloc`/`ExtractPostReturn`/`ExtractCallback`,
and the import vector of `GlobalInitializer::InstantiateModule`).

Provided:

* (from `Instantiate/Items.lean`) `ItemVal E`, `Closure E`, `Frame E`: the value of each
  component index space at run time. Core entities are engine addresses/extern values; component
  functions are `FuncId`s; types are semantic types over resource-type identities
  `Types.TypeDef RtId E.ExternType`; a component is a closure over its enclosing frames
  (innermost first). `Frame.empty`, per-sort lookups (`coreFunc?`, ..., `component?`), the
  sort-indexed `Frame.size`/`Frame.get?`/`Frame.push` over `Entry E`, with `get?_push`,
  `size_push`, `get?_push_lt` and `get?_push_ne`.
* `resolveValType?`, `resolveDefValType?`, `resolveFuncType?`: syntactic value/function types
  to closed WIT types over `RtId` (a type index must denote a value type; the index of
  `own`/`borrow` must denote a resource type; a `map` key must resolve to a key primitive).
* `resolveOpts?`: `canonopt` lists to `CanonOpts E` (memory index → `E.MemAddr` via
  `coreMems` and `E.asMemory?`; realloc/post-return/callback → `E.FuncAddr`); a list with two
  options of the same kind (two string encodings count as the same kind) is rejected
  (`resolveOpts?_eq_none_of_not_nodup`, `nodup_of_resolveOpts?_eq_some`).
* `resolveBuiltin?`: `Syntax.Builtin` to `Runtime.ResolvedBuiltin E`, carrying exactly the
  `Runtime.ResolvedBuiltin` immediates; `resolveLift?`, `resolveLower?` for `canon lift`/`canon
  lower`.
* `coreImportsFor?`: the positional import vector of a core module (for each
  `(module, name, type)` of `E.importTypes m` in declaration order: the core-instance
  argument named `module`, its export `name`, whose type `E.externType?` must be an
  `E.ExternSub`-subtype of the declared type), with `coreImportsFor_length` and the
  relational characterisation `coreImportsFor?_eq_some_iff`.
* Resolution of instance and component types (Explainer.md, "Type Definitions" and
  "Declarators"): `resolveDefType?`, `resolveInstanceDecl(s)?`, `resolveComponentDecl(s)?` over
  the per-scope state `TyScope E` (local index spaces, ∀-binders and imports, ∃-binders and
  exports), `descEntity?` (the entity type of an `externdesc` and the binders it introduces)
  and `pushEntityType`. Binders are the reserved identities `binderVar k = ⟨binderBase + k⟩`
  with `binderBase = 2 ^ 32`; this assumes the store allocates fewer than `2 ^ 32` resource
  types (not proved). A standalone instance type used in import or export position is
  freshened and its binders hoisted to the enclosing scope (`freshenInstance`). Unsupported
  declarators (`alias export`/`alias core export` inside a type, 🪙 value descriptors) make
  resolution fail (`none`); callers fall back to an empty placeholder type
  (`Instantiate.staticType?`). `coreTypeSlots`: core type definitions as frame slots, one per
  recursion group member (core module types are inert placeholders).
* Run-time item typing: `itemEntity?`/`itemEntities`, the entity type of an item value
  (functions from their `CFuncInst`, types, instances of those); core modules and components
  are typed by sort only (empty placeholder types); 🪙 values and unallocated function ids are
  untyped (`none`) and dropped from instance types.
* Kernel tests (`Tests`): canonical-option, value-type, builtin and core-import resolution,
  and the type-resolution tests `instType_resolve`, `instType_func`, `instType_bad_outer` and
  `desc_freshen`.

Design notes:
* Fallible functions carry the `?` suffix (`resolveOpts?` and so on).
* `Frame.coreTypes` stores `Validation.CoreTypeSlot E.ExternType` (a Core 3.0 recursion group,
  or a core module type over the engine's extern types), mirroring the validation context:
  the engine interface has no translation of Core 3.0 syntax into `E.FuncType`.
  A recursion group occupies one slot per member (`coreTypeSlots`).
  `thread.new-indirect`'s expected type is read from the member's function type through
  `V1.FuncType.ofCore?` (flat signatures are `V1.FuncType`, as in `ResolvedBuiltin`).
* `coreImportsFor?` also takes the engine store (for `E.externType?`) and a decidability
  instance for `E.ExternSub`.
* `resolveBuiltin?` takes `rep : RtId → Option AddrType` (the representation type of a
  resource type lives in the `CStore`, see `CStore.resourceRep?`), since
  `ResolvedBuiltin.resourceNew`/`resourceRep` carry it.
* `Frame.push` takes an `Entry E` (the value of any sort) and fails on a sort mismatch:
  core functions, tables, memories and globals are checked with `E.asFunc?`-style accessors
  (the constructor for functions, `E.asTable?`/`E.asMemory?`/`E.asGlobal?` for the others);
  tags are not checked (the engine interface has no `asTag?`).
* A `map` key that is a type index naming a primitive key type is accepted (types are
  index-free, so `(type $k u8) (type (map $k u32))` is `map<u8, u32>`), as in
  `Validation/ValTypes.lean`; `Binary.md` says "if k is in `<keytype>`".

NOT modelled here: the instantiation program itself (`Instantiate/Defs.lean`), resource-type
allocation, validation of options against their use
site (which options a builtin admits, `realloc`/`callback` signatures) and of builtin
immediates beyond "the index denotes an entity of the right kind". Resolution success is not
claimed to coincide with validity.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Instantiate

open Engine _root_.Silmaril.Wasm.Component.Runtime
open _root_.Silmaril.Wasm.Component.Validation (CoreTypeSlot)

variable {E : CoreEngine}

/-- Look up an export of an instance's export map (first match). -/
def lookupExport? {α : Type} (exports : List (String × α)) (name : String) : Option α :=
  exports.lookup name

namespace Frame

/-! ### Lookups by index -/

variable (f : Frame E) (i : Nat)

def coreFunc? : Option E.FuncAddr := f.coreFuncs[i]?
def coreTable? : Option E.ExternVal := f.coreTables[i]?
def coreMem? : Option E.ExternVal := f.coreMems[i]?
def coreGlobal? : Option E.ExternVal := f.coreGlobals[i]?
def coreTag? : Option E.ExternVal := f.coreTags[i]?
def coreType? : Option (CoreTypeSlot E.ExternType) := f.coreTypes[i]?
def coreModule? : Option E.Module := f.coreModules[i]?
def coreInstance? : Option (List (String × E.ExternVal)) := f.coreInstances[i]?
def func? : Option FuncId := f.funcs[i]?
def value? : Option Value.Val := f.values[i]?
def type? : Option (Types.TypeDef RtId E.ExternType) := f.types[i]?
def instance? : Option (List (String × ItemVal E)) := f.instances[i]?
def component? : Option (Closure E) := f.components[i]?

/-- The memory address of core memory index `i`. -/
def memAddr? : Option E.MemAddr := (f.coreMem? i).bind E.asMemory?

/-- The table address of core table index `i`. -/
def tableAddr? : Option E.TableAddr := (f.coreTable? i).bind E.asTable?

/-- The resource type denoted by type index `i`. -/
def resourceType? : Option RtId :=
  match f.type? i with
  | some (.resource r) => some r
  | _ => none

/-- The flat function type denoted by core type index `i`: a recursion group member whose
body is a numeric function type (`V1.FuncType.ofCore?`; finality and supertypes are not
inspected, as in validation's `startParam?`). -/
def coreFuncType? : Option V1.FuncType :=
  ((f.coreType? i).bind CoreTypeSlot.funcType?).bind V1.FuncType.ofCore?

end Frame

/-! ### Sort-indexed access -/

/-- The value of an entry of any index space. Component-level sorts (and core modules) are
`item`s. -/
inductive Entry (E : CoreEngine) where
  | coreFunc (a : E.FuncAddr)
  /-- A core table, memory, global or tag. -/
  | coreExtern (x : E.ExternVal)
  | coreType (t : CoreTypeSlot E.ExternType)
  | coreInstance (exports : List (String × E.ExternVal))
  | item (v : ItemVal E)

/-- The entry of an aliased core export of sort `s` (`alias core export`): functions,
memories, tables and globals must be of that kind; tags are taken as they are. -/
def Entry.ofExtern? (s : Syntax.CoreSort) (x : E.ExternVal) : Option (Entry E) :=
  match s with
  | .func => (E.asFunc? x).map .coreFunc
  | .memory => (E.asMemory? x).map fun _ => .coreExtern x
  | .table => (E.asTable? x).map fun _ => .coreExtern x
  | .global => (E.asGlobal? x).map fun _ => .coreExtern x
  | .tag => some (.coreExtern x)
  | .type | .module_ | .instance_ => none

namespace Frame

/-- The number of entries of sort `s`. -/
def size (f : Frame E) : Syntax.Sort_ → Nat
  | .core .func => f.coreFuncs.length
  | .core .table => f.coreTables.length
  | .core .memory => f.coreMems.length
  | .core .global => f.coreGlobals.length
  | .core .tag => f.coreTags.length
  | .core .type => f.coreTypes.length
  | .core .module_ => f.coreModules.length
  | .core .instance_ => f.coreInstances.length
  | .func => f.funcs.length
  | .value => f.values.length
  | .type => f.types.length
  | .component => f.components.length
  | .instance_ => f.instances.length

/-- The entry at index `i` of sort `s`. -/
def get? (f : Frame E) : Syntax.Sort_ → Nat → Option (Entry E)
  | .core .func, i => (f.coreFunc? i).map .coreFunc
  | .core .table, i => (f.coreTable? i).map .coreExtern
  | .core .memory, i => (f.coreMem? i).map .coreExtern
  | .core .global, i => (f.coreGlobal? i).map .coreExtern
  | .core .tag, i => (f.coreTag? i).map .coreExtern
  | .core .type, i => (f.coreType? i).map .coreType
  | .core .module_, i => (f.coreModule? i).map (.item ∘ .coreModule)
  | .core .instance_, i => (f.coreInstance? i).map .coreInstance
  | .func, i => (f.func? i).map (.item ∘ .func)
  | .value, i => (f.value? i).map (.item ∘ .value)
  | .type, i => (f.type? i).map (.item ∘ .type)
  | .component, i => (f.component? i).map (.item ∘ .component)
  | .instance_, i => (f.instance? i).map (.item ∘ .instance)

/-- Push an entry onto the index space of sort `s` (every definition that creates an index
does this); `none` when the entry does not belong to that sort. Tables, memories and globals
are checked with `E.asTable?`/`E.asMemory?`/`E.asGlobal?`; tags are not checked (the engine
interface has no `asTag?`). -/
def push (f : Frame E) : Syntax.Sort_ → Entry E → Option (Frame E)
  | .core .func, .coreFunc a => some { f with coreFuncs := f.coreFuncs ++ [a] }
  | .core .table, .coreExtern x =>
    (E.asTable? x).map fun _ => { f with coreTables := f.coreTables ++ [x] }
  | .core .memory, .coreExtern x =>
    (E.asMemory? x).map fun _ => { f with coreMems := f.coreMems ++ [x] }
  | .core .global, .coreExtern x =>
    (E.asGlobal? x).map fun _ => { f with coreGlobals := f.coreGlobals ++ [x] }
  | .core .tag, .coreExtern x => some { f with coreTags := f.coreTags ++ [x] }
  | .core .type, .coreType t => some { f with coreTypes := f.coreTypes ++ [t] }
  | .core .module_, .item (.coreModule m) => some { f with coreModules := f.coreModules ++ [m] }
  | .core .instance_, .coreInstance es =>
    some { f with coreInstances := f.coreInstances ++ [es] }
  | .func, .item (.func g) => some { f with funcs := f.funcs ++ [g] }
  | .value, .item (.value v) => some { f with values := f.values ++ [v] }
  | .type, .item (.type t) => some { f with types := f.types ++ [t] }
  | .component, .item (.component c) => some { f with components := f.components ++ [c] }
  | .instance_, .item (.instance es) => some { f with instances := f.instances ++ [es] }
  | _, _ => none

end Frame

/-- The representation address type of a resource type in the component store. -/
def _root_.Silmaril.Wasm.Component.Runtime.CStore.resourceRep? (s : CStore E) (r : RtId) :
    Option AddrType :=
  (s.resourceType? r).map (·.rep)

/-! ## Resolution of value and function types -/

/-- A syntactic primitive as a closed WIT type. -/
def primType {R : Type} : Syntax.Prim → WIT.ClosedType R
  | .bool => .prim .bool
  | .s8 => .prim .s8
  | .u8 => .prim .u8
  | .s16 => .prim .s16
  | .u16 => .prim .u16
  | .s32 => .prim .s32
  | .u32 => .prim .u32
  | .s64 => .prim .s64
  | .u64 => .prim .u64
  | .f32 => .prim .f32
  | .f64 => .prim .f64
  | .char => .prim .char
  | .string => .prim .string
  | .errorContext => .errorContext

/-- The `map` key type of a closed type, if it is a key primitive (not a float). -/
def keyType? {R : Type} : WIT.ClosedType R → Option WIT.KeyType
  | .prim .bool => some .bool
  | .prim .u8 => some .u8
  | .prim .u16 => some .u16
  | .prim .u32 => some .u32
  | .prim .u64 => some .u64
  | .prim .s8 => some .s8
  | .prim .s16 => some .s16
  | .prim .s32 => some .s32
  | .prim .s64 => some .s64
  | .prim .char => some .char
  | .prim .string => some .string
  | _ => none

/-- A `valtype`: a primitive, or a type index that must denote a value type. -/
def resolveValType? (f : Frame E) : Syntax.VT → Option (WIT.ClosedType RtId)
  | .prim p => some (primType p)
  | .idx i =>
    match f.type? i with
    | some (.val t) => some t
    | _ => none

/-- An optional `valtype`. -/
def resolveOptValType? (f : Frame E) : Option Syntax.VT → Option (Option (WIT.ClosedType RtId))
  | none => some none
  | some t => (resolveValType? f t).map some

/-- A `defvaltype`. `own`/`borrow` indices must denote resource types; `map` keys must resolve
to key primitives. Deviation (shared with `Validation/ValTypes.lean`): a key given as a type
index naming a primitive key type is accepted, whereas `Binary.md` requires `k ∈ <keytype>`
syntactically. -/
def resolveDefValType? (f : Frame E) : Syntax.DefValType → Option (WIT.ClosedType RtId)
  | .prim p => some (primType p)
  | .record fs => .record <$> fs.mapM fun (n, t) => (n, ·) <$> resolveValType? f t
  | .variant cs => .variant <$> cs.mapM fun (n, t) => (n, ·) <$> resolveOptValType? f t
  | .list t => .list <$> resolveValType? f t
  | .fixedList t n => (.fixedList · n) <$> resolveValType? f t
  | .tuple ts => .tuple <$> ts.mapM (resolveValType? f)
  | .flags ls => some (.flags ls)
  | .enum ls => some (.enum ls)
  | .option t => .option <$> resolveValType? f t
  | .result ok err => do
    let ok ← resolveOptValType? f ok
    let err ← resolveOptValType? f err
    some (.result ok err)
  | .map k v => do
    let k ← (resolveValType? f k).bind keyType?
    let v ← resolveValType? f v
    some (.map k v)
  | .own r => .own <$> f.resourceType? r
  | .borrow r => .borrow <$> f.resourceType? r
  | .stream t => .stream <$> resolveOptValType? f t
  | .future t => .future <$> resolveOptValType? f t

/-- A `functype`. -/
def resolveFuncType? (f : Frame E) (t : Syntax.FuncType) : Option (Types.FuncType RtId) := do
  let params ← t.params.mapM fun (n, p) => (n, ·) <$> resolveValType? f p
  let result ← resolveOptValType? f t.result
  some { params, result, async_ := t.async_ }

/-- The function type denoted by type index `i`. -/
def funcTypeAt? (f : Frame E) (i : Nat) : Option (Types.FuncType RtId) :=
  match f.type? i with
  | some (.func t) => some t
  | _ => none

/-- The element type of the `stream` type denoted by type index `i`. -/
def streamElem? (f : Frame E) (i : Nat) : Option (Option (WIT.ClosedType RtId)) :=
  match f.type? i with
  | some (.val (.stream e)) => some e
  | _ => none

/-- The element type of the `future` type denoted by type index `i`. -/
def futureElem? (f : Frame E) (i : Nat) : Option (Option (WIT.ClosedType RtId)) :=
  match f.type? i with
  | some (.val (.future e)) => some e
  | _ => none

/-! ## Canonical options -/

/-- The kind of a `canonopt`; all string encodings are one kind (they are mutually
exclusive). -/
def canonOptKind : Syntax.CanonOpt → Nat
  | .encoding _ => 0
  | .memory _ => 1
  | .realloc _ => 2
  | .postReturn _ => 3
  | .async_ => 4
  | .callback _ => 5

/-- Apply one option to partially resolved options. -/
def applyOpt (f : Frame E) (o : CanonOpts E) : Syntax.CanonOpt → Option (CanonOpts E)
  | .encoding e => some { o with encoding := e }
  | .memory i => (f.memAddr? i).map fun m => { o with memory := some m }
  | .realloc i => (f.coreFunc? i).map fun a => { o with realloc := some a }
  | .postReturn i => (f.coreFunc? i).map fun a => { o with postReturn := some a }
  | .async_ => some { o with async_ := true }
  | .callback i => (f.coreFunc? i).map fun a => { o with callback := some a }

/-- Resolve a `canonopt` list (`canon lift`: the resolved options are the memory address, the
realloc/post-return/callback function addresses, the encoding and async;
wasmtime `Extract*` initializers). Two options of the same kind are rejected. Absent options
take the REF `CanonicalOptions` defaults (utf8, no memory, sync). -/
def resolveOpts? (f : Frame E) (opts : List Syntax.CanonOpt) : Option (CanonOpts E) :=
  if (opts.map canonOptKind).Nodup then opts.foldlM (applyOpt f) {} else none

@[simp] theorem resolveOpts?_nil (f : Frame E) : resolveOpts? f [] = some {} := by
  simp [resolveOpts?]

/-! ## Canonical definitions -/

/-- `canon lift f opts ft`: the core function, the function type (type index `ft` must denote a
function type) and the resolved options. -/
def resolveLift? (f : Frame E) (coreFunc : Nat) (opts : List Syntax.CanonOpt) (ft : Nat) :
    Option (E.FuncAddr × Types.FuncType RtId × CanonOpts E) := do
  let a ← f.coreFunc? coreFunc
  let t ← funcTypeAt? f ft
  let o ← resolveOpts? f opts
  some (a, t, o)

/-- `canon lower g opts`: the component function and the resolved options. -/
def resolveLower? (f : Frame E) (func : Nat) (opts : List Syntax.CanonOpt) :
    Option (FuncId × CanonOpts E) := do
  let g ← f.func? func
  let o ← resolveOpts? f opts
  some (g, o)

/-- Resolve the immediates of a canon built-in (`canon <builtin>`):
resource type indices to `RtId` (with their representation type from `rep`), stream/future
type indices to their element types, `canonopt` lists with `resolveOpts?`, memory indices to
`E.MemAddr`, and `thread.new-indirect`'s core type and table indices to the flat function type
and the `E.TableAddr`. -/
def resolveBuiltin? (rep : RtId → Option AddrType) (f : Frame E) :
    Syntax.Builtin → Option (ResolvedBuiltin E)
  | .resourceNew rt => do
    let r ← f.resourceType? rt
    let a ← rep r
    some (.resourceNew r a)
  | .resourceDrop rt => .resourceDrop <$> f.resourceType? rt
  | .resourceRep rt => do
    let r ← f.resourceType? rt
    let a ← rep r
    some (.resourceRep r a)
  | .backpressureInc => some .backpressureInc
  | .backpressureDec => some .backpressureDec
  | .taskReturn result opts => do
    let r ← resolveOptValType? f result
    let o ← resolveOpts? f opts
    some (.taskReturn r o)
  | .taskCancel => some .taskCancel
  | .contextGet t i => some (.contextGet t i)
  | .contextSet t i => some (.contextSet t i)
  | .subtaskCancel a => some (.subtaskCancel a)
  | .subtaskDrop => some .subtaskDrop
  | .streamNew t => .streamNew <$> streamElem? f t
  | .streamRead t opts => do
    let e ← streamElem? f t
    let o ← resolveOpts? f opts
    some (.streamRead e o)
  | .streamWrite t opts => do
    let e ← streamElem? f t
    let o ← resolveOpts? f opts
    some (.streamWrite e o)
  | .streamCancelRead t a => (.streamCancelRead · a) <$> streamElem? f t
  | .streamCancelWrite t a => (.streamCancelWrite · a) <$> streamElem? f t
  | .streamDropReadable t => .streamDropReadable <$> streamElem? f t
  | .streamDropWritable t => .streamDropWritable <$> streamElem? f t
  | .streamForward t => .streamForward <$> streamElem? f t
  | .futureNew t => .futureNew <$> futureElem? f t
  | .futureRead t opts => do
    let e ← futureElem? f t
    let o ← resolveOpts? f opts
    some (.futureRead e o)
  | .futureWrite t opts => do
    let e ← futureElem? f t
    let o ← resolveOpts? f opts
    some (.futureWrite e o)
  | .futureCancelRead t a => (.futureCancelRead · a) <$> futureElem? f t
  | .futureCancelWrite t a => (.futureCancelWrite · a) <$> futureElem? f t
  | .futureDropReadable t => .futureDropReadable <$> futureElem? f t
  | .futureDropWritable t => .futureDropWritable <$> futureElem? f t
  | .futureForward t => .futureForward <$> futureElem? f t
  | .errorContextNew opts => .errorContextNew <$> resolveOpts? f opts
  | .errorContextDebugMessage opts => .errorContextDebugMessage <$> resolveOpts? f opts
  | .errorContextDrop => some .errorContextDrop
  | .waitableSetNew => some .waitableSetNew
  | .waitableSetWait mem => .waitableSetWait <$> f.memAddr? mem
  | .waitableSetPoll mem => .waitableSetPoll <$> f.memAddr? mem
  | .waitableSetDrop => some .waitableSetDrop
  | .waitableJoin => some .waitableJoin
  | .threadIndex => some .threadIndex
  | .threadNewIndirect ct tbl => do
    let ft ← f.coreFuncType? ct
    let t ← f.tableAddr? tbl
    some (.threadNewIndirect t ft)
  | .threadResumeLater => some .threadResumeLater
  | .threadSuspend => some .threadSuspend
  | .threadYield => some .threadYield
  | .threadSuspendThenResume => some .threadSuspendThenResume
  | .threadYieldThenResume => some .threadYieldThenResume
  | .threadSuspendThenPromote => some .threadSuspendThenPromote
  | .threadYieldThenPromote => some .threadYieldThenPromote

/-! ## Core instantiation arguments -/

section CoreImports

variable {H : Type} [∀ a b, Decidable (E.ExternSub a b)]

/-- The provided value of one core import `(module, name, type)`: the export `name` of the
core-instance argument named `module`, if its type is a subtype of `type`. -/
def coreImportFor? (s : E.Store H) (args : List (String × Nat)) (f : Frame E)
    (imp : String × String × E.ExternType) : Option E.ExternVal := do
  let i ← args.lookup imp.1
  let exports ← f.coreInstance? i
  let v ← lookupExport? exports imp.2.1
  let τ ← E.externType? s v
  if E.ExternSub τ imp.2.2 then some v else none

/-- The positional import vector of `core instance (instantiate m args)`
(Explainer.md, "Instance Definitions"): for each import of `m` in declaration order,
`coreImportFor?`. -/
def coreImportsFor? (s : E.Store H) (m : E.Module) (args : List (String × Nat)) (f : Frame E) :
    Option (List E.ExternVal) :=
  (E.importTypes m).mapM (coreImportFor? s args f)

/-- The relational reading of one import. -/
def CoreImportOk (s : E.Store H) (args : List (String × Nat)) (f : Frame E)
    (imp : String × String × E.ExternType) (v : E.ExternVal) : Prop :=
  ∃ i exports τ, args.lookup imp.1 = some i ∧ f.coreInstance? i = some exports ∧
    lookupExport? exports imp.2.1 = some v ∧ E.externType? s v = some τ ∧
    E.ExternSub τ imp.2.2

end CoreImports

/-! ## Resolution of instance and component types -/

section TypeResolution

/-- The reserved range of binder identities: the ∃/∀-bound resource variables of resolved
instance and component types are the resource identities `⟨binderBase + k⟩`. Real resource
types are arena indices of the component store, so the two never meet in runs that allocate
fewer than `2 ^ 32` resource types (an assumption, not a proved invariant). -/
def binderBase : Nat := 2 ^ 32

/-- The `k`-th binder identity. -/
def binderVar (k : Nat) : RtId := ⟨binderBase + k⟩

/-- A semantic entity type over resource identities and the engine's core extern types. -/
abbrev EntityT (E : CoreEngine) := Types.Entity RtId E.ExternType

/-- The position of `r` in `bs`. -/
def binderIdx? (r : RtId) : List RtId → Option Nat
  | [] => none
  | b :: bs => if b = r then some 0 else (binderIdx? r bs).map (· + 1)

/-- Send the `i`-th binder of `bs` to `binderVar (next + i)`; other identities are kept. -/
def renameBinders (bs : List RtId) (next : Nat) (r : RtId) : RtId :=
  match binderIdx? r bs with
  | some i => binderVar (next + i)
  | none => r

/-- Use a standalone instance type (∃-binders `defined`) in import or export position: its
binders are renamed to fresh identities from `next` on and hoisted to the enclosing scope
(the instance type keeps `defined = []`, the form of `Types/Basic.lean`'s binder convention).
Returns the instance type, the new binders and the next free binder number. -/
def freshenInstance (it : Types.InstanceType RtId E.ExternType) (next : Nat) :
    Types.InstanceType RtId E.ExternType × List RtId × Nat :=
  let it' := it.map (renameBinders it.defined next)
  (⟨[], it'.exports⟩, it'.defined, next + it.defined.length)

/-- A core type definition as frame slots after the slots `prev`: one per member of a
recursion group, with its closed defined type, as in validation (`Validation.Ctx.pushCoreRec`).
Core module types are runtime-inert placeholders: the engine interface has no translation of
Core 3.0 extern types into `E.ExternType`. -/
def coreTypeSlots (prev : List (CoreTypeSlot E.ExternType)) :
    Syntax.CoreTypeDef → List (CoreTypeSlot E.ExternType)
  | .rec_ t => CoreTypeSlot.ofRec prev t
  | .module_ _ => [.module_ ⟨[], []⟩]

/-- The entity type described by an `externdesc` in frame `f`, with the binders it introduces
and the next free binder number: `func i`, `component i` and `instance i` read type index `i`
(an instance type is freshened, `freshenInstance`), `type (eq i)` is the type at index `i`,
`type (sub resource)` introduces one binder, `core module i` reads core type index `i` (a
placeholder module type, see `coreTypeSlots`). 🪙 value descriptors are not modelled
(`none`). -/
def descEntity? (f : Frame E) (next : Nat) :
    Syntax.ExternDesc → Option (EntityT E × List RtId × Nat)
  | .coreModule i =>
    match f.coreType? i with
    | some (.module_ mt) => some (.module mt, [], next)
    | _ => none
  | .func i => (funcTypeAt? f i).map fun t => (.func t, [], next)
  | .value _ => none
  | .type (.eq i) => (f.type? i).map fun t => (.type t, [], next)
  | .type .subResource => some (.type (.resource (binderVar next)), [binderVar next], next + 1)
  | .instance_ i =>
    match f.type? i with
    | some (.instance it) =>
      let (it', bs, n) := freshenInstance it next
      some (.instance it', bs, n)
    | _ => none
  | .component i =>
    match f.type? i with
    | some (.component ct) => some (.component ct, [], next)
    | _ => none

/-- An exported or imported type entity adds an entry to the type index space of the scope
(Explainer.md, "Declarators": `(export "t" (type ...))` in a type introduces a type
index);
entities of other sorts leave the frame unchanged. -/
def pushEntityType (f : Frame E) : EntityT E → Frame E
  | .type t => { f with types := f.types ++ [t] }
  | _ => f

/-- The state of the resolution of one instance or component type scope: the local index
spaces, the ∀-binders and imports (component types only), the ∃-binders and exports, and the
next free binder number. -/
structure TyScope (E : CoreEngine) where
  frame : Frame E := Frame.empty
  imported : List RtId := []
  imports : List (String × EntityT E) := []
  defined : List RtId := []
  exports : List (String × EntityT E) := []
  next : Nat := 0

mutual

/-- Resolve a type definition in frame `f` with enclosing frames `outer` (innermost first) and
next free binder number `next` (Explainer.md, "Type Definitions"): value and function types as
`resolveDefValType?`/`resolveFuncType?`; instance and component types by resolving their
declarators in a new scope whose enclosing frames are `f :: outer`. Resource types are not
type *expressions* here (`none`; they are allocated by instantiation). Unsupported declarators
(`alias export`/`alias core export` inside a type, 🪙 value descriptors) make resolution fail. -/
def resolveDefType? (outer : List (Frame E)) (f : Frame E) (next : Nat) :
    Syntax.DefType → Option (Types.TypeDef RtId E.ExternType × Nat)
  | .val d => (resolveDefValType? f d).map fun t => (.val t, next)
  | .func ft => (resolveFuncType? f ft).map fun t => (.func t, next)
  | .resource _ _ => none
  | .instance_ ds =>
    (resolveInstanceDecls? (f :: outer) { next } ds).map fun sc =>
      (.instance ⟨sc.defined, sc.exports⟩, sc.next)
  | .component ds =>
    (resolveComponentDecls? (f :: outer) { next } ds).map fun sc =>
      (.component ⟨sc.imported, sc.imports, sc.defined, sc.exports⟩, sc.next)

/-- One `instancedecl`: a core type, a type definition, an outer alias, or an export (whose
binders become ∃-binders of the scope). -/
def resolveInstanceDecl? (outer : List (Frame E)) (sc : TyScope E) :
    Syntax.InstanceDecl → Option (TyScope E)
  | .coreType t =>
    some { sc with frame := { sc.frame with
      coreTypes := sc.frame.coreTypes ++ coreTypeSlots sc.frame.coreTypes t } }
  | .type t =>
    (resolveDefType? outer sc.frame sc.next t).map fun (td, n) =>
      { sc with frame := { sc.frame with types := sc.frame.types ++ [td] }, next := n }
  | .alias (.outer ct idx s) =>
    match (sc.frame :: outer)[ct]? with
    | none => none
    | some g =>
      match g.get? s idx with
      | none => none
      | some e => (sc.frame.push s e).map fun fr => { sc with frame := fr }
  | .alias _ => none
  | .export_ n d =>
    (descEntity? sc.frame sc.next d).map fun (e, bs, k) =>
      { sc with frame := pushEntityType sc.frame e, defined := sc.defined ++ bs,
                exports := sc.exports ++ [(n.name, e)], next := k }

/-- The declarators of an instance type, in order. -/
def resolveInstanceDecls? (outer : List (Frame E)) (sc : TyScope E) :
    List Syntax.InstanceDecl → Option (TyScope E)
  | [] => some sc
  | d :: ds =>
    match resolveInstanceDecl? outer sc d with
    | none => none
    | some sc' => resolveInstanceDecls? outer sc' ds

/-- One `componentdecl`: an import (whose binders become ∀-binders) or an `instancedecl`. -/
def resolveComponentDecl? (outer : List (Frame E)) (sc : TyScope E) :
    Syntax.ComponentDecl → Option (TyScope E)
  | .import_ n d =>
    (descEntity? sc.frame sc.next d).map fun (e, bs, k) =>
      { sc with frame := pushEntityType sc.frame e, imported := sc.imported ++ bs,
                imports := sc.imports ++ [(n.name, e)], next := k }
  | .decl d => resolveInstanceDecl? outer sc d

/-- The declarators of a component type, in order. -/
def resolveComponentDecls? (outer : List (Frame E)) (sc : TyScope E) :
    List Syntax.ComponentDecl → Option (TyScope E)
  | [] => some sc
  | d :: ds =>
    match resolveComponentDecl? outer sc d with
    | none => none
    | some sc' => resolveComponentDecls? outer sc' ds

end

end TypeResolution

/-! ## Run-time types of item values -/

mutual

/-- The entity type of a run-time item value, where it is computable: a function value has the
type of its `CFuncInst`, a type is itself, an instance has the instance type of its typable
exports (no binders: its resources are concrete identities). Core modules and components
(closures) are typed by their sort only, as the empty placeholder types `module ⟨[], []⟩` and
`component ⟨[], [], [], []⟩` (the import check erases expected module and component types to
the same placeholders, `pruneEntity`, so it compares their sorts: wasmtime's
`TypeChecker::definition` in `crates/wasmtime/src/runtime/component/matching.rs` rejects a
definition of another sort, `expected module found instance`). 🪙 values and unallocated
function ids are not typed (`none`): they are dropped from instance types, and `importTypeCheck`
rejects them where a typed entity is expected. -/
def itemEntity? (s : CStore E) : ItemVal E → Option (EntityT E)
  | .func f => (ArenaField.funcs.get? s f).map fun fi => .func fi.ft
  | .type t => some (.type t)
  | .instance es => some (.instance ⟨[], itemEntities s es⟩)
  | .coreModule _ => some (.module ⟨[], []⟩)
  | .value _ => none
  | .component _ => some (.component ⟨[], [], [], []⟩)

/-- The typable entries of an export map (`itemEntity?`). -/
def itemEntities (s : CStore E) : List (String × ItemVal E) → List (String × EntityT E)
  | [] => []
  | (n, v) :: es =>
    match itemEntity? s v with
    | some e => (n, e) :: itemEntities s es
    | none => itemEntities s es

end

/-! ## Tests (Mock engine) -/

namespace Tests

open Engine.Mock

/-- The adder's function type `func(a: u32, b: u32) -> u32` (`Profiles.adderComponent`). -/
def adderSyntaxType : Syntax.FuncType :=
  { params := [("a", .prim .u32), ("b", .prim .u32)], result := some (.prim .u32) }

def adderType : Types.FuncType RtId :=
  { params := [("a", .prim .u32), ("b", .prim .u32)], result := some (.prim .u32) }

/-- The adder frame after `core instance`, `alias core export 0 "add"` and the function type
definition: one core function (address 7) and one type. -/
def adderFrame : Frame mock :=
  { Frame.empty with coreFuncs := [7], types := [.func adderType] }

/-- A frame with a memory, two core functions, a resource type, a stream type, a u32 type,
a table and the core function type `[i32] → []`. -/
def optFrame : Frame mock :=
  { Frame.empty with
    coreFuncs := [10, 11]
    coreMems := [.memory 3, .func 4]
    coreTables := [.table 2]
    coreTypes := CoreTypeSlot.ofRec [] (V1.FuncType.toCoreRec ⟨[.i32], []⟩)
    types := [.resource ⟨5⟩, .val (.stream (some (.prim .u8))), .val (.prim .u32)] }

/-- A Mock module importing `env.f : [i32] → []` and `env.m` (a memory of at least 1 byte). -/
def importer : Mock.Module :=
  { imports := [("env", "f", .func ⟨[.i32], []⟩), ("env", "m", .memory .i32 1 none)] }

/-- A Mock store with one host function `[i32] → []` and one 4-byte memory. -/
def importStore : Mock.Store Unit :=
  { funcs := [.host ⟨[.i32], []⟩ ()], mems := [⟨.i32, ByteArray.mk #[0, 0, 0, 0]⟩] }

def importFrame : Frame mock :=
  { Frame.empty with
    coreInstances := [[("m", .memory 0), ("f", .func 0)], [("f", .memory 0)]] }

instance (a b : mock.ExternType) : Decidable (mock.ExternSub a b) :=
  inferInstanceAs (Decidable (CoreExternType.Sub a b))

/-- The observable shape of a resolved instance type: binders, export names and their sorts,
and the next binder number. -/
def instShape : Option (Types.TypeDef RtId mock.ExternType × Nat) →
    Option (List RtId × List (String × Types.EntitySort) × Nat)
  | some (.instance it, n) => some (it.defined, it.exports.map fun (k, e) => (k, e.sort), n)
  | _ => none

/-- `(instance (export "t" (type (sub resource))) (alias outer 1 0 type) (export "f" (func 1)))`
in `adderFrame`: one binder, the outer function type reached by the alias. -/
def instDecls : List Syntax.InstanceDecl :=
  [.export_ { name := "t" } (.type .subResource), .alias (.outer 1 0 .type),
    .export_ { name := "f" } (.func 1)]

end Tests

end Silmaril.Wasm.Component.Instantiate
