module

public import Silmaril.Wasm.Component.Binary.Defs
public import Silmaril.Wasm.Component.Reference.Defs
public import Silmaril.Wasm.Spec.Component.RefMulti.Defs
public import Silmaril.Wasm.Resource.Component.Defs
public import Silmaril.Wasi.World.Defs
public import Silmaril.Wasm.Binary.Core.Decode

/-!
# The Wasm components pilot: binary components read by the reference semantics

The pilot's other denotation of a component (`irDen`, `Silmaril.Project.WasmComponents.Code`) goes
through the IR lowering, which rejects resources. This module reads a binary component
(`Silmaril.Wasm.Component.Binary.Ast`) by the **reference semantics** of the Component Model
(`Silmaril.Wasm.Spec.Component`, multi-call traces `refMultiTraces`), which has resources, and turns
its traces into a model of a WASI world (`Silmaril.Wasi.World.Model`), so that the shapes
`silmaril.shapes.component.{wasi_sat,wasi_every_host}` apply to it.

* `toRef? c`: the binary component `c` as a reference component (`Core3Component`), section by
  section; core modules are decoded by silmaril-lean's `Binary.Core.decode?` (the parser of
  `wasm.binary.core`), custom sections are dropped. It is **partial**: nested components,
  component and instance types, core types, `start`, values and the async or thread built-ins
  give `none` (the fragment of Silmaril's generated components).
* `wval`: the WASI view of a reference value. Scalars are kept; an `own r` handle is
  `variant 0 (some (variant r none))` and a `borrow r` handle `variant 1 (some (variant r none))`
  (a WASI `Val` has no handles; the case number carries the unbounded representation `r`);
  every other value (strings, lists, records, variants, flags, streams, futures, error contexts)
  is the placeholder `record []`. `hval` reads a handle back (`hval_wval`).
* `wevOf fnI fnE`: the WASI event of a reference event, the imports and exports named by `fnI`
  and `fnE`; a return carries the result values (`none` for a trap, a cancellation, a deadlock
  or divergence). `strip` forgets the call arguments that a WASI return event repeats (a
  reference return event does not carry them).
* `traceModel W fnI fnE T`: the model of the world `W` generated (`Strategy.generate`) by the
  plays whose events, stripped, are the WASI events of a trace in `T`.
* `refDen P prof h σ0 X args names W fnI fnE c`: the model of `toRef? c` as the reference program
  `⟨_, args, names⟩` at interface `X`, over the multi-call traces of the Core 3.0 engine at
  profile `P` (`core3P P`), choice profile `prof` and host `h`; the least model when `toRef?` fails.
* `hevW fnE new drop`, `provGuar fnE new drop`: the provider handle sentence
  `compProviderSpec new drop` (`Silmaril.Wasm.Resource.Component`) read on WASI events: the return
  of `new` with one `own r` result allocates `r`, a call of `drop` on one `own r` frees `r`,
  another call on one handle uses it.

The transfer theorem (`Silmaril.Project.WasmComponents.Ref.Thms`): a reference program that models
`compProviderSpec new drop` gives a model `traceModel` satisfying `provGuar` under every WASI
theory, hence over every host.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.WasmComponents.Ref

open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Syntax
open Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Component
open Silmaril.Wasm.Component.Reference (Core3Component Host)
open Silmaril.Wasm.Resource (HEv handleProto Protocol compProviderEv)
open Silmaril.Wasi (World FnName WEv wtrace)

/-! ## Binary components as reference components -/

/-- A core sort. -/
def coreSort : Binary.CoreSort → CoreSort
  | .func => .func | .table => .table | .memory => .memory | .global => .global
  | .tag => .tag | .type => .type | .module => .module_ | .instance => .instance_

/-- A sort. -/
def sort : Binary.ItemSort → Sort_
  | .core s => .core (coreSort s)
  | .func => .func | .value => .value | .type => .type | .component => .component
  | .instance => .instance_

/-- A primitive value type. -/
def prim : Binary.PrimValType → Prim
  | .bool => .bool | .s8 => .s8 | .u8 => .u8 | .s16 => .s16 | .u16 => .u16 | .s32 => .s32
  | .u32 => .u32 | .s64 => .s64 | .u64 => .u64 | .f32 => .f32 | .f64 => .f64 | .char => .char
  | .string => .string | .errorContext => .errorContext

/-- A value type. -/
def valType : Binary.ValType → VT
  | .prim p => .prim (prim p)
  | .idx i => .idx i

/-- A defined value type. -/
def defValType : Binary.DefValType → DefValType
  | .prim p => .prim (prim p)
  | .record fs => .record (fs.map fun f => (f.1, valType f.2))
  | .variant cs => .variant (cs.map fun c => (c.1, c.2.map valType))
  | .list t => .list (valType t)
  | .tuple ts => .tuple (ts.map valType)
  | .flags ls => .flags ls
  | .enum ls => .enum ls
  | .option t => .option (valType t)
  | .result a b => .result (a.map valType) (b.map valType)
  | .own i => .own i
  | .borrow i => .borrow i
  | .fixedList t n => .fixedList (valType t) n
  | .stream t => .stream (t.map valType)
  | .future t => .future (t.map valType)
  | .map k v => .map (valType k) (valType v)

/-- A function type. -/
def funcType (f : Binary.FuncType) : FuncType :=
  { async_ := f.async, params := f.params.map fun p => (p.1, valType p.2),
    result := f.result.map valType }

/-- The representation type of a resource: `i32` or `i64`. -/
def addrType : Binary.CoreValType → Option Silmaril.Wasm.AddrType
  | .i32 => some .i32
  | .i64 => some .i64
  | _ => none

/-- A type definition; component and instance types are outside the fragment. -/
def defType : Binary.DefType → Option DefType
  | .val d => some (.val (defValType d))
  | .func f => some (.func (funcType f))
  | .resource rep dtor => (addrType rep).map fun a => .resource a dtor
  | _ => none

/-- A type bound. -/
def typeBound : Binary.TypeBound → TypeBound
  | .eq i => .eq i
  | .subResource => .subResource

/-- A value bound. -/
def valueBound : Binary.ValueBound → ValueBound
  | .eq i => .eq i
  | .type t => .type (valType t)

/-- An extern descriptor. -/
def externDesc : Binary.ExternDesc → ExternDesc
  | .coreModule i => .coreModule i
  | .func i => .func i
  | .value b => .value (valueBound b)
  | .type b => .type (typeBound b)
  | .component i => .component i
  | .instance i => .instance_ i

/-- A name attribute. -/
def attr : Binary.Attribute → Attribute
  | .implements n => .implements n
  | .versionSuffix s => .versionSuffix s
  | .externalId i => .externalId i

/-- An import or export name: the spelling of `nameattributes` is dropped. -/
def externName (n : Binary.ExternName) : ExternName :=
  { name := n.name,
    attrs := match n.form with
      | .attrs as => as.map attr
      | _ => [] }

/-- A canonical option. -/
def canonOpt : Binary.CanonOpt → CanonOpt
  | .utf8 => .encoding .utf8
  | .utf16 => .encoding .utf16
  | .latin1utf16 => .encoding .latin1Utf16
  | .memory i => .memory i
  | .realloc i => .realloc i
  | .postReturn i => .postReturn i
  | .async => .async_
  | .callback i => .callback i

/-- A canonical definition. -/
def canon : Binary.Canon → Canon
  | .lift f opts t => .lift f (opts.map canonOpt) t
  | .lower f opts => .lower f (opts.map canonOpt)
  | .resourceNew t => .builtin (.resourceNew t)
  | .resourceDrop t => .builtin (.resourceDrop t)
  | .resourceRep t => .builtin (.resourceRep t)

/-- An alias; a core export alias must have a core sort, an export alias a component sort. -/
def alias_ (a : Binary.Alias) : Option Alias :=
  match a.sort, a.target with
  | .core s, .coreExport i n => some (.coreExport i n (coreSort s))
  | .core _, .export _ _ => none
  | s, .export i n => some (.export_ i n (sort s))
  | _, .coreExport _ _ => none
  | s, .outer ct i => some (.outer ct i (sort s))

/-- A core sort index. -/
def coreSortIdx (x : Binary.CoreSortIdx) : SortIdx CoreSort := ⟨coreSort x.sort, x.idx⟩

/-- A sort index. -/
def sortIdx (x : Binary.SortIdx) : SortIdx Sort_ := ⟨sort x.sort, x.idx⟩

/-- A core instance. -/
def coreInstance : Binary.CoreInstanceExpr → CoreInstanceExpr
  | .instantiate m args => .instantiate m args
  | .exports es => .exports (es.map fun e => (e.1, coreSortIdx e.2))

/-- A component instance. -/
def instance_ : Binary.InstanceExpr → InstanceExpr
  | .instantiate c args => .instantiate c (args.map fun a => (a.1, sortIdx a.2))
  | .exports es => .exports (es.map fun e => (externName e.1, sortIdx e.2))

/-- An export. -/
def export_ (e : Binary.Export) : Definition Silmaril.Wasm.Module :=
  .export_ (externName e.name) (sortIdx e.item) (e.desc.map externDesc)

/-- An import. -/
def import_ (i : Binary.Import) : Definition Silmaril.Wasm.Module :=
  .import_ (externName i.name) (externDesc i.desc)

/-- The definitions of a section; `none` outside the fragment. -/
def section_ : Binary.Section → Option (List (Definition Silmaril.Wasm.Module))
  | .custom _ _ => some []
  | .coreModule b => (Silmaril.Wasm.Binary.Core.decode? b).map fun m => [.coreModule m]
  | .coreInstances xs => some (xs.map fun x => .coreInstance (coreInstance x))
  | .instances xs => some (xs.map fun x => .instance_ (instance_ x))
  | .aliases xs => (xs.mapM alias_).map fun as => as.map .alias
  | .types xs => (xs.mapM defType).map fun ts => ts.map .type
  | .canons xs => some (xs.map fun x => .canon (canon x))
  | .imports xs => some (xs.map import_)
  | .exports xs => some (xs.map export_)
  | _ => none

/-- **A binary component as a reference component**, on the fragment of `section_`. -/
def toRef? (c : Binary.Ast) : Option Core3Component :=
  (c.sections.mapM section_).map List.flatten

/-! ## The WASI view of reference events -/

/-- The WASI view of a reference value: scalars kept, handles tagged, the rest a placeholder. -/
def wval : RVal → Val
  | .bool b => .bool b
  | .int .u8 n => .u8 (BitVec.ofInt 8 n)
  | .int .u16 n => .u16 (BitVec.ofInt 16 n)
  | .int .u32 n => .u32 (BitVec.ofInt 32 n)
  | .int .u64 n => .u64 (BitVec.ofInt 64 n)
  | .int .s8 n => .s8 (BitVec.ofInt 8 n)
  | .int .s16 n => .s16 (BitVec.ofInt 16 n)
  | .int .s32 n => .s32 (BitVec.ofInt 32 n)
  | .int .s64 n => .s64 (BitVec.ofInt 64 n)
  | .f32 x => .f32 x
  | .f64 x => .f64 x
  | .char c => .char c
  | .own r => .variant 0 (some (.variant r none))
  | .borrow r => .variant 1 (some (.variant r none))
  | _ => .record []

/-- A handle read back from its WASI view: `(true, r)` for `own r`, `(false, r)` for
`borrow r`. -/
def hval : Val → Option (Bool × ℕ)
  | .variant 0 (some (.variant r none)) => some (true, r)
  | .variant 1 (some (.variant r none)) => some (false, r)
  | _ => none

/-- The WASI result of a reference outcome: the results of a resolved call, else `none`. -/
def wout : Outcome → Option (List Val)
  | .returns (some vs) => some (vs.map wval)
  | _ => none

variable {X : CIface}

/-- The WASI event of a reference event, with the imports named `fnI` and the exports `fnE`. A
return carries no arguments (see `strip`). -/
def wevOf (fnI : X.Imp → FnName) (fnE : X.Exp → FnName) : CEvent X → WEv
  | .inl (.ask i a) => .req (fnI i) (a.map wval)
  | .inl (.ans i o) => .imp (fnI i) [] (wout o)
  | .inr (.ask j a) => .call (fnE j) (a.map wval)
  | .inr (.ans j o) => .ret (fnE j) [] (wout o)

/-- A WASI event without the call arguments repeated by answers. -/
def strip : WEv → WEv
  | .imp f _ r => .imp f [] r
  | .ret f _ r => .ret f [] r
  | e => e

/-- **The model generated by a set of reference traces**: the plays whose stripped events are
the WASI events of one of them. -/
def traceModel (W : World) (fnI : X.Imp → FnName) (fnE : X.Exp → FnName)
    (T : Set (List (CEvent X))) : W.Model :=
  Silmaril.Games.Strategy.generate
    {s | ∃ t ∈ T, (wtrace s).map strip = t.map (wevOf fnI fnE)}

/-- **The reference denotation of a binary component**: the multi-call traces of `toRef? c` as
the reference program `⟨_, args, names⟩` over the Core 3.0 engine at profile `P`
(`Silmaril.Wasm.Component.Reference.core3P`), as a model of `W`; the least model when `c` is
outside the fragment. -/
noncomputable def refDen {σ : Type} (P : Silmaril.Wasm.Numerics.Profile)
    (prof : Silmaril.Wasm.Component.ProfileKind) (h : Host (Silmaril.Wasm.Component.Reference.core3P P) σ) (σ0 : σ)
    (X : CIface)
    (args : Silmaril.Wasm.Component.Instantiate.Exports (Silmaril.Wasm.Component.Reference.core3P P))
    (names : X.Exp → String) (W : World) (fnI : X.Imp → FnName) (fnE : X.Exp → FnName)
    (c : Binary.Ast) : W.Model :=
  match toRef? c with
  | some rc => traceModel W fnI fnE (refMultiTraces prof h σ0 (⟨rc, args, names⟩ : RefProg (Silmaril.Wasm.Component.Reference.core3P P) X))
  | none => Silmaril.Games.Strategy.generate ∅

/-! ## The provider handle sentence on WASI events -/

/-- The handle event of the return `res` of the export `f`: one `own r` result of `new`
allocates `r`. -/
def retEv (fnE : X.Exp → FnName) (new : X.Exp) (f : FnName) : Option (List Val) → HEv ℕ
  | some [v] =>
    match hval v with
    | some (true, r) => if f = fnE new then .alloc r else .skip
    | _ => .skip
  | _ => .skip

/-- The handle event of a call of the export `f` on `a`: one `own r` argument of `drop` frees
`r`; one handle argument of another export is used. -/
def callEv (fnE : X.Exp → FnName) (drop : X.Exp) (f : FnName) : List Val → HEv ℕ
  | [v] =>
    match hval v with
    | some (true, r) => if f = fnE drop then .free r else .use r
    | some (false, r) => .use r
    | none => .skip
  | _ => .skip

/-- The handle event of a WASI event (provider orientation, exports named by `fnE`). -/
def hevW (fnE : X.Exp → FnName) (new drop : X.Exp) : WEv → HEv ℕ
  | .ret f _ res => retEv fnE new f res
  | .call f a => callEv fnE drop f a
  | _ => .skip

/-- **The provider sentence on WASI events**: `new` never returns a live representation. -/
def provGuar (fnE : X.Exp → FnName) (new drop : X.Exp) : Protocol (Option (List ℕ)) WEv :=
  (handleProto ℕ .provider).comap (hevW fnE new drop)

end Silmaril.Project.WasmComponents.Ref

end
