module

public import Silmaril.Wasm.Component.Binary.Defs
public import Silmaril.Wasm.Component.RefValid.Defs
public import Silmaril.Wasm.Binary.Core.Decode

/-!
# Component binaries as reference-semantics syntax

`toRef : Binary.Ast → Except String Core3Component` reads the abstract syntax of a component
binary (`Silmaril.Wasm.Component.Binary`, the verified grammar of `Binary.md` at `8505ba7`) as the
index-based AST of the copied reference semantics (`Silmaril.Wasm.Component.Syntax`, which
follows `Binary.md` at `a25fc0b`). Core modules are decoded by silmaril-lean's core decoder
`Silmaril.Wasm.Binary.Core.decode?`. `decodeRef bytes` composes it with `Binary.parse`.

The two ASTs transcribe the same productions, so the map is nearly the identity. The cases
that are not:

* custom sections are dropped (the reference AST has none);
* `nameattributes` keeps only its attributes (the `0x00`/`0x01` spellings are forgotten);
* a core function type `0x60` is the one-element final recursion group;
* core value types become Core 3.0 value types (`funcref`/`externref` are nullable abstract
  references); a table whose element type is not a reference type, a resource or
  `context.*` representation that is not `i32`/`i64`, and a limit at or above `2^64`, are
  rejected with a message;
* a core module the core decoder rejects is rejected.

What `Binary` does not decode (the async, stream, future, error-context, waitable and thread
built-ins; the GC forms of core types) never reaches this map: `Binary.parse` fails first.
No theorem relates `toRef` to the reference's own reading of `Binary.md`; this is the
executable entry point of the conformance runner (`tools/wasm-tools/README.md`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Conformance

open Silmaril.Wasm.Component
open Silmaril.Wasm.Component

/-- A component of the reference semantics over Core 3.0 modules. -/
abbrev RefComponent : Type := Reference.Core3Component

namespace ToRef

/-- `core:sort`. -/
def coreSort : Binary.CoreSort → Syntax.CoreSort
  | .func => .func | .table => .table | .memory => .memory | .global => .global
  | .tag => .tag | .type => .type | .module => .module_ | .instance => .instance_

/-- `sort`. -/
def sort : Binary.ItemSort → Syntax.Sort_
  | .core s => .core (coreSort s)
  | .func => .func | .value => .value | .type => .type | .component => .component
  | .instance => .instance_

def coreSortIdx (s : Binary.CoreSortIdx) : Syntax.SortIdx Syntax.CoreSort :=
  ⟨coreSort s.sort, s.idx⟩

def sortIdx (s : Binary.SortIdx) : Syntax.SortIdx Syntax.Sort_ := ⟨sort s.sort, s.idx⟩

def attr : Binary.Attribute → Syntax.Attribute
  | .implements n => .implements n
  | .versionSuffix s => .versionSuffix s
  | .externalId i => .externalId i

/-- `nameattributes`: the name and its attributes. -/
def externName (n : Binary.ExternName) : Syntax.ExternName :=
  { name := n.name
    attrs := match n.form with
      | .attrs as => as.map attr
      | _ => [] }

def coreInstanceExpr : Binary.CoreInstanceExpr → Syntax.CoreInstanceExpr
  | .instantiate m args => .instantiate m args
  | .exports es => .exports (es.map fun p => (p.1, coreSortIdx p.2))

def instanceExpr : Binary.InstanceExpr → Syntax.InstanceExpr
  | .instantiate c args => .instantiate c (args.map fun p => (p.1, sortIdx p.2))
  | .exports es => .exports (es.map fun p => (externName p.1, sortIdx p.2))

def aliasDef (a : Binary.Alias) : Except String Syntax.Alias :=
  match a.target, a.sort with
  | .export i n, s => .ok (.export_ i n (sort s))
  | .coreExport i n, .core s => .ok (.coreExport i n (coreSort s))
  | .coreExport _ n, _ => .error s!"core export alias {n} of a non-core sort"
  | .outer c i, s => .ok (.outer c i (sort s))

/-! ## Core types -/

def coreValType : Binary.CoreValType → Silmaril.Wasm.ValType
  | .i32 => .num (.int .i32) | .i64 => .num (.int .i64)
  | .f32 => .num (.float .f32) | .f64 => .num (.float .f64)
  | .v128 => .vec .v128
  | .funcref => .ref ⟨true, .abstract .func⟩
  | .externref => .ref ⟨true, .abstract .extern⟩

def refType : Binary.CoreValType → Except String Silmaril.Wasm.RefType
  | .funcref => .ok ⟨true, .abstract .func⟩
  | .externref => .ok ⟨true, .abstract .extern⟩
  | _ => .error "table element type is not a reference type"

def addrType : Binary.CoreValType → Except String Silmaril.Wasm.AddrType
  | .i32 => .ok .i32
  | .i64 => .ok .i64
  | _ => .error "representation type is neither i32 nor i64"

def bound (n : Nat) : Except String (Fin (2 ^ 64)) :=
  if h : n < 2 ^ 64 then .ok ⟨n, h⟩ else .error "limit out of range"

def idx {k : Silmaril.Wasm.IndexKind} (n : Nat) : Except String (Silmaril.Wasm.Idx k) :=
  match Silmaril.Wasm.Idx.ofNat? n with
  | some i => .ok i
  | none => .error "index out of range"

def limits (l : Binary.Limits) : Except String Silmaril.Wasm.Limits := do
  let min ← bound l.min
  let max ← match l.max with
    | none => pure none
    | some m => some <$> bound m
  pure ⟨min, max⟩

def externType : Binary.CoreImportDesc → Except String Silmaril.Wasm.ExternType
  | .func t => .func <$> idx t
  | .table e l => do pure (.table ⟨.i32, ← limits l, ← refType e⟩)
  | .memory l => do pure (.memory ⟨.i32, ← limits l⟩)
  | .global t m => .ok (.global ⟨if m then .var else .const, coreValType t⟩)
  | .tag t => .tag <$> idx t

/-- A core function type is a singleton final recursion group. -/
def recType (t : Binary.CoreFuncType) : Silmaril.Wasm.RecType :=
  ⟨[⟨true, [], .func ⟨t.params.map coreValType, t.results.map coreValType⟩⟩]⟩

def moduleDecl : Binary.ModuleDecl → Except String Syntax.CoreModuleDecl
  | .import m n d => .import_ m n <$> externType d
  | .type t => .ok (.type (recType t))
  | .alias c i => .ok (.aliasOuter c i)
  | .export n d => .export_ n <$> externType d

def coreType : Binary.CoreType → Except String Syntax.CoreTypeDef
  | .func t => .ok (.rec_ (recType t))
  | .module ds => .module_ <$> ds.mapM moduleDecl

/-! ## Component types -/

def prim : Binary.PrimValType → Syntax.Prim
  | .bool => .bool | .s8 => .s8 | .u8 => .u8 | .s16 => .s16 | .u16 => .u16 | .s32 => .s32
  | .u32 => .u32 | .s64 => .s64 | .u64 => .u64 | .f32 => .f32 | .f64 => .f64 | .char => .char
  | .string => .string | .errorContext => .errorContext

def valType : Binary.ValType → Syntax.VT
  | .prim p => .prim (prim p)
  | .idx i => .idx i

def defValType : Binary.DefValType → Syntax.DefValType
  | .prim p => .prim (prim p)
  | .record fs => .record (fs.map fun p => (p.1, valType p.2))
  | .variant cs => .variant (cs.map fun p => (p.1, p.2.map valType))
  | .list t => .list (valType t)
  | .tuple ts => .tuple (ts.map valType)
  | .flags ls => .flags ls
  | .enum ls => .enum ls
  | .option t => .option (valType t)
  | .result ok err => .result (ok.map valType) (err.map valType)
  | .own i => .own i
  | .borrow i => .borrow i
  | .fixedList t n => .fixedList (valType t) n
  | .stream t => .stream (t.map valType)
  | .future t => .future (t.map valType)
  | .map k v => .map (valType k) (valType v)

def funcType (f : Binary.FuncType) : Syntax.FuncType :=
  { async_ := f.async, params := f.params.map fun p => (p.1, valType p.2),
    result := f.result.map valType }

def valueBound : Binary.ValueBound → Syntax.ValueBound
  | .eq i => .eq i
  | .type t => .type (valType t)

def typeBound : Binary.TypeBound → Syntax.TypeBound
  | .eq i => .eq i
  | .subResource => .subResource

def externDesc : Binary.ExternDesc → Syntax.ExternDesc
  | .coreModule i => .coreModule i
  | .func i => .func i
  | .value b => .value (valueBound b)
  | .type b => .type (typeBound b)
  | .component i => .component i
  | .instance i => .instance_ i

mutual

def defType : Binary.DefType → Except String Syntax.DefType
  | .val d => .ok (.val (defValType d))
  | .func f => .ok (.func (funcType f))
  | .component ds => .component <$> componentDecls ds
  | .instance ds => .instance_ <$> instanceDecls ds
  | .resource rep dtor => do pure (.resource (← addrType rep) dtor)

def instanceDecl : Binary.InstanceDecl → Except String Syntax.InstanceDecl
  | .coreType t => .coreType <$> coreType t
  | .type t => .type <$> defType t
  | .alias a => .alias <$> aliasDef a
  | .export n d => .ok (.export_ (externName n) (externDesc d))

def instanceDecls : List Binary.InstanceDecl → Except String (List Syntax.InstanceDecl)
  | [] => .ok []
  | d :: ds => do pure ((← instanceDecl d) :: (← instanceDecls ds))

def componentDecl : Binary.ComponentDecl → Except String Syntax.ComponentDecl
  | .import n d => .ok (.import_ (externName n) (externDesc d))
  | .inst d => .decl <$> instanceDecl d

def componentDecls : List Binary.ComponentDecl → Except String (List Syntax.ComponentDecl)
  | [] => .ok []
  | d :: ds => do pure ((← componentDecl d) :: (← componentDecls ds))

end

/-! ## Canonical definitions -/

def canonOpt : Binary.CanonOpt → Syntax.CanonOpt
  | .utf8 => .encoding .utf8
  | .utf16 => .encoding .utf16
  | .latin1utf16 => .encoding .latin1Utf16
  | .memory i => .memory i
  | .realloc i => .realloc i
  | .postReturn i => .postReturn i
  | .async => .async_
  | .callback i => .callback i

def canon : Binary.Canon → Syntax.Canon
  | .lift f opts t => .lift f (opts.map canonOpt) t
  | .lower f opts => .lower f (opts.map canonOpt)
  | .resourceNew t => .builtin (.resourceNew t)
  | .resourceDrop t => .builtin (.resourceDrop t)
  | .resourceRep t => .builtin (.resourceRep t)

/-! ## Sections -/

/-- A core module, decoded by silmaril-lean's core decoder. -/
def coreModule (bytes : ByteArray) : Except String Silmaril.Wasm.Module :=
  match Silmaril.Wasm.Binary.Core.decode? bytes with
  | some m => .ok m
  | none => .error "core module rejected by the core decoder"

mutual

/-- The definitions of one section, in order. -/
def section_ : Binary.Section → Except String (List (Syntax.Definition Silmaril.Wasm.Module))
  | .custom _ _ => .ok []
  | .coreModule bs => do pure [.coreModule (← coreModule bs)]
  | .coreInstances xs => .ok (xs.map fun x => .coreInstance (coreInstanceExpr x))
  | .coreTypes xs => xs.mapM fun x => .coreType <$> coreType x
  | .component c => do pure [.component (← ast c)]
  | .instances xs => .ok (xs.map fun x => .instance_ (instanceExpr x))
  | .aliases xs => xs.mapM fun x => .alias <$> aliasDef x
  | .types xs => xs.mapM fun x => .type <$> defType x
  | .canons xs => .ok (xs.map fun x => .canon (canon x))
  | .start s => .ok [.start s.func s.args s.results]
  | .imports xs => .ok (xs.map fun x => .import_ (externName x.name) (externDesc x.desc))
  | .exports xs => .ok (xs.map fun x =>
      .export_ (externName x.name) (sortIdx x.item) (x.desc.map externDesc))
  | .values xs => .ok (xs.map fun x => .value (valType x.type) x.bytes.toList)

def sections : List Binary.Section → Except String (List (Syntax.Definition Silmaril.Wasm.Module))
  | [] => .ok []
  | s :: ss => do pure ((← section_ s) ++ (← sections ss))

/-- A component: the definitions of its sections, in order (`flatten(sections)`). -/
def ast : Binary.Ast → Except String (List (Syntax.Definition Silmaril.Wasm.Module))
  | .mk ss => sections ss

end

end ToRef

/-- **The reference syntax of a component binary's AST.** -/
def toRef (a : Binary.Ast) : Except String RefComponent := ToRef.ast a

/-- Decode a component binary into reference syntax: the verified grammar, then `toRef`. -/
def decodeRef (bytes : ByteArray) : Except String RefComponent :=
  match Binary.parse bytes with
  | .error e => .error s!"binary: {repr e}"
  | .ok a => toRef a

end Silmaril.Wasm.Component.Conformance
