module

public import Silmaril.Wasm.Component.Binary.Defs
public import Silmaril.Wasm.Component.IR.Defs
public import Silmaril.Wasm.Binary.Core.Decode

/-!
# Lowering component binaries to the component IR (partial)

`lower : Ast → Except String (Comp CoreMod)` turns the abstract syntax of a
component binary into the nested IR `Silmaril.Wasm.Component.Comp`, for the
subset that the IR models. Everything else is rejected with a message naming
the construct. `parseComponent` composes it with the verified parser.

## Supported

* core modules, decoded by silmaril's verified core decoder
  (`Silmaril.Wasm.Binary.Core.decode?`, sound for the Core grammar); their
  function imports and exports with numeric (`i32`/`i64`/`f32`/`f64`) types
  form the `CoreModule` interface of `CoreMod`;
* core instances: `instantiate` (function imports only, resolved by module
  and field name through the argument instances) and inline function exports;
* aliases of core instance function exports, of imported or inline
  component instance function exports, and of types;
* type definitions: `bool`, the integers, `f32`, `f64`, `char`, records,
  tuples, variants, enums, options, results; sync function types;
  instance types (their function exports, for imported instances);
* `canon lift` and `canon lower` (string-encoding and `memory`/`realloc`
  options are ignored: the supported types never touch memory); functions
  whose flattening exceeds `MAX_FLAT_PARAMS = 16` or `MAX_FLAT_RESULTS = 1`
  are rejected (the canonical ABI would spill them to memory);
* imports of functions and of instances (an instance import contributes its
  function exports as imports named `instance#function`), and of types;
* exports of functions, of inline instances (flattened as
  `instance#function`), and of types (no runtime content, skipped).

## Rejected

Strings, lists, flags, resources, `own`/`borrow`, streams/futures; module and
value imports; core modules importing tables, memories, globals or tags;
`post-return`, `async` and `callback` options; resource built-ins; nested
components and component instantiation; the start and value sections; outer
aliases. The IR has no linear memory, so this is where it stops.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Binary

open Silmaril.Wasm.Component

/-- A core module of a lowered component: its bytes and its function
interface, as decoded by silmaril's core decoder. -/
structure CoreMod where
  bytes : ByteArray
  /-- The module and field names of the function imports, in order. -/
  importNames : List (String × String)
  /-- The function imports (field name, type), in order. -/
  imports : CoreIface
  /-- The function exports, in order. -/
  exports : CoreIface

instance : CoreModule CoreMod := ⟨CoreMod.imports, CoreMod.exports⟩

instance : Repr CoreMod := ⟨fun m _ => s!"<core module: {m.bytes.size} bytes, imports {repr m.imports}, exports {repr m.exports}>"⟩

namespace Lower

open Silmaril.Wasm (NumType)

instance : ToString ExternName := ⟨ExternName.name⟩

/-- A numeric core value type. -/
def numType : Silmaril.Wasm.ValType → Except String NumType
  | .num t => .ok t
  | _ => .error "core function types must be numeric (i32/i64/f32/f64)"

/-- The flat type of the core type definition `t` of `m`. -/
def coreFuncTy (m : Silmaril.Wasm.Module) (t : Silmaril.Wasm.TypeIdx) : Except String CoreFuncTy := do
  match m.typeDefinitions[t.value.val]? with
  | some ⟨_, _, .func ft⟩ =>
    pure ⟨← ft.params.mapM numType, ← ft.results.mapM numType⟩
  | _ => throw s!"core type {t.value.val} is not a function type"

/-- Decode an embedded core module and extract its function interface. -/
def coreMod (bytes : ByteArray) : Except String CoreMod := do
  let some m := Silmaril.Wasm.Binary.Core.decode? bytes
    | throw "embedded core module rejected by silmaril's core decoder (outside its fragment)"
  let mut names := #[]
  let mut imps := #[]
  for i in m.imports do
    match i.type with
    | .func t =>
      names := names.push (i.moduleName, i.name)
      imps := imps.push (i.name, ← coreFuncTy m t)
    | _ => throw s!"core module imports a non-function ({i.moduleName} {i.name}); unsupported"
  let fts := m.functionTypes
  let mut exps := #[]
  for e in m.exports do
    match e.index with
    | .func f =>
      match fts[f.value.val]? with
      | some t => exps := exps.push (e.name, ← coreFuncTy m t)
      | none => throw s!"core export {e.name}: function {f.value.val} out of range"
    | _ => pure ()
  pure ⟨bytes, names.toList, imps.toList, exps.toList⟩

/-! ## Index spaces -/

/-- A core instance. -/
inductive CoreInst where
  /-- An instance of a module whose function exports start at `base`. -/
  | node (base : Nat) (m : CoreMod)
  /-- Inline exports of core functions. -/
  | inline (es : List (String × Impl))

/-- A component instance (only its function exports are kept). -/
structure CompInst where
  funcs : List (String × Nat)

/-- An entry of the type index space. -/
inductive TypeEntry where
  | val (t : ValTy)
  | func (ft : FuncTy)
  | inst (decls : List InstanceDecl)
  /-- Anything else, with the reason it is not supported. -/
  | other (why : String)

/-- The lowering state. -/
structure St where
  modules : Array CoreMod := #[]
  coreInsts : Array CoreInst := #[]
  /-- Core functions: wiring programs over the environment, with flat types. -/
  coreFuncs : Array Impl := #[]
  types : Array TypeEntry := #[]
  /-- Component functions: wiring programs with their types. -/
  funcs : Array (Impl × FuncTy) := #[]
  insts : Array CompInst := #[]
  /-- The next import index. -/
  nextImport : Nat := 0
  /-- The size of the environment (imports, then node exports). -/
  env : Nat
  nodes : Array (Node CoreMod) := #[]
  exports : Array Component.Export := #[]

abbrev M := StateT St (Except String)

def get? {α : Type} (xs : Array α) (i : Nat) (what : String) : M α :=
  match xs[i]? with
  | some x => pure x
  | none => throw s!"{what} index {i} out of range"

/-! ## Types -/

def primTy : PrimValType → Except String ValTy
  | .bool => .ok .bool | .s8 => .ok .s8 | .u8 => .ok .u8 | .s16 => .ok .s16
  | .u16 => .ok .u16 | .s32 => .ok .s32 | .u32 => .ok .u32 | .s64 => .ok .s64
  | .u64 => .ok .u64 | .f32 => .ok .f32 | .f64 => .ok .f64 | .char => .ok .char
  | .string => .error "string (needs linear memory)"
  | .errorContext => .error "error-context"

def valTy (types : Array TypeEntry) : ValType → Except String ValTy
  | .prim p => primTy p
  | .idx i => match types[i]? with
    | some (.val t) => .ok t
    | some (.other why) => .error why
    | some _ => .error s!"type {i} is not a value type"
    | none => .error s!"type index {i} out of range"

def optTy (types : Array TypeEntry) : Option ValType → Except String (Option ValTy)
  | none => .ok none
  | some t => some <$> valTy types t

def defValTy (types : Array TypeEntry) : DefValType → Except String ValTy
  | .prim p => primTy p
  | .record fs => .record <$> fs.mapM (valTy types ·.2)
  | .tuple ts => .record <$> ts.mapM (valTy types)
  | .variant cs => .variant <$> cs.mapM (optTy types ·.2)
  | .enum ls => .ok (.enum ls.length)
  | .option t => ValTy.option <$> valTy types t
  | .result o e => do pure (ValTy.result (← optTy types o) (← optTy types e))
  | .list _ | .fixedList _ _ => .error "list (needs linear memory)"
  | .flags _ => .error "flags"
  | .own _ | .borrow _ => .error "resource handles"
  | .stream _ | .future _ => .error "streams and futures"
  | .map _ _ => .error "maps (need linear memory)"

def funcTy (types : Array TypeEntry) (f : FuncType) : Except String FuncTy := do
  let ps ← f.params.mapM (valTy types ·.2)
  if f.async then throw "async functions"
  let rs ← match f.result with
    | some t => do pure [← valTy types t]
    | none => pure []
  let ft : FuncTy := ⟨ps, rs⟩
  if ft.flat.params.length > 16 then throw "more than 16 flat parameters (spilled to memory)"
  if ft.flat.results.length > 1 then throw "more than one flat result (returned through memory)"
  pure ft

def typeEntry (types : Array TypeEntry) : DefType → TypeEntry
  | .val d => match defValTy types d with
    | .ok t => .val t
    | .error why => .other why
  | .func f => match funcTy types f with
    | .ok ft => .func ft
    | .error why => .other why
  | .instance ds => .inst ds
  | .component _ => .other "component types"
  | .resource _ _ => .other "resources"

def lookupFuncTy (i : Nat) : M FuncTy := do
  match (← get).types[i]? with
  | some (.func ft) => pure ft
  | some (.other why) => throw s!"function type {i}: unsupported {why}"
  | some _ => throw s!"type {i} is not a function type"
  | none => throw s!"type index {i} out of range"

/-! ## Instance types (for imported instances) -/

/-- The function exports of an instance type, with their types, resolved in
its local type space (outer aliases of count 1 reach the enclosing types). -/
def instFuncs (outer : Array TypeEntry) (decls : List InstanceDecl) :
    Except String (List (String × FuncTy)) := do
  let mut loc : Array TypeEntry := #[]
  let mut out := #[]
  for d in decls do
    match d with
    | .type t => loc := loc.push (typeEntry loc t)
    | .coreType _ => pure ()
    | .alias ⟨.type, .outer 1 i⟩ => match outer[i]? with
      | some e => loc := loc.push e
      | none => throw s!"outer type alias {i} out of range"
    | .alias ⟨.type, _⟩ => loc := loc.push (.other "aliased types")
    | .alias _ => pure ()
    | .export n (.func i) => match loc[i]? with
      | some (.func ft) => out := out.push (n.name, ft)
      | some (.other why) => throw s!"instance export {n}: unsupported {why}"
      | _ => throw s!"instance export {n}: type {i} is not a function type"
    | .export _ (.type _) => loc := loc.push (.other "exported (abstract) types")
    | .export n _ => throw s!"instance export {n}: only functions and types are supported"
  pure out.toList

/-! ## Sections -/

def addImport : M Nat := do
  let s ← get
  set { s with nextImport := s.nextImport + 1 }
  pure s.nextImport

def import_ (i : Import) : M Unit := do
  match i.desc with
  | .func t =>
    let ft ← lookupFuncTy t
    let r ← addImport
    modify fun s => { s with funcs := s.funcs.push (⟨[], .call r⟩, ft) }
  | .instance t =>
    let s ← get
    let decls ← match s.types[t]? with
      | some (.inst ds) => pure ds
      | _ => throw s!"import {i.name}: type {t} is not an instance type"
    let fs ← instFuncs s.types decls
    let mut names := #[]
    for (n, ft) in fs do
      let r ← addImport
      let s ← get
      names := names.push (n, s.funcs.size)
      set { s with funcs := s.funcs.push (⟨[], .call r⟩, ft) }
    modify fun s => { s with insts := s.insts.push ⟨names.toList⟩ }
  | .type (.eq t) => do
    let e ← get? (← get).types t "type"
    modify fun s => { s with types := s.types.push e }
  | .type .subResource => modify fun s => { s with types := s.types.push (.other "resources") }
  | _ => throw s!"import {i.name}: only functions, instances and types are supported"

/-- The function imports of a component, in order (for the environment base). -/
def importIface (types : Array TypeEntry) (i : Import) : Except String Iface := do
  match i.desc with
  | .func t => match types[t]? with
    | some (.func ft) => pure [(i.name.name, ft)]
    | _ => throw s!"import {i.name}: type {t} is not a supported function type"
  | .instance t => match types[t]? with
    | some (.inst ds) => return (← instFuncs types ds).map fun (n, ft) => (s!"{i.name}#{n}", ft)
    | _ => throw s!"import {i.name}: type {t} is not an instance type"
  | _ => pure []

def coreExportImpl (inst : CoreInst) (name : String) : Except String Impl :=
  match inst with
  | .node base m =>
    match (CoreModule.exports m).findIdx? (·.1 == name) with
    | some j => .ok (Impl.fwd (base + j))
    | none => .error s!"core instance has no function export {name}"
  | .inline es =>
    match es.find? (·.1 == name) with
    | some (_, im) => .ok im
    | none => .error s!"inline core instance has no function export {name}"

def coreInstance (e : CoreInstanceExpr) : M Unit := do
  match e with
  | .instantiate mi args =>
    let s ← get
    let m ← get? s.modules mi "core module"
    let mut wiring := #[]
    for (modName, field) in m.importNames do
      let some (_, j) := args.find? (·.1 == modName)
        | throw s!"instantiate: no argument for import module {modName}"
      let inst ← get? s.coreInsts j "core instance"
      wiring := wiring.push (← (coreExportImpl inst field : Except String Impl))
    set { s with
      nodes := s.nodes.push (.core m wiring.toList)
      coreInsts := s.coreInsts.push (.node s.env m)
      env := s.env + (CoreModule.exports m).length }
  | .exports es =>
    let s ← get
    let mut out := #[]
    for (n, ⟨sort, i⟩) in es do
      if sort = .func then out := out.push (n, ← get? s.coreFuncs i "core function")
    set { s with coreInsts := s.coreInsts.push (.inline out.toList) }

def alias_ (a : Alias) : M Unit := do
  let s ← get
  match a.sort, a.target with
  | .core .func, .coreExport i n =>
    let inst ← get? s.coreInsts i "core instance"
    let im ← (coreExportImpl inst n : Except String Impl)
    set { s with coreFuncs := s.coreFuncs.push im }
  | .func, .export i n =>
    let inst ← get? s.insts i "instance"
    let some (_, f) := inst.funcs.find? (·.1 == n) | throw s!"instance {i} has no function {n}"
    set { s with funcs := s.funcs.push (← get? s.funcs f "function") }
  | .type, .export _ _ => set { s with types := s.types.push (.other "aliased instance types") }
  | _, .outer _ _ => throw "outer aliases are not supported at the top level"
  | _, _ => throw "only function and type aliases are supported"

def canon (c : Canon) : M Unit := do
  let s ← get
  match c with
  | .lift f opts t =>
    for o in opts do
      match o with
      | .postReturn _ => throw "canon lift: post-return is not supported"
      | .async | .callback _ => throw "canon lift: async is not supported"
      | _ => pure ()
    let im ← get? s.coreFuncs f "core function"
    let ft ← lookupFuncTy t
    set { s with funcs := s.funcs.push (⟨.lift ft :: im.chain, im.target⟩, ft) }
  | .lower f opts =>
    for o in opts do
      match o with
      | .postReturn _ | .async | .callback _ => throw "canon lower: unsupported option"
      | _ => pure ()
    let (im, ft) ← get? s.funcs f "function"
    set { s with coreFuncs := s.coreFuncs.push ⟨.lower ft :: im.chain, im.target⟩ }
  | _ => throw "resource built-ins are not supported"

def export_ (e : Export) : M Unit := do
  let s ← get
  match e.item.sort with
  | .func =>
    let (im, ft) ← get? s.funcs e.item.idx "function"
    set { s with exports := s.exports.push (⟨e.name.name, ft, im⟩ : Component.Export), funcs := s.funcs.push (im, ft) }
  | .instance =>
    let inst ← get? s.insts e.item.idx "instance"
    let mut xs := s.exports
    for (n, f) in inst.funcs do
      let (im, ft) ← get? s.funcs f "function"
      xs := xs.push (⟨s!"{e.name}#{n}", ft, im⟩ : Component.Export)
    set { s with exports := xs, insts := s.insts.push inst }
  | .type =>
    let t ← get? s.types e.item.idx "type"
    set { s with types := s.types.push t }
  | _ => throw s!"export {e.name}: only functions, instances and types are supported"

def instance_ (e : InstanceExpr) : M Unit := do
  match e with
  | .instantiate _ _ => throw "component instantiation is not supported"
  | .exports es =>
    let mut fs := #[]
    for (n, ⟨sort, i⟩) in es do
      match sort with
      | .func => fs := fs.push (n.name, i)
      | .type => pure ()
      | _ => throw s!"inline instance export {n}: only functions and types are supported"
    modify fun s => { s with insts := s.insts.push ⟨fs.toList⟩ }

def section_ (sec : Section) : M Unit := do
  match sec with
  | .custom _ _ => pure ()
  | .coreModule b =>
    let m ← (coreMod b : Except String CoreMod)
    modify fun s => { s with modules := s.modules.push m }
  | .coreInstances xs => xs.forM coreInstance
  | .coreTypes _ => pure ()
  | .component _ => throw "nested components are not supported"
  | .instances xs => xs.forM instance_
  | .aliases xs => xs.forM alias_
  | .types xs => xs.forM fun t => modify fun s => { s with types := s.types.push (typeEntry s.types t) }
  | .canons xs => xs.forM canon
  | .start _ => throw "the start section is not supported"
  | .imports xs => xs.forM import_
  | .exports xs => xs.forM export_
  | .values _ => throw "values are not supported"

/-- First pass: the function imports, in order, under the type space as it
grows (types and imported types only). -/
def importsPass (ss : List Section) : Except String Iface := do
  let mut types : Array TypeEntry := #[]
  let mut out : Iface := []
  for sec in ss do
    match sec with
    | .types xs => for t in xs do types := types.push (typeEntry types t)
    | .imports xs =>
      for i in xs do
        out := out ++ (← importIface types i)
        match i.desc with
        | .type (.eq t) => types := types.push (types[t]?.getD (.other "bad type import"))
        | .type .subResource => types := types.push (.other "resources")
        | _ => pure ()
    | .aliases xs =>
      for a in xs do
        if a.sort = .type then types := types.push (.other "aliased instance types")
    | .exports xs =>
      for e in xs do
        if e.item.sort = .type then
          types := types.push (types[e.item.idx]?.getD (.other "bad type export"))
    | _ => pure ()
  pure out

end Lower

/-- Lower a parsed component binary to the component IR (partial; see the
module documentation for the supported subset). -/
def lower (c : Ast) : Except String (Comp CoreMod) := do
  let imports ← Lower.importsPass c.sections
  let (_, s) ← (c.sections.forM Lower.section_).run { env := imports.length }
  if s.nextImport ≠ imports.length then
    throw "internal: the import passes disagree"
  pure (.mk imports s.nodes.toList s.exports.toList)

/-- **Driver entry point**: parse a component binary and lower it to the
component IR. Parsing is verified (`parse_sound`, `parse_encode`); lowering
is partial and unverified. -/
def parseComponent (bytes : ByteArray) : Except String (Comp CoreMod) := do
  let ast ← match parse bytes with
    | .ok a => pure a
    | .error e => throw s!"component binary: {repr e.kind} at byte {e.pos}"
  lower ast

end Silmaril.Wasm.Component.Binary
