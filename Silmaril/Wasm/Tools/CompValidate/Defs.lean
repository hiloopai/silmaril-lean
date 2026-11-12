module

public import Silmaril.Wasm.Tools.Validate.Defs
public import Silmaril.Wasm.Tools.FastPaths.Defs
public import Silmaril.Wasm.Tools.CompNames.Defs
public import Silmaril.Wasm.Component.BinaryP3.Check.Defs

/-!
# `wasm-tools validate` for components

`check F b` validates a component binary under the wasmparser feature set `F`:

1. the bytes parse as a component (`Silmaril.Wasm.Component.BinaryP3.parse`, the whole `Binary.md`
   at component-model `d095e2f` including the async built-ins), and the checks the grammar does
   not make hold (`BinaryP3.Check.strict`: outer alias sorts, attribute uniqueness);
2. every embedded core module is accepted by the core validator `Validate.check F`
   (`Silmaril.Wasm.Tools.Validate`, proved equal to the specification's module validity), and has
   no duplicate import names;
3. a walk over the sections (`walk`) maintains wasmparser's index spaces with what is known of
   each entry: resolved value types (`RTy`, with resources as unique identities), the function
   types of component functions, the core function types of core functions (from the modules'
   own types, the canonical ABI lowering of `canon lower` and the fixed types of the
   built-ins), the exports of instances, the imports and exports of modules and components. It
   checks what wasmparser's `ComponentState` checks, in the same order: indices in bounds,
   aliases of exports that exist with the right sort, outer alias counts, instantiation
   arguments against the imports they satisfy (presence and sort), the kinds of types
   referenced, import and export names (`Silmaril.Wasm.Tools.CompNames`: kebab case, interface
   names and versions, uniqueness), defined types (labels, `borrow` only in parameters),
   canonical options (repeats, string encodings, the options a lowering needs), the core
   function type of a `canon lift` against the canonical ABI flattening of the component
   function type (`lowerSig`, as `ComponentFuncType::lower`), `post-return`, `callback`,
   `realloc` and destructor signatures, and the feature gates of the component-model proposals.

**Not** checked (so `check` may accept a component wasmparser rejects; each is listed in
`tools/wasm-tools/README.md`): subtyping of instantiation arguments and of export ascriptions,
resource identity across instantiations, the "valid to be used as export/import" rule on types
that mention unexported resources, `[constructor]`/`[method]`/`[static]` name rules against the
functions' types, type sizes and nesting depth, and the GC (`cm-gc`), memory64 and
shared-everything forms the component decoder does not read. The theorem `check_core` in `Thms`
states what an acceptance does guarantee: the binary parses, and every embedded core module is
accepted by the core validator. The rest is a tested transcription of wasmparser
(`tools/wasm-tools/tests/comp-diff.sh`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.CompValidate

open Silmaril.Wasm.Component.Binary (CoreSort ItemSort CoreSortIdx SortIdx ExternName NameForm
  Attribute CoreInstanceExpr InstanceExpr AliasTarget Alias CoreValType CoreImportDesc
  ModuleDecl CoreType PrimValType ValType DefValType FuncType ExternDesc TypeBound DefType
  InstanceDecl ComponentDecl CanonOpt Start Import Export Value)
open Silmaril.Wasm.Component.BinaryP3 (Ast Section Canon)
open Silmaril.Wasm.Tools.Features Silmaril.Wasm.Tools.CompNames

/-! ## Resolved types -/

/-- A resolved component value type: indices replaced by what they denote, resources by their
identities. Records, variants, flags and enums carry the identity of their definition (a
`ComponentDefinedTypeId`), which the named-types rule of imports and exports uses. -/
inductive RTy where
  | prim (p : PrimValType)
  | record (id : Nat) (fs : List (String × RTy))
  | variant (id : Nat) (cs : List (String × Option RTy))
  | list (t : RTy)
  | tuple (ts : List RTy)
  | flags (id : Nat) (names : List String)
  | enum (id : Nat) (names : List String)
  | option (t : RTy)
  | result (ok err : Option RTy)
  | own (r : Nat)
  | borrow (r : Nat)
  | fixedList (t : RTy) (n : Nat)
  | stream (t : Option RTy)
  | future (t : Option RTy)
  | map (k v : RTy)
  /-- A type of unknown structure (from an entry whose detail is not tracked). -/
  | unknown
  deriving Inhabited

/-- A component function type. -/
structure FTy where
  params : List (String × RTy)
  result : Option RTy
  async : Bool
  deriving Inhabited

/-- A core function type, value types spelled as wasmparser prints them (`i32`, …). -/
abbrev CFT := List String × List String

mutual
/-- What is known of an entry of a component-level index space. -/
inductive Ent where
  | func (f : Option FTy)
  | ty (t : TyInfo)
  | inst (exports : Option (List (String × Ent)))
  | comp (sig : Option (List (String × Ent) × List (String × Ent)))
  | module (sig : Option (List (String × String × CoreSort × Option (List String × List String)) ×
      List (String × CoreSort × Option (List String × List String))))
  | other (s : ItemSort)

/-- What is known of a type. -/
inductive TyInfo where
  | val (t : RTy)
  | func (f : FTy)
  | comp (imports exports : List (String × Ent))
  | inst (exports : List (String × Ent))
  /-- A resource type with its identity; `local` when defined in this component. -/
  | resource (id : Nat) (isLocal : Bool)
  | unknown
end

instance : Inhabited TyInfo := ⟨.unknown⟩
instance : Inhabited Ent := ⟨.other .value⟩

/-- Named entries. -/
abbrev Items := List (String × Ent)

/-- The sort of an entry. -/
def Ent.sort : Ent → ItemSort
  | .func _ => .func | .ty _ => .type | .inst _ => .instance | .comp _ => .component
  | .module _ => .core .module | .other s => s

/-- Exports of a core instance: name, sort, and the core function type of a function (for a
memory, table or global its type key: `memShape`, `tableShape`, `globalShape`). -/
abbrev CItems := List (String × CoreSort × Option CFT)

/-- A core module's imports and exports (with function types). -/
abbrev ModSig := List (String × String × CoreSort × Option CFT) × CItems

/-- What is known of a core type. -/
inductive CTyInfo where
  | func (t : CFT)
  | module (sig : ModSig)
  | unknown
  deriving Inhabited

/-- One component (or component/instance/module type) scope. -/
structure Scope where
  ctypes : Array CTyInfo := #[]
  cfuncs : Array (Option CFT) := #[]
  ctables : Nat := 0
  /-- The memories: is each 64-bit? -/
  cmems : Array Bool := #[]
  cglobals : Nat := 0
  ctags : Nat := 0
  cmodules : Array (Option ModSig) := #[]
  cinsts : Array (Option CItems) := #[]
  types : Array TyInfo := #[]
  funcs : Array (Option FTy) := #[]
  values : Nat := 0
  comps : Array (Option (Items × Items)) := #[]
  insts : Array (Option Items) := #[]
  importKeys : List String := []
  exportKeys : List String := []
  imports : Items := []
  exports : Items := []
  /-- Is this a type scope (a component or instance type)? -/
  isType : Bool := false
  /-- Is this an instance type (where the named-types rule is not applied)? -/
  isInst : Bool := false
  /-- The type identities imported (`imported_types`) and exported (`exported_types`). -/
  impSet : List Nat := []
  expSet : List Nat := []
  /-- The resources (of the whole walk) represented by `i64`. -/
  rep64 : List Nat := []
  /-- The resources named by top-level imports and by exports (`ComponentNameContext`). -/
  impRes : List (Nat × String) := []
  expRes : List (Nat × String) := []
  deriving Inhabited

/-- The checker's monad: the next fresh resource identity, and errors. -/
abbrev M := StateT Nat (Except String)

/-- A fresh resource identity. -/
def fresh : M Nat := modifyGet fun n => (n, n + 1)

/-! ## Sorts and index spaces -/

def coreSortName : CoreSort → String
  | .func => "func" | .table => "table" | .memory => "memory" | .global => "global"
  | .tag => "tag" | .type => "type" | .module => "module" | .instance => "instance"

def sortName : ItemSort → String
  | .core s => s!"core {coreSortName s}"
  | .func => "func" | .value => "value" | .type => "type" | .component => "component"
  | .instance => "instance"

/-- The size of a core index space. -/
def Scope.coreLen (s : Scope) : CoreSort → Nat
  | .func => s.cfuncs.size | .table => s.ctables | .memory => s.cmems.size | .global => s.cglobals
  | .tag => s.ctags | .type => s.ctypes.size | .module => s.cmodules.size
  | .instance => s.cinsts.size

/-- The size of an index space. -/
def Scope.len (s : Scope) : ItemSort → Nat
  | .core c => s.coreLen c
  | .func => s.funcs.size | .value => s.values | .type => s.types.size
  | .component => s.comps.size | .instance => s.insts.size

/-- Add an entry of unknown detail to a core index space. -/
def Scope.pushCore (s : Scope) : CoreSort → Scope
  | .func => { s with cfuncs := s.cfuncs.push none }
  | .table => { s with ctables := s.ctables + 1 }
  | .memory => { s with cmems := s.cmems.push false }
  | .global => { s with cglobals := s.cglobals + 1 }
  | .tag => { s with ctags := s.ctags + 1 }
  | .type => { s with ctypes := s.ctypes.push .unknown }
  | .module => { s with cmodules := s.cmodules.push none }
  | .instance => { s with cinsts := s.cinsts.push none }

/-- Add an entry to an index space. -/
def Scope.pushEnt (s : Scope) : Ent → Scope
  | .func f => { s with funcs := s.funcs.push f }
  | .ty t => { s with types := s.types.push t }
  | .inst e => { s with insts := s.insts.push e }
  | .comp c => { s with comps := s.comps.push c }
  | .module m => { s with cmodules := s.cmodules.push m }
  | .other (.core c) => s.pushCore c
  | .other .value => { s with values := s.values + 1 }
  | .other .func => { s with funcs := s.funcs.push none }
  | .other .type => { s with types := s.types.push .unknown }
  | .other .component => { s with comps := s.comps.push none }
  | .other .instance => { s with insts := s.insts.push none }

/-- The entry at an index (what is known of it). -/
def Scope.ent (s : Scope) (srt : ItemSort) (i : Nat) : Ent :=
  match srt with
  | .func => .func (s.funcs[i]?.getD none)
  | .type => .ty (s.types[i]?.getD .unknown)
  | .instance => .inst (s.insts[i]?.getD none)
  | .component => .comp (s.comps[i]?.getD none)
  | .core .module => .module (s.cmodules[i]?.getD none)
  | srt => .other srt

/-- wasmparser's out-of-bounds message for a sort. -/
def oobMsg (srt : ItemSort) (i : Nat) : String :=
  match srt with
  | .core .func => s!"unknown core function {i}: function index out of bounds"
  | .core .table => s!"unknown table {i}: table index out of bounds"
  | .core .memory => s!"unknown memory {i}: memory index out of bounds"
  | .core .global => s!"unknown global {i}: global index out of bounds"
  | .core .tag => s!"unknown tag {i}: tag index out of bounds"
  | .core .type => s!"unknown core type {i}: type index out of bounds"
  | .core .module => s!"unknown module {i}: module index out of bounds"
  | .core .instance => s!"unknown core instance {i}: instance index out of bounds"
  | .func => s!"unknown function {i}: function index out of bounds"
  | .value => s!"unknown value {i}: value index out of bounds"
  | .type => s!"unknown type {i}: type index out of bounds"
  | .component => s!"unknown component {i}: component index out of bounds"
  | .instance => s!"unknown instance {i}: instance index out of bounds"

/-- Check an index is in bounds. -/
def Scope.idx (s : Scope) (srt : ItemSort) (i : Nat) : M Unit :=
  if i < s.len srt then pure () else throw (oobMsg srt i)

/-- The type at an index. -/
def Scope.ty (s : Scope) (i : Nat) : M TyInfo :=
  match s.types[i]? with
  | some t => pure t
  | none => throw (oobMsg .type i)

/-- The core type at an index. -/
def Scope.cty (s : Scope) (i : Nat) : M CTyInfo :=
  match s.ctypes[i]? with
  | some t => pure t
  | none => throw (oobMsg (.core .type) i)

/-- The core function type at an index. -/
def Scope.cfunc (s : Scope) (i : Nat) : M (Option CFT) :=
  match s.cfuncs[i]? with
  | some t => pure t
  | none => throw (oobMsg (.core .func) i)

/-! ## Core modules -/

open Silmaril.Wasm in
def externTypeSort : ExternType → CoreSort
  | .func _ => .func | .table _ => .table | .memory _ => .memory | .global _ => .global
  | .tag _ => .tag

open Silmaril.Wasm in
/-- A core value type as wasmparser prints it in signatures. -/
def coreValName : Silmaril.Wasm.ValType → String
  | .num (.int .i32) => "i32" | .num (.int .i64) => "i64"
  | .num (.float .f32) => "f32" | .num (.float .f64) => "f64"
  | .vec _ => "v128"
  | .ref r => if r.nullable && r.heap == .abstract .func then "funcref"
      else if r.nullable && r.heap == .abstract .extern then "externref" else "ref"

open Silmaril.Wasm in
/-- The function type of a core type index of a module. -/
def modFuncType (m : Module) (t : Nat) : Option CFT :=
  match m.typeDefinitions[t]? with
  | some st => match st.body with
    | .func ft => some (ft.params.map coreValName, ft.results.map coreValName)
    | _ => none
  | none => none

open Silmaril.Wasm in
/-- The core function type of each function index of a module. -/
def modFuncTypes (m : Module) : Array (Option CFT) :=
  (m.importedFunctions.map (fun t => modFuncType m t.value.val) ++
    m.funcs.map (fun f => modFuncType m f.type.value.val)).toArray

open Silmaril.Wasm in
/-- The limits of a memory or table as `[min, max]` (`-` for no maximum). -/
def limitsStr (l : Limits) : List String :=
  [toString l.min.val, match l.max with | some m => toString m.val | none => "-"]

open Silmaril.Wasm in
/-- The type of a memory, table, global or tag as a `CFT`-shaped key (`#mem`, `#table`,
`#global`, `#tag` first), for wasmparser's import matching (`exttype` subtyping). A function's
`CFT` is its signature; a 64-bit memory's starts `#mem 64`. -/
def memShape (t : MemoryType) : CFT :=
  ("#mem" :: (if t.address == .i64 then "64" else "32") :: limitsStr t.limits, [])

open Silmaril.Wasm in
def tableShape (t : TableType) : CFT :=
  ("#table" :: toString (repr t.element) :: (if t.address == .i64 then "64" else "32") ::
    limitsStr t.limits, [])

open Silmaril.Wasm in
def globalShape (t : GlobalType) : CFT :=
  ("#global" :: (if t.mutability == .var then "mut" else "const") ::
    (match t.value with
      | .ref r => ["ref", if r.nullable then "null" else "nonnull", toString (repr r.heap)]
      | v => [toString (repr v)]), [])

/-- Whether a `CFT` key is a 64-bit memory's. -/
def isMem64 : Option CFT → Bool
  | some ("#mem" :: "64" :: _, _) => true
  | _ => false

/-- wasmparser's matching of an import's memory, table, global or tag type `imp` by an
export's `act`: the same kind and index width, limits within the import's (a larger
minimum, a maximum no larger), equal element, global and tag types. -/
def shapeSub (imp act : CFT) : Bool :=
  let lim (mn mx mn' mx' : String) : Bool :=
    mn'.toNat! ≥ mn.toNat! && (mx == "-" || (mx' != "-" && mx'.toNat! ≤ mx.toNat!))
  match imp.1, act.1 with
  | ["#mem", w, mn, mx], ["#mem", w', mn', mx'] => w == w' && lim mn mx mn' mx'
  | ["#table", r, w, mn, mx], ["#table", r', w', mn', mx'] => r == r' && w == w' && lim mn mx mn' mx'
  -- an immutable global is covariant: a reference with the same heap type may drop `null`;
  -- other heap types are not compared here (accepted)
  | ["#global", "const", "ref", n, h], ["#global", "const", "ref", n', h'] =>
    h != h' || n == n' || n == "null"
  | "#global" :: g, "#global" :: g' => g == g'
  | "#tag" :: _, "#tag" :: _ => imp == act
  | _, _ => true

open Silmaril.Wasm in
/-- The memories, tables and globals of a module, imported ones first. -/
def modMems (m : Module) : Array MemoryType :=
  (m.imports.filterMap (fun i => match i.type with | .memory t => some t | _ => none) ++
    m.memories).toArray

open Silmaril.Wasm in
def modTables (m : Module) : Array TableType :=
  (m.imports.filterMap (fun i => match i.type with | .table t => some t | _ => none) ++
    m.tables.map (·.type)).toArray

open Silmaril.Wasm in
def modGlobals (m : Module) : Array GlobalType :=
  (m.imports.filterMap (fun i => match i.type with | .global t => some t | _ => none) ++
    m.globals.map (·.type)).toArray

open Silmaril.Wasm in
/-- The type key of an import (`none` when not known). -/
def importShape (m : Module) : ExternType → Option CFT
  | .func t => modFuncType m t.value.val
  | .memory t => some (memShape t)
  | .table t => some (tableShape t)
  | .global t => some (globalShape t)
  | .tag t => (modFuncType m t.value.val).map fun (p, r) => ("#tag" :: p, r)

open Silmaril.Wasm in
/-- The sort and type key of an export. -/
def exportInfo (m : Module) (fts : Array (Option CFT)) : ExternIdx → CoreSort × Option CFT
  | .func i => (.func, fts[i.value.val]?.getD none)
  | .memory i => (.memory, (modMems m)[i.value.val]?.map memShape)
  | .table i => (.table, (modTables m)[i.value.val]?.map tableShape)
  | .global i => (.global, (modGlobals m)[i.value.val]?.map globalShape)
  | .tag _ => (.tag, none)

/-- Read an embedded core module's imports and exports (`check` has validated it already). -/
def coreModule (F : WFeatures) (b : ByteArray) : M ModSig := do
    match Validate.decodeW F b with
    | .error e => throw e
    | .ok m =>
      let imps := m.imports.map fun i => (i.moduleName, i.name, externTypeSort i.type,
        importShape m i.type)
      let keys := imps.map fun (a, b, _) => s!"{a}:{b}"
      if let some k := keys.find? (fun k => (keys.filter (· == k)).length > 1) then
        throw s!"module has a duplicate import name `{k}` that is not allowed in components"
      let fts := modFuncTypes m
      return (imps, m.exports.map fun e =>
        let (s, t) := exportInfo m fts e.index; (e.name, s, t))

def descSort : CoreImportDesc → CoreSort
  | .func _ => .func | .table .. => .table | .memory _ => .memory | .global .. => .global
  | .tag _ => .tag

/-! ## Names -/

/-- Semantic versions (`semver::Version::parse`): `MAJOR.MINOR.PATCH`, numbers without leading
zeros, optional `-PRE` and `+BUILD` of non-empty dot-separated identifiers. -/
def semverOk (v : String) : Bool :=
  let (core, build) : String × Option String := match v.splitOn "+" with
    | [c] => (c, some "")
    | [c, b] => (c, some b)
    | _ => ("", none)
  match build with
  | none => false
  | some b =>
    let (core, pre) : String × Option String := match core.splitOn "-" with
      | c :: rest => (c, if rest.isEmpty then none else some (String.intercalate "-" rest))
      | [] => ("", none)
    let num (s : String) := !s.isEmpty && s.all Char.isDigit && (s == "0" || !s.startsWith "0")
    let ident (s : String) := !s.isEmpty && s.all fun c => c.isAlphanum || c == '-'
    let ids (s : String) := (s.splitOn ".").all ident
    (match core.splitOn "." with
      | [a, b, c] => num a && num b && num c
      | _ => false) &&
    (match pre with | some p => ids p | none => true) &&
    (!v.contains '+' || ids b)

/-- The canonical prefix of a version (`split_canonical_version`): `MAJOR` when it is not 0,
else `0.MINOR` when MINOR is not 0, else the version without `+BUILD` (also with a `-PRE`). -/
def canonicalVersion (v : String) : String :=
  let noBuild := (v.splitOn "+").headD v
  if noBuild.contains '-' then noBuild else
  match noBuild.splitOn "." with
  | maj :: mi :: _ => if maj != "0" then maj else if mi != "0" then s!"0.{mi}" else noBuild
  | _ => noBuild

/-- Check an import or export name: its grammar, its attributes, uniqueness among `keys`. -/
def checkName (F : WFeatures) (what : String) (keys : List String) (n : ExternName)
    (srt : ItemSort) : M String := do
  let kind ← match parseName F n.name with
    | .ok k => pure k
    | .error e => throw s!"{what} name `{n.name}` is not a valid extern name: {e}"
  let attrs := match n.form with | .attrs as => as | _ => []
  let suffix := attrs.findSome? fun | .versionSuffix s => some s | _ => none
  let impl := attrs.findSome? fun | .implements s => some s | _ => none
  if !attrs.isEmpty && !F.hasFlag "cm-implements" && !F.hasFlag "cm-canon-names" then
    throw "the `cm-implements` feature is not active"
  if let some s := suffix then
    if !F.hasFlag "cm-canon-names" then throw "the `cm-canon-names` feature is not active"
    if srt != .instance then throw "only instances can have a `version-suffix`"
    if s.isEmpty then throw "version suffix cannot be empty"
    if impl.isNone && kind != .interface then
      throw "`version-suffix` requires an interface name or `implements`"
  if let some i := impl then
    if !F.hasFlag "cm-implements" then throw "the `cm-implements` feature is not active"
    if kind != .plain || n.name.startsWith "[" then
      throw s!"name `{n.name}` is not valid with `implements`"
    if srt != .instance then throw "only instances can have an `implements`"
    match parseName F i with
    | .ok .interface => pure ()
    | _ => throw s!"name `{i}` must be an interface"
  if attrs.any (fun | .externalId _ => true | _ => false) && !F.hasFlag "cm-implements" then
    throw "the `cm-implements` feature is not active"
  -- the version of an interface name
  if kind == .interface then
    match n.name.splitOn "@", suffix with
    | [_], none => pure ()
    | [_], some _ =>
      throw "invalid interface version: a version suffix requires the name to have a version"
    | [_, v], none =>
      if !semverOk v then throw s!"invalid interface version: `{v}` is not a semantic version"
    | [_, v], some s =>
      if !semverOk (v ++ s) then
        throw s!"invalid interface version: `{v ++ s}` is not a semantic version"
      if canonicalVersion (v ++ s) != v then
        throw s!"invalid interface version: `{v}` is not the canonical version of `{v ++ s}`"
    | _, _ => throw "invalid interface version"
  let k := nameKey n.name
  if keys.contains k then
    throw s!"{what} name `{n.name}` conflicts with previous name `{n.name}`"
  return k

/-! ## Types -/

/-- Duplicate labels (as kebab strings). -/
def dupLabel (ls : List String) : Option String :=
  let ks := ls.map canonChars
  (ls.zip ks).find? (fun (_, k) => (ks.filter (· == k)).length > 1) |>.map (·.1)

/-- Resolve a value type reference. -/
def resolveVal (F : WFeatures) (s : Scope) : Silmaril.Wasm.Component.Binary.ValType → M RTy
  | .prim .errorContext => do
    if !F.hasFlag "cm-error-context" then
      throw "`error-context` requires the component model error-context feature"
    pure (.prim .errorContext)
  | .prim p => pure (.prim p)
  | .idx i => do
    match ← s.ty i with
    | .val t => pure t
    | .unknown => pure .unknown
    | _ => throw s!"type index {i} is not a defined type"

def resolveOpt (F : WFeatures) (s : Scope) :
    Option Silmaril.Wasm.Component.Binary.ValType → M (Option RTy)
  | some t => some <$> resolveVal F s t
  | none => pure none

/-- The identity of a resource type index. -/
def resourceId (s : Scope) (i : Nat) : M Nat := do
  match ← s.ty i with
  | .resource r _ => pure r
  | .unknown => fresh
  | _ => throw s!"type index {i} is not a resource type"

/-! ## Termination helpers -/

theorem sizeOf_snd_lt_of_mem {α β : Type} [SizeOf α] [SizeOf β] {p : α × β}
    {l : List (α × β)} (h : p ∈ l) : sizeOf p.2 < sizeOf l := by
  have := List.sizeOf_lt_of_mem h
  obtain ⟨a, b⟩ := p
  simp at this ⊢
  omega

theorem sizeOf_zip_fst_lt {α β : Type} [SizeOf α] [SizeOf β] {p : α × β} {l₁ : List α}
    {l₂ : List β} (h : p ∈ l₁.zip l₂) : sizeOf p.1 < sizeOf l₁ := by
  obtain ⟨a, b⟩ := p
  exact List.sizeOf_lt_of_mem (List.of_mem_zip h).1

theorem sizeOf_zip_fst_snd_lt {α β γ : Type} [SizeOf α] [SizeOf β] [SizeOf γ]
    {p : (α × β) × γ} {l₁ : List (α × β)} {l₂ : List γ} (h : p ∈ l₁.zip l₂) :
    sizeOf p.1.2 < sizeOf l₁ := by
  obtain ⟨⟨a, b⟩, c⟩ := p
  have := List.sizeOf_lt_of_mem (List.of_mem_zip h).1
  simp at this ⊢
  omega

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- Does a resolved type contain `borrow`? -/
def RTy.hasBorrow : RTy → Bool
  | .borrow _ => true
  | .record _ fs => fs.attach.any fun ⟨(_, t), _⟩ => t.hasBorrow
  | .variant _ cs => cs.attach.any fun ⟨(_, t), _⟩ => match t with
    | some t => t.hasBorrow
    | none => false
  | .list t | .option t | .fixedList t _ => t.hasBorrow
  | .tuple ts => ts.attach.any fun ⟨t, _⟩ => t.hasBorrow
  | .result a b => (match a with | some t => t.hasBorrow | none => false) ||
      (match b with | some t => t.hasBorrow | none => false)
  | .map k v => k.hasBorrow || v.hasBorrow
  | _ => false
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)
    | (have := sizeOf_snd_lt_of_mem ‹_ ∈ _›; simp_all; omega)

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- Does a resolved type contain a pointer (a string or list)? -/
def RTy.hasPtr : RTy → Bool
  | .prim .string | .list _ | .map .. => true
  | .record _ fs => fs.attach.any fun ⟨(_, t), _⟩ => t.hasPtr
  | .variant _ cs => cs.attach.any fun ⟨(_, t), _⟩ => match t with
    | some t => t.hasPtr
    | none => false
  | .option t | .fixedList t _ => t.hasPtr
  | .tuple ts => ts.attach.any fun ⟨t, _⟩ => t.hasPtr
  | .result a b => (match a with | some t => t.hasPtr | none => false) ||
      (match b with | some t => t.hasPtr | none => false)
  | _ => false
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)
    | (have := sizeOf_snd_lt_of_mem ‹_ ∈ _›; simp_all; omega)

/-- Resolve and check a defined value type. -/
def checkDefVal (F : WFeatures) (s : Scope) : DefValType → M RTy
  | .prim p => resolveVal F s (.prim p)
  | .record fs => do
    if fs.isEmpty then throw "record type must have at least one field"
    let mut out := []
    for (n, t) in fs do
      if !isKebab n then throw s!"record field name `{n}` is not in kebab case"
      out := out ++ [(n, ← resolveVal F s t)]
    if let some d := dupLabel (fs.map (·.1)) then
      throw s!"record field name `{d}` conflicts with previous field name `{d}`"
    pure (.record (← fresh) out)
  | .variant cs => do
    if cs.isEmpty then throw "variant type must have at least one case"
    let mut out := []
    for (n, t) in cs do
      if !isKebab n then throw s!"variant case name `{n}` is not in kebab case"
      out := out ++ [(n, ← resolveOpt F s t)]
    if let some d := dupLabel (cs.map (·.1)) then
      throw s!"variant case name `{d}` conflicts with previous case name `{d}`"
    pure (.variant (← fresh) out)
  | .list t => .list <$> resolveVal F s t
  | .tuple ts => do
    if ts.isEmpty then throw "tuple type must have at least one type"
    .tuple <$> ts.mapM (resolveVal F s)
  | .flags ls => do
    if ls.isEmpty then throw "flags must have at least one entry"
    if ls.length > 32 then throw "cannot have more than 32 flags"
    for l in ls do
      if !isKebab l then throw s!"flag name `{l}` is not in kebab case"
    if let some d := dupLabel ls then
      throw s!"flag name `{d}` conflicts with previous flag name `{d}`"
    pure (.flags (← fresh) ls)
  | .enum ls => do
    if ls.isEmpty then throw "enum type must have at least one variant"
    for l in ls do
      if !isKebab l then throw s!"enum tag name `{l}` is not in kebab case"
    if let some d := dupLabel ls then
      throw s!"enum tag name `{d}` conflicts with previous tag name `{d}`"
    pure (.enum (← fresh) ls)
  | .option t => .option <$> resolveVal F s t
  | .result ok err => do pure (.result (← resolveOpt F s ok) (← resolveOpt F s err))
  | .own i => .own <$> resourceId s i
  | .borrow i => .borrow <$> resourceId s i
  | .fixedList t n => do
    if !F.hasFlag "cm-fixed-length-lists" then
      throw "Fixed-length lists require the component model fixed-length lists feature"
    if n = 0 then throw "Fixed-length list must have more than zero elements"
    pure (.fixedList (← resolveVal F s t) n)
  | .stream t => do
    if !F.hasFlag "cm-async" then throw "`stream` requires the component model async feature"
    let t ← resolveOpt F s t
    if t.any RTy.hasBorrow then throw "stream payload cannot contain a `borrow` type"
    pure (.stream t)
  | .future t => do
    if !F.hasFlag "cm-async" then throw "`future` requires the component model async feature"
    let t ← resolveOpt F s t
    if t.any RTy.hasBorrow then throw "future payload cannot contain a `borrow` type"
    pure (.future t)
  | .map k v => do
    if !F.hasFlag "cm-map" then throw "Maps require the component model map feature"
    let k ← resolveVal F s k
    match k with
    | .prim p =>
      if p == .f32 || p == .f64 || p == .errorContext then throw "invalid map key type"
    | .unknown => pure ()
    | _ => throw "invalid map key type"
    let v ← resolveVal F s v
    pure (.map k v)

/-- Resolve and check a function type. -/
def checkFuncType (F : WFeatures) (s : Scope) (f : Silmaril.Wasm.Component.Binary.FuncType) :
    M FTy := do
  if f.async && !F.hasFlag "cm-async" then
    throw "async component functions require the component model async feature"
  let mut ps := []
  for (n, t) in f.params do
    if !isKebab n then throw s!"function parameter name `{n}` is not in kebab case"
    ps := ps ++ [(n, ← resolveVal F s t)]
  if let some d := dupLabel (f.params.map (·.1)) then
    throw s!"function parameter name `{d}` conflicts with previous parameter name `{d}`"
  let r ← resolveOpt F s f.result
  if r.any RTy.hasBorrow then throw "function result cannot contain a `borrow` type"
  pure ⟨ps, r, f.async⟩

/-! ## The canonical ABI flattening (`push_wasm_types`) -/

/-- `join_types`. -/
def joinTy (a b : String) : String :=
  if a == b then a else if (a == "i32" && b == "f32") || (a == "f32" && b == "i32") then "i32"
  else "i64"

/-- Merge the flattening of a variant case into the joined payload. -/
def joinList : List String → List String → List String
  | a :: as, b :: bs => joinTy a b :: joinList as bs
  | [], bs => bs
  | as, [] => as

/-- The flattening of a sequence of types, given the flattening of each (`none` when one
does not fit). -/
def flatAll (cap : Nat) (fs : List (Option (List String))) : Option (List String) :=
  fs.foldlM (fun acc f => do
    let f ← f
    let r := acc ++ f
    if r.length > cap then none else some r) []

/-- The flattening of a variant, given the flattening of each case with a payload: the
discriminant, then the joined cases. -/
def flatVariant (cap : Nat) (fs : List (Option (List String))) : Option (List String) := do
  let cases ← fs.mapM id
  let r := "i32" :: cases.foldl joinList []
  if r.length > cap then none else some r

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- The flattened core types of a value type, `none` when longer than `cap`. -/
def flat (ptr : String) (cap : Nat) : RTy → Option (List String)
  | .prim p => some (match p with
    | .s64 | .u64 => ["i64"] | .f32 => ["f32"] | .f64 => ["f64"] | .string => [ptr, ptr]
    | _ => ["i32"])
  | .record _ fs => flatAll cap (fs.attach.map fun ⟨(_, t), _⟩ => flat ptr cap t)
  | .tuple ts => flatAll cap (ts.attach.map fun ⟨t, _⟩ => flat ptr cap t)
  | .list _ | .map .. => some [ptr, ptr]
  | .fixedList t n => do
    let e ← flat ptr cap t
    if e.length * n > cap then none else some ((List.replicate n e).flatten)
  | .flags _ n => some (List.replicate ((n.length + 31) / 32) "i32")
  | .enum .. | .own _ | .borrow _ | .stream _ | .future _ => some ["i32"]
  | .variant _ cs => flatVariant cap (cs.attach.filterMap fun ⟨(_, t), _⟩ => match t with
    | some t => some (flat ptr cap t)
    | none => none)
  | .option t => flatVariant cap [flat ptr cap t]
  | .result a b => flatVariant cap
    ((match a with | some t => [flat ptr cap t] | none => []) ++
      (match b with | some t => [flat ptr cap t] | none => []))
  | .unknown => some ["?"]
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)
    | (have := sizeOf_snd_lt_of_mem ‹_ ∈ _›; simp_all; omega)

/-- The flattening within `cap` entries. -/
def flatC (ptr : String) (cap : Nat) (t : RTy) : Option (List String) :=
  (flat ptr cap t).filter (·.length ≤ cap)

/-- The lowering direction. -/
inductive Abi where
  | lift
  | lower
  deriving DecidableEq

/-- The canonical options in force. -/
structure Opts where
  /-- `memory`, and whether it is 64-bit. -/
  memory : Option Bool := none
  realloc : Option Nat := none
  postReturn : Option Nat := none
  async : Bool := false
  callback : Option Nat := none

def Opts.ofList (os : List CanonOpt) : Opts :=
  os.foldl (fun o x => match x with
    | .memory _ => { o with memory := some false }
    | .realloc i => { o with realloc := some i }
    | .postReturn i => { o with postReturn := some i }
    | .async => { o with async := true }
    | .callback i => { o with callback := some i }
    | _ => o) {}

def needMemory (o : Opts) (b : Bool) : M Unit :=
  if b && o.memory.isNone then throw "canonical option `memory` is required" else pure ()

def needRealloc (o : Opts) (b : Bool) : M Unit := do
  if b then
    needMemory o true
    if o.realloc.isNone then throw "canonical option `realloc` is required"

/-- **`ComponentFuncType::lower`**: the core signature of a lifted or lowered function, and the
options it requires. A `?` entry stands for a type of unknown structure. -/
def lowerSig (f : FTy) (o : Opts) (abi : Abi) : M CFT := do
  let maxP := if abi == .lower && o.async then 4 else 16
  let ptr := if o.memory == some true then "i64" else "i32"
  let mut ps : List String := []
  let mut over := false
  for (_, t) in f.params do
    if !over then
      match abi with
      | .lower => needMemory o t.hasPtr
      | .lift => needRealloc o t.hasPtr
      match flatC ptr maxP t with
      | some l =>
        if ps.length + l.length ≤ maxP then ps := ps ++ l
        else over := true
      | none => over := true
      if over then
        ps := [ptr]
        needMemory o true
        if abi == .lift then needRealloc o true
  if let some r := f.result then
    needRealloc o (abi == .lower && r.hasPtr)
  match abi, o.async with
  | _, false =>
    match f.result with
    | none => pure (ps, [])
    | some r =>
      match flatC ptr 1 r with
      | some l => pure (ps, l)
      | none =>
        needMemory o true
        match abi with
        | .lower => pure (ps ++ [ptr], [])
        | .lift => pure (ps, [ptr])
  | .lower, true =>
    if f.result.isSome then
      needMemory o true
      pure (ps ++ [ptr], ["i32"])
    else pure (ps, ["i32"])
  | .lift, true =>
    if let some r := f.result then
      needMemory o ((flatC ptr 16 r).isNone || r.hasPtr)
    pure (ps, if o.callback.isSome then ["i32"] else [])

/-- Equal core signatures, an unknown (`?`) entry matching anything. -/
def cftEq (a b : CFT) : Bool :=
  let eq (x y : List String) := x.length == y.length &&
    (x.zip y).all fun (p, q) => p == q || p == "?" || q == "?"
  (a.1.contains "?" || b.1.contains "?" || eq a.1 b.1) &&
    (a.2.contains "?" || b.2.contains "?" || eq a.2 b.2)

/-- wasmparser's spelling of a core function type. -/
def cftShow (t : CFT) : String :=
  "(func" ++ (if t.1.isEmpty then "" else " (param " ++ " ".intercalate t.1 ++ ")") ++
    (if t.2.isEmpty then "" else " (result " ++ " ".intercalate t.2 ++ ")") ++ ")"

/-! ## The named-types rule of imports and exports (`validate_and_register_named_types`) -/

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- `type_named_valtype`: records, variants, flags and enums must be named themselves, other
types through their components, handles through their resources. -/
def namedVal (set : List Nat) : RTy → Bool
  | .record id _ | .variant id _ | .flags id _ | .enum id _ => set.contains id
  | .tuple ts => ts.attach.all fun ⟨t, _⟩ => namedVal set t
  | .result a b => (match a with | some t => namedVal set t | none => true) &&
      (match b with | some t => namedVal set t | none => true)
  | .list t | .option t | .fixedList t _ => namedVal set t
  | .map k v => namedVal set k && namedVal set v
  | .own r | .borrow r => set.contains r
  | .stream t | .future t => match t with | some t => namedVal set t | none => true
  | _ => true
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)
    | (have := sizeOf_snd_lt_of_mem ‹_ ∈ _›; simp_all; omega)

/-- `all_valtypes_named_in_defined`. -/
def namedDefined (set : List Nat) : RTy → Bool
  | .record _ fs => fs.all fun (_, t) => namedVal set t
  | .variant _ cs => cs.all fun (_, t) => t.all (namedVal set)
  | .flags .. | .enum .. | .prim _ => true
  | t => namedVal set t

/-- `all_valtypes_named_in_func`. -/
def namedFunc (set : List Nat) (f : FTy) : Bool :=
  f.params.all (fun (_, t) => namedVal set t) && f.result.all (namedVal set)

/-- The identity of a type, where it has one. -/
def TyInfo.id? : TyInfo → Option Nat
  | .val (.record i _) | .val (.variant i _) | .val (.flags i _) | .val (.enum i _) => some i
  | .resource r _ => some r
  | _ => none

/-- A fresh identity for the type an import or export creates (`with_unique`). -/
def retag : TyInfo → M TyInfo
  | .val (.record _ fs) => do pure (.val (.record (← fresh) fs))
  | .val (.variant _ cs) => do pure (.val (.variant (← fresh) cs))
  | .val (.flags _ n) => do pure (.val (.flags (← fresh) n))
  | .val (.enum _ n) => do pure (.val (.enum (← fresh) n))
  | t => pure t

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
mutual
/-- `all_valtypes_named` of a type. -/
def namedTy (set : List Nat) : TyInfo → Bool
  | .val t => namedDefined set t
  | .func f => namedFunc set f
  | .inst exps => namedInst set exps
  | _ => true
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)
    | (have := sizeOf_snd_lt_of_mem ‹_ ∈ _›; simp_all; omega)

/-- `all_valtypes_named_in_instance`: types exported by the instance are named within it. -/
def namedInst (set : List Nat) : List (String × Ent) → Bool
  | [] => true
  | (_, e) :: rest =>
    match e with
    | .func (some f) => namedFunc set f && namedInst set rest
    | .ty t =>
      let ok := namedTy set t
      ok && namedInst (match t.id? with | some i => i :: set | none => set) rest
    | .inst (some ex) => namedInst set ex && namedInst set rest
    | _ => namedInst set rest
termination_by l => sizeOf l
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)
    | (have := sizeOf_snd_lt_of_mem ‹_ ∈ _›; simp_all; omega)
end

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- Register an import or export (the named-types rule), giving the entry it creates. -/
def registerNamed (s : Scope) (isImport : Bool) (top : Bool) (e : Ent) : M (Scope × Ent) := do
  if s.isInst then return (s, e)
  let what := if isImport then "import" else "export"
  let set := if isImport then s.impSet else s.expSet
  let bad : M (Scope × Ent) := throw s!"{(sortName e.sort)} not valid to be used as {what}"
  match e with
  | .ty t =>
    if isImport then
      if let some i := t.id? then
        if s.expSet.contains i && !s.impSet.contains i then return ← bad
    if !namedTy set t then return ← bad
    let t' ← if top then retag t else pure t
    let ids := t'.id?.toList
    let s := if isImport then { s with impSet := ids ++ s.impSet, expSet := ids ++ s.expSet }
      else { s with expSet := ids ++ s.expSet }
    return (s, .ty t')
  | .inst (some exps) =>
    let mut s := s
    for _h : p in exps do
      s := (← registerNamed s isImport false p.2).1
    return (s, e)
  | .func (some f) => if namedFunc set f then return (s, e) else bad
  | _ => return (s, e)
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)
    | (have := sizeOf_snd_lt_of_mem ‹_ ∈ _›; simp_all; omega)

/-! ## Resource function names (`ComponentNameContext::validate`) -/

/-- The resource a `[constructor]R`, `[method]R.m` or `[static]R.m` name refers to, and its kind
(0, 1, 2). -/
def resourceFuncName (n : String) : Option (Nat × String) :=
  match eatStr "[constructor]" n with
  | some r => some (0, r)
  | none =>
    let noAcc (r : String) := (eatStr "[get]" r).getD ((eatStr "[set]" r).getD r)
    let dotted (k : Nat) (r : String) := match (noAcc r).splitOn "." with
      | res :: _ :: _ => some (k, res)
      | _ => none
    match eatStr "[method]" n with
    | some r => dotted 1 r
    | none => match eatStr "[static]" n with
      | some r => dotted 2 r
      | none => none

/-- Check a resource function's name against its type and the resources named in the context
`ctx` (resource identity ↦ name), as wasmparser's `validate` does. -/
def checkResourceFunc (ctx : List (Nat × String)) (n : String) (e : Ent) : M Unit := do
  match resourceFuncName n with
  | none => return ()
  | some (k, res) =>
  let f ← match e with
    | .func (some f) => pure f
    | .func none => return ()
    | _ => throw "item is not a func"
  let named (r : Nat) : M Unit :=
    match ctx.lookup r with
    | none => throw "resource used in function does not have a name in this context"
    | some nm =>
      if nm != res then throw s!"function does not match expected resource name `{nm}`"
      else pure ()
  match k with
  | 0 =>
    if f.async then throw "constructor function cannot be async"
    match f.result with
    | none => throw "function should return one value"
    | some (.own r) | some (.result (some (.own r)) _) => named r
    | some .unknown | some (.result (some .unknown) _) => pure ()
    | some _ => throw "function should return `(own $T)` or `(result (own $T))`"
  | 1 =>
    match f.params with
    | [] => throw "function should have at least one argument"
    | (pn, pt) :: _ =>
      if pn != "self" then throw "function should have a first argument called `self`"
      match pt with
      | .borrow r => named r
      | .unknown => pure ()
      | _ => throw "function should take a first argument of `(borrow $T)`"
  | _ =>
    if !(ctx.any (·.2 == res)) then throw "static resource name is not known in this context"

/-- Check a top-level import or export name against the resources named so far, then name the
resource it introduces (if any). -/
def nameResources (s : Scope) (isImport : Bool) (n : String) (e : Ent) : M Scope := do
  checkResourceFunc (if isImport then s.impRes else s.expRes) n e
  match e with
  | .ty (.resource r _) =>
    -- the first name of a resource is its name (`register` keeps one per alias)
    if isImport then return { s with impRes := s.impRes ++ [(r, n)] }
    else return { s with expRes := s.expRes ++ [(r, n)] }
  | _ => return s

/-! ## Substitution at instantiation -/

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- Rename resources in a value type. -/
def RTy.subst (m : List (Nat × Nat × Bool)) : RTy → RTy
  | .own r => .own ((m.lookup r).map (·.1) |>.getD r)
  | .borrow r => .borrow ((m.lookup r).map (·.1) |>.getD r)
  | .record i fs =>
    .record ((m.lookup i).map (·.1) |>.getD i) (fs.attach.map fun ⟨(n, t), _⟩ => (n, t.subst m))
  | .variant i cs =>
    .variant ((m.lookup i).map (·.1) |>.getD i) (cs.attach.map fun ⟨(n, t), _⟩ => (n, match t with
      | some t => some (t.subst m)
      | none => none))
  | .flags i n => .flags ((m.lookup i).map (·.1) |>.getD i) n
  | .enum i n => .enum ((m.lookup i).map (·.1) |>.getD i) n
  | .list t => .list (t.subst m)
  | .tuple ts => .tuple (ts.attach.map fun ⟨t, _⟩ => t.subst m)
  | .option t => .option (t.subst m)
  | .result a b => .result (match a with | some t => some (t.subst m) | none => none)
      (match b with | some t => some (t.subst m) | none => none)
  | .fixedList t n => .fixedList (t.subst m) n
  | .stream t => .stream (match t with | some t => some (t.subst m) | none => none)
  | .future t => .future (match t with | some t => some (t.subst m) | none => none)
  | .map k v => .map (k.subst m) (v.subst m)
  | t => t
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)
    | (have := sizeOf_snd_lt_of_mem ‹_ ∈ _›; simp_all; omega)

def FTy.subst (m : List (Nat × Nat × Bool)) (f : FTy) : FTy :=
  { f with params := f.params.map (fun (n, t) => (n, t.subst m)), result := f.result.map (·.subst m) }

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
mutual
/-- Rename resources in a type; resources not renamed are no longer local. -/
def TyInfo.subst (m : List (Nat × Nat × Bool)) : TyInfo → TyInfo
  | .val t => .val (t.subst m)
  | .func f => .func (f.subst m)
  | .resource r _ => match m.lookup r with
    | some (r', l) => .resource r' l
    | none => .resource r false
  | .inst ex => .inst (ex.attach.map fun ⟨(n, e), _⟩ => (n, e.subst m))
  | t => t
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)
    | (have := sizeOf_snd_lt_of_mem ‹_ ∈ _›; simp_all; omega)

/-- Rename resources in an entry. -/
def Ent.subst (m : List (Nat × Nat × Bool)) : Ent → Ent
  | .func f => .func (f.map (·.subst m))
  | .ty t => .ty (t.subst m)
  | .inst ex => .inst (match ex with
    | some ex => some (ex.attach.map fun ⟨(n, e), _⟩ => (n, e.subst m))
    | none => none)
  | e => e
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)
    | (have := sizeOf_snd_lt_of_mem ‹_ ∈ _›; simp_all; omega)
end

/-! ## Extern descriptors -/

/-- The sort an extern descriptor declares. -/
def descItemSort : ExternDesc → ItemSort
  | .coreModule _ => .core .module | .func _ => .func | .value _ => .value
  | .type _ => .type | .component _ => .component | .instance _ => .instance

/-- Check an extern descriptor and give the entry it declares. -/
def checkDesc (F : WFeatures) (s : Scope) : ExternDesc → M Ent
  | .coreModule i => do
    match ← s.cty i with
    | .module sig => pure (.module (some sig))
    | .unknown => pure (.module none)
    | _ => throw s!"core type index {i} is not a module type"
  | .func i => do
    match ← s.ty i with
    | .func f => pure (.func (some f))
    | .unknown => pure (.func none)
    | _ => throw s!"type index {i} is not a function type"
  | .value b => do
    if !F.hasFlag "cm-values" then
      throw "support for component model `value`s is not enabled"
    match b with
    | .eq i => s.idx .value i
    | .type t => let _ ← resolveVal F s t
    pure (.other .value)
  | .type b => do
    match b with
    | .eq i => pure (.ty (← s.ty i))
    | .subResource => pure (.ty (.resource (← fresh) false))
  | .component i => do
    match ← s.ty i with
    | .comp im ex => pure (.comp (some (im, ex)))
    | .unknown => pure (.comp none)
    | _ => throw s!"type index {i} is not a component type"
  | .instance i => do
    match ← s.ty i with
    | .inst ex => pure (.inst (some ex))
    | .unknown => pure (.inst none)
    | _ => throw s!"type index {i} is not an instance type"

/-! ## Aliases -/

/-- The entry an outer alias copies. -/
def outerEntry (s outer : Scope) (srt : ItemSort) (i : Nat) : M Scope := do
  outer.idx srt i
  match srt with
  | .type => pure (s.pushEnt (outer.ent .type i))
  | .core .type => pure { s with ctypes := s.ctypes.push (outer.ctypes[i]?.getD .unknown) }
  | .core .module => pure { s with cmodules := s.cmodules.push (outer.cmodules[i]?.getD none) }
  | .component => pure (s.pushEnt (outer.ent .component i))
  | _ => throw "invalid leading byte for component outer alias kind"

/-- Check an alias; `outers` are the enclosing scopes, innermost first. -/
def checkAlias (s : Scope) (outers : List Scope) (a : Alias) : M Scope := do
  match a.target with
  | .export inst name =>
    s.idx .instance inst
    match s.insts[inst]? with
    | some (some ex) =>
      match ex.find? (·.1 == name) with
      | none => throw s!"instance {inst} has no export named `{name}`"
      | some (_, e) =>
        if e.sort != a.sort then
          throw s!"expected {sortName a.sort}, found {sortName e.sort} for export `{name}`"
        pure (s.pushEnt e)
    | _ => pure (s.pushEnt (.other a.sort))
  | .coreExport inst name =>
    s.idx (.core .instance) inst
    match a.sort with
    | .core c =>
      match s.cinsts[inst]? with
      | some (some ex) =>
        match ex.find? (·.1 == name) with
        | none => throw s!"core instance {inst} has no export named `{name}`"
        | some (_, c', ft) =>
          if c' != c then
            throw s!"expected {coreSortName c}, found {coreSortName c'} for export `{name}`"
          if c == .func then pure { s with cfuncs := s.cfuncs.push ft }
          else if c == .memory then pure { s with cmems := s.cmems.push (isMem64 ft) }
          else pure (s.pushCore c)
      | _ => pure (s.pushCore c)
    | _ => throw "invalid alias kind"
  | .outer count i =>
    if count = 0 then outerEntry s s a.sort i
    else
      match outers[count - 1]? with
      | none => throw s!"invalid outer alias count of {count}"
      | some o => outerEntry s o a.sort i

/-! ## Canonical built-ins -/

/-- The name wasmparser uses for a canonical option. -/
def optName : CanonOpt → String
  | .utf8 => "utf8" | .utf16 => "utf16" | .latin1utf16 => "latin1-utf16"
  | .memory _ => "memory" | .realloc _ => "realloc" | .postReturn _ => "post-return"
  | .async => "async" | .callback _ => "callback"

def optTag : CanonOpt → Nat
  | .utf8 | .utf16 | .latin1utf16 => 0
  | .memory _ => 1 | .realloc _ => 2 | .postReturn _ => 3 | .async => 4 | .callback _ => 5

/-- Check canonical options: indices in bounds, no repeats, one string encoding, `realloc`'s
signature. -/
def checkOpts (F : WFeatures) (s : Scope) (lift : Bool) (os : List CanonOpt) : M Opts := do
  let mut seen : List CanonOpt := []
  let mem64 := os.any fun | .memory i => s.cmems[i]?.getD false | _ => false
  let p := if mem64 then "i64" else "i32"
  for o in os do
    match seen.find? (fun p => optTag p == optTag o) with
    | some p =>
      if optTag o = 0 then
        throw s!"canonical encoding option `{optName p}` conflicts with option `{optName o}`"
      else throw s!"canonical option `{optName o}` is specified more than once"
    | none => pure ()
    seen := seen ++ [o]
    match o with
    | .memory i => s.idx (.core .memory) i
    | .realloc i =>
      if let some t ← s.cfunc i then
        if !cftEq t ([p, p, p, p], [p]) then
          throw "canonical option `realloc` uses a core function with an incorrect signature"
    | .postReturn i =>
      let _ ← s.cfunc i
      if !lift then throw "canonical option `post-return` cannot be specified for lowerings"
    | .callback i =>
      let _ ← s.cfunc i
      if !lift then throw "canonical option `callback` cannot be specified for lowerings"
    | .async =>
      if !F.hasFlag "cm-async" then
        throw "canonical option `async` requires the component model async feature"
    | _ => pure ()
  let o := Opts.ofList os
  let o := if mem64 then { o with memory := some true } else o
  if o.async && o.postReturn.isSome then throw "cannot specify post-return function in async"
  if !o.async && o.callback.isSome then throw "cannot specify callback without async"
  return o

/-- The features a built-in needs. -/
def canonFeature : Canon → List String
  | .lift .. | .lower .. | .resourceNew _ | .resourceDrop _ | .resourceRep _ => []
  | .errorContextNew _ | .errorContextDebugMessage _ | .errorContextDrop => ["cm-error-context"]
  | .streamForward _ | .futureForward _ => ["cm-async", "cm-forward"]
  | .threadIndex | .threadNewIndirect .. | .threadResumeLater | .threadSuspend
  | .threadSuspendThenResume | .threadYieldThenResume | .threadSuspendThenPromote
  | .threadYieldThenPromote => ["cm-threading"]
  | .threadSpawnRef .. | .threadSpawnIndirect .. | .threadAvailableParallelism _ =>
    ["shared-everything-threads"]
  | .subtaskCancel true | .streamCancelRead _ true | .streamCancelWrite _ true
  | .futureCancelRead _ true | .futureCancelWrite _ true => ["cm-async", "cm-more-async-builtins"]
  | _ => ["cm-async"]

/-- The type index of a `stream`/`future` built-in, and whether it is a stream. -/
def canonStreamType : Canon → Option (Nat × Bool)
  | .streamNew t | .streamRead t _ | .streamWrite t _ | .streamCancelRead t _
  | .streamCancelWrite t _ | .streamDropReadable t | .streamDropWritable t
  | .streamForward t => some (t, true)
  | .futureNew t | .futureRead t _ | .futureWrite t _ | .futureCancelRead t _
  | .futureCancelWrite t _ | .futureDropReadable t | .futureDropWritable t
  | .futureForward t => some (t, false)
  | _ => none

/-- The options of a built-in. -/
def canonOpts : Canon → List CanonOpt
  | .lift _ o _ | .lower _ o | .taskReturn _ o | .streamRead _ o | .streamWrite _ o
  | .futureRead _ o | .futureWrite _ o | .errorContextNew o | .errorContextDebugMessage o => o
  | _ => []

/-- A component core value type as in signatures. -/
def coreValStr : Silmaril.Wasm.Component.Binary.CoreValType → String
  | .i32 => "i32" | .i64 => "i64" | .f32 => "f32" | .f64 => "f64" | .v128 => "v128"
  | .funcref => "funcref" | .externref => "externref"

/-- The fixed core signature of a built-in (where it does not depend on types). -/
def canonSig (p : String) : Canon → Option CFT
  | .resourceNew _ | .resourceRep _ => some (["i32"], ["i32"])
  | .resourceDrop _ => some (["i32"], [])
  | .backpressureInc | .backpressureDec | .taskCancel => some ([], [])
  | .subtaskDrop | .waitableSetDrop | .errorContextDrop => some (["i32"], [])
  | .waitableSetNew => some ([], ["i32"])
  | .waitableJoin => some (["i32", "i32"], [])
  | .waitableSetWait _ | .waitableSetPoll _ => some (["i32", p], ["i32"])
  | .subtaskCancel _ => some (["i32"], ["i32"])
  | .streamNew _ | .futureNew _ => some ([], ["i64"])
  | .streamRead .. | .streamWrite .. => some (["i32", p, p], [p])
  | .futureRead .. | .futureWrite .. => some (["i32", p], ["i32"])
  | .streamCancelRead .. | .streamCancelWrite .. | .futureCancelRead .. | .futureCancelWrite .. =>
    some (["i32"], ["i32"])
  | .streamDropReadable _ | .streamDropWritable _ | .futureDropReadable _
  | .futureDropWritable _ => some (["i32"], [])
  | .streamForward _ | .futureForward _ => some (["i32", "i32"], [])
  | .threadIndex | .threadSuspend | .threadYield => some ([], ["i32"])
  | .threadResumeLater => some (["i32"], [])
  | .threadSuspendThenResume | .threadYieldThenResume | .threadSuspendThenPromote
  | .threadYieldThenPromote => some (["i32"], ["i32"])
  | .contextGet t _ => some ([], [coreValStr t])
  | .contextSet t _ => some ([coreValStr t], [])
  | .errorContextNew _ => some ([p, p], ["i32"])
  | .errorContextDebugMessage _ => some (["i32", p], [])
  | _ => none

/-- Check a built-in and add the function it defines. -/
def checkCanon (F : WFeatures) (s : Scope) (c : Canon) : M Scope := do
  for f in canonFeature c do
    if !F.hasFlag f then throw s!"`{c.kind}` requires the `{f}` feature"
  let isLift := match c with | .lift .. => true | _ => false
  let o ← checkOpts F s isLift (canonOpts c)
  match c with
  | .streamRead .. | .streamWrite .. | .futureRead .. | .futureWrite .. =>
    if !o.async && !F.hasFlag "cm-more-async-builtins" then
      throw s!"synchronous `{c.kind}` requires the component model more async builtins feature"
  | _ => pure ()
  -- the pointer type of the built-in's memory
  let p := match c with
    | .waitableSetWait m | .waitableSetPoll m => if s.cmems[m]?.getD false then "i64" else "i32"
    | _ => if o.memory == some true then "i64" else "i32"
  if let some (t, isStream) := canonStreamType c then
    match ← s.ty t with
    | .val (.stream _) => if !isStream then throw s!"`{c.kind}` requires a future type"
    | .val (.future _) => if isStream then throw s!"`{c.kind}` requires a stream type"
    | .unknown => pure ()
    | _ => throw s!"`{c.kind}` requires a {if isStream then "stream" else "future"} type"
  match c with
  | .lift f _ t =>
    let core ← s.cfunc f
    let ft ← match ← s.ty t with
      | .func ft => pure (some ft)
      | .unknown => pure none
      | _ => throw s!"type index {t} is not a function type"
    if let some ct := core then
      if let some pr := o.postReturn then
        if let some pt ← s.cfunc pr then
          if !cftEq pt (ct.2, []) then
            throw "canonical option `post-return` uses a core function with an incorrect signature"
    if o.async && o.callback.isNone && !F.hasFlag "cm-async-stackful" then
      throw "requires the component model async stackful feature"
    if let some cb := o.callback then
      if let some cbt ← s.cfunc cb then
        if !cftEq cbt (["i32", "i32", "i32"], ["i32"]) then
          throw "canonical option `callback` uses a core function with an incorrect signature"
    if let some ft := ft then
      if o.async && !ft.async then
        throw "the `async` canonical option requires an async function type"
      let sig ← lowerSig ft o .lift
      if let some ct := core then
        if !cftEq sig ct then
          throw s!"lowered function type `{cftShow sig}` does not match type `{cftShow ct}` of core function {f}"
    return { s with funcs := s.funcs.push ft }
  | .lower f _ =>
    s.idx .func f
    match s.funcs[f]?.getD none with
    | some ft =>
      if o.async && !ft.async then
        throw "the `async` canonical option requires an async function type"
      let sig ← lowerSig ft o .lower
      return { s with cfuncs := s.cfuncs.push (some sig) }
    | none => return s.pushCore .func
  | .resourceNew t | .resourceRep t =>
    match ← s.ty t with
    | .resource _ true => pure ()
    | .resource _ false | .unknown => throw s!"type {t} is not a local resource"
    | _ => throw s!"type index {t} is not a resource type"
    let r ← resourceId s t
    let v := if s.rep64.contains r then "i64" else "i32"
    let sig : CFT := match c with | .resourceNew _ => ([v], ["i32"]) | _ => (["i32"], [v])
    return { s with cfuncs := s.cfuncs.push (some sig) }
  | .resourceDrop t =>
    let _ ← resourceId s t
    return { s with cfuncs := s.cfuncs.push (canonSig p c) }
  | .taskReturn r _ =>
    let r ← resolveOpt F s r
    if r.any RTy.hasBorrow then throw "`task.return` result cannot contain a `borrow` type"
    if o.realloc.isSome then throw "cannot specify `realloc` option on `task.return`"
    if o.async then throw "cannot specify `async` option on `task.return`"
    let sig ← lowerSig ⟨r.toList.map ("v", ·), none, false⟩ o .lower
    return { s with cfuncs := s.cfuncs.push (some sig) }
  | .contextGet t i | .contextSet t i =>
    if t == .i64 && !F.hasFlag "cm64" then
      throw s!"`{c.kind}` with `i64` requires the `cm64` feature"
    if t != .i32 && t != .i64 then throw s!"`{c.kind}` only supports `i32` or `i64`"
    if i > 0 && !F.hasFlag "cm-threading" then
      throw s!"`{c.kind}` immediate must be zero: {i}"
    if i > 1 then throw s!"`{c.kind}` immediate must be zero or one: {i}"
    let v := if t == .i64 then "i64" else "i32"
    let sig : CFT := match c with | .contextGet .. => ([], [v]) | _ => ([v], [])
    return { s with cfuncs := s.cfuncs.push (some sig) }
  | .waitableSetWait m | .waitableSetPoll m =>
    s.idx (.core .memory) m
    return { s with cfuncs := s.cfuncs.push (canonSig p c) }
  | .threadNewIndirect ft tbl | .threadSpawnIndirect _ ft tbl =>
    let _ ← s.cty ft
    s.idx (.core .table) tbl
    return s.pushCore .func
  | .threadSpawnRef _ ft =>
    let _ ← s.cty ft
    return s.pushCore .func
  | _ => return { s with cfuncs := s.cfuncs.push (canonSig p c) }

/-! ## Subtyping of instantiation arguments (`SubtypeCx`) -/

/-- A resource renaming: an abstract (imported) resource of the instantiated component and the
argument's resource it stands for. -/
abbrev RMap := List (Nat × Nat × Bool)

/-- The argument's resource standing for `r`. -/
def RMap.res (m : RMap) (r : Nat) : Nat := (m.lookup r).map (·.1) |>.getD r

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
mutual
/-- `component_val_type`: is the argument's value type `a` the expected `x`? (Structure, labels,
resources through `m`; unknown types match anything.) -/
def valSub (m : RMap) (a x : RTy) : Except String Unit :=
  match a, x with
  | .unknown, _ | _, .unknown => .ok ()
  | .prim p, .prim q =>
    if p == q then .ok () else .error s!"expected primitive `{reprStr q}` found primitive `{reprStr p}`"
  | .record _ fs, .record _ gs => do
    if fs.length != gs.length then throw "expected a record with a different number of fields"
    for _h : p in fs.zip gs do
      if p.1.1 != p.2.1 then throw s!"expected field name `{p.2.1}`, found `{p.1.1}`"
      valSub m p.1.2 p.2.2
  | .variant _ cs, .variant _ ds => do
    if cs.length != ds.length then throw "expected a variant with a different number of cases"
    for _h : p in cs.zip ds do
      if p.1.1 != p.2.1 then throw s!"expected case named `{p.2.1}`, found `{p.1.1}`"
      optSub m p.1.2 p.2.2
  | .list t, .list t' | .option t, .option t' => valSub m t t'
  | .tuple ts, .tuple us => do
    if ts.length != us.length then throw "expected a tuple of a different size"
    for _h : p in ts.zip us do valSub m p.1 p.2
  | .flags _ n, .flags _ n' => if n == n' then .ok () else .error "mismatch in flags elements"
  | .enum _ n, .enum _ n' => if n == n' then .ok () else .error "mismatch in enum elements"
  | .result a b, .result a' b' => do optSub m a a'; optSub m b b'
  | .own r, .own r' | .borrow r, .borrow r' =>
    if r == m.res r' then .ok () else .error "resource types are not the same"
  | .fixedList t n, .fixedList t' n' => do
    if n != n' then throw "mismatch in fixed-length list lengths"
    valSub m t t'
  | .stream t, .stream t' | .future t, .future t' => optSub m t t'
  | .map k v, .map k' v' => do valSub m k k'; valSub m v v'
  | .own _, .borrow _ => .error "expected borrow, found own"
  | .borrow _, .own _ => .error "expected own, found borrow"
  | _, _ => .error "type mismatch"
termination_by sizeOf a
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)
    | (have := sizeOf_snd_lt_of_mem ‹_ ∈ _›; simp_all; omega)
    | (have := sizeOf_zip_fst_snd_lt ‹_ ∈ _›; simp_all; omega)
    | (have := sizeOf_zip_fst_lt ‹_ ∈ _›; simp_all; omega)

def optSub (m : RMap) : Option RTy → Option RTy → Except String Unit
  | some a, some x => valSub m a x
  | none, none => .ok ()
  | _, _ => .error "type mismatch in optional payload"
termination_by a => sizeOf a
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)
    | (have := sizeOf_snd_lt_of_mem ‹_ ∈ _›; simp_all; omega)
    | (have := sizeOf_zip_fst_snd_lt ‹_ ∈ _›; simp_all; omega)
    | (have := sizeOf_zip_fst_lt ‹_ ∈ _›; simp_all; omega)
end

/-- Is the argument's function type the expected one? -/
def funcSub (m : RMap) (a x : FTy) : Except String Unit := do
  if a.async != x.async then throw "expected an async function"
  if a.params.length != x.params.length then
    throw s!"expected {x.params.length} parameters, found {a.params.length}"
  for ((n, t), (n', t')) in a.params.zip x.params do
    if n != n' then throw s!"expected parameter named `{n'}`, found `{n}`"
    valSub m t t'
  match a.result, x.result with
  | some r, some r' => valSub m r r'
  | none, none => pure ()
  | _, _ => throw "expected a result, found none"

/-- Core module subtyping (`module_type`): every expected export present with a matching
type, every import of the argument provided by the expected type with a matching type. -/
def modSub (a x : List (String × String × CoreSort × Option CFT) ×
    List (String × CoreSort × Option CFT)) : Except String Unit := do
  let tyOk (srt : CoreSort) (sup sub : Option CFT) : Bool :=
    match sup, sub with
    | some p, some q => if srt == .func then cftEq p q else shapeSub p q
    | _, _ => true
  for (n, srt, t) in x.2 do
    match a.2.find? (·.1 == n) with
    | none => throw s!"missing expected export `{n}`"
    | some (_, srt', t') =>
      if srt' != srt then
        throw s!"type mismatch in export `{n}` expected {coreSortName srt}, found {coreSortName srt'}"
      unless tyOk srt t t' do throw s!"type mismatch in export `{n}`"
  for (mn, n, srt, t) in a.1 do
    match x.1.find? (fun (mn', n', _) => mn' == mn && n' == n) with
    | none => throw s!"missing expected import `{mn}::{n}`"
    | some (_, _, srt', t') =>
      if srt' != srt then
        throw s!"type mismatch in import `{mn}::{n}` expected {coreSortName srt}, found {coreSortName srt'}"
      unless tyOk srt t t' do throw s!"type mismatch in import `{mn}::{n}`"

/-- Types: abstract resources are fixed, others compared. -/
def tySub (m : RMap) (t u : TyInfo) : Except String RMap :=
  match t, u with
  | .resource r l, .resource r' false =>
    match m.lookup r' with
    | some (r'', _) => if r == r'' then .ok m else .error "resource types are not the same"
    | none => .ok ((r', r, l) :: m)
  | .resource r _, .resource r' true =>
    if r == r' then .ok m else .error "resource types are not the same"
  | .val a, .val x => do
    valSub m a x
    -- the expected definition stands for the argument's (its identity is renamed)
    match (TyInfo.val x).id?, (TyInfo.val a).id? with
    | some i, some j => pure (if m.any (·.1 == i) then m else (i, j, false) :: m)
    | _, _ => pure m
  | .func f, .func g => do funcSub m f g; pure m
  | .unknown, _ | _, .unknown => .ok m
  | .resource .., .val _ | .val _, .resource .. => .error "expected resource, found defined type"
  | _, _ => .ok m

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
mutual
/-- Is the argument's entry `a` a subtype of the expected `x`? Extends `m` with the abstract
resources of `x` the argument fixes. -/
def entSub (m : RMap) (a x : Ent) : Except String RMap :=
  match a, x with
  | .func (some f), .func (some g) => do funcSub m f g; pure m
  | .module (some sa), .module (some sx) => do modSub sa sx; pure m
  | .ty t, .ty u => tySub m t u
  | .inst (some ea), .inst (some ex) => instSub m ea ex
  | _, _ => .ok m
termination_by sizeOf x
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)
    | (have := sizeOf_snd_lt_of_mem ‹_ ∈ _›; simp_all; omega)
    | (have := sizeOf_zip_fst_snd_lt ‹_ ∈ _›; simp_all; omega)
    | (have := sizeOf_zip_fst_lt ‹_ ∈ _›; simp_all; omega)

/-- Instances: every expected export, in order, present and a subtype. -/
def instSub (m : RMap) (ea : Items) : Items → Except String RMap
  | [] => .ok m
  | (n, x) :: rest =>
    match ea.find? (·.1 == n) with
    | none => .error s!"missing expected export `{n}`"
    | some (_, a) => do
      if a.sort != x.sort then throw s!"expected {sortName x.sort}, found {sortName a.sort}"
      let m ← entSub m a x
      instSub m ea rest
termination_by l => sizeOf l
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)
    | (have := sizeOf_snd_lt_of_mem ‹_ ∈ _›; simp_all; omega)
    | (have := sizeOf_zip_fst_snd_lt ‹_ ∈ _›; simp_all; omega)
    | (have := sizeOf_zip_fst_lt ‹_ ∈ _›; simp_all; omega)
end

/-! ## Instances -/

/-- Duplicate names (exact strings). -/
def dupName (ns : List String) : Option String :=
  ns.find? fun n => (ns.filter (· == n)).length > 1

def checkCoreInstance (s : Scope) : CoreInstanceExpr → M Scope
  | .instantiate m args => do
    s.idx (.core .module) m
    for (_, i) in args do s.idx (.core .instance) i
    if let some d := dupName (args.map (·.1)) then
      throw s!"duplicate module instantiation argument named `{d}`"
    match s.cmodules[m]? with
    | some (some (imps, exps)) =>
      for (mn, n, srt, ift) in imps do
        match args.find? (·.1 == mn) with
        | none => throw s!"missing module instantiation argument named `{mn}`"
        | some (_, i) =>
          match s.cinsts[i]? with
          | some (some ex) =>
            match ex.find? (·.1 == n) with
            | none =>
              throw s!"module instantiation argument `{mn}` does not export an item named `{n}`"
            | some (_, srt', aft) =>
              if srt' != srt then
                throw s!"module instantiation argument `{mn}` exports an item named `{n}` of the wrong kind: expected {coreSortName srt}, found {coreSortName srt'}"
              if srt == .func then
                if let (some a, some b) := (ift, aft) then
                  if !cftEq a b then
                    throw s!"type mismatch for export `{n}` of module instantiation argument `{mn}`: expected {cftShow a}, found {cftShow b}"
              else
                if let (some a, some b) := (ift, aft) then
                  if !shapeSub a b then
                    throw s!"type mismatch for export `{n}` of module instantiation argument `{mn}`"
          | _ => pure ()
      return { s with cinsts := s.cinsts.push (some exps) }
    | _ => return s.pushCore .instance
  | .exports es => do
    for (_, si) in es do s.idx (.core si.sort) si.idx
    if let some d := dupName (es.map (·.1)) then
      throw s!"export name `{d}` already defined"
    let items : CItems := es.map fun (n, si) =>
      (n, si.sort, if si.sort == .func then s.cfuncs[si.idx]?.getD none else none)
    return { s with cinsts := s.cinsts.push (some items) }

def checkInstance (F : WFeatures) (s : Scope) : InstanceExpr → M Scope
  | .instantiate c args => do
    s.idx .component c
    for (_, si) in args do s.idx si.sort si.idx
    if let some d := dupName (args.map (·.1)) then
      throw s!"instantiation argument `{d}` conflicts with previous argument `{d}`"
    match s.comps[c]? with
    | some (some (imps, exps)) =>
      let mut m : List (Nat × Nat × Bool) := []
      for (n, e) in imps do
        match args.find? (fun a => nameKey a.1 == nameKey n) with
        | none => throw s!"missing import named `{n}`"
        | some (_, si) =>
          if si.sort != e.sort then
            throw s!"expected {sortName e.sort}, found {sortName si.sort} for import `{n}`"
          let a := s.ent si.sort si.idx
          match entSub m a e with
          | .ok m' => m := m'
          | .error err => throw s!"type mismatch for import `{n}`: {err}"
          match e, a with
          | .ty t, .ty t' =>
            if let (some i, some j) := (t.id?, t'.id?) then
              if !(m.any (·.1 == i)) then m := (i, j, false) :: m
          | _, _ => pure ()
      return { s with insts := s.insts.push (some (exps.map fun (n, e) => (n, e.subst m))) }
    | _ => return s.pushEnt (.inst none)
  | .exports es => do
    let mut keys : List String := []
    for (n, si) in es do
      s.idx si.sort si.idx
      let k ← checkName F "instance export" keys n si.sort
      keys := k :: keys
    return { s with insts := s.insts.push (some (es.map fun (n, si) => (n.name, s.ent si.sort si.idx))) }

/-! ## Types, and declarations of component and instance types -/

/-- The spelling of a core function type. -/
def coreFT (t : Silmaril.Wasm.Component.Binary.CoreFuncType) : CFT :=
  let n : CoreValType → String
    | .i32 => "i32" | .i64 => "i64" | .f32 => "f32" | .f64 => "f64" | .v128 => "v128"
    | .funcref => "funcref" | .externref => "externref"
  (t.params.map n, t.results.map n)

/-- Check a core import descriptor of a module type. -/
def checkCoreDesc (ms : Scope) : CoreImportDesc → M Unit
  | .func t => do
    match ← ms.cty t with
    | .func _ | .unknown => pure ()
    | _ => throw s!"type index {t} is not a function type"
  | .tag t => do let _ ← ms.cty t
  | _ => pure ()

/-- The function type of a core descriptor in a module type. -/
def descFT (ms : Scope) : CoreImportDesc → Option CFT
  | .func t => match ms.ctypes[t]? with | some (.func f) => some f | _ => none
  | _ => none

/-- Check a core type. -/
def checkCoreType (s : Scope) (outers : List Scope) : CoreType → M Scope
  | .func t => pure { s with ctypes := s.ctypes.push (.func (coreFT t)) }
  | .module decls => do
    let mut ms : Scope := { isType := true }
    let mut imps : List (String × String × CoreSort × Option CFT) := []
    let mut exps : CItems := []
    for d in decls do
      match d with
      | .type t => ms := { ms with ctypes := ms.ctypes.push (.func (coreFT t)) }
      | .alias count i =>
        let o ← if count = 0 then pure ms else
          match (s :: outers)[count - 1]? with
          | none => throw s!"invalid outer alias count of {count}"
          | some o => pure o
        o.idx (.core .type) i
        ms := { ms with ctypes := ms.ctypes.push (o.ctypes[i]?.getD .unknown) }
      | .import a b desc =>
        checkCoreDesc ms desc
        if imps.any (fun (x, y, _) => x == a && y == b) then
          throw s!"duplicate import name `{a}:{b}`"
        imps := imps ++ [(a, b, descSort desc, descFT ms desc)]
      | .export n desc =>
        checkCoreDesc ms desc
        if exps.any (·.1 == n) then throw s!"export name `{n}` already defined"
        exps := exps ++ [(n, descSort desc, descFT ms desc)]
    return { s with ctypes := s.ctypes.push (.module (imps, exps)) }

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
mutual

/-- Check a type definition (`outers`: the enclosing scopes, innermost first). -/
def checkDefType (F : WFeatures) (s : Scope) (outers : List Scope) : DefType → M Scope
  | .val d => do
    let t ← checkDefVal F s d
    pure { s with types := s.types.push (.val t) }
  | .func f => do
    let f ← checkFuncType F s f
    pure { s with types := s.types.push (.func f) }
  | .resource rep dtor => do
    if s.isType then throw "resources can only be defined within a concrete component"
    if rep == .i64 && !F.hasFlag "cm64" then
      throw "resources with `i64` require the `cm64` feature to be enabled"
    if rep != .i32 && rep != .i64 then
      throw "resources can only be represented by `i32` or `i64`"
    if let some d := dtor then
      if let some t ← s.cfunc d then
        if !cftEq t ([if rep == .i64 then "i64" else "i32"], []) then
          throw s!"core function {d} has wrong signature for a destructor"
    let r ← fresh
    pure { s with types := s.types.push (.resource r true),
                  rep64 := if rep == .i64 then r :: s.rep64 else s.rep64 }
  | .component decls => do
    let mut cs : Scope := { isType := true }
    for _h : d in decls do
      match _hd : d with
      | .import n desc =>
        let k ← checkName F "import" cs.importKeys n (descItemSort desc)
        let e ← checkDesc F cs desc
        let cs₁ ← nameResources cs true n.name e
        let (cs', e) ← registerNamed cs₁ true true e
        cs := cs'.pushEnt e
        cs := { cs with importKeys := k :: cs.importKeys, imports := cs.imports ++ [(n.name, e)] }
      | .inst d => cs ← checkInstDecl F cs (s :: outers) d
    pure { s with types := s.types.push (.comp cs.imports cs.exports) }
  | .instance decls => do
    let mut is : Scope := { isType := true, isInst := true }
    for _h : d in decls do is ← checkInstDecl F is (s :: outers) d
    pure { s with types := s.types.push (.inst is.exports) }
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)
    | (subst_vars; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)

/-- One declaration of an instance (or component) type. -/
def checkInstDecl (F : WFeatures) (s : Scope) (outers : List Scope) :
    InstanceDecl → M Scope
  | .coreType t => checkCoreType s outers t
  | .type t => checkDefType F s outers t
  | .alias a => do
    match a.target, a.sort with
    | .outer .., .type | .outer .., .core .type | .export .., .type | .export .., .instance
    | .outer .., .component | .outer .., .core .module => pure ()
    | _, _ => throw "aliases in a component or instance type may only refer to types or instances"
    checkAlias s outers a
  | .export n desc => do
    let k ← checkName F "export" s.exportKeys n (descItemSort desc)
    let e ← checkDesc F s desc
    let s ← nameResources s false n.name e
    let (s, e) ← registerNamed s false true e
    let s := s.pushEnt e
    pure { s with exportKeys := k :: s.exportKeys, exports := s.exports ++ [(n.name, e)] }
termination_by d => sizeOf d
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)

end

/-! ## Components -/

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
mutual

/-- Check one section of a component. -/
def checkSection (F : WFeatures) (outers : List Scope) (s : Scope) : Section → M Scope
  | .custom .. => pure s
  | .coreModule b => do
    let info ← coreModule F b
    pure { s with cmodules := s.cmodules.push (some info) }
  | .coreInstances xs => xs.foldlM checkCoreInstance s
  | .coreTypes xs => xs.foldlM (fun s t => checkCoreType s outers t) s
  | .component c => do
    let inner ← checkComponent F (s :: outers) c
    pure { s with comps := s.comps.push (some (inner.imports, inner.exports)) }
  | .instances xs => xs.foldlM (checkInstance F) s
  | .aliases xs => xs.foldlM (fun s a => checkAlias s outers a) s
  | .types xs => xs.foldlM (fun s t => checkDefType F s outers t) s
  | .canons xs => xs.foldlM (checkCanon F) s
  | .start st => do
    if !F.hasFlag "cm-values" then
      throw "support for component model `value`s is not enabled"
    s.idx .func st.func
    for a in st.args do s.idx .value a
    pure { s with values := s.values + st.results }
  | .imports xs => xs.foldlM (fun s i => do
      let k ← checkName F "import" s.importKeys i.name (descItemSort i.desc)
      let e ← checkDesc F s i.desc
      let s ← nameResources s true i.name.name e
      let (s, e) ← registerNamed s true true e
      let s := s.pushEnt e
      pure { s with importKeys := k :: s.importKeys, imports := s.imports ++ [(i.name.name, e)] }) s
  | .exports xs => xs.foldlM (fun s e => do
      s.idx e.item.sort e.item.idx
      let k ← checkName F "export" s.exportKeys e.name e.item.sort
      let ent := s.ent e.item.sort e.item.idx
      let ent ← match e.desc with
        | some d =>
          if descItemSort d != e.item.sort then throw "export type mismatch"
          checkDesc F s d
        | none => pure ent
      let s ← nameResources s false e.name.name ent
      let (s, ent) ← registerNamed s false true ent
      let s := s.pushEnt ent
      pure { s with exportKeys := k :: s.exportKeys, exports := s.exports ++ [(e.name.name, ent)] }) s
  | .values _ =>
    if F.hasFlag "cm-values" then pure s
    else throw "support for component model `value`s is not enabled"
termination_by sec => sizeOf sec
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)

/-- Check a component; `outers` are the enclosing components, innermost first. -/
def checkComponent (F : WFeatures) (outers : List Scope) (c : Ast) : M Scope :=
  match c with
  | .mk ss => ss.attach.foldlM (fun s ⟨sec, _⟩ => checkSection F outers s sec) {}
termination_by sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; simp_all; omega)

end

/-- The core modules embedded in a component (nested components included). -/
def coreModules (c : Ast) : List ByteArray :=
  (Silmaril.Wasm.Component.BinaryP3.Check.strict c).2.2

/-- The walk over a parsed component (index spaces, types, names, built-ins). -/
def walk (F : WFeatures) (c : Ast) : Except String Unit :=
  ((checkComponent F [] c).run 0).map fun _ => ()

/-- Does the core validator accept an embedded module? -/
def coreOk (F : WFeatures) (m : ByteArray) : Bool :=
  match FastPaths.checkFast F m with
  | .ok () => true
  | .error _ => false

/-- The message for a rejected embedded module. -/
def coreMsg (F : WFeatures) (m : ByteArray) : String :=
  match FastPaths.checkFast F m with
  | .ok () => ""
  | .error e => e.message

/-- **The component validator.** -/
def check (F : WFeatures) (b : ByteArray) : Except String Unit :=
  if !F.hasFlag "component-model" then
    .error "unknown binary version and encoding combination: 0xd and 0x1, note: encoded as a \
      component but the WebAssembly component model feature is not enabled - enable the feature \
      to allow component validation"
  else
  match Silmaril.Wasm.Component.BinaryP3.parse b with
  | .error e => .error s!"failed to parse component: {Silmaril.Wasm.Component.BinaryP3.Check.errStr e}"
  | .ok c =>
    let st := Silmaril.Wasm.Component.BinaryP3.Check.strict c
    if !st.1 then .error "invalid leading byte for component outer alias kind"
    else if !st.2.1 then .error "duplicate name attribute"
    else
      match (coreModules c).find? (fun m => !coreOk F m) with
      | some m => .error (coreMsg F m)
      | none => walk F c

end Silmaril.Wasm.Tools.CompValidate
