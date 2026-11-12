module

public import Silmaril.Wasm.JcoTool.NewI.Defs
public import Silmaril.Wasm.JcoTool.Cm32.Defs

/-!
# `wasm-tools component embed --dummy`: the dummy core module of a world

wit-component's `dummy_module` (`crates/wit-component/src/dummy.rs` of wasm-tools 1.262.0)
writes, for a world, the WAT text of a core module that has the core imports and exports the
canonical ABI asks of a module implementing the world, with `unreachable` bodies, and parses
it with the `wat` crate. This module computes the same module as data (`Module`) and encodes it
the way `wat` encodes that text (`encode`):

* **imports**, in the world's import order: every function of an imported interface or of the
  world (`canon lower` type, `lowerCoreR`), the `[resource-drop]` of every resource of an
  imported interface or of the world; then, for every exported interface, the
  `[resource-drop]`, `[resource-new]` and `[resource-rep]` built-ins of its resources;
* **functions**, in the world's export order: every exported function (`canon lift` type,
  `liftCoreR`, body `unreachable`) followed by its post-return function (the results as
  parameters, empty body); for an exported interface, its functions, then a destructor
  `(param i32)` per resource;
* a memory of 0 pages, `realloc` `(i32 i32 i32 i32) -> i32`, and `initialize`.

Names follow `Resolve::wasm_import_name`/`wasm_export_name` under the two manglings of
`ManglingAndAbi` used here: `legacy` (`$root`, `ns:pkg/iface`, `iface#f`, `cabi_post_…`,
`memory`, `cabi_realloc`, `_initialize`) and `standard32` (`cm32p2|…` with canonical
interface ids, `…_post`, `cm32p2_memory`, …).

Encoding as `wat` does: implicit function types in order of first use (imports first, then the
functions), deduplicated; sections type, import, function, memory, export, code; exports in the
order of the text (functions, then memory, realloc, initialize); no name section (the text has
no identifiers).

Asynchronous functions (`async`) and the async manglings (`--async-callback`,
`--async-stackful`) are refused here (`Known limitations` in docs/projects/wasm-components.md).
Theorems: `Silmaril.Wasm.Tools.Component.Dummy.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Dummy

open Silmaril.Wasm.Wit.Binary (Func TypeDef TyDefKind Interface IfaceName DItem WorldFull)
open Silmaril.Wasm.JcoTool (Scope Resolver lowerCoreR liftCoreR)
open Silmaril.Wasm.Component (CoreFuncTy)
open Silmaril.Parse.ByteParse (Bytes)
open Silmaril.Parse.ByteParse.Enc (u32 sized)

/-- The two manglings of `ManglingAndAbi` with the synchronous ABI. -/
inductive Mangling where
  | legacy
  | standard32
  deriving Repr, DecidableEq, Inhabited

/-! ## Names -/

/-- `name_world_key` (legacy) or `name_canonicalized_world_key` (standard32). -/
def keyName : Mangling → (IfaceName ⊕ String) → String
  | .legacy, .inl i => i.id
  | .standard32, .inl i => JcoTool.Cm32.canonId i
  | _, .inr n => n

/-- The import module of a function or resource drop of an imported item (`none`: the world). -/
def importModule : Mangling → Option (IfaceName ⊕ String) → String
  | .legacy, none => "$root"
  | .legacy, some k => keyName .legacy k
  | .standard32, none => "cm32p2"
  | .standard32, some k => "cm32p2|" ++ keyName .standard32 k

/-- The name of the drop of an imported resource. -/
def importedDrop : Mangling → String → String
  | .legacy, r => "[resource-drop]" ++ r
  | .standard32, r => r ++ "_drop"

/-- The module of the resource built-ins of an exported interface. -/
def exportedModule (m : Mangling) (k : IfaceName ⊕ String) : String :=
  match m with
  | .legacy => "[export]" ++ keyName .legacy k
  | .standard32 => "cm32p2|_ex_" ++ keyName .standard32 k

/-- The names of `[resource-drop]`, `[resource-new]`, `[resource-rep]` of an exported resource. -/
def exportedBuiltins : Mangling → String → List String
  | .legacy, r => ["[resource-drop]" ++ r, "[resource-new]" ++ r, "[resource-rep]" ++ r]
  | .standard32, r => [r ++ "_drop", r ++ "_new", r ++ "_rep"]

/-- The export name of a function (`post`: its post-return function). -/
def exportName (m : Mangling) (k : Option (IfaceName ⊕ String)) (f : String) (post : Bool) :
    String :=
  match m with
  | .legacy =>
    (if post then "cabi_post_" else "") ++ (k.map fun k => keyName .legacy k ++ "#").getD "" ++ f
  | .standard32 =>
    "cm32p2|" ++ (k.map (keyName .standard32)).getD "" ++ "|" ++ f ++ (if post then "_post" else "")

/-- The export name of the destructor of resource `r` of the exported interface `k`. -/
def dtorName (m : Mangling) (k : IfaceName ⊕ String) (r : String) : String :=
  match m with
  | .legacy => keyName .legacy k ++ "#[dtor]" ++ r
  | .standard32 => "cm32p2|" ++ keyName .standard32 k ++ "|" ++ r ++ "_dtor"

def memoryName : Mangling → String
  | .legacy => "memory"
  | .standard32 => "cm32p2_memory"

def reallocName : Mangling → String
  | .legacy => "cabi_realloc"
  | .standard32 => "cm32p2_realloc"

def initializeName : Mangling → String
  | .legacy => "_initialize"
  | .standard32 => "cm32p2_initialize"

/-! ## The module as data -/

open Silmaril.Wasm (NumType)

/-- A defined function: export name, type, and whether its body is `unreachable` (else empty). -/
structure DFunc where
  name : String
  ty : CoreFuncTy
  unreachable : Bool

/-- The dummy module: imports `(module, name, type)` and defined functions. -/
structure Module where
  imports : List (String × String × CoreFuncTy)
  funcs : List DFunc
  mangling : Mangling

def t32 : NumType := .int .i32

/-- The resources among a list of type definitions. -/
def resources (ts : List TypeDef) : List String :=
  ts.filterMap fun t => match t.kind with
    | .resource => some t.name
    | _ => none

/-- A function name as wit-parser's `Function::name` (`[method]r.f`, `[constructor]r`, …). -/
def fname (f : Func) : String := f.mangled

def noAsync (f : Func) : Except String Unit :=
  if f.async then
    throw s!"function `{fname f}` is async: dummy modules of async functions are not implemented by this wasm-tools"
  else pure ()

/-- The core imports of the world's imports (functions and resource drops). -/
def importsOf (ρ : Resolver) (m : Mangling) : List DItem →
    Except String (List (String × String × CoreFuncTy))
  | [] => pure []
  | .func f :: is => do
    noAsync f
    let t ← lowerCoreR ρ .world f
    pure ((importModule m none, fname f, t) :: (← importsOf ρ m is))
  | .iface k b :: is => do
    let fs ← b.funcs.mapM fun f => do
      noAsync f
      pure (importModule m (some k), fname f, ← lowerCoreR ρ (.iface k) f)
    let ds := (resources b.types).map fun r =>
      (importModule m (some k), importedDrop m r, (⟨[t32], []⟩ : CoreFuncTy))
    pure (fs ++ ds ++ (← importsOf ρ m is))
  | .type t :: is => do
    let ds := (resources [t]).map fun r =>
      (importModule m none, importedDrop m r, (⟨[t32], []⟩ : CoreFuncTy))
    pure (ds ++ (← importsOf ρ m is))

/-- The resource built-ins of the exported interfaces. -/
def exportBuiltins (m : Mangling) (es : List DItem) : List (String × String × CoreFuncTy) :=
  es.flatMap fun
    | .iface k b => (resources b.types).flatMap fun r =>
        match exportedBuiltins m r with
        | [d, n, p] => [(exportedModule m k, d, ⟨[t32], []⟩), (exportedModule m k, n, ⟨[t32], [t32]⟩),
            (exportedModule m k, p, ⟨[t32], [t32]⟩)]
        | _ => []
    | _ => []

/-- An exported function and its post-return function. -/
def exportFunc (ρ : Resolver) (m : Mangling) (k : Option (IfaceName ⊕ String)) (f : Func) :
    Except String (List DFunc) := do
  noAsync f
  let sc : Scope := match k with
    | none => .world
    | some k => .iface k
  let t ← liftCoreR ρ sc f
  pure [⟨exportName m k (fname f) false, t, true⟩, ⟨exportName m k (fname f) true, ⟨t.results, []⟩, false⟩]

/-- The defined functions of the world's exports. -/
def funcsOf (ρ : Resolver) (m : Mangling) : List DItem → Except String (List DFunc)
  | [] => pure []
  | .func f :: es => do pure ((← exportFunc ρ m none f) ++ (← funcsOf ρ m es))
  | .iface k b :: es => do
    let fs := (← b.funcs.mapM (exportFunc ρ m (some k))).flatten
    let ds := (resources b.types).map fun r => (⟨dtorName m k r, ⟨[t32], []⟩, false⟩ : DFunc)
    pure (fs ++ ds ++ (← funcsOf ρ m es))
  | .type _ :: es => funcsOf ρ m es

/-- **`dummy_module`** of a decoded world. -/
def dummy (wf : WorldFull) (m : Mangling) : Except String Module := do
  let ρ := JcoTool.NewI.rho wf
  let is ← importsOf ρ m wf.imports
  let fs ← funcsOf ρ m wf.exports
  let tail : List DFunc := [⟨reallocName m, ⟨[t32, t32, t32, t32], [t32]⟩, true⟩,
    ⟨initializeName m, ⟨[], []⟩, false⟩]
  pure ⟨is ++ exportBuiltins m wf.exports, fs ++ tail, m⟩

/-! ## Encoding as `wat` does -/

/-- The function types in order of first use, without repetition. -/
def typeTable (ts : List CoreFuncTy) : List CoreFuncTy :=
  ts.foldl (fun acc t => if acc.contains t then acc else acc ++ [t]) []

/-- The index of a type in the table. -/
def typeIdx (tab : List CoreFuncTy) (t : CoreFuncTy) : Nat := tab.idxOf t

open Silmaril.Wasm.JcoTool.CMod (funcType vecSec section_)

def importBytes (tab : List CoreFuncTy) (i : String × String × CoreFuncTy) : Option Bytes := do
  let a ← Silmaril.Parse.ByteParse.Enc.name i.1
  let b ← Silmaril.Parse.ByteParse.Enc.name i.2.1
  let c ← u32 (typeIdx tab i.2.2)
  pure (a ++ b ++ 0x00 :: c)

def exportBytes (e : String × UInt8 × Nat) : Option Bytes := do
  let a ← Silmaril.Parse.ByteParse.Enc.name e.1
  let b ← u32 e.2.2
  pure (a ++ e.2.1 :: b)

def codeBytes (f : DFunc) : Option Bytes :=
  sized (0x00 :: ((if f.unreachable then [0x00] else []) ++ [0x0b]))

/-- The exports in text order: the functions, then the memory between the exported functions
of the world and `realloc` (the text writes the memory there). -/
def exportsOf (d : Module) : List (String × UInt8 × Nat) :=
  let n := d.imports.length
  let fs := d.funcs.zipIdx.map fun (f, i) => (f.name, (0x00 : UInt8), n + i)
  let k := d.funcs.length - 2
  fs.take k ++ [(memoryName d.mangling, 0x02, 0)] ++ fs.drop k

/-- **The bytes `wat` writes** for the text of the dummy module. -/
def encode (d : Module) : Option ByteArray := do
  let tab := typeTable (d.imports.map (·.2.2) ++ d.funcs.map (·.ty))
  let ty ← vecSec 0x01 funcType tab
  let im ← vecSec 0x02 (importBytes tab) d.imports
  let fn ← vecSec 0x03 (fun f => u32 (typeIdx tab f.ty)) d.funcs
  let me ← section_ 0x05 [0x01, 0x00, 0x00]
  let ex ← vecSec 0x07 exportBytes (exportsOf d)
  let cd ← vecSec 0x0a codeBytes d.funcs
  let body := [0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00] ++ ty ++ im ++ fn ++ me ++ ex ++ cd
  pure ⟨body.toArray⟩

/-- The dummy module of the world of a `component-type` payload. -/
def dummyOfPayload (payload : ByteArray) (m : Mangling) : Except String ByteArray := do
  let wf ← Silmaril.Wasm.Wit.Binary.decodeWorldFull payload
  let d ← dummy wf m
  match encode d with
  | some b => pure b
  | none => throw "a number or size of the dummy module exceeds 2^32"

end Silmaril.Wasm.Tools.Component.Dummy
