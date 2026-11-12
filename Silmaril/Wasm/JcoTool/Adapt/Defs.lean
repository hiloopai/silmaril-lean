module

public import Silmaril.Wasm.JcoTool.NewI.Defs
public import Silmaril.Wasm.JcoTool.AdaptGC.Defs
public import Silmaril.Wasm.JcoTool.Front.Defs
public import Silmaril.Wasm.Perf.CoreDecode.Defs

/-!
# `wasm-jco new --adapt NAME=ADAPTER.wasm`: components with adapter modules

wit-component's `--adapt` (wasm-tools 1.262.0): the main module imports functions from a core
module `NAME` (e.g. `wasi_snapshot_preview1`) that an **adapter** module implements in terms of
the Component Model (e.g. WASI 0.2). The component holds two (or more) core modules:

* each adapter is first reduced to what is needed (`AdaptGC.run`): the functions the main
  module imports from it, the functions its own world exports (e.g. `wasi:cli/run#run` of the
  command adapter) and its allocators (`cabi_import_realloc`, `cabi_export_realloc`), with the
  functions they reach; its stack is allocated as wit-component does;
* the component's world is the main module's world merged with the adapters' worlds
  (`WorldMerge.liveWorld`), restricted to what the main module and the reduced adapters import;
* the main module and the adapters import each other: the main module the adapter's functions,
  the adapter the main module's memory (`env.memory`) and functions (`__main_module__`, e.g.
  `_start`, `cabi_realloc`). The cycle is broken as wit-component does, by the indirect
  pattern: the main module imports trampolines of a `shim` module, which call through a table
  that the `fixup` module fills once every module is instantiated. The trampolines also serve
  the lowered imports that need the memory or an allocator;
* the main module's lowered imports use its `cabi_import_realloc` (else `cabi_realloc`), its
  lifted exports its `cabi_export_realloc` (else `cabi_realloc`); an adapter's likewise.

The output is refused unless silmaril's reference validator accepts it (`newAdapt`). Nothing
about the layout is proved here (see the Known limitations of `docs/projects/wasm-components.md`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.Adapt

open Silmaril.Wasm.Wit.Binary (Ty Func WorldFull World PackageName)
open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component (CoreFuncTy)
open Silmaril.Wasm.JcoTool.New (TS TyM Lift coreExport? expectExport require shimMod fixupMod
  mustEncode EM addSec coreFunc coreInst aliasCoreFunc moduleNames)
open Silmaril.Wasm.JcoTool.NewI

/-! ## Requests -/

/-- What a core import of the main module asks for. -/
inductive MainReq where
  | req (r : IReq)
  /-- Function `exp` of adapter `a`. -/
  | adp (a : Nat) (exp : String)

/-- What a core import of an adapter asks for. -/
inductive AdReq where
  | req (r : IReq)
  /-- The main module's export `n`. -/
  | main (n : String)

instance : Inhabited MainReq := ⟨.adp 0 ""⟩
instance : Inhabited AdReq := ⟨.main ""⟩
instance : Inhabited CoreFuncTy := ⟨⟨[], []⟩⟩

/-- An adapter after collection, with its requests. -/
structure APlan where
  name : String
  gc : AdaptGC.Out
  mod : CoreMod
  reqs : List ((String × String) × AdReq × CoreFuncTy)

instance : Inhabited AdaptGC.Out := ⟨⟨{}, ByteArray.empty, [], none, []⟩⟩
instance : Inhabited CoreMod := ⟨⟨ByteArray.empty, [], [], []⟩⟩
instance : Inhabited APlan := ⟨⟨"", default, default, []⟩⟩

/-- Who implements a world export: the main module (`none`) or adapter `a`. -/
structure Impl where
  x : XFn
  lift : Lift
  by_ : Option Nat

instance : Inhabited XFn := ⟨⟨.world, "", default⟩⟩
instance : Inhabited Impl := ⟨⟨default, default, none⟩⟩

/-- A wrapper of the task hook module: the main module's export `name` at type `ty`, with the
event codes passed to `__wasm_task_hook` before (`enter`) and after (`exit`) the call. -/
structure HookFn where
  /-- The instance the function comes from: `main`, or `adapterK` for adapter `K`. -/
  inst : String
  name : String
  ty : CoreFuncTy
  enter : Option Nat
  exit : Option Nat
  /-- An async entry point or callback: after the call, the code is 4 (blocked) when the
  returned code is nonzero, else 5 (finished). -/
  asyncEnd : Bool := false

/-- The name of a hook wrapper in the hook module's exports. -/
def HookFn.export (f : HookFn) : String := "hook-" ++ f.inst ++ "-" ++ f.name

/-- A memory import: module, name, limits (64 KiB pages). -/
structure MemImport where
  module : String
  name : String
  min : Nat
  max : Option Nat

/-- A plan. -/
structure Plan where
  core : ByteArray
  mod : CoreMod
  wf : WorldFull
  reqs : List ((String × String) × MainReq × CoreFuncTy)
  adapters : List APlan
  impls : List Impl
  dtors : List ((Scope × String) × Option String)
  memory : Bool
  /-- The main module's memory import, if it imports its memory. -/
  mainMem : Option MemImport
  /-- The task hook wrappers, when the main module exports `__wasm_task_hook`. -/
  hooks : List HookFn
  /-- Whether the main module exports `_initialize` (called after instantiation). -/
  callInit : Bool
  /-- Allocators: of the main module's imports, of its exports; per adapter likewise. -/
  mainImpRa : Option String
  mainExpRa : Option String
  adImpRa : List (Option String)
  adExpRa : List (Option String)

/-- The general-purpose allocator of a module (`cabi_realloc`, else `canonical_abi_realloc`). -/
def generalRealloc (m : CoreMod) : Option String :=
  let ty : CoreFuncTy := ⟨[ti32, ti32, ti32, ti32], [ti32]⟩
  if coreExport? m "cabi_realloc" == some ty then some "cabi_realloc"
  else if coreExport? m "canonical_abi_realloc" == some ty then some "canonical_abi_realloc"
  else none

/-- The import and export allocators of a module, as wit-component chooses them. -/
def reallocs (m : CoreMod) : Option String × Option String :=
  let ty : CoreFuncTy := ⟨[ti32, ti32, ti32, ti32], [ti32]⟩
  let has (n : String) := coreExport? m n == some ty
  let gen := if has "cabi_realloc" then some "cabi_realloc"
    else if has "canonical_abi_realloc" then some "canonical_abi_realloc" else none
  (if has "cabi_import_realloc" then some "cabi_import_realloc" else gen,
   if has "cabi_export_realloc" then some "cabi_export_realloc" else gen)

/-- The core module (imports and exports) of a collected adapter. -/
def gcMod (o : AdaptGC.Out) : CoreMod :=
  ⟨o.bytes, o.funcImports.map (fun (m, n, _) => (m, n)), o.funcImports.map (fun (_, n, t) => (n, t)),
   o.exports⟩

/-- The core names of a world export, as a module may export them. -/
def exportNames (x : XFn) : List String :=
  [x.core, "[async-lift]" ++ x.core, "[callback][async-lift]" ++ x.core,
   "[async-lift-stackful]" ++ x.core, "cabi_post_" ++ x.core]

/-- The exports of an adapter wit-component keeps (besides what the main module imports): the
allocators and the implementation of its world's exported functions. -/
def adapterRequired (aw : WorldFull) (exports : List String) : List String :=
  let special := ["cabi_import_realloc", "cabi_export_realloc", "canonical_abi_realloc",
    "cabi_realloc", "cabi_realloc_adapter"]
  let xs := (exportFns aw).flatMap exportNames
  exports.filter fun e => special.contains e || xs.contains e

/-- Distinct, in order. -/
def dedup (xs : List String) : List String :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- The world of a module without a `component-type` section: the empty world `root:component/root`. -/
def emptyWorld : Except String WorldFull := do
  let p ← Silmaril.Wasm.Wit.Binary.encodeWorldType [] { ns := "root", name := "component" } "root" {} .utf8
  Silmaril.Wasm.Wit.Binary.decodeWorldFull p

/-- The worlds of the main module: the `--wit` world, else its `component-type` sections,
else the empty world. -/
def mainWorlds (core : ByteArray)
    (wit : Option ((String × String) × List (String × String) × String)) :
    Except String (List WorldFull) :=
  match wit with
  | some _ => Front.worldsOf core wit
  | none => match WorldMerge.sectionWorlds core with
    | .ok ws => pure ws
    | .error _ => do pure [← emptyWorld]

/-- The main module as `Adapt` reads it (silmaril's verified decoder): its function imports and
exports, and its memory import if any (wit-component's `import-memory`: the memory is then
defined by the shim module). Table, global and tag imports are refused. -/
def readMainOf (d : Option Silmaril.Wasm.Module) (b : ByteArray) :
    Except String (CoreMod × Option MemImport) := do
  let some m := d
    | throw "embedded core module rejected by silmaril's core decoder (outside its fragment)"
  let mut names := #[]
  let mut imps := #[]
  let mut mem : Option MemImport := none
  for i in m.imports do
    match i.type with
    | .func t =>
      names := names.push (i.moduleName, i.name)
      imps := imps.push (i.name, ← Lower.coreFuncTy m t)
    | .memory mt =>
      if mem.isSome then throw "the main module imports two memories"
      if mt.address != .i32 then throw "a 64-bit memory import is not supported"
      mem := some ⟨i.moduleName, i.name, mt.limits.min.val, mt.limits.max.map (·.val)⟩
    | _ => throw s!"core module imports a table, global or tag ({i.moduleName} {i.name}); unsupported"
  let fts := m.functionTypes
  let mut exps := #[]
  for e in m.exports do
    match e.index with
    | .func f =>
      match fts[f.value.val]? with
      | some t => exps := exps.push (e.name, ← Lower.coreFuncTy m t)
      | none => throw s!"core export {e.name}: function {f.value.val} out of range"
    | _ => pure ()
  pure (⟨b, names.toList, imps.toList, exps.toList⟩, mem)

/-- `readMainOf` on the module silmaril's verified decoder reads from `b`. -/
def readMain (b : ByteArray) : Except String (CoreMod × Option MemImport) :=
  readMainOf (Silmaril.Wasm.Perf.CoreDecode.decodeF b) b

open CMod in
open Silmaril.Parse.ByteParse.Enc (u32) in
/-- The shim module with a memory of the given limits, exported as `$memory` (wit-component's
shim when the main module imports its memory): `New.shimMod` plus a memory section. -/
def shimWithMem (tys : List CoreFuncTy) (min : Nat) (max : Option Nat) : Option ByteArray := do
  let m := shimMod tys
  let ty ← vecSec 0x01 funcType m.types
  let fn ← vecSec 0x03 (fun f => u32 f.1) m.funcs
  let tb ← match m.table with
    | none => some []
    | some (mn, mx) => do
      let l ← limits mn mx
      section_ 0x04 (0x01 :: 0x70 :: l)
  let lim ← match max with
    | some mx => limits min mx
    | none => (0x00 :: ·) <$> u32 min
  let me ← section_ 0x05 ([0x01] ++ lim)
  let ex ← vecSec 0x07 export_ (m.exports ++ [("$memory", 0x02, 0)])
  let cd ← vecSec 0x0a code m.funcs
  pure ⟨([0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00] ++ ty ++ fn ++ tb ++ me ++ ex ++ cd).toArray⟩

/-! ## Task hooks -/

/-- wit-component's task hook wrappers (`__wasm_task_hook(code)` around every entry point: 0/1
around an export, 1 after its post-return instead, 12/13 around an allocator, 8/9 around a
destructor): a module importing the hook and the wrapped functions from `main` and exporting
`hook-NAME` for each, written as a silmaril module and encoded by silmaril's encoder. -/
def hookModule (fns : List HookFn) : Except String ByteArray := do
  let vt (t : Silmaril.Wasm.NumType) : Silmaril.Wasm.ValType := .num t
  let fty (t : CoreFuncTy) : Silmaril.Wasm.RecType :=
    ⟨[⟨true, [], .func ⟨t.params.map vt, t.results.map vt⟩⟩]⟩
  let ix {k : Silmaril.Wasm.IndexKind} (n : Nat) : Silmaril.Wasm.Idx k := ⟨Fin.ofNat _ n⟩
  let n := fns.length
  let callHook (code : Nat) : List Silmaril.Wasm.Instr := [AdaptGC.c32 code, .call (ix 0)]
  let body (f : HookFn) (k : Nat) : List Silmaril.Wasm.Instr :=
    let np := f.ty.params.length
    (f.enter.map callHook).getD [] ++
    ((List.range np).map AdaptGC.lget) ++ [.call (ix (k + 1))] ++
    (if f.asyncEnd then
      [.localSet (ix np), AdaptGC.c32 4, AdaptGC.c32 5, AdaptGC.lget np, .select none,
       .call (ix 0), AdaptGC.lget np]
    else (f.exit.map callHook).getD [])
  let m : Silmaril.Wasm.Module :=
    { types := fty ⟨[ti32], []⟩ :: fns.map (fty ·.ty)
      imports := ⟨"main", "__wasm_task_hook", .func (ix 0)⟩ ::
        fns.zipIdx.map fun (f, k) => ⟨f.inst, f.name, .func (ix (k + 1))⟩
      funcs := fns.zipIdx.map fun (f, k) =>
        ⟨ix (k + 1), (if f.asyncEnd then [vt (.int .i32)] else []), body f k⟩
      exports := fns.zipIdx.map fun (f, k) => ⟨f.export, .func (ix (n + 1 + k))⟩ }
  match Silmaril.Wasm.Binaryen.Exe.encodeModule? m with
  | .ok bs => pure ⟨bs.toArray⟩
  | .error e => throw s!"the task hook module does not encode: {e}"

/-- The module that calls the main module's `_initialize` when it is instantiated (its start
function), instantiated last, as wit-component does (after the fixups, so that the adapters'
functions are in place). -/
def initModule (hook : Bool) : Except String ByteArray := do
  let i32 : Silmaril.Wasm.ValType := .num (.int .i32)
  -- with a task hook: `__wasm_task_hook(6)`, `_initialize`, `__wasm_task_hook(7)` (wit-component's
  -- InitializeStart / InitializeFinish)
  let m : Silmaril.Wasm.Module := if hook then
      { types := [⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[i32], []⟩⟩]⟩]
        imports := [⟨"main", "_initialize", .func ⟨0⟩⟩, ⟨"main", "__wasm_task_hook", .func ⟨1⟩⟩]
        funcs := [⟨⟨0⟩, [], [AdaptGC.c32 6, .call ⟨1⟩, .call ⟨0⟩, AdaptGC.c32 7, .call ⟨1⟩]⟩]
        start := some ⟨2⟩ }
    else
      { types := [⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩]
        imports := [⟨"main", "_initialize", .func ⟨0⟩⟩]
        start := some ⟨0⟩ }
  match Silmaril.Wasm.Binaryen.Exe.encodeModule? m with
  | .ok bs => pure ⟨bs.toArray⟩
  | .error e => throw s!"the initialize module does not encode: {e}"

/-- **The plan** of a main module with adapters `ads` (name, bytes). -/
def plan (core : ByteArray) (wit : Option ((String × String) × List (String × String) × String))
    (ads : List (String × ByteArray)) (growRealloc : Bool := false) : Except String Plan := do
  let mainWfs ← mainWorlds core wit
  let prepared ← Front.prepareCore core
  let (m, mainMem) ← readMain prepared
  let adNames := ads.map (·.1)
  let (_, mainExpRa0) := reallocs m
  -- collect each adapter (skipped when nothing of it is needed, as wit-component does)
  let mut adWfs : List WorldFull := []
  let mut gcs : List (String × AdaptGC.Out × List WorldFull) := []
  for (an, ab) in ads do
    let aws ← match WorldMerge.sectionWorlds ab with
      | .ok ws => pure ws
      | .error e => throw s!"adapter {an}: {e} (an adapter carries its world in a component-type section)"
    adWfs := adWfs ++ aws
    let byImport := dedup (m.importNames.filterMap fun (mn, n) => if mn == an then some n else none)
    let some a0 := Silmaril.Wasm.Perf.CoreDecode.decodeF ab
      | throw s!"adapter {an}: rejected by silmaril's core decoder"
    let exps := a0.exports.map (·.name)
    let req := dedup (byImport ++ aws.flatMap fun aw => adapterRequired aw exps)
    let fnExports := aws.any fun aw => !(exportFns aw).isEmpty
    if byImport.isEmpty && !fnExports then continue
    -- wit-component's `realloc_to_import_into_adapter`
    let mainRealloc := if growRealloc then none
      else if m.exports.any (·.1 == "cabi_realloc_adapter") then some "cabi_realloc_adapter"
      else generalRealloc m
    let o ← AdaptGC.run ab req mainRealloc
    gcs := gcs ++ [(an, o, aws)]
  -- the world: the main module's and the adapters', live for what the modules import; the
  -- adapters' imports come first (as `wasm-tools component new` 1.262.0 orders them)
  let groups := m.importNames.filter (fun (mn, _) => !adNames.contains mn) ::
    gcs.map fun (_, o, _) => o.funcImports.filterMap fun (mn, n, _) =>
      if mn == "__main_module__" then none else some (mn, n)
  let wf ← Front.checkUtf8 (← WorldMerge.liveWorldSeq (mainWfs ++ adWfs) groups (some (adWfs ++ mainWfs)))
  let tb : Tables := ⟨funcTable wf, resourcesOf wf⟩
  -- the main module's imports
  let reqs ← (m.importNames.zip m.imports).mapM fun ((mn, n), (_, t)) => do
    match adNames.idxOf? mn with
    | some _ =>
      match gcs.findIdx? (·.1 == mn) with
      | some a =>
        let (_, o, _) := gcs[a]!
        match o.exports.find? (·.1 == n) with
        | some (_, t') =>
          require (decide (t = t')) s!"core import {mn} {n}: type {repr t}, the adapter exports {repr t'}"
          pure ((mn, n), MainReq.adp a n, t)
        | none => throw s!"core import {mn} {n}: the adapter does not export {n}"
      | none => throw s!"internal: adapter {mn} not collected"
    | none =>
      let (_, r) ← reqOf wf tb ((mn, n), (n, t))
      pure ((mn, n), MainReq.req r, t)
  -- the adapters' imports
  let aplans ← gcs.mapM fun (an, o, _) => do
    let rs ← o.funcImports.mapM fun (mn, n, t) => do
      if mn == "__main_module__" then
        match coreExport? m n with
        | some t' =>
          require (decide (t = t')) s!"adapter {an} imports {n} from the main module at {repr t}, exported at {repr t'}"
          pure ((mn, n), AdReq.main n, t)
        | none => throw s!"adapter {an} imports {n} from the main module, which does not export it"
      else
        let (_, r) ← reqOf wf tb ((mn, n), (n, t))
        pure ((mn, n), AdReq.req r, t)
    pure (⟨an, o, gcMod o, rs⟩ : APlan)
  -- who implements each export
  let impls ← (exportFns wf).mapM fun x => do
    let by_ := aplans.findIdx? fun a => (exportNames x).any fun n => a.gc.exports.any (·.1 == n)
    let mm := match by_ with
      | some a => aplans[a]!.mod
      | none => m
    pure (⟨x, ← liftOf wf mm x, by_⟩ : Impl)
  let exported := tb.resources.filter fun r => match r.1 with
    | .iface k => (ifaces wf).any fun i => i.key == k && !i.imported
    | .world => false
  -- an interface both imported and exported lists its resources twice
  let dtors ← exported.eraseDups.mapM fun r => do pure (r, ← dtorOf m r)
  -- memory and allocators
  let mainReqs : List IReq := reqs.filterMap fun (_, r, _) => match r with
    | .req r => some r
    | _ => none
  let adReqs (a : APlan) : List IReq := a.reqs.filterMap fun (_, r, _) => match r with
    | .req r => some r
    | _ => none
  let mut mem := aplans.any (·.gc.memImport.isSome)
  for i in impls do
    if ← liftUsesMemoryR (rho wf) i.x.sc i.x.f then mem := true
  for r in mainReqs ++ aplans.flatMap adReqs do
    if ← r.usesMem wf then mem := true
  if mainMem.isSome then mem := true
  require (!mem || mainMem.isSome || New.hasMemory prepared) "the component needs the main module's linear memory: export it as `memory`"
  let needImpRa (rs : List IReq) : Except String Bool := rs.anyM (·.usesRealloc wf)
  let needExpRa (by_ : Option Nat) : Except String Bool :=
    (impls.filter (·.by_ == by_)).anyM fun i => needsReallocR (rho wf) i.x.sc i.x.f
  let (mImp, mExp) := reallocs m
  let _ := mainExpRa0
  let mainImpRa ← do
    if ← needImpRa mainReqs then
      match mImp with
      | some r => pure (some r)
      | none => throw "the main module's imports need an allocator: export cabi_realloc (or cabi_import_realloc)"
    else pure none
  let mainExpRa ← do
    if ← needExpRa none then
      match mExp with
      | some r => pure (some r)
      | none => throw "the main module's exports need an allocator: export cabi_realloc (or cabi_export_realloc)"
    else pure none
  let adImpRa ← aplans.mapM fun a => do
    if ← needImpRa (adReqs a) then
      match (reallocs a.mod).1 with
      | some r => pure (some r)
      | none => throw s!"adapter {a.name}: its imports need an allocator (cabi_import_realloc)"
    else pure none
  let adExpRa ← (List.range aplans.length).mapM fun k => do
    if ← needExpRa (some k) then
      match (reallocs aplans[k]!.mod).2 with
      | some r => pure (some r)
      | none => throw s!"adapter {aplans[k]!.name}: its exports need an allocator (cabi_export_realloc)"
    else pure none
  let hooks ← if (coreExport? m "__wasm_task_hook").isNone then pure [] else do
    require (coreExport? m "__wasm_task_hook" == some ⟨[ti32], []⟩) "core export __wasm_task_hook: type (i32) -> ()"
    let ty (mm : CoreMod) (n : String) : Except String CoreFuncTy := match coreExport? mm n with
      | some t => pure t
      | none => throw s!"internal: no export {n}"
    let instOf : Option Nat → String × CoreMod := fun
      | some a => (s!"adapter{a}", (aplans[a]?.map (·.mod)).getD m)
      | none => ("main", m)
    let mut hs : Array HookFn := #[]
    -- wit-component's codes: 0/1 sync start/finish, 2 async start, 3 async resume (callback),
    -- 4/5 async blocked/finished, 8/9 destructor, 12/13 allocator
    for i in impls do
      let (inst, mm) := instOf i.by_
      match i.lift with
      | .sync c none => hs := hs.push ⟨inst, c, ← ty mm c, some 0, some 1, false⟩
      | .sync c (some pr) =>
        hs := hs.push ⟨inst, c, ← ty mm c, some 0, none, false⟩
        hs := hs.push ⟨inst, pr, ← ty mm pr, none, some 1, false⟩
      | .stackful c => hs := hs.push ⟨inst, c, ← ty mm c, some 2, some 5, false⟩
      | .callback c cb =>
        hs := hs.push ⟨inst, c, ← ty mm c, some 2, none, true⟩
        hs := hs.push ⟨inst, cb, ← ty mm cb, some 3, none, true⟩
    for r in dedup (mainImpRa.toList ++ mainExpRa.toList) do
      hs := hs.push ⟨"main", r, ← ty m r, some 12, some 13, false⟩
    for k in List.range aplans.length do
      let (inst, mm) := instOf (some k)
      for r in dedup ((adImpRa[k]?.join).toList ++ (adExpRa[k]?.join).toList) do
        hs := hs.push ⟨inst, r, ← ty mm r, some 12, some 13, false⟩
    for (_, d) in dtors do
      if let some c := d then hs := hs.push ⟨"main", c, ⟨[ti32], []⟩, some 8, some 9, false⟩
    pure hs.toList
  let callInit := coreExport? m "_initialize" == some ⟨[], []⟩
  pure ⟨prepared, m, wf, reqs, aplans, impls, dtors, mem, mainMem, hooks, callInit, mainImpRa, mainExpRa, adImpRa, adExpRa⟩

/-! ## Emission -/

/-- A shim slot. -/
inductive ASlot where
  /-- A request of the main module (`none`) or of adapter `a` that needs memory. -/
  | req (who : Option Nat) (r : IReq)
  /-- Function `exp` of adapter `a`, imported by the main module. -/
  | adp (a : Nat) (exp : String)
  | dtor (r : Scope × String) (core : String)

/-- The first entry of every name (a core instance's exports must have distinct names; a module
may import the same name several times). -/
def dedupNames {α : Type} (xs : List (String × α)) : List (String × α) :=
  xs.foldl (fun acc x => if acc.any (·.1 == x.1) then acc else acc ++ [x]) []

/-- **The component** of a plan. -/
def emit (p : Plan) : Except String XAst := do
  let wf := p.wf
  let nA := p.adapters.length
  -- shim slots: the main module's adapter functions and memory-using requests (in import
  -- order), the adapters' memory-using requests, the destructors
  let mainSlotOf ← p.reqs.mapM fun (_, r, _) => match r with
    | .adp _ _ => pure true
    | .req r => r.usesMem wf
  let adSlotOf ← p.adapters.mapM fun a => a.reqs.mapM fun (_, r, _) => match r with
    | .main _ => pure false
    | .req r => r.usesMem wf
  let mainSlots : List (ASlot × CoreFuncTy) := (p.reqs.zip mainSlotOf).filterMap fun ((_, r, t), b) =>
    if b then some (match r with
      | .adp a e => (.adp a e, t)
      | .req r => (.req none r, t)) else none
  let adSlots : List (ASlot × CoreFuncTy) := (List.range nA).flatMap fun k =>
    ((p.adapters[k]!.reqs.zip (adSlotOf[k]!))).filterMap fun ((_, r, t), b) =>
      match r, b with
      | .req r, true => some (.req (some k) r, t)
      | _, _ => none
  let dtorSlots : List (ASlot × CoreFuncTy) := p.dtors.filterMap fun (r, d) =>
    d.map fun c => (.dtor r c, ⟨[ti32], []⟩)
  let slots := mainSlots ++ adSlots ++ dtorSlots
  let shim := !slots.isEmpty || p.mainMem.isSome
  let (declSecs, x0) ← copyDecls {} (plainComp wf.decls)
  -- core module indices: main 0, adapters 1..nA, shim nA+1, fixup nA+2 (or nA+1)
  let hook := !p.hooks.isEmpty
  let hookModIdx := nA + 1
  let shimModIdx := nA + 1 + (if hook then 1 else 0)
  let fixupModIdx := shimModIdx + 1
  let go : StateT Silmaril.Wasm.JcoTool.NewI.Idx EM Unit := do
    addSec (.sec (.coreModule p.core))
    for a in p.adapters do addSec (.sec (.coreModule a.gc.bytes))
    if hook then addSec (.sec (.coreModule (← (hookModule p.hooks : Except String _))))
    if shim then
      match p.mainMem with
      | some mi =>
        addSec (.sec (.coreModule (← (mustEncode "shim" (shimWithMem (slots.map (·.2)) mi.min mi.max)))))
        let _ ← coreInst (.instantiate shimModIdx [])
        -- the memory is the shim's: core memory 0
        addSec (.sec (.aliases [⟨.core .memory, .coreExport 0 "$memory"⟩]))
      | none =>
        addSec (.sec (.coreModule (← (mustEncode "shim" (shimMod (slots.map (·.2))).encode))))
        let _ ← coreInst (.instantiate shimModIdx [])
    for s in declSecs do addSec (.sec s)
    set x0
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
    -- destructors through the shim
    let mut dtorIdx : List ((Scope × String) × Nat) := []
    let mut dk := mainSlots.length + adSlots.length
    for (s, _) in dtorSlots do
      match s with
      | .dtor r _ =>
        let c ← aliasCoreFunc 0 (toString dk)
        dtorIdx := dtorIdx ++ [(r, c)]
        dk := dk + 1
      | _ => pure ()
    -- exported interfaces' types
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
    -- types for task.return and streams/futures of every module's requests
    let allReqs : List IReq := (p.reqs.filterMap fun (_, r, _) => match r with
        | .req r => some r
        | _ => none) ++ p.adapters.flatMap fun a => a.reqs.filterMap fun (_, r, _) => match r with
        | .req r => some r
        | _ => none
    let x ← get
    let names := x.names
    let ts0 : TS := { types := Array.replicate x.types (.val (.prim .bool)) }
    let ((), ts) ← ((do
      for r in allReqs do
        match r with
        | .taskReturn sc f => do let _ ← optType names sc f.result
        | .chan _ _ sc c _ => do let _ ← valType names sc (chanTy c)
        | _ => pure ()
      : TyM Unit).run ts0)
    let fresh := ts.types.toList.drop x.types
    if !fresh.isEmpty then
      addSec (.sec (.types fresh))
      modify fun x => { x with types := x.types + fresh.length }
    -- the main module's imports
    let mut fs : Array Nat := #[]
    let mut slot := 0
    for k in List.range p.reqs.length do
      let (_, r, _) := p.reqs[k]!
      if mainSlotOf[k]! then
        fs := fs.push (← aliasCoreFunc 0 (toString slot))
        slot := slot + 1
      else match r with
        | .req r => fs := fs.push (← coreFunc (← (reqFunc wf names ts none none r)))
        | .adp _ _ => throw "internal: an adapter function outside the shim"
    let memMod := p.mainMem.map (·.module)
    let mnames := moduleNames (p.reqs.map (·.1) ++ (p.mainMem.map (fun mi => (mi.module, mi.name))).toList)
    let mut args : List (String × Nat) := []
    for mn in mnames do
      -- a name imported several times is exported once (all its imports get the first's function)
      let es := dedupNames (((List.range p.reqs.length).filter fun k => (p.reqs[k]!).1.1 == mn).map fun k =>
        ((p.reqs[k]!).1.2, (⟨.func, fs[k]!⟩ : CoreSortIdx)))
      let ms : List (String × CoreSortIdx) := match p.mainMem with
        | some mi => if memMod == some mn then [(mi.name, ⟨.memory, 0⟩)] else []
        | none => []
      args := args ++ [(mn, ← coreInst (.exports (ms ++ es)))]
    let main ← coreInst (.instantiate 0 args)
    let mem : Option Nat := if p.memory then some 0 else none
    if p.memory && p.mainMem.isNone then
      addSec (.sec (.aliases [⟨.core .memory, .coreExport main "memory"⟩]))
    -- the adapters, in order
    let mut adInst : Array Nat := #[]
    let mut adImpRa : Array (Option Nat) := #[]
    let mut aslot := mainSlots.length
    for k in List.range nA do
      let a := p.adapters[k]!
      let mut afs : Array Nat := #[]
      for j in List.range a.reqs.length do
        let (_, r, _) := a.reqs[j]!
        if (adSlotOf[k]!)[j]! then
          afs := afs.push (← aliasCoreFunc 0 (toString aslot))
          aslot := aslot + 1
        else match r with
          | .main n => afs := afs.push (← aliasCoreFunc main n)
          | .req r => afs := afs.push (← coreFunc (← (reqFunc wf names ts none none r)))
      let mut aargs : List (String × Nat) := []
      if let some (mmod, mname) := a.gc.memImport then
        aargs := aargs ++ [(mmod, ← coreInst (.exports [(mname, ⟨.memory, 0⟩)]))]
      for mn in moduleNames (a.reqs.map (·.1)) do
        let es := dedupNames (((List.range a.reqs.length).filter fun j => (a.reqs[j]!).1.1 == mn).map fun j =>
          ((a.reqs[j]!).1.2, (⟨.func, afs[j]!⟩ : CoreSortIdx)))
        match aargs.find? (·.1 == mn) with
        | some _ => throw s!"adapter {a.name}: module {mn} imports both a memory and functions"
        | none => aargs := aargs ++ [(mn, ← coreInst (.exports es))]
      let ai ← coreInst (.instantiate (k + 1) aargs)
      adInst := adInst.push ai
    -- the task hook wrappers (of the main module's and the adapters' entry points)
    let hookInst ← if hook then
        coreInst (.instantiate hookModIdx (("main", main) :: (List.range nA).map fun k => (s!"adapter{k}", adInst[k]!)))
      else pure 0
    -- a function of the main module (`none`) or of adapter `k`, through its task hook wrapper
    -- when it has one
    let fnIn (who : Option Nat) (n : String) : StateT Silmaril.Wasm.JcoTool.NewI.Idx EM Nat :=
      let (iname, inst) := match who with
        | some k => (s!"adapter{k}", adInst[k]!)
        | none => ("main", main)
      match p.hooks.find? fun f => f.inst == iname && f.name == n with
      | some f => if hook then aliasCoreFunc hookInst f.export else aliasCoreFunc inst n
      | none => aliasCoreFunc inst n
    let mainFn := fnIn none
    let mainImpRa ← match p.mainImpRa with
      | some n => some <$> mainFn n
      | none => pure none
    for k in List.range nA do
      adImpRa := adImpRa.push (← match p.adImpRa[k]! with
        | some n => some <$> fnIn (some k) n
        | none => pure none)
    -- fixup: the real functions behind the shim's slots
    if shim then
      let mut real : List (String × CoreSortIdx) := []
      let mut i := 0
      for (s, _) in slots do
        let f ← match s with
          | .req none r => coreFunc (← (reqFunc wf names ts mem mainImpRa r))
          | .req (some k) r => coreFunc (← (reqFunc wf names ts mem adImpRa[k]! r))
          | .adp a e => aliasCoreFunc adInst[a]! e
          | .dtor _ c => mainFn c
        real := real ++ [(toString i, ⟨.func, f⟩)]
        i := i + 1
      let actual ← coreInst (.exports real)
      addSec (.sec (.coreModule (← (mustEncode "fixup" (fixupMod (slots.map (·.2))).encode))))
      let _ ← coreInst (.instantiate fixupModIdx [("actual", actual), ("shim", 0)])
    -- `_initialize`, called once everything is in place
    if p.callInit then
      addSec (.sec (.coreModule (← (initModule hook : Except String _))))
      let nMods := 1 + nA + (if hook then 1 else 0) + (if shim then 2 else 0)
      let _ ← coreInst (.instantiate nMods [("main", main)])
    -- lifts
    let liftOne (im : Impl) (ty : Nat) : StateT Silmaril.Wasm.JcoTool.NewI.Idx EM Nat := do
      let inst := match im.by_ with
        | some a => adInst[a]!
        | none => main
      let _ := inst
      let fnOf (n : String) : StateT Silmaril.Wasm.JcoTool.NewI.Idx EM Nat := fnIn im.by_ n
      let raName := match im.by_ with
        | some a => p.adExpRa[a]!
        | none => p.mainExpRa
      let ra ← match raName with
        | some n => some <$> fnOf n
        | none => pure none
      let (cf, pr, cb) ← match im.lift with
        | .sync c pr => do
          let a ← fnOf c
          let b ← match pr with
            | some n => some <$> fnOf n
            | none => pure none
          pure (a, b, none)
        | .stackful c => do pure (← fnOf c, none, none)
        | .callback c cbn => do
          let a ← fnOf c
          let b ← fnOf cbn
          pure (a, none, some b)
      let opts ← (liftOpts wf mem ra im.x pr cb)
      addSec (.sec (.canons [.lift cf opts ty]))
      let s ← get
      set { s with funcs := s.funcs + 1 }
      pure s.funcs
    for im in p.impls do
      if im.x.sc = .world then
        let some ty := lookupIdx im.x.core (← get).expFunc
          | (throw s!"world export {im.x.core} has no function type")
        let fi ← liftOne im ty
        addSec (.sec (.exports [⟨⟨im.x.core, .plain0⟩, ⟨.func, fi⟩, none⟩]))
        modify fun s => { s with funcs := s.funcs + 1 }
    for (i, r, ds) in replays do
      let mut fargs : List (String × SortIdx) := []
      for im in p.impls do
        if im.x.sc = .iface i.key then
          let some ty := lookupIdx (fname im.x.f) r.funcs
            | (throw s!"{keyName i.key}: no function type for {fname im.x.f}")
          let fi ← liftOne im ty
          fargs := fargs ++ [(funcImportName (fname im.x.f), ⟨.func, fi⟩)]
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

/-- A summary of a plan. -/
def summary (p : Plan) : List String :=
  p.adapters.map (fun a =>
    s!"adapter {a.name}: {a.gc.bytes.size} bytes after collection, {a.gc.funcImports.length} function imports, {a.gc.exports.length} exports") ++
  p.impls.map (fun i => s!"export {i.x.core}: by " ++ match i.by_ with
    | some a => s!"adapter {p.adapters[a]!.name}"
    | none => "the main module")

/-! ## Component-level custom sections -/

/-- A `component-name` section naming core modules (subsection 1, sort `core module`): the debug
names wit-component writes, for the core modules. -/
def componentNameSection (mods : List (Nat × String)) : Option ByteArray := do
  let entries ← Silmaril.Parse.ByteParse.Enc.vec (fun (x : Nat × String) => do
    pure ((← Silmaril.Parse.ByteParse.Enc.u32 x.1) ++ (← Silmaril.Parse.ByteParse.Enc.name x.2))) mods
  let sub ← Silmaril.Parse.ByteParse.Enc.sized ([0x00, 0x11] ++ entries)
  Silmaril.Wasm.Wit.Binary.customSection "component-name" ⟨(0x01 :: sub).toArray⟩

/-- **The component-level custom sections** `wasm-jco new` appends, as wit-component does: a
`component-name` section (the core modules' names) and a `producers` section
(`processed-by: wasm-jco`). Custom sections carry no semantics: the reference translation maps
them to no definition (`LayoutRef.secTo`), so they change neither validity nor the layout
reading. -/
def metaSections (mods : List String) : Option ByteArray := do
  let names ← componentNameSection (mods.zipIdx.map fun (n, i) => (i, n))
  let p ← (Front.addProcessedBy []).encode
  let prod ← Silmaril.Wasm.Wit.Binary.customSection "producers" ⟨p.toArray⟩
  pure (names ++ prod)

/-- The names of the core modules of the certified layout (`NewI.emit`): the main module, and the
shim and fixup modules when there are three. -/
def certifiedNames (n : Nat) : List String :=
  if n = 3 then ["main", "wasm-jco:shim", "wasm-jco:fixups"] else (List.range n).map fun i =>
    if i = 0 then "main" else s!"wasm-jco:module{i}"

/-- An output with the custom sections appended (`withMeta_bytes`: the bytes are the
component's, then the sections). -/
def withMeta (o : Tool.Out) (mods : List String) : Tool.Out :=
  match metaSections mods with
  | some m => { o with bytes := o.bytes ++ m }
  | none => o

theorem withMeta_bytes (o : Tool.Out) (mods : List String) :
    ∃ m : ByteArray, (withMeta o mods).bytes = o.bytes ++ m := by
  unfold withMeta
  split
  · exact ⟨_, rfl⟩
  · exact ⟨ByteArray.empty, by simp⟩

/-- Whether a module needs the general layout even when the certified one accepts it: it exports
`__wasm_task_hook` (the certified layout does not wrap entry points in task hooks) or
`_initialize` (the certified layout does not call it). -/
def needsGeneralOf (d : Option Silmaril.Wasm.Module) (core : ByteArray) : Bool :=
  match readMainOf d core with
  | .ok (m, _) => (coreExport? m "__wasm_task_hook").isSome || (coreExport? m "_initialize").isSome
  | .error _ => false

/-- `needsGeneralOf` on the module silmaril's verified decoder reads (`wasm-jco new` passes the
module it has already decoded: `NewMain.newMain_eq`). -/
def needsGeneral (core : ByteArray) : Bool :=
  needsGeneralOf (Silmaril.Wasm.Perf.CoreDecode.decodeF core) core

/-- An output, refused unless the reference validator accepts it (`refChecked_valid`). -/
def refChecked (b : ByteArray) (ls : List String) : Except String (ByteArray × List String) :=
  match ToolV.refCheckX b with
  | .ok _ => pure (b, ls ++ ["reference-valid: yes (Reference.check? at Features.all)"])
  | .error e => throw s!"refusing to write an output the reference validator rejects: {e}"

/-- The bytes of the general layout of a plan, refused unless the reference validator accepts
them. -/
def newAdaptOf (p : Plan) : Except String (ByteArray × List String) := do
  let c ← emit p
  let b0 ← mustEncode "the component" c.encode
  let mods := ["main"] ++ p.adapters.map (fun a => "wasm-jco:adapter:" ++ a.name) ++
    (if p.hooks.isEmpty then [] else ["wasm-jco:task-hooks"]) ++ ["wasm-jco:shim", "wasm-jco:fixups"] ++
    (if p.callInit then ["wasm-jco:initialize"] else [])
  let nMods := c.sections.countP fun | .sec (.coreModule _) => true | _ => false
  let mods := mods.take nMods
  let b := match metaSections mods with
    | some m => b0 ++ m
    | none => b0
  refChecked b (summary p)


/-- **`wasm-jco new --adapt`**: the component's bytes, refused unless the reference validator
accepts them. -/
def newAdapt (core : ByteArray) (wit : Option ((String × String) × List (String × String) × String))
    (ads : List (String × ByteArray)) (growRealloc : Bool := false) :
    Except String (ByteArray × List String) := do
  let p ← plan core wit ads growRealloc
  newAdaptOf p

end Silmaril.Wasm.JcoTool.Adapt
