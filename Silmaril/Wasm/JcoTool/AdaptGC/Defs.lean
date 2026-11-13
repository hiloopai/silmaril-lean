module

public import Silmaril.Wasm.Binary.Core.Decode
public import Silmaril.Wasm.Binaryen.Exe.Encode
public import Silmaril.Wasm.Component.Binary.Lower.Defs
public import Silmaril.Wasm.Wit.Binary.Embed.Defs
public import Silmaril.Parse.ByteParse.Defs
public import Silmaril.Wasm.Perf.CoreDecode.Defs

/-!
# Garbage collection of a WASI adapter module (`wasm-jco new --adapt`)

wit-component's `gc::run` (wasm-tools 1.262.0, `crates/wit-component/src/gc.rs`), on silmaril's
decoded module (`Perf.CoreDecode.decodeModule`, equal to silmaril's `Decode.decodeModule`:
`CoreDecode.decodeModule_eq`) and re-encoded by silmaril's verified
encoder (`Binaryen.Exe.encodeModule?`):

1. only the **required** exports are kept (the functions the main module imports from the
   adapter, the functions the adapter's world exports, and its allocators);
2. the functions, globals, tables and memories reachable from them are computed (a worklist
   over `call`, `return_call`, `ref.func`, `global.get/set`, the table and the memory
   instructions); unreachable functions are removed, **imported ones included**, so the
   component imports only the WASI functions the main module can reach;
3. the adapter's stack is provided as wit-component does: when the adapter has a mutable
   `i32` global named `__stack_pointer` (by its `name` section) it is allocated by a function
   `allocate_stack` that calls `cabi_realloc` for 64 KiB; lazily (called at the start of every
   exported function, guarded by the `allocation_state` global) when the main module exports a
   `cabi_realloc` and the adapter has that global, else once, as the module's start function.
   An import `__main_module__.cabi_realloc` is renamed to the main module's allocator, or, when
   the main module exports none, replaced by a local allocator that grows the memory by one
   page (`reallocViaMemoryGrow`).

Function indices are renumbered (`remapL`); types and globals are kept as they are (wit-component
also drops unused ones, which changes no import and no behaviour). Custom sections are not
kept (the `name` section is read for the global names only).

Nothing here is proved: the module is checked downstream (the component that contains it is
refused unless silmaril's reference validator accepts it), and tested against wit-component
(`tools/wasm-jco/tests/adapt.sh`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.AdaptGC

open Silmaril.Wasm
open Silmaril.Wasm.Component (CoreFuncTy)

/-! ## What an instruction refers to -/

/-- The function and global indices, and whether tables or the memory are used. -/
structure Uses where
  funcs : Array Nat := #[]
  globals : Array Nat := #[]
  tables : Bool := false
  mem : Bool := false

mutual
/-- What instruction `i` refers to, added to `u`. -/
def usesI : Instr → Uses → Uses
  | .block _ b, u => usesL b u
  | .loop _ b, u => usesL b u
  | .tryTable _ _ b, u => usesL b u
  | .if_ _ t e, u => usesL e (usesL t u)
  | .call f, u => { u with funcs := u.funcs.push f.toNat }
  | .returnCall f, u => { u with funcs := u.funcs.push f.toNat }
  | .refFunc f, u => { u with funcs := u.funcs.push f.toNat }
  | .globalGet g, u => { u with globals := u.globals.push g.toNat }
  | .globalSet g, u => { u with globals := u.globals.push g.toNat }
  | .callIndirect _ _, u | .returnCallIndirect _ _, u | .tableGet _, u | .tableSet _, u
  | .tableSize _, u | .tableGrow _, u | .tableFill _, u | .tableCopy _ _, u
  | .tableInit _ _, u | .elemDrop _, u => { u with tables := true }
  | .intLoad _ _ _ _, u | .floatLoad _ _ _, u | .intStore _ _ _ _, u | .floatStore _ _ _, u
  | .vecLoad _ _ _, u | .vecLoadLane _ _ _ _, u | .vecStore _ _, u | .vecStoreLane _ _ _ _, u
  | .memorySize _, u | .memoryGrow _, u | .memoryFill _, u | .memoryCopy _ _, u
  | .memoryInit _ _, u | .dataDrop _, u => { u with mem := true }
  | _, u => u
/-- What an instruction sequence refers to. -/
def usesL : List Instr → Uses → Uses
  | [], u => u
  | i :: is, u => usesL is (usesI i u)
end

/-- A function index renumbered by `f`. -/
def fidx (f : Nat → Nat) (i : FuncIdx) : FuncIdx := ⟨Fin.ofNat (2 ^ 32) (f i.toNat)⟩

mutual
/-- Renumber the function indices of an instruction. -/
def remapI (f : Nat → Nat) : Instr → Instr
  | .block t b => .block t (remapL f b)
  | .loop t b => .loop t (remapL f b)
  | .tryTable t cs b => .tryTable t cs (remapL f b)
  | .if_ t a b => .if_ t (remapL f a) (remapL f b)
  | .call i => .call (fidx f i)
  | .returnCall i => .returnCall (fidx f i)
  | .refFunc i => .refFunc (fidx f i)
  | i => i
/-- Renumber the function indices of an instruction sequence. -/
def remapL (f : Nat → Nat) : List Instr → List Instr
  | [] => []
  | i :: is => remapI f i :: remapL f is
end

/-! ## The functions wit-component adds -/

def i32 : ValType := .num (.int .i32)
def c32 (n : Int) : Instr := .intConst .i32 (BitVec.ofInt 32 n)
def lget (n : Nat) : Instr := .localGet ⟨Fin.ofNat (2 ^ 32) n⟩
def gget (n : Nat) : Instr := .globalGet ⟨Fin.ofNat (2 ^ 32) n⟩
def gset (n : Nat) : Instr := .globalSet ⟨Fin.ofNat (2 ^ 32) n⟩
def callN (n : Nat) : Instr := .call ⟨Fin.ofNat (2 ^ 32) n⟩
def trapUnless (cond : List Instr) : List Instr := cond ++ [.if_ .empty [.unreachable] []]

/-- The page size (64 KiB pages only: wit-component's `page_size_log2` is 16 for them). -/
def pageSize : Int := 65536

/-- wit-component's `realloc_via_memory_grow`: `cabi_realloc` for fresh one-page allocations
(type `(i32 i32 i32 i32) -> i32`, one extra local). -/
def reallocViaMemoryGrow : List ValType × Expr :=
  ([i32],
    trapUnless [c32 0, lget 0, .intRelOp .i32 .ne] ++
    trapUnless [c32 0, lget 1, .intRelOp .i32 .ne] ++
    trapUnless [c32 pageSize, lget 3, .intRelOp .i32 .ne] ++
    [c32 1, .memoryGrow ⟨0⟩, .localTee ⟨4⟩] ++
    trapUnless [c32 (-1), .intRelOp .i32 .eq] ++
    [lget 4, c32 16, .intBinOp .i32 .shl])

/-- wit-component's `allocate_stack_via_realloc`: `__stack_pointer := realloc(0, 0, 8, 64 KiB) +
64 KiB`, guarded by `allocation_state` (0 unallocated, 1 allocating, 2 allocated) if any. -/
def allocateStack (realloc sp : Nat) (state : Option Nat) : Expr :=
  let body := [c32 0, c32 0, c32 8, c32 pageSize, callN realloc, c32 pageSize,
    .intBinOp .i32 .add, gset sp]
  match state with
  | some st => [gget st, c32 0, .intRelOp .i32 .eq,
      .if_ .empty ([c32 1, gset st] ++ body ++ [c32 2, gset st]) []]
  | none => body

/-- A function type as a recursive group of one. -/
def fty (ps rs : List ValType) : RecType := ⟨[⟨true, [], .func ⟨ps, rs⟩⟩]⟩

/-! ## The `name` section's global names -/

open Silmaril.Parse.ByteParse in
/-- The global names (subsection 7) of a `name` section's payload. -/
def globalNamesP : Parser (List (Nat × String)) := do
  let subs ← untilEnd (do
    let id ← byte
    let n ← u32
    if id = 7 then
      sized n (vec (do let i ← u32; let s ← name; pure (i, s)))
    else do
      let _ ← bytes n
      pure [])
  pure subs.flatten

/-- The global names of a module (empty when it has no readable `name` section). -/
def globalNames (b : ByteArray) : List (Nat × String) :=
  match Silmaril.Wasm.Wit.Binary.customSections b with
  | .ok cs => match cs.find? (·.1 == "name") with
    | some (_, p) => match Silmaril.Parse.ByteParse.runAll globalNamesP p with
      | .ok l => l
      | .error _ => []
    | none => []
  | .error _ => []

/-! ## The collector -/

instance : Inhabited TypeIdx := ⟨⟨0⟩⟩
instance : Inhabited Func := ⟨⟨default, [], []⟩⟩
instance : Inhabited Global := ⟨⟨⟨.const, i32⟩, []⟩⟩

/-- What the collector returns: the module and what the component needs to know of it. -/
structure Out where
  mod : Silmaril.Wasm.Module
  bytes : ByteArray
  /-- The function imports, in order: module, name, core type. -/
  funcImports : List (String × String × CoreFuncTy)
  /-- Whether the module imports a memory (`env.memory`, the main module's). -/
  memImport : Option (String × String)
  /-- The function exports and their core types. -/
  exports : List (String × CoreFuncTy)

/-- Is `(m, n)` the adapter's import of the main module's allocator? -/
def isRealloc (m n : String) : Bool :=
  m == "__main_module__" && (n == "canonical_abi_realloc" || n == "cabi_realloc")

/-- A function of the output, before renumbering. -/
inductive NewFn where
  | imported (orig : Nat) (m n : String) (t : TypeIdx)
  | local (orig : Nat) (f : Func)
  /-- The allocator that replaces an import of the main module's when it has none. -/
  | growRealloc (orig : Nat) (t : TypeIdx)

def NewFn.orig? : NewFn → Option Nat
  | .imported o _ _ _ | .local o _ | .growRealloc o _ => some o

/-- The live mutable `i32` global of name `n` (by the `name` section), if exactly one. -/
def findGlobalIn (globals : Array Global) (liveG : Array Bool) (gnames : List (Nat × String))
    (n : String) : Except String (Option Nat) := do
  let ms := (List.range globals.size).filter fun i =>
    liveG[i]! && globals[i]!.type.mutability == Mutability.var && globals[i]!.type.value == i32 &&
      (gnames.find? (·.1 == i)).map (·.2) == some n
  match ms with
  | [] => pure none
  | [i] => pure (some i)
  | _ => throw s!"found {ms.length} mutable i32 globals with name {n}"

/-- **wit-component's `gc::run`** on an adapter: keep the exports `required` and what they
reach; `mainRealloc` is the main module's allocator export (`cabi_realloc`), if any. -/
def run (b : ByteArray) (required : List String) (mainRealloc : Option String) :
    Except String Out := do
  let m ← match Silmaril.Wasm.Perf.CoreDecode.decodeModule b with
    | .ok m => pure m
    | .error e => throw s!"adapter module rejected by silmaril's core decoder: {e}"
  if !m.elems.isEmpty || !m.data.isEmpty then
    throw "an adapter module may not have element or data segments"
  if m.start.isSome then throw "unsupported section `start` in adapter"
  for r in required do
    if !m.exports.any (·.name == r) then throw s!"adapter module does not have export `{r}`"
  let exps := m.exports.filter fun e => required.contains e.name
  -- the index spaces
  let fimps : Array (Nat × String × String × TypeIdx) := Id.run do
    let mut acc := #[]
    for i in m.imports do
      if let .func t := i.type then acc := acc.push (acc.size, i.moduleName, i.name, t)
    pure acc
  let gimps : List (Import × GlobalType) := m.imports.filterMap fun i => match i.type with
    | .global t => some (i, t)
    | _ => none
  if !gimps.isEmpty then throw "an adapter module importing globals is not supported"
  if m.imports.any (fun i => match i.type with | .table _ | .tag _ => true | _ => false) then
    throw "an adapter module importing tables or tags is not supported"
  let nImp := fimps.size
  let funcs := m.funcs.toArray
  let total := nImp + funcs.size
  let globals := m.globals.toArray
  -- liveness: a worklist over functions; globals' initializers scanned when they become live
  let (liveF, liveG, tablesLive, memLive) := Id.run do
    let mut liveF : Array Bool := Array.replicate total false
    let mut liveG : Array Bool := Array.replicate globals.size false
    let mut work : Array Nat := #[]
    let mut tbl := false
    let mut mem := false
    let mut pendingG : Array Nat := #[]
    for e in exps do
      match e.index with
      | .func f => if f.toNat < total && !liveF[f.toNat]! then
          liveF := liveF.set! f.toNat true; work := work.push f.toNat
      | .global g => pendingG := pendingG.push g.toNat
      | .table _ => tbl := true
      | .memory _ => mem := true
      | .tag _ => pure ()
    for _ in [0:total + globals.size + 1] do
      -- globals first (their initializers may refer to functions)
      for g in pendingG do
        if g < globals.size && !liveG[g]! then
          liveG := liveG.set! g true
          let u := usesL globals[g]!.init {}
          for f in u.funcs do
            if f < total && !liveF[f]! then liveF := liveF.set! f true; work := work.push f
      pendingG := #[]
      match work.back? with
      | none => break
      | some f =>
        work := work.pop
        if f ≥ nImp then
          let u := usesL funcs[f - nImp]!.body {}
          if u.tables then tbl := true
          if u.mem then mem := true
          pendingG := pendingG ++ u.globals
          for g in u.funcs do
            if g < total && !liveF[g]! then liveF := liveF.set! g true; work := work.push g
    pure (liveF, liveG, tbl, mem)
  if tablesLive then throw "tables should not be present in the final adapter module"
  let gnames := globalNames b
  let findGlobal := findGlobalIn globals liveG gnames
  let sp ← findGlobal "__stack_pointer"
  let state ← findGlobal "allocation_state"
  -- the memory import (kept when live)
  let memImp : Option Import := m.imports.find? fun i => match i.type with
    | .memory _ => true
    | _ => false
  let memLive := memLive || (exps.any fun e => match e.index with | .memory _ => true | _ => false)
  if m.memories.length + (if memImp.isSome then 1 else 0) > 1 then
    throw "the adapter module should not use multi-memory"
  if !m.memories.isEmpty && memLive then
    throw "locally-defined memories are not allowed define a local memory"
  -- the output's functions, in wit-component's order
  let live := (List.range total).filter fun i => liveF[i]!
  let mut kept : Array NewFn := #[]
  let mut locals : Array NewFn := #[]
  for i in live do
    if i < nImp then
      let (_, mn, n, t) := fimps[i]!
      if isRealloc mn n && mainRealloc.isNone then locals := locals.push (.growRealloc i t)
      else kept := kept.push (.imported i mn (if isRealloc mn n then mainRealloc.getD n else n) t)
    else locals := locals.push (.local i funcs[i - nImp]!)
  let reallocKept : Option Nat := (kept.toList.zipIdx.find? fun (f, _) => match f with
    | .imported o _ _ _ => let (_, a, n, _) := fimps[o]!; isRealloc a n
    | _ => false).map (·.2)
  let mut types := m.types
  let typeCount := m.typeDefinitions.length
  let mut nTypes := typeCount
  let mut reallocTy : Option Nat := none
  let addType (ps rs : List ValType) (ts : List RecType) (k : Nat) : List RecType × Nat :=
    (ts ++ [fty ps rs], k)
  -- an import of the main module's allocator, added to allocate the stack
  let extraImport : Option String := match mainRealloc, sp, reallocKept with
    | some r, some _, none => some r
    | _, _, _ => none
  if extraImport.isSome then
    let (ts, k) := addType [i32, i32, i32, i32] [i32] types nTypes
    types := ts; reallocTy := some k; nTypes := nTypes + 1
  let nKept := kept.size + (if extraImport.isSome then 1 else 0)
  let mut realloc : Option Nat := match reallocKept with
    | some k => some k
    | none => if extraImport.isSome then some kept.size else none
  -- the local allocator that replaces the main module's, if any
  match locals.toList.zipIdx.find? (fun (f, _) => match f with | .growRealloc _ _ => true | _ => false) with
  | some (_, j) => realloc := some (nKept + j)
  | none => pure ()
  let lazy : Bool := sp.isSome && state.isSome && mainRealloc.isSome
  let lazyIdx := nKept + locals.size
  let next0 := lazyIdx + (if lazy then 1 else 0)
  -- the renumbering
  let newIdx : Array Nat := Id.run do
    let mut a := Array.replicate total 0
    for (f, j) in kept.toList.zipIdx do
      if let some o := f.orig? then a := a.set! o j
    for (f, j) in locals.toList.zipIdx do
      if let some o := f.orig? then a := a.set! o (nKept + j)
    pure a
  let rn : Nat → Nat := fun i => newIdx[i]?.getD i
  let exported : List Nat := exps.filterMap fun e => match e.index with
    | .func f => some f.toNat
    | _ => none
  -- the bodies
  let mut outFuncs : Array Func := #[]
  for f in locals do
    match f with
    | .growRealloc _ t => outFuncs := outFuncs.push ⟨t, reallocViaMemoryGrow.1, reallocViaMemoryGrow.2⟩
    | .local o fn =>
      let body := remapL rn fn.body
      let body := if lazy && exported.contains o then callN lazyIdx :: body else body
      outFuncs := outFuncs.push ⟨fn.type, fn.locals, body⟩
    | .imported .. => pure ()
  let mut emptyTy : Option Nat := none
  let getEmpty (ts : List RecType) (k : Nat) (e : Option Nat) : List RecType × Nat × Nat :=
    match e with
    | some i => (ts, k, i)
    | none => (ts ++ [fty [] []], k + 1, k)
  if lazy then
    let (ts, k, e) := getEmpty types nTypes emptyTy
    types := ts; nTypes := k; emptyTy := some e
    match realloc, sp with
    | some r, some s => outFuncs := outFuncs.push ⟨⟨Fin.ofNat _ e⟩, [], allocateStack r s state⟩
    | _, _ => throw "internal: lazy stack allocation without an allocator"
  let mut next := next0
  if sp.isSome && (realloc.isNone || state.isNone) then
    let t ← match reallocTy with
      | some t => pure t
      | none => do
        let (ts, k) := addType [i32, i32, i32, i32] [i32] types nTypes
        types := ts; nTypes := k + 1; reallocTy := some k; pure k
    outFuncs := outFuncs.push ⟨⟨Fin.ofNat _ t⟩, reallocViaMemoryGrow.1, reallocViaMemoryGrow.2⟩
    realloc := some next
    next := next + 1
  let mut start : Option Nat := none
  if let some s := sp then
    if !lazy && (memLive && memImp.isSome) then
      let (ts, k, e) := getEmpty types nTypes emptyTy
      types := ts; nTypes := k; emptyTy := some e
      match realloc with
      | some r => outFuncs := outFuncs.push ⟨⟨Fin.ofNat _ e⟩, [], allocateStack r s state⟩
      | none => throw "internal: stack allocation without an allocator"
      start := some next
      next := next + 1
  -- imports: the memory (if live), the kept functions, the added allocator import
  let memImports : List Import := if memLive then memImp.toList else []
  let fnImports : List Import := kept.toList.filterMap fun
    | .imported _ mn n t => some ⟨mn, n, .func t⟩
    | _ => none
  let extra : List Import := match extraImport, reallocTy with
    | some r, some t => [⟨"__main_module__", r, .func ⟨Fin.ofNat _ t⟩⟩]
    | _, _ => []
  let outExports : List Export := exps.map fun e => match e.index with
    | .func f => ⟨e.name, .func (fidx rn f)⟩
    | ix => ⟨e.name, ix⟩
  let out : Silmaril.Wasm.Module :=
    { m with types := types, imports := memImports ++ fnImports ++ extra,
             tables := [], funcs := outFuncs.toList, exports := outExports,
             start := start.map fun s => ⟨Fin.ofNat _ s⟩ }
  let bytes ← match Silmaril.Wasm.Binaryen.Exe.encodeModule? out with
    | .ok bs => pure (⟨bs.toArray⟩ : ByteArray)
    | .error e => throw s!"the collected adapter does not encode: {e}"
  -- what the component needs: the function imports and exports with their core types
  let fts := out.functionTypes
  let fImps ← (fnImports ++ extra).mapM fun i => match i.type with
    | .func t => do pure (i.moduleName, i.name, ← Silmaril.Wasm.Component.Binary.Lower.coreFuncTy out t)
    | _ => throw "internal"
  let fExps ← outExports.filterMapM fun e => match e.index with
    | .func f => match fts[f.toNat]? with
      | some t => do pure (some (e.name, ← Silmaril.Wasm.Component.Binary.Lower.coreFuncTy out t))
      | none => throw s!"adapter export {e.name}: function out of range"
    | _ => pure none
  pure ⟨out, bytes, fImps, (memImports.head?.map fun i => (i.moduleName, i.name)), fExps⟩

end Silmaril.Wasm.JcoTool.AdaptGC
