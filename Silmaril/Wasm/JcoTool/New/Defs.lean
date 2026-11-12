module

public import Silmaril.Wasm.JcoTool.Abi.Defs
public import Silmaril.Wasm.JcoTool.Emit.Defs
public import Silmaril.Wasm.Component.Binary.Lower.Defs
public import Silmaril.Wasm.Perf.CoreMod.Defs

/-!
# `wasm-jco new`: a core module and a WIT world to a component binary

`plan core w` reads the function interface of the core module `core` (silmaril's verified
decoder, through `Silmaril.Wasm.Perf.CoreMod.coreModF`, which is
`Silmaril.Wasm.Component.Binary.Lower.coreMod` with the fast decoder: `CoreMod.coreModF_eq`) and
matches it against the
world `w` under the canonical ABI's core signatures (`Silmaril.Wasm.JcoTool.Abi`) and
wit-component's legacy core names:

* a world export `f` is the core export `f` (sync), `[async-lift]f` with the callback
  `[callback][async-lift]f`, or `[async-lift-stackful]f` (async); a sync export may have a
  post-return `cabi_post_f`;
* a core import from module `$root` named `f` is `canon lower` of world import `f`; from
  `$root` or `[export]$root`, the names `[task-return]f`, `[waitable-set-new]`,
  `[stream-new-N]f`, `[async-lower][stream-read-N]f`, … are the async built-ins (`N` indexes
  the streams and futures of `f`, `funcChans`);
* every core type must be the canonical one, else `plan` fails with the offending name.

`emit` turns the plan into a component (`XAst`): the core module, the world's types and
imports, one core function per core import, inline core instances per import module, the
instance of the module, and `canon lift` of each export. Core functions that need the
module's own memory (`canon lower` of a function with strings or lists, `stream.read`,
`waitable-set.wait`, …) go through wit-component's indirect pattern: a `shim` module with a
`funcref` table and trampolines is instantiated first, the main instance imports the
trampolines, and a `fixup` module fills the table once the memory exists.

The theorems are in `Silmaril.Wasm.JcoTool.New.Thms` and at the entry point
`Silmaril.Wasm.JcoTool.Tool`.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.New

open Silmaril.Wasm.Wit.Binary (Ty Func World WorldItem)
open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component (CoreFuncTy)

/-! ## Component types -/

/-- The type section being built, with a memo of value type definitions. -/
structure TS where
  types : Array DefType := #[]
  memo : List (DefValType × Nat) := []

abbrev TyM := StateT TS (Except String)

/-- The index of a value type definition, defined once. -/
def intern (d : DefValType) : TyM Silmaril.Wasm.Component.Binary.ValType := do
  let s ← get
  match s.memo.find? (·.1 == d) with
  | some (_, i) => pure (.idx i)
  | none =>
    set { s with types := s.types.push (.val d), memo := (d, s.types.size) :: s.memo }
    pure (.idx s.types.size)

mutual
/-- A resolved WIT type as a component value type. -/
def valType : Silmaril.Wasm.Wit.Binary.Ty → TyM Silmaril.Wasm.Component.Binary.ValType
  | .prim p => pure (.prim p)
  | .list t => do
    let a ← valType t
    intern (.list a)
  | .option t => do
    let a ← valType t
    intern (.option a)
  | .result ok err => do
    let a ← optType ok
    let b ← optType err
    intern (.result a b)
  | .tuple ts => do
    let a ← valTypes ts
    intern (.tuple a)
  | .stream t => do
    let a ← optType t
    intern (.stream a)
  | .future t => do
    let a ← optType t
    intern (.future a)
  | .map k v => do
    let a ← valType k
    let b ← valType v
    intern (.map a b)
  | .fixedList _ _ => throw "fixed-size lists are not supported"
  | .own _ | .borrow _ => throw "resources are not supported by `wasm-jco new` yet"
  | .ref r => throw s!"named type `{r.name}` is not supported (anonymous types only)"
def optType : Option Silmaril.Wasm.Wit.Binary.Ty → TyM (Option Silmaril.Wasm.Component.Binary.ValType)
  | none => pure none
  | some t => some <$> valType t
def valTypes : List Silmaril.Wasm.Wit.Binary.Ty → TyM (List Silmaril.Wasm.Component.Binary.ValType)
  | [] => pure []
  | t :: ts => do
    let a ← valType t
    let b ← valTypes ts
    pure (a :: b)
end

/-- The index of the function type of `f`. -/
def funcType (f : Silmaril.Wasm.Wit.Binary.Func) : TyM Nat := do
  let ps ← f.params.mapM fun (n, t) => do pure (n, ← valType t)
  let r ← optType f.result
  let s ← get
  set { s with types := s.types.push (.func ⟨ps, r, f.async⟩) }
  pure s.types.size

/-! ## Core names -/

def dropPrefix : List Char → List Char → Option (List Char)
  | [], s => some s
  | c :: p, d :: s => if c = d then dropPrefix p s else none
  | _ :: _, [] => none

/-- `s` without the prefix `p`. -/
def strip? (p s : String) : Option String := String.ofList <$> dropPrefix p.toList s.toList

/-- `N]rest` as `(N, rest)`. -/
def indexBracket (s : String) : Option (Nat × String) :=
  match s.toList.span (· ≠ ']') with
  | (ds, ']' :: rest) => (String.ofList ds).toNat?.map fun n => (n, String.ofList rest)
  | _ => none

/-- An operation on a stream or future end. -/
inductive ChanOp where
  | new | read | write | cancelRead | cancelWrite | dropReadable | dropWritable
  deriving Repr, DecidableEq, Inhabited

def chanOps : List (String × ChanOp) :=
  [("new-", .new), ("read-", .read), ("write-", .write), ("cancel-read-", .cancelRead),
   ("cancel-write-", .cancelWrite), ("drop-readable-", .dropReadable),
   ("drop-writable-", .dropWritable)]

/-- What a core import of the module asks for. -/
inductive Req where
  /-- `canon lower` of world import `i`. -/
  | lower (i : Nat) (f : Silmaril.Wasm.Wit.Binary.Func)
  /-- `canon lower` of world import `i` with the `async` option (`[async-lower]f`). -/
  | lowerAsync (i : Nat) (f : Silmaril.Wasm.Wit.Binary.Func)
  /-- `error-context.new` with the string encoding `enc` (`[error-context-new-<enc>]`). -/
  | errorContextNew (enc : CanonOpt)
  /-- `error-context.debug-message` with the string encoding `enc`. -/
  | errorContextDebugMessage (enc : CanonOpt)
  | errorContextDrop
  | taskReturn (f : Silmaril.Wasm.Wit.Binary.Func)
  | taskCancel
  | backpressureInc
  | backpressureDec
  | contextGet (slot : Nat)
  | contextSet (slot : Nat)
  | threadYield
  | subtaskDrop
  | subtaskCancel
  | waitableSetNew
  | waitableSetWait
  | waitableSetPoll
  | waitableSetDrop
  | waitableJoin
  /-- An operation on stream or future `c` of function `f` (`async`: `[async-lower]`). -/
  | chan (op : ChanOp) (async : Bool) (c : Chan) (f : Silmaril.Wasm.Wit.Binary.Func)
  deriving Repr, Inhabited

/-- The general built-ins, by their names in module `$root`. -/
def generalReq : String → Option Req
  | "[backpressure-inc]" => some .backpressureInc
  | "[backpressure-dec]" => some .backpressureDec
  | "[thread-yield]" => some .threadYield
  | "[subtask-drop]" => some .subtaskDrop
  | "[subtask-cancel]" => some .subtaskCancel
  | "[waitable-set-new]" => some .waitableSetNew
  | "[waitable-set-wait]" => some .waitableSetWait
  | "[waitable-set-poll]" => some .waitableSetPoll
  | "[waitable-set-drop]" => some .waitableSetDrop
  | "[waitable-join]" => some .waitableJoin
  | "[error-context-new-utf8]" => some (.errorContextNew .utf8)
  | "[error-context-new-utf16]" => some (.errorContextNew .utf16)
  | "[error-context-new-latin1+utf16]" => some (.errorContextNew .latin1utf16)
  | "[error-context-debug-message-utf8]" => some (.errorContextDebugMessage .utf8)
  | "[error-context-debug-message-utf16]" => some (.errorContextDebugMessage .utf16)
  | "[error-context-debug-message-latin1+utf16]" => some (.errorContextDebugMessage .latin1utf16)
  | "[error-context-drop]" => some .errorContextDrop
  | s => match strip? "[context-get-" s >>= indexBracket with
    | some (n, "") => some (.contextGet n)
    | _ => match strip? "[context-set-" s >>= indexBracket with
      | some (n, "") => some (.contextSet n)
      | _ => none

/-- A stream or future operation `[stream-<op>-N]f`, `f` looked up in `fs`. -/
def chanReq (async : Bool) (fs : List Silmaril.Wasm.Wit.Binary.Func) (s : String) : Except String (Option Req) := do
  let kinds : List (String × Bool) := [("[stream-", true), ("[future-", false)]
  for (pre, isStream) in kinds do
    if let some r := strip? pre s then
      for (opName, op) in chanOps do
        if let some r' := strip? opName r then
          -- `[stream-<op>-unit]f`: a stream or future with no element type (`stream`,
          -- `future`); `f` names no function of the world (wit-component ignores it)
          if let some fname := strip? "unit]" r' then
            let f : Silmaril.Wasm.Wit.Binary.Func := { name := fname, params := [] }
            return some (.chan op async (if isStream then .stream none else .future none) f)
          let some (n, fname) := indexBracket r' | throw s!"core import {s}: malformed index"
          let some f := fs.find? (·.name == fname) | throw s!"core import {s}: no function {fname}"
          let some c := (funcChans f)[n]? | throw s!"core import {s}: {fname} has no stream or future {n}"
          match c, isStream with
          | .stream _, true | .future _, false => return some (.chan op async c f)
          | _, _ => throw s!"core import {s}: element {n} of {fname} is of the other kind"
  pure none

/-- Classify a core import `(module, name)`. -/
def classify (imps exps : List Silmaril.Wasm.Wit.Binary.Func) (modName name : String) : Except String Req := do
  let (async, base) := match strip? "[async-lower]" name with
    | some b => (true, b)
    | none => (false, name)
  match modName with
  | "$root" =>
    if !async then
      if let some r := generalReq name then return r
      match imps.findIdx? (·.name == name) with
      | some i => return .lower i imps[i]!
      | none => pure ()
    else
      match imps.findIdx? (·.name == base) with
      | some i => return .lowerAsync i imps[i]!
      | none => pure ()
    match ← chanReq async imps base with
    | some r => pure r
    | none => throw s!"core import $root {name}: neither a world import nor a built-in"
  | "[export]$root" =>
    if name == "[task-cancel]" then return .taskCancel
    if let some fname := strip? "[task-return]" name then
      match exps.find? (·.name == fname) with
      | some f => return .taskReturn f
      | none => throw s!"core import [export]$root {name}: no exported function {fname}"
    match ← chanReq async exps base with
    | some r => pure r
    | none => throw s!"core import [export]$root {name}: not a built-in"
  | m => throw s!"core import {m} {name}: interface imports are not supported yet"


/-- The canonical core type of a request. -/
def Req.coreTy : Req → Except String CoreFuncTy
  | .lower _ f => lowerCore f
  | .lowerAsync _ f => lowerAsyncCore f
  | .errorContextNew _ => pure ⟨[ti32, ti32], [ti32]⟩
  | .errorContextDebugMessage _ => pure ⟨[ti32, ti32], []⟩
  | .errorContextDrop => pure ⟨[ti32], []⟩
  | .taskReturn f => taskReturnCore f
  | .taskCancel | .backpressureInc | .backpressureDec => pure ⟨[], []⟩
  | .contextGet _ => pure ⟨[], [ti32]⟩
  | .contextSet _ => pure ⟨[ti32], []⟩
  | .threadYield => pure ⟨[], [ti32]⟩
  | .subtaskDrop | .waitableSetDrop => pure ⟨[ti32], []⟩
  | .subtaskCancel => pure ⟨[ti32], [ti32]⟩
  | .waitableSetNew => pure ⟨[], [ti32]⟩
  | .waitableSetWait | .waitableSetPoll => pure ⟨[ti32, ti32], [ti32]⟩
  | .waitableJoin => pure ⟨[ti32, ti32], []⟩
  | .chan op _ c _ => pure <| match op, c with
    | .new, _ => ⟨[], [ti64]⟩
    | .read, .stream _ | .write, .stream _ => ⟨[ti32, ti32, ti32], [ti32]⟩
    | .read, .future _ | .write, .future _ => ⟨[ti32, ti32], [ti32]⟩
    | .cancelRead, _ | .cancelWrite, _ => ⟨[ti32], [ti32]⟩
    | .dropReadable, _ | .dropWritable, _ => ⟨[ti32], []⟩


/-- Whether the request's core function needs the module's memory (the indirect pattern). -/
def Req.usesMem : Req → Except String Bool
  | .lower _ f => usesMemory f
  | .lowerAsync _ f => lowerAsyncUsesMemory f
  | .errorContextNew _ | .errorContextDebugMessage _ => pure true
  | .taskReturn f => taskReturnUsesMemory f
  | .waitableSetWait | .waitableSetPoll => pure true
  | .chan .read _ _ _ | .chan .write _ _ _ => pure true
  | _ => pure false

/-! ## Plans -/

/-- How a world export is implemented. -/
inductive Lift where
  | sync (core : String) (postReturn : Option String)
  | stackful (core : String)
  | callback (core callback : String)
  deriving Repr, DecidableEq, Inhabited

/-- A plan: the module, the world's functions, the requests of its core imports (in order),
the implementation of each export, and the memory and allocator exports when needed. -/
structure Plan where
  core : ByteArray
  mod : CoreMod
  imports : List Silmaril.Wasm.Wit.Binary.Func
  exports : List Silmaril.Wasm.Wit.Binary.Func
  reqs : List ((String × String) × Req)
  lifts : List Lift
  memory : Option String
  realloc : Option String

/-- The freestanding functions of world items. -/
def worldFuncs (what : String) (items : List WorldItem) : Except String (List Silmaril.Wasm.Wit.Binary.Func) :=
  items.filterMapM fun
    | .func f =>
      if f.kind = .freestanding then pure (some f)
      else throw s!"{what} {f.name}: resource functions are not supported yet"
    | .type _ => pure none
    | .ifaceRef i _ _ => throw s!"{what} {i.id}: interface items are not supported yet"
    | .ifaceInline n _ => throw s!"{what} {n}: interface items are not supported yet"

/-- The type of a core export, if the module exports a function of that name. -/
def coreExport? (m : CoreMod) (n : String) : Option CoreFuncTy :=
  (m.exports.find? (·.1 == n)).map (·.2)

/-- Check that the module exports `n` at type `t`. -/
def expectExport (m : CoreMod) (n : String) (t : CoreFuncTy) : Except String Unit :=
  match coreExport? m n with
  | some t' => if t' = t then pure () else
      .error s!"core export {n}: type {repr t'}, the canonical ABI expects {repr t}"
  | none => .error s!"the module does not export the core function {n}"

/-- Fail with `msg` unless `b`. -/
def require (b : Bool) (msg : String) : Except String Unit := if b then pure () else throw msg

/-- The post-return function of sync export `f` lifted at core type `t`, if any. -/
def postReturn (m : CoreMod) (f : Silmaril.Wasm.Wit.Binary.Func) (t : CoreFuncTy) : Except String Lift :=
  match coreExport? m ("cabi_post_" ++ f.name) with
  | some t' =>
    if t' = ⟨t.results, []⟩ then pure (.sync f.name (some ("cabi_post_" ++ f.name)))
    else throw s!"core export cabi_post_{f.name}: not a post-return function of {f.name}"
  | none => pure (.sync f.name none)

/-- A sync export: the core export `f` at `liftCore f`. -/
def liftSync (m : CoreMod) (f : Silmaril.Wasm.Wit.Binary.Func) : Except String Lift := do
  let t ← liftCore f
  expectExport m f.name t
  postReturn m f t

/-- An async export with a callback. -/
def liftCallback (m : CoreMod) (f : Silmaril.Wasm.Wit.Binary.Func) : Except String Lift := do
  let t ← liftAsyncCore f true
  expectExport m ("[async-lift]" ++ f.name) t
  expectExport m ("[callback][async-lift]" ++ f.name) callbackCore
  pure (.callback ("[async-lift]" ++ f.name) ("[callback][async-lift]" ++ f.name))

/-- A stackful async export. -/
def liftStackful (m : CoreMod) (f : Silmaril.Wasm.Wit.Binary.Func) : Except String Lift := do
  let t ← liftAsyncCore f false
  expectExport m ("[async-lift-stackful]" ++ f.name) t
  pure (.stackful ("[async-lift-stackful]" ++ f.name))

/-- How export `f` is implemented by the module. -/
def liftOf (m : CoreMod) (f : Silmaril.Wasm.Wit.Binary.Func) : Except String Lift :=
  if f.async then
    if (coreExport? m ("[async-lift]" ++ f.name)).isSome then liftCallback m f
    else liftStackful m f
  else liftSync m f

/-- The core module's memory export, if it has one called `memory`. -/
def hasMemory (core : ByteArray) : Bool :=
  match Silmaril.Wasm.Perf.CoreDecode.decodeF core with
  | some m => m.exports.any fun e => e.name == "memory" && (match e.index with
      | .memory _ => true
      | _ => false)
  | none => false

/-- Whether any export or request needs the memory or the allocator. -/
def needs (exps : List Silmaril.Wasm.Wit.Binary.Func) (reqs : List Req) : Except String (Bool × Bool) := do
  let mut mem := false
  let mut ra := false
  for f in exps do
    if ← usesMemory f then mem := true
    if ← needsRealloc f then ra := true
  for r in reqs do
    if ← r.usesMem then mem := true
    match r with
    | .lower _ f | .lowerAsync _ f => if usesMemOpt f.result then ra := true
    | .errorContextDebugMessage _ => ra := true
    | .chan .read _ (.stream (some t)) _ | .chan .read _ (.future (some t)) _ =>
      if usesMem t then ra := true
    | _ => pure ()
  pure (mem, ra)

/-- A core import of the module: its request, at the canonical core type. -/
def reqOf (imps exps : List Silmaril.Wasm.Wit.Binary.Func) (x : (String × String) × (String × CoreFuncTy)) :
    Except String ((String × String) × Req) := do
  let r ← classify imps exps x.1.1 x.1.2
  let t' ← r.coreTy
  require (decide (x.2.2 = t'))
    s!"core import {x.1.1} {x.1.2}: type {repr x.2.2}, the canonical ABI expects {repr t'}"
  pure (x.1, r)

/-- The allocator, when needed, at its canonical type. -/
def reallocOk (m : CoreMod) (ra : Bool) : Except String Unit :=
  if ra then expectExport m "cabi_realloc" ⟨[ti32, ti32, ti32, ti32], [ti32]⟩ else pure ()

/-- **The plan** of a core module against a world. -/
def plan (core : ByteArray) (w : World) : Except String Plan := do
  let m ← Silmaril.Wasm.Perf.CoreMod.coreModF core
  let imps ← worldFuncs "world import" w.imports
  let exps ← worldFuncs "world export" w.exports
  let reqs ← (m.importNames.zip m.imports).mapM (reqOf imps exps)
  let lifts ← exps.mapM (liftOf m)
  let (mem, ra) ← needs exps (reqs.map (·.2))
  require (!mem || hasMemory core) "the world needs linear memory: export it as `memory`"
  reallocOk m ra
  pure ⟨core, m, imps, exps, reqs, lifts, if mem then some "memory" else none,
    if ra then some "cabi_realloc" else none⟩

/-! ## Emission -/

/-- The emission state: sections and the sizes of the index spaces. -/
structure ES where
  secs : Array XSection := #[]
  coreFuncs : Nat := 0
  coreInsts : Nat := 0
  funcs : Nat := 0

abbrev EM := StateT ES (Except String)

def addSec (s : XSection) : EM Unit := modify fun e => { e with secs := e.secs.push s }

/-- Define a core function by a section that defines one; its index. -/
def coreFunc (s : XSection) : EM Nat := do
  let e ← get
  set { e with secs := e.secs.push s, coreFuncs := e.coreFuncs + 1 }
  pure e.coreFuncs

def coreInst (x : CoreInstanceExpr) : EM Nat := do
  let e ← get
  set { e with secs := e.secs.push (.sec (.coreInstances [x])), coreInsts := e.coreInsts + 1 }
  pure e.coreInsts

def aliasCoreFunc (inst : Nat) (n : String) : EM Nat :=
  coreFunc (.sec (.aliases [⟨.core .func, .coreExport inst n⟩]))

/-- The type index of stream or future `c` (already interned). -/
def chanTy (ts : TS) (c : Chan) : Except String Nat := do
  let t := match c with
    | .stream t => Silmaril.Wasm.Wit.Binary.Ty.stream t
    | .future t => Silmaril.Wasm.Wit.Binary.Ty.future t
  match (valType t).run ts with
  | .ok (.idx i, _) => pure i
  | .ok _ => throw "internal: a stream type is not a defined type"
  | .error e => throw e

/-- The core function of a request, defined with the memory `mem` and allocator `ra`. -/
def reqFunc (ts : TS) (mem ra : Option Nat) : Req → Except String XSection
  | .lower i f => do
    let mo := (mem.map CanonOpt.memory).toList
    let ro := if usesMemOpt f.result then (ra.map CanonOpt.realloc).toList else []
    pure (.sec (.canons [.lower i (mo ++ ro)]))
  | .lowerAsync i f => do
    let mo := (mem.map CanonOpt.memory).toList
    let ro := if usesMemOpt f.result then (ra.map CanonOpt.realloc).toList else []
    pure (.sec (.canons [.lower i (mo ++ ro ++ [.async])]))
  | .errorContextNew e => pure (.builtins [.errorContextNew ((mem.map CanonOpt.memory).toList ++ [e])])
  | .errorContextDebugMessage e => pure (.builtins [.errorContextDebugMessage
      ((mem.map CanonOpt.memory).toList ++ (ra.map CanonOpt.realloc).toList ++ [e])])
  | .errorContextDrop => pure (.builtins [.errorContextDrop])
  | .taskReturn f => do
    let r ← match (optType f.result).run ts with
      | .ok (r, _) => pure r
      | .error e => throw e
    pure (.builtins [.taskReturn r (mem.map CanonOpt.memory).toList])
  | .taskCancel => pure (.builtins [.taskCancel])
  | .backpressureInc => pure (.builtins [.backpressureInc])
  | .backpressureDec => pure (.builtins [.backpressureDec])
  | .contextGet n => pure (.builtins [.contextGet n])
  | .contextSet n => pure (.builtins [.contextSet n])
  | .threadYield => pure (.builtins [.threadYield false])
  | .subtaskDrop => pure (.builtins [.subtaskDrop])
  | .subtaskCancel => pure (.builtins [.subtaskCancel false])
  | .waitableSetNew => pure (.builtins [.waitableSetNew])
  | .waitableSetWait => pure (.builtins [.waitableSetWait false (mem.getD 0)])
  | .waitableSetPoll => pure (.builtins [.waitableSetPoll false (mem.getD 0)])
  | .waitableSetDrop => pure (.builtins [.waitableSetDrop])
  | .waitableJoin => pure (.builtins [.waitableJoin])
  | .chan op async c _ => do
    let t ← chanTy ts c
    let payloadMem := match c with
      | .stream (some p) | .future (some p) => usesMem p
      | _ => false
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

/-- Module names of the core imports, in order of first occurrence. -/
def moduleNames (ns : List (String × String)) : List String :=
  ns.foldl (fun acc (m, _) => if acc.contains m then acc else acc ++ [m]) []

/-- The `shim` module of the indirect pattern: a table of `n` slots and one trampoline per
slot (at the slot's core type). -/
def shimMod (tys : List CoreFuncTy) : CMod :=
  let n := tys.length
  { types := tys
    funcs := (List.range n).zip tys |>.map fun (i, t) =>
      (i, (CMod.trampoline t.params.length i i).getD [])
    table := some (n, n)
    exports := ((List.range n).map fun i => (toString i, (0x00 : UInt8), i)) ++
      [("$imports", 0x01, 0)] }

/-- The `fixup` module: imports the real functions and the shim's table and fills it. -/
def fixupMod (tys : List CoreFuncTy) : CMod :=
  let n := tys.length
  { types := tys
    imports := ((List.range n).map fun i => ("actual", toString i, CImport.func i)) ++
      [("shim", "$imports", .table n n)]
    elems := [(0, List.range n)] }

/-- The options of `canon lift` of export `f`. -/
def liftOpts (mem ra : Option Nat) (f : Silmaril.Wasm.Wit.Binary.Func) (postRet callback : Option Nat) :
    Except String (List CanonOpt) := do
  let um ← usesMemory f
  let nr ← needsRealloc f
  let mo := if um then (mem.map CanonOpt.memory).toList else []
  let ro := if nr then (ra.map CanonOpt.realloc).toList else []
  let po := (postRet.map CanonOpt.postReturn).toList
  let ao := if f.async then CanonOpt.async :: (callback.map CanonOpt.callback).toList else []
  pure (mo ++ ro ++ po ++ ao)

def mustEncode (what : String) : Option ByteArray → Except String ByteArray
  | some b => pure b
  | none => throw s!"internal: {what} does not encode (an index of 2^32 or more)"

/-- **The component** of a plan. -/
def emit (p : Plan) : Except String XAst := do
  -- types: world imports, world exports, and the streams and futures of every function
  let ((impTys, expTys), ts) ← (do
    let a ← p.imports.mapM funcType
    let b ← p.exports.mapM funcType
    for f in p.imports ++ p.exports do
      for c in funcChans f do
        let _ ← valType (match c with | .stream t => .stream t | .future t => .future t)
    pure (a, b) : TyM (List Nat × List Nat)).run {}
  let viaShim ← p.reqs.mapM fun (_, r) => r.usesMem
  let slots : List (Nat × Req) := ((List.range p.reqs.length).zip (p.reqs.map (·.2))).filter
    fun (k, _) => viaShim[k]!
  let slotTys ← slots.mapM fun (_, r) => r.coreTy
  let shim := !slots.isEmpty
  let go : EM Unit := do
    addSec (.sec (.coreModule p.core))
    if shim then
      addSec (.sec (.coreModule (← mustEncode "shim" (shimMod slotTys).encode)))
      let _ ← coreInst (.instantiate 1 [])
    addSec (.sec (.types ts.types.toList))
    if !p.imports.isEmpty then
      addSec (.sec (.imports ((p.imports.zip impTys).map fun (f, t) => ⟨f.name, .func t⟩)))
      modify fun e => { e with funcs := e.funcs + p.imports.length }
    -- one core function per core import
    let mut fs : Array Nat := #[]
    let mut slot := 0
    for k in List.range p.reqs.length do
      let r := (p.reqs[k]!).2
      if viaShim[k]! then
        fs := fs.push (← aliasCoreFunc 0 (toString slot))
        slot := slot + 1
      else
        fs := fs.push (← coreFunc (← (reqFunc ts none none r : Except String XSection)))
    -- inline instances per module name, then the main instance
    let names := moduleNames (p.reqs.map (·.1))
    let mut args : List (String × Nat) := []
    for mn in names do
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
      for (_, r) in slots do
        let f ← coreFunc (← (reqFunc ts mem ra r : Except String XSection))
        real := real ++ [(toString i, ⟨.func, f⟩)]
        i := i + 1
      let actual ← coreInst (.exports real)
      addSec (.sec (.coreModule (← mustEncode "fixup" (fixupMod slotTys).encode)))
      let _ ← coreInst (.instantiate 2 [("actual", actual), ("shim", 0)])
    -- exports
    for (f, t, l) in p.exports.zip (expTys.zip p.lifts) do
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
      let opts ← (liftOpts mem ra f pr cb : Except String (List CanonOpt))
      addSec (.sec (.canons [.lift cf opts t]))
      let e ← get
      set { e with funcs := e.funcs + 1 }
      addSec (.sec (.exports [⟨f.name, ⟨.func, e.funcs⟩, none⟩]))
      modify fun e => { e with funcs := e.funcs + 1 }
  let ((), e) ← go.run {}
  pure ⟨e.secs.toList⟩

/-- `wasm-jco new`: the bytes of the component of a core module and a world. -/
def new (core : ByteArray) (w : World) : Except String ByteArray := do
  let p ← plan core w
  let c ← emit p
  mustEncode "the component" c.encode

end Silmaril.Wasm.JcoTool.New
