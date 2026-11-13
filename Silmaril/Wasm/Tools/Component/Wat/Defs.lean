module

public import Silmaril.Wasm.Component.Codec.Defs
public import Silmaril.Wasm.Component.BinaryP3.Encode.Defs
public import Silmaril.Wasm.Wac.WatX.Defs

/-!
# Component WAT for the whole `canon` production (`wasm-tools print`/`parse` on components)

`Silmaril.Wasm.Component.Wat` prints and reads component WAT for the component binary AST of
component-model `8505ba7` (`Binary`), whose `canon` has only `lift`, `lower` and
`resource.*`. This module extends it to `BinaryP3` (component-model `Binary.md` at `d095e2f`:
every async, stream, future, error-context, waitable-set, backpressure, context and thread
built-in), reusing `Wat.P`/`Wat.R` for every other production:

* `P.canon` spells each built-in as `wasmprinter` 1.262.0 does (`crates/wasmprinter/src/component.rs`,
  `print_canonical_functions`): `(core func (canon task.return (result T) OPTS))`,
  `(core func (canon context.get i32 0))`, `(core func (canon stream.read T OPTS))`,
  `(core func (canon stream.cancel-read T async))`, `(core func (canon waitable-set.wait
  (memory M)))`, `(core func (canon thread.new-indirect FT TBL))`, `thread.available_parallelism`
  (wasmprinter's spelling), …; the 🧵② `shared` flag (which wasmprinter 1.262.0 does not
  print) is the keyword `shared` after the built-in's name;
* `R.coreCanon` reads them back; `R.item`/`R.items` read items as one-element sections, with
  `Wat.R.itemKw` for every item that is not a `canon` built-in or a nested component;
* `norm`: the normal form of the text round trip (`Wat.norm` with the new `canon`).

`Thms` proves `read (print c) = some (norm c)` (`read_print`), the printer's independence of
the normal form, and the byte-level round trip `parseText (printAst c) = encode (norm c)`.

Entry points of the tool (`printBytes`, `parseText`): `Codec.decodeLax` and the printer; the
reader (with `Wac.WatX`'s expansion of identifiers, inline abbreviations and text core
modules where the printer's spelling is not used) and `BinaryP3.encode`.

The printer's spelling is `Wat.print`'s, not wasmprinter's layout: core modules are kept as
`(core module binary "…")` (upstream's text parser does not read this form), there are no
`(;i;)` index comments and no `$name`s from the `name` sections. See
`tools/wasm-tools/README.md` for what differs from `wasm-tools print`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Wat

open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Wat (Sexp kw num num? nm nm? bytesS bytes? mapO)
open Silmaril.Wasm.Component.Binary (CanonOpt CoreValType)
open Silmaril.Wasm.Component.BinaryP3 (Canon Section Ast)

/-! ## Built-in names -/

/-- The canonical built-ins by name (the keyword after `canon` in `(core func (canon …))`;
`threadAvailableParallelismAlt` is the spelling `thread.available-parallelism`, read but not
printed). -/
inductive BK where
  | lower
  | resourceNew
  | resourceDrop
  | resourceRep
  | backpressureInc
  | backpressureDec
  | taskReturn
  | taskCancel
  | contextGet
  | contextSet
  | subtaskCancel
  | subtaskDrop
  | streamNew
  | streamRead
  | streamWrite
  | streamCancelRead
  | streamCancelWrite
  | streamDropReadable
  | streamDropWritable
  | streamForward
  | futureNew
  | futureRead
  | futureWrite
  | futureCancelRead
  | futureCancelWrite
  | futureDropReadable
  | futureDropWritable
  | futureForward
  | errorContextNew
  | errorContextDebugMessage
  | errorContextDrop
  | waitableSetNew
  | waitableSetWait
  | waitableSetPoll
  | waitableSetDrop
  | waitableJoin
  | threadIndex
  | threadNewIndirect
  | threadResumeLater
  | threadSuspend
  | threadYield
  | threadSuspendThenResume
  | threadYieldThenResume
  | threadSuspendThenPromote
  | threadYieldThenPromote
  | threadSpawnRef
  | threadSpawnIndirect
  | threadAvailableParallelism
  | threadAvailableParallelismAlt
  deriving Repr, DecidableEq

/-- The keyword of a built-in. -/
def BK.name : BK → String
  | .lower => "lower"
  | .resourceNew => "resource.new"
  | .resourceDrop => "resource.drop"
  | .resourceRep => "resource.rep"
  | .backpressureInc => "backpressure.inc"
  | .backpressureDec => "backpressure.dec"
  | .taskReturn => "task.return"
  | .taskCancel => "task.cancel"
  | .contextGet => "context.get"
  | .contextSet => "context.set"
  | .subtaskCancel => "subtask.cancel"
  | .subtaskDrop => "subtask.drop"
  | .streamNew => "stream.new"
  | .streamRead => "stream.read"
  | .streamWrite => "stream.write"
  | .streamCancelRead => "stream.cancel-read"
  | .streamCancelWrite => "stream.cancel-write"
  | .streamDropReadable => "stream.drop-readable"
  | .streamDropWritable => "stream.drop-writable"
  | .streamForward => "stream.forward"
  | .futureNew => "future.new"
  | .futureRead => "future.read"
  | .futureWrite => "future.write"
  | .futureCancelRead => "future.cancel-read"
  | .futureCancelWrite => "future.cancel-write"
  | .futureDropReadable => "future.drop-readable"
  | .futureDropWritable => "future.drop-writable"
  | .futureForward => "future.forward"
  | .errorContextNew => "error-context.new"
  | .errorContextDebugMessage => "error-context.debug-message"
  | .errorContextDrop => "error-context.drop"
  | .waitableSetNew => "waitable-set.new"
  | .waitableSetWait => "waitable-set.wait"
  | .waitableSetPoll => "waitable-set.poll"
  | .waitableSetDrop => "waitable-set.drop"
  | .waitableJoin => "waitable.join"
  | .threadIndex => "thread.index"
  | .threadNewIndirect => "thread.new-indirect"
  | .threadResumeLater => "thread.resume-later"
  | .threadSuspend => "thread.suspend"
  | .threadYield => "thread.yield"
  | .threadSuspendThenResume => "thread.suspend-then-resume"
  | .threadYieldThenResume => "thread.yield-then-resume"
  | .threadSuspendThenPromote => "thread.suspend-then-promote"
  | .threadYieldThenPromote => "thread.yield-then-promote"
  | .threadSpawnRef => "thread.spawn-ref"
  | .threadSpawnIndirect => "thread.spawn-indirect"
  | .threadAvailableParallelism => "thread.available_parallelism"
  | .threadAvailableParallelismAlt => "thread.available-parallelism"

/-- Every built-in. -/
def BK.all : List BK :=
  [.lower, .resourceNew, .resourceDrop, .resourceRep, .backpressureInc, .backpressureDec, .taskReturn, .taskCancel, .contextGet, .contextSet, .subtaskCancel, .subtaskDrop, .streamNew, .streamRead, .streamWrite, .streamCancelRead, .streamCancelWrite, .streamDropReadable, .streamDropWritable, .streamForward, .futureNew, .futureRead, .futureWrite, .futureCancelRead, .futureCancelWrite, .futureDropReadable, .futureDropWritable, .futureForward, .errorContextNew, .errorContextDebugMessage, .errorContextDrop, .waitableSetNew, .waitableSetWait, .waitableSetPoll, .waitableSetDrop, .waitableJoin, .threadIndex, .threadNewIndirect, .threadResumeLater, .threadSuspend, .threadYield, .threadSuspendThenResume, .threadYieldThenResume, .threadSuspendThenPromote, .threadYieldThenPromote, .threadSpawnRef, .threadSpawnIndirect,
   .threadAvailableParallelism, .threadAvailableParallelismAlt]

/-- The built-in a keyword names. -/
def bkOf? (s : String) : Option BK := BK.all.find? (·.name == s)

/-! ## Printer -/

namespace P

/-- `(core func (canon NAME ARGS…))`. -/
def builtin (b : BK) (args : List Sexp) : Sexp :=
  .list [kw "core", kw "func", .list (kw "canon" :: kw b.name :: args)]

/-- `async` when set. -/
def asyncL (b : Bool) : List Sexp := if b then [kw "async"] else []

/-- `shared` when set (🧵②). -/
def sharedL (b : Bool) : List Sexp := if b then [kw "shared"] else []

def opts (os : List CanonOpt) : List Sexp := os.map _root_.Silmaril.Wasm.Component.Wat.P.canonOpt

/-- A canonical built-in. -/
def canon : Canon → Sexp
  | .lift f os t => _root_.Silmaril.Wasm.Component.Wat.P.canon (.lift f os t)
  | .lower f os => _root_.Silmaril.Wasm.Component.Wat.P.canon (.lower f os)
  | .resourceNew t => builtin .resourceNew [num t]
  | .resourceDrop t => builtin .resourceDrop [num t]
  | .resourceRep t => builtin .resourceRep [num t]
  | .backpressureInc => builtin .backpressureInc []
  | .backpressureDec => builtin .backpressureDec []
  | .taskReturn r os =>
    builtin .taskReturn ((r.map fun t => .list [kw "result", _root_.Silmaril.Wasm.Component.Wat.P.valType t]).toList ++ opts os)
  | .taskCancel => builtin .taskCancel []
  | .contextGet t i => builtin .contextGet [_root_.Silmaril.Wasm.Component.Wat.P.coreValType t, num i]
  | .contextSet t i => builtin .contextSet [_root_.Silmaril.Wasm.Component.Wat.P.coreValType t, num i]
  | .subtaskCancel a => builtin .subtaskCancel (asyncL a)
  | .subtaskDrop => builtin .subtaskDrop []
  | .streamNew t => builtin .streamNew [num t]
  | .streamRead t os => builtin .streamRead (num t :: opts os)
  | .streamWrite t os => builtin .streamWrite (num t :: opts os)
  | .streamCancelRead t a => builtin .streamCancelRead (num t :: asyncL a)
  | .streamCancelWrite t a => builtin .streamCancelWrite (num t :: asyncL a)
  | .streamDropReadable t => builtin .streamDropReadable [num t]
  | .streamDropWritable t => builtin .streamDropWritable [num t]
  | .streamForward t => builtin .streamForward [num t]
  | .futureNew t => builtin .futureNew [num t]
  | .futureRead t os => builtin .futureRead (num t :: opts os)
  | .futureWrite t os => builtin .futureWrite (num t :: opts os)
  | .futureCancelRead t a => builtin .futureCancelRead (num t :: asyncL a)
  | .futureCancelWrite t a => builtin .futureCancelWrite (num t :: asyncL a)
  | .futureDropReadable t => builtin .futureDropReadable [num t]
  | .futureDropWritable t => builtin .futureDropWritable [num t]
  | .futureForward t => builtin .futureForward [num t]
  | .errorContextNew os => builtin .errorContextNew (opts os)
  | .errorContextDebugMessage os => builtin .errorContextDebugMessage (opts os)
  | .errorContextDrop => builtin .errorContextDrop []
  | .waitableSetNew => builtin .waitableSetNew []
  | .waitableSetWait m => builtin .waitableSetWait [.list [kw "memory", num m]]
  | .waitableSetPoll m => builtin .waitableSetPoll [.list [kw "memory", num m]]
  | .waitableSetDrop => builtin .waitableSetDrop []
  | .waitableJoin => builtin .waitableJoin []
  | .threadIndex => builtin .threadIndex []
  | .threadNewIndirect ft tbl => builtin .threadNewIndirect [num ft, num tbl]
  | .threadResumeLater => builtin .threadResumeLater []
  | .threadSuspend => builtin .threadSuspend []
  | .threadYield => builtin .threadYield []
  | .threadSuspendThenResume => builtin .threadSuspendThenResume []
  | .threadYieldThenResume => builtin .threadYieldThenResume []
  | .threadSuspendThenPromote => builtin .threadSuspendThenPromote []
  | .threadYieldThenPromote => builtin .threadYieldThenPromote []
  | .threadSpawnRef sh ft => builtin .threadSpawnRef (sharedL sh ++ [num ft])
  | .threadSpawnIndirect sh ft tbl =>
    builtin .threadSpawnIndirect (sharedL sh ++ [num ft, num tbl])
  | .threadAvailableParallelism sh => builtin .threadAvailableParallelism (sharedL sh)

mutual
/-- The items of a section. -/
def section_ : Section → List Sexp
  | .custom n d => _root_.Silmaril.Wasm.Component.Wat.P.section_ (.custom n d)
  | .coreModule b => _root_.Silmaril.Wasm.Component.Wat.P.section_ (.coreModule b)
  | .coreInstances xs => _root_.Silmaril.Wasm.Component.Wat.P.section_ (.coreInstances xs)
  | .coreTypes xs => _root_.Silmaril.Wasm.Component.Wat.P.section_ (.coreTypes xs)
  | .component c => [.list (kw "component" :: ast c)]
  | .instances xs => _root_.Silmaril.Wasm.Component.Wat.P.section_ (.instances xs)
  | .aliases xs => _root_.Silmaril.Wasm.Component.Wat.P.section_ (.aliases xs)
  | .types xs => _root_.Silmaril.Wasm.Component.Wat.P.section_ (.types xs)
  | .canons xs => xs.map canon
  | .start s => _root_.Silmaril.Wasm.Component.Wat.P.section_ (.start s)
  | .imports xs => _root_.Silmaril.Wasm.Component.Wat.P.section_ (.imports xs)
  | .exports xs => _root_.Silmaril.Wasm.Component.Wat.P.section_ (.exports xs)
  | .values xs => _root_.Silmaril.Wasm.Component.Wat.P.section_ (.values xs)

def sections : List Section → List Sexp
  | [] => []
  | s :: ss => section_ s ++ sections ss

/-- The items of a component. -/
def ast : Ast → List Sexp
  | .mk ss => sections ss
end

end P

/-! ## Reader -/

namespace R

/-- `async`? -/
def asyncFlag : List Sexp → Option Bool
  | [] => some false
  | [.atom "async"] => some true
  | _ => none

/-- A type index followed by `async`?. -/
def tAsync (ss : List Sexp) (k : Nat → Bool → Canon) : Option Canon :=
  match ss with
  | t :: r => do
    let i ← num? t
    let a ← asyncFlag r
    pure (k i a)
  | [] => none

/-- A type index followed by canonical options. -/
def tOpts (ss : List Sexp) (k : Nat → List CanonOpt → Canon) : Option Canon :=
  match ss with
  | t :: r => do
    let i ← num? t
    let os ← mapO _root_.Silmaril.Wasm.Component.Wat.R.canonOpt r
    pure (k i os)
  | [] => none

/-- A single type index. -/
def tOnly (ss : List Sexp) (k : Nat → Canon) : Option Canon :=
  match ss with
  | [t] => (num? t).map k
  | _ => none

/-- No operands. -/
def none0 (ss : List Sexp) (c : Canon) : Option Canon :=
  match ss with
  | [] => some c
  | _ => none

/-- `shared`? then the rest. -/
def sharedPre : List Sexp → Bool × List Sexp
  | .atom "shared" :: r => (true, r)
  | r => (false, r)

/-- `(result T)`? then options (`task.return`). -/
def taskReturn : List Sexp → Option Canon
  | .list [.atom "result", t] :: r => do
    let v ← _root_.Silmaril.Wasm.Component.Wat.R.valType t
    let os ← mapO _root_.Silmaril.Wasm.Component.Wat.R.canonOpt r
    pure (.taskReturn (some v) os)
  | r => (mapO _root_.Silmaril.Wasm.Component.Wat.R.canonOpt r).map (.taskReturn none ·)

/-- `context.get`/`context.set` operands. -/
def context (ss : List Sexp) (k : CoreValType → Nat → Canon) : Option Canon :=
  match ss with
  | [t, i] => do
    let v ← _root_.Silmaril.Wasm.Component.Wat.R.coreValType t
    let n ← num? i
    pure (k v n)
  | _ => none

/-- `(memory M)`. -/
def memory (ss : List Sexp) (k : Nat → Canon) : Option Canon :=
  match ss with
  | [.list [.atom "memory", m]] => (num? m).map k
  | _ => none

/-- Two indices. -/
def two (ss : List Sexp) (k : Nat → Nat → Canon) : Option Canon :=
  match ss with
  | [a, b] => do
    let x ← num? a
    let y ← num? b
    pure (k x y)
  | _ => none

/-- The body of `(core func (canon NAME …))`, by the built-in. -/
def builtinK (b : BK) (ss : List Sexp) : Option Canon :=
  match b with
  | .lower => match ss with
      | .list [.atom "func", f] :: os => do
        let fi ← num? f
        let o ← mapO _root_.Silmaril.Wasm.Component.Wat.R.canonOpt os
        pure (.lower fi o)
      | _ => none
  | .resourceNew => tOnly ss .resourceNew
  | .resourceDrop => tOnly ss .resourceDrop
  | .resourceRep => tOnly ss .resourceRep
  | .backpressureInc => none0 ss .backpressureInc
  | .backpressureDec => none0 ss .backpressureDec
  | .taskReturn => taskReturn ss
  | .taskCancel => none0 ss .taskCancel
  | .contextGet => context ss .contextGet
  | .contextSet => context ss .contextSet
  | .subtaskCancel => (asyncFlag ss).map .subtaskCancel
  | .subtaskDrop => none0 ss .subtaskDrop
  | .streamNew => tOnly ss .streamNew
  | .streamRead => tOpts ss .streamRead
  | .streamWrite => tOpts ss .streamWrite
  | .streamCancelRead => tAsync ss .streamCancelRead
  | .streamCancelWrite => tAsync ss .streamCancelWrite
  | .streamDropReadable => tOnly ss .streamDropReadable
  | .streamDropWritable => tOnly ss .streamDropWritable
  | .streamForward => tOnly ss .streamForward
  | .futureNew => tOnly ss .futureNew
  | .futureRead => tOpts ss .futureRead
  | .futureWrite => tOpts ss .futureWrite
  | .futureCancelRead => tAsync ss .futureCancelRead
  | .futureCancelWrite => tAsync ss .futureCancelWrite
  | .futureDropReadable => tOnly ss .futureDropReadable
  | .futureDropWritable => tOnly ss .futureDropWritable
  | .futureForward => tOnly ss .futureForward
  | .errorContextNew => (mapO _root_.Silmaril.Wasm.Component.Wat.R.canonOpt ss).map .errorContextNew
  | .errorContextDebugMessage => (mapO _root_.Silmaril.Wasm.Component.Wat.R.canonOpt ss).map .errorContextDebugMessage
  | .errorContextDrop => none0 ss .errorContextDrop
  | .waitableSetNew => none0 ss .waitableSetNew
  | .waitableSetWait => memory ss .waitableSetWait
  | .waitableSetPoll => memory ss .waitableSetPoll
  | .waitableSetDrop => none0 ss .waitableSetDrop
  | .waitableJoin => none0 ss .waitableJoin
  | .threadIndex => none0 ss .threadIndex
  | .threadNewIndirect => two ss .threadNewIndirect
  | .threadResumeLater => none0 ss .threadResumeLater
  | .threadSuspend => none0 ss .threadSuspend
  | .threadYield => none0 ss .threadYield
  | .threadSuspendThenResume => none0 ss .threadSuspendThenResume
  | .threadYieldThenResume => none0 ss .threadYieldThenResume
  | .threadSuspendThenPromote => none0 ss .threadSuspendThenPromote
  | .threadYieldThenPromote => none0 ss .threadYieldThenPromote
  | .threadSpawnRef => tOnly (sharedPre ss).2 (.threadSpawnRef (sharedPre ss).1)
  | .threadSpawnIndirect => two (sharedPre ss).2 (.threadSpawnIndirect (sharedPre ss).1)
  | .threadAvailableParallelism | .threadAvailableParallelismAlt =>
    none0 (sharedPre ss).2 (.threadAvailableParallelism (sharedPre ss).1)

/-- The body of `(core func (canon NAME …))`, by the built-in's name. -/
def builtin (k : String) (ss : List Sexp) : Option Canon := (bkOf? k).bind (builtinK · ss)

/-- Items starting with `core`: built-ins here, the rest through `Wat.R.coreItem`. -/
def coreItem : List Sexp → Option Section
  | [.atom "func", .list (.atom "canon" :: .atom k :: ss)] => (builtin k ss).map fun c => .canons [c]
  | ss => (_root_.Silmaril.Wasm.Component.Wat.R.coreItem ss).map Section.ofV0

/-- Merge two adjacent sections of the same vector kind. -/
def merge : Section → Section → Option Section
  | .coreInstances a, .coreInstances b => some (.coreInstances (a ++ b))
  | .coreTypes a, .coreTypes b => some (.coreTypes (a ++ b))
  | .instances a, .instances b => some (.instances (a ++ b))
  | .aliases a, .aliases b => some (.aliases (a ++ b))
  | .types a, .types b => some (.types (a ++ b))
  | .canons a, .canons b => some (.canons (a ++ b))
  | .imports a, .imports b => some (.imports (a ++ b))
  | .exports a, .exports b => some (.exports (a ++ b))
  | .values a, .values b => some (.values (a ++ b))
  | _, _ => none

/-- Group consecutive sections of the same vector kind. -/
def group : List Section → List Section
  | [] => []
  | s :: ss => match group ss with
    | [] => [s]
    | t :: ts => match merge s t with
      | some u => u :: ts
      | none => s :: t :: ts

mutual
/-- One item, as a section of one element. -/
def item : Sexp → Option Section
  | .list (.atom "component" :: ss) => (items ss).map fun xs => .component (.mk (group xs))
  | .list (.atom "core" :: ss) => coreItem ss
  | .list (.atom k :: ss) => (_root_.Silmaril.Wasm.Component.Wat.R.itemKw k ss).map Section.ofV0
  | _ => none

/-- Items, each as a section of one element. -/
def items : List Sexp → Option (List Section)
  | [] => some []
  | s :: ss => do
    let x ← item s
    let xs ← items ss
    pure (x :: xs)
end

end R

/-! ## Normal form -/

mutual
/-- A section, split into sections of one element (with `Wat`'s normal names). -/
def normSection : Section → List Section
  | .component c => [.component (norm c)]
  | .canons xs => xs.map fun x => .canons [x]
  | .custom n d => (_root_.Silmaril.Wasm.Component.Wat.normSection (.custom n d)).map Section.ofV0
  | .coreModule b => (_root_.Silmaril.Wasm.Component.Wat.normSection (.coreModule b)).map Section.ofV0
  | .coreInstances xs => (_root_.Silmaril.Wasm.Component.Wat.normSection (.coreInstances xs)).map Section.ofV0
  | .coreTypes xs => (_root_.Silmaril.Wasm.Component.Wat.normSection (.coreTypes xs)).map Section.ofV0
  | .instances xs => (_root_.Silmaril.Wasm.Component.Wat.normSection (.instances xs)).map Section.ofV0
  | .aliases xs => (_root_.Silmaril.Wasm.Component.Wat.normSection (.aliases xs)).map Section.ofV0
  | .types xs => (_root_.Silmaril.Wasm.Component.Wat.normSection (.types xs)).map Section.ofV0
  | .start s => (_root_.Silmaril.Wasm.Component.Wat.normSection (.start s)).map Section.ofV0
  | .imports xs => (_root_.Silmaril.Wasm.Component.Wat.normSection (.imports xs)).map Section.ofV0
  | .exports xs => (_root_.Silmaril.Wasm.Component.Wat.normSection (.exports xs)).map Section.ofV0
  | .values xs => (_root_.Silmaril.Wasm.Component.Wat.normSection (.values xs)).map Section.ofV0

def normSections : List Section → List Section
  | [] => []
  | s :: ss => normSection s ++ normSections ss

/-- **The normal form** of the text round trip: `Wat.norm`'s (names without attributes as
`0x00`, consecutive items of one kind in one section), recursively. -/
def norm : Ast → Ast
  | .mk ss => .mk (R.group (normSections ss))
end

/-! ## Entry points -/

/-- The S-expression of a component. -/
def toSexp (c : Ast) : Sexp := .list (kw "component" :: P.ast c)

/-- The component of an S-expression. -/
def ofSexp : Sexp → Option Ast
  | .list (.atom "component" :: ss) => (R.items ss).map fun xs => .mk (R.group xs)
  | _ => none

/-- **Print a component as WAT.** -/
def print (c : Ast) : String := Sexp.printAll [toSexp c]

/-- **Read a component from WAT** in the printer's spelling. -/
def read (s : String) : Option Ast :=
  match Sexp.read s with
  | some [x] => ofSexp x
  | _ => none

/-- Read component WAT as people write it: the printer's spelling, else `Wac.WatX`'s
expansion of inline abbreviations and text core modules (`desugar`), identifiers (`resolve`),
then `ofSexp`. -/
def readX (s : String) : Option Ast :=
  match read s with
  | some c => some c
  | none =>
    match Sexp.read s with
    | some [x] => Wac.WatX.desugar (Wac.WatX.clean x) >>= _root_.Silmaril.Wasm.Component.Wat.resolve >>= ofSexp
    | _ => none

/-- **`wasm-tools print`** on a component binary. -/
def printBytes (b : ByteArray) : Except String String :=
  match Silmaril.Wasm.Component.Codec.decodeLax b with
  | .ok c => .ok (print c)
  | .error e => .error s!"failed to parse component: {repr e}"

/-- **`wasm-tools parse`** of component WAT. -/
def parseText (t : String) : Except String ByteArray :=
  match readX t with
  | none => .error "not component WAT this reader accepts"
  | some c => match BinaryP3.encode c with
    | some b => .ok b
    | none => .error "a number or size exceeds 2^32"

end Silmaril.Wasm.Tools.Component.Wat
