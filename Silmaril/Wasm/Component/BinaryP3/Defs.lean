module

public import Silmaril.Wasm.Component.Binary.Defs

/-!
# Component binaries with the async (WASI 0.3) canonical built-ins

`Silmaril.Wasm.Component.Binary` decodes `Binary.md` at component-model `8505ba7`
except the canonical built-ins other than `lift`, `lower` and `resource.*`,
which it reports as unknown tags. This module extends it to the whole `canon`
production of `design/mvp/Binary.md` of WebAssembly/component-model at commit
`d095e2f60ddae1f9a1e9b1e2fb547ec1114da677` (2026-10-20, the newest commit on `main`
at least two weeks old on 2026-11-09; vendored in `vendor/component-model/d095e2f/`):

```
canon ::= 0x00 0x00 f opts ft        (lift)          | 0x01 0x00 f opts       (lower)
        | 0x02 rt | 0x03 rt | 0x04 rt                (resource.new/drop/rep)
        | 0x24 | 0x25                                (backpressure.inc/dec)
        | 0x09 rs:resultlist opts                    (task.return)
        | 0x05                                       (task.cancel)
        | 0x0a t:core:valtype i:u32 | 0x0b t i       (context.get/set)
        | 0x06 async? | 0x0d                         (subtask.cancel/drop)
        | 0x0e t | 0x0f t opts | 0x10 t opts         (stream.new/read/write)
        | 0x11 t async? | 0x12 t async?              (stream.cancel-read, cancel-write)
        | 0x13 t | 0x14 t | 0x2e t                   (stream.drop-readable, drop-writable, forward)
        | 0x15 … 0x1b, 0x2f                          (the same for future)
        | 0x1c opts | 0x1d opts | 0x1e               (error-context.new/debug-message/drop)
        | 0x1f | 0x20 0x00 m | 0x21 0x00 m | 0x22 | 0x23
                                                     (waitable-set.new/wait/poll/drop, waitable.join)
        | 0x26 | 0x27 ft tbl | 0x28 | 0x29 0x00 | 0x0c 0x00
        | 0x2a 0x00 | 0x2b 0x00 | 0x2c 0x00 | 0x2d 0x00
                                                     (thread.index/new-indirect/resume-later/
                                                      suspend/yield/…-then-resume/…-then-promote)
        | 0x40 sh? ft | 0x41 sh? ft tbl | 0x42 sh?   (thread.spawn-ref, spawn-indirect, available-parallelism)
async? ::= 0x00 | 0x01          sh? ::= 0x00 | 0x01
```

`canonopt` (including `async` `0x06` and `callback` `0x07`) is unchanged and is
`Binary.canonOptG`. Every other production is the one of
`Silmaril.Wasm.Component.Binary` (its `Binary.md` at `8505ba7` differs from `d095e2f`
only by a validation note on `map`; see `tools/wasm-tools/README.md`). Sections and
components are restated here because `Section.canons` carries the new `Canon`.

`Ast.ofV0` embeds the old syntax; `Silmaril.Wasm.Component.BinaryP3.Thms` proves that
the new parser accepts every component the old one accepts, with the embedded result.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.BinaryP3

open Silmaril.Parse.ByteParse (Grammar GrammarE NonEmpty Bytes Error runAll)
open Silmaril.Wasm.Component.Binary (CoreValType CanonOpt ValType Alias CoreInstanceExpr
  CoreType InstanceExpr DefType Start Import Export Value)

/-! ## Abstract syntax -/

/-- `canon`, every production of `Binary.md` at `d095e2f`. Type indices `t` are
component type indices (of a `stream`/`future` type); `ft` a core type index; `tbl` a
core table index; `mem` a core memory index. -/
inductive Canon where
  /-- `0x00 0x00 f:core:funcidx opts ft:typeidx`. -/
  | lift (coreFunc : Nat) (opts : List CanonOpt) (type : Nat)
  /-- `0x01 0x00 f:funcidx opts`. -/
  | lower (func : Nat) (opts : List CanonOpt)
  | resourceNew (t : Nat)
  | resourceDrop (t : Nat)
  | resourceRep (t : Nat)
  /-- `0x24`. -/
  | backpressureInc
  /-- `0x25`. -/
  | backpressureDec
  /-- `0x09 rs:resultlist opts`. -/
  | taskReturn (result : Option Binary.ValType) (opts : List CanonOpt)
  /-- `0x05`. -/
  | taskCancel
  /-- `0x0a t:core:valtype i:u32`. -/
  | contextGet (t : CoreValType) (i : Nat)
  /-- `0x0b t:core:valtype i:u32`. -/
  | contextSet (t : CoreValType) (i : Nat)
  /-- `0x06 async?`. -/
  | subtaskCancel (async : Bool)
  /-- `0x0d`. -/
  | subtaskDrop
  | streamNew (t : Nat)
  | streamRead (t : Nat) (opts : List CanonOpt)
  | streamWrite (t : Nat) (opts : List CanonOpt)
  | streamCancelRead (t : Nat) (async : Bool)
  | streamCancelWrite (t : Nat) (async : Bool)
  | streamDropReadable (t : Nat)
  | streamDropWritable (t : Nat)
  /-- `0x2e t` (marked ➡️ in `Binary.md`). -/
  | streamForward (t : Nat)
  | futureNew (t : Nat)
  | futureRead (t : Nat) (opts : List CanonOpt)
  | futureWrite (t : Nat) (opts : List CanonOpt)
  | futureCancelRead (t : Nat) (async : Bool)
  | futureCancelWrite (t : Nat) (async : Bool)
  | futureDropReadable (t : Nat)
  | futureDropWritable (t : Nat)
  /-- `0x2f t` (marked ➡️). -/
  | futureForward (t : Nat)
  | errorContextNew (opts : List CanonOpt)
  | errorContextDebugMessage (opts : List CanonOpt)
  | errorContextDrop
  | waitableSetNew
  /-- `0x20 0x00 m:core:memoryidx`. -/
  | waitableSetWait (mem : Nat)
  /-- `0x21 0x00 m:core:memoryidx`. -/
  | waitableSetPoll (mem : Nat)
  | waitableSetDrop
  | waitableJoin
  /-- `0x26`. -/
  | threadIndex
  /-- `0x27 ft:core:typeidx t:core:tableidx`. -/
  | threadNewIndirect (ft tbl : Nat)
  /-- `0x28`. -/
  | threadResumeLater
  /-- `0x29 0x00`. -/
  | threadSuspend
  /-- `0x0c 0x00`. -/
  | threadYield
  /-- `0x2a 0x00`. -/
  | threadSuspendThenResume
  /-- `0x2b 0x00`. -/
  | threadYieldThenResume
  /-- `0x2c 0x00`. -/
  | threadSuspendThenPromote
  /-- `0x2d 0x00`. -/
  | threadYieldThenPromote
  /-- `0x40 sh? ft` (shared-everything threads, 🧵②). -/
  | threadSpawnRef (shared : Bool) (ft : Nat)
  /-- `0x41 sh? ft tbl` (🧵②). -/
  | threadSpawnIndirect (shared : Bool) (ft tbl : Nat)
  /-- `0x42 sh?` (🧵②). -/
  | threadAvailableParallelism (shared : Bool)
  deriving Repr, DecidableEq, Inhabited

/-- The `wasm-tools print` spelling of a built-in (without operands). -/
def Canon.kind : Canon → String
  | .lift .. => "lift" | .lower .. => "lower"
  | .resourceNew _ => "resource.new" | .resourceDrop _ => "resource.drop"
  | .resourceRep _ => "resource.rep"
  | .backpressureInc => "backpressure.inc" | .backpressureDec => "backpressure.dec"
  | .taskReturn .. => "task.return" | .taskCancel => "task.cancel"
  | .contextGet .. => "context.get" | .contextSet .. => "context.set"
  | .subtaskCancel _ => "subtask.cancel" | .subtaskDrop => "subtask.drop"
  | .streamNew _ => "stream.new" | .streamRead .. => "stream.read"
  | .streamWrite .. => "stream.write" | .streamCancelRead .. => "stream.cancel-read"
  | .streamCancelWrite .. => "stream.cancel-write"
  | .streamDropReadable _ => "stream.drop-readable"
  | .streamDropWritable _ => "stream.drop-writable" | .streamForward _ => "stream.forward"
  | .futureNew _ => "future.new" | .futureRead .. => "future.read"
  | .futureWrite .. => "future.write" | .futureCancelRead .. => "future.cancel-read"
  | .futureCancelWrite .. => "future.cancel-write"
  | .futureDropReadable _ => "future.drop-readable"
  | .futureDropWritable _ => "future.drop-writable" | .futureForward _ => "future.forward"
  | .errorContextNew _ => "error-context.new"
  | .errorContextDebugMessage _ => "error-context.debug-message"
  | .errorContextDrop => "error-context.drop"
  | .waitableSetNew => "waitable-set.new" | .waitableSetWait _ => "waitable-set.wait"
  | .waitableSetPoll _ => "waitable-set.poll" | .waitableSetDrop => "waitable-set.drop"
  | .waitableJoin => "waitable.join"
  | .threadIndex => "thread.index" | .threadNewIndirect .. => "thread.new-indirect"
  | .threadResumeLater => "thread.resume-later" | .threadSuspend => "thread.suspend"
  | .threadYield => "thread.yield"
  | .threadSuspendThenResume => "thread.suspend-then-resume"
  | .threadYieldThenResume => "thread.yield-then-resume"
  | .threadSuspendThenPromote => "thread.suspend-then-promote"
  | .threadYieldThenPromote => "thread.yield-then-promote"
  | .threadSpawnRef .. => "thread.spawn-ref"
  | .threadSpawnIndirect .. => "thread.spawn-indirect"
  | .threadAvailableParallelism _ => "thread.available-parallelism"

/-- The embedding of the built-ins `Silmaril.Wasm.Component.Binary` decodes. -/
def Canon.ofV0 : Binary.Canon → Canon
  | .lift f o t => .lift f o t
  | .lower f o => .lower f o
  | .resourceNew t => .resourceNew t
  | .resourceDrop t => .resourceDrop t
  | .resourceRep t => .resourceRep t

mutual
/-- Sections; as `Binary.Section`, with the new `Canon`. -/
inductive Section where
  | custom (name : String) (data : ByteArray)
  | coreModule (bytes : ByteArray)
  | coreInstances (xs : List CoreInstanceExpr)
  | coreTypes (xs : List CoreType)
  | component (c : Ast)
  | instances (xs : List InstanceExpr)
  | aliases (xs : List Alias)
  | types (xs : List DefType)
  | canons (xs : List Canon)
  | start (s : Start)
  | imports (xs : List Binary.Import)
  | exports (xs : List Binary.Export)
  | values (xs : List Value)

/-- A component: its sections in order. -/
inductive Ast where
  | mk (sections : List Section)
end

def Ast.sections : Ast → List Section | .mk ss => ss

instance : Inhabited Ast := ⟨.mk []⟩

mutual
/-- The embedding of the old syntax. -/
def Section.ofV0 : Binary.Section → Section
  | .custom n d => .custom n d
  | .coreModule b => .coreModule b
  | .coreInstances xs => .coreInstances xs
  | .coreTypes xs => .coreTypes xs
  | .component c => .component (Ast.ofV0 c)
  | .instances xs => .instances xs
  | .aliases xs => .aliases xs
  | .types xs => .types xs
  | .canons xs => .canons (xs.map Canon.ofV0)
  | .start s => .start s
  | .imports xs => .imports xs
  | .exports xs => .exports xs
  | .values xs => .values xs

def Section.listOfV0 : List Binary.Section → List Section
  | [] => []
  | s :: ss => Section.ofV0 s :: Section.listOfV0 ss

def Ast.ofV0 : Binary.Ast → Ast
  | .mk ss => .mk (Section.listOfV0 ss)
end

/-- Every built-in of a component, nested components included, in section order. -/
partial def Ast.canons : Ast → List Canon
  | .mk ss => ss.flatMap fun
    | .canons xs => xs
    | .component c => c.canons
    | _ => []

/-! ## Grammar -/

section Grammar
open Silmaril.Parse.ByteParse.Grammar
open Silmaril.Wasm.Component.Binary (canonOptsG coreValTypeG resultListG tag0 coreInstanceExprG
  coreTypeG coreTypeG_nonEmpty instanceExprG aliasG aliasG_nonEmpty startG importG
  externNameG_nonEmpty exportG valueG valTypeG_nonEmpty defTypeG defTypeG_nonEmpty
  preambleBytes)

/-- `async? ::= 0x00 | 0x01` (also `sh?`). -/
def flagG (what : String) : Grammar Bool := tagged what fun b => match b.toNat with
  | 0x00 => tag0 false | 0x01 => tag0 true | _ => none

/-- A built-in with a fixed `0x00` byte after its tag. -/
@[inline] def zero {α : Type} (a : α) : Option (Grammar α) :=
  some ((expect "canon 0x00" 0x00).then_ (Grammar.pure a))

def canonG : Grammar Canon := tagged "canon" fun b => match b.toNat with
  | 0x00 => some ((expect "canon lift" 0x00).then_
      (((u32.seq canonOptsG).seq u32).map fun p => .lift p.1.1 p.1.2 p.2))
  | 0x01 => some ((expect "canon lower" 0x00).then_
      ((u32.seq canonOptsG).map fun p => .lower p.1 p.2))
  | 0x02 => some (u32.map .resourceNew)
  | 0x03 => some (u32.map .resourceDrop)
  | 0x04 => some (u32.map .resourceRep)
  | 0x05 => tag0 .taskCancel
  | 0x06 => some ((flagG "async?").map .subtaskCancel)
  | 0x09 => some ((resultListG.seq canonOptsG).map fun p => .taskReturn p.1 p.2)
  | 0x0a => some ((coreValTypeG.seq u32).map fun p => .contextGet p.1 p.2)
  | 0x0b => some ((coreValTypeG.seq u32).map fun p => .contextSet p.1 p.2)
  | 0x0c => zero .threadYield
  | 0x0d => tag0 .subtaskDrop
  | 0x0e => some (u32.map .streamNew)
  | 0x0f => some ((u32.seq canonOptsG).map fun p => .streamRead p.1 p.2)
  | 0x10 => some ((u32.seq canonOptsG).map fun p => .streamWrite p.1 p.2)
  | 0x11 => some ((u32.seq (flagG "async?")).map fun p => .streamCancelRead p.1 p.2)
  | 0x12 => some ((u32.seq (flagG "async?")).map fun p => .streamCancelWrite p.1 p.2)
  | 0x13 => some (u32.map .streamDropReadable)
  | 0x14 => some (u32.map .streamDropWritable)
  | 0x15 => some (u32.map .futureNew)
  | 0x16 => some ((u32.seq canonOptsG).map fun p => .futureRead p.1 p.2)
  | 0x17 => some ((u32.seq canonOptsG).map fun p => .futureWrite p.1 p.2)
  | 0x18 => some ((u32.seq (flagG "async?")).map fun p => .futureCancelRead p.1 p.2)
  | 0x19 => some ((u32.seq (flagG "async?")).map fun p => .futureCancelWrite p.1 p.2)
  | 0x1a => some (u32.map .futureDropReadable)
  | 0x1b => some (u32.map .futureDropWritable)
  | 0x1c => some (canonOptsG.map .errorContextNew)
  | 0x1d => some (canonOptsG.map .errorContextDebugMessage)
  | 0x1e => tag0 .errorContextDrop
  | 0x1f => tag0 .waitableSetNew
  | 0x20 => some ((expect "canon 0x00" 0x00).then_ (u32.map .waitableSetWait))
  | 0x21 => some ((expect "canon 0x00" 0x00).then_ (u32.map .waitableSetPoll))
  | 0x22 => tag0 .waitableSetDrop
  | 0x23 => tag0 .waitableJoin
  | 0x24 => tag0 .backpressureInc
  | 0x25 => tag0 .backpressureDec
  | 0x26 => tag0 .threadIndex
  | 0x27 => some ((u32.seq u32).map fun p => .threadNewIndirect p.1 p.2)
  | 0x28 => tag0 .threadResumeLater
  | 0x29 => zero .threadSuspend
  | 0x2a => zero .threadSuspendThenResume
  | 0x2b => zero .threadYieldThenResume
  | 0x2c => zero .threadSuspendThenPromote
  | 0x2d => zero .threadYieldThenPromote
  | 0x2e => some (u32.map .streamForward)
  | 0x2f => some (u32.map .futureForward)
  | 0x40 => some (((flagG "sh?").seq u32).map fun p => .threadSpawnRef p.1 p.2)
  | 0x41 => some ((((flagG "sh?").seq u32).seq u32).map
      fun p => .threadSpawnIndirect p.1.1 p.1.2 p.2)
  | 0x42 => some ((flagG "sh?").map .threadAvailableParallelism)
  | _ => none

theorem canonG_nonEmpty : NonEmpty canonG.G := tagged_nonEmpty _ _

/-- A size-prefixed `vec` section body. -/
@[inline] def vecSection {α β : Type} (g : Grammar α) (hne : NonEmpty g.G) (f : List α → β) :
    Option (Grammar β) := some ((sizedBy (vec g hne)).map f)

/-- Sections, given the grammar of nested components and of type definitions. -/
def sectionG (c : GrammarE Ast) (t : Grammar DefType) (ht : NonEmpty t.G) : Grammar Section :=
  tagged "section" fun b => match b.toNat with
  | 0x00 => some (GrammarE.sizedBy (GrammarE.after name fun n => GrammarE.rest.map (.custom n)))
  | 0x01 => some (GrammarE.sizedBy (GrammarE.rest.map .coreModule))
  | 0x02 => vecSection coreInstanceExprG (tagged_nonEmpty _ _) .coreInstances
  | 0x03 => vecSection coreTypeG coreTypeG_nonEmpty .coreTypes
  | 0x04 => some (GrammarE.sizedBy (c.map .component))
  | 0x05 => vecSection instanceExprG (tagged_nonEmpty _ _) .instances
  | 0x06 => vecSection aliasG aliasG_nonEmpty .aliases
  | 0x07 => vecSection t ht .types
  | 0x08 => vecSection canonG canonG_nonEmpty .canons
  | 0x09 => some ((sizedBy startG).map .start)
  | 0x0a => vecSection importG (map_nonEmpty (seq_nonEmpty externNameG_nonEmpty)) .imports
  | 0x0b => vecSection exportG (map_nonEmpty (seq_nonEmpty (seq_nonEmpty externNameG_nonEmpty)))
      .exports
  | 0x0c => vecSection valueG (map_nonEmpty (seq_nonEmpty valTypeG_nonEmpty)) .values
  | _ => none

/-- A component (preamble and sections to the end of the window), nested at
most `k` deep; type definitions at most `k` deep. -/
def componentG : Nat → GrammarE Ast
  | 0 => GrammarE.ofGrammar fail
  | k + 1 => GrammarE.after (lit preambleBytes) fun _ =>
      (GrammarE.items (sectionG (componentG k) (defTypeG (k + 1)) (defTypeG_nonEmpty _))
        (tagged_nonEmpty _ _)).map
        .mk

end Grammar

/-! ## Entry point -/

/-- Parse a component binary, async built-ins included. -/
def parse (bs : ByteArray) : Except Error Ast :=
  runAll (componentG (bs.size + 1)).parse bs

end Silmaril.Wasm.Component.BinaryP3
