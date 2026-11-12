module

public import Silmaril.Wasm.Component.BinaryP3.Defs
public import Silmaril.Wasm.Component.Conformance.ToRef.Defs

/-!
# The conformance runner's decoder: `BinaryP3`, then reference syntax

`decodeP3 bytes` parses a component binary with the binary track's verified grammar
`Silmaril.Wasm.Component.BinaryP3` (every production of `Binary.md` at component-model `d095e2f`,
with encoder, round trip, unambiguity and conservativity over `Silmaril.Wasm.Component.Binary`
proved in `Silmaril.Wasm.Component.BinaryP3.Thms`) and maps the result to the index-based AST of
the copied reference semantics (`Silmaril.Wasm.Component.Syntax`, `Binary.md` at `a25fc0b`):

* `canonRef : BinaryP3.Canon → Except String Syntax.Canon` is the identity on the built-ins
  the reference AST has; it rejects the three 🧵② built-ins (`thread.spawn-ref`,
  `thread.spawn-indirect`, `thread.available-parallelism`, which the reference AST lacks)
  and a `context.get`/`context.set` whose value type is neither `i32` nor `i64`;
* every other section is mapped by `Conformance.ToRef` (the sections of `BinaryP3.Section`
  other than `canons` and `component` carry `Silmaril.Wasm.Component.Binary` syntax).

This replaces `Conformance.Decode.decode` (`canonXG`, a grammar written for the runner in
An earlier step) as the runner's decoder. The old decoder stays as a cross-check: the runner decodes
every binary with both and reports any disagreement (`tools/wasm-tools/README.md`).
`Conformance.DecodeP3.Thms` proves that `decodeP3` extends the old verified pipeline
`decodeRef` (`Binary.parse` then `toRef`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Conformance

open Silmaril.Wasm.Component
open Silmaril.Wasm.Component

namespace ToRefP3

/-- A `BinaryP3` built-in as reference syntax. -/
def canonRef : BinaryP3.Canon → Except String Syntax.Canon
  | .lift f opts t => .ok (.lift f (opts.map ToRef.canonOpt) t)
  | .lower f opts => .ok (.lower f (opts.map ToRef.canonOpt))
  | .resourceNew t => .ok (.builtin (.resourceNew t))
  | .resourceDrop t => .ok (.builtin (.resourceDrop t))
  | .resourceRep t => .ok (.builtin (.resourceRep t))
  | .backpressureInc => .ok (.builtin .backpressureInc)
  | .backpressureDec => .ok (.builtin .backpressureDec)
  | .taskReturn r opts =>
    .ok (.builtin (.taskReturn (r.map ToRef.valType) (opts.map ToRef.canonOpt)))
  | .taskCancel => .ok (.builtin .taskCancel)
  | .contextGet t i => do pure (.builtin (.contextGet (← ToRef.addrType t) i))
  | .contextSet t i => do pure (.builtin (.contextSet (← ToRef.addrType t) i))
  | .subtaskCancel a => .ok (.builtin (.subtaskCancel a))
  | .subtaskDrop => .ok (.builtin .subtaskDrop)
  | .streamNew t => .ok (.builtin (.streamNew t))
  | .streamRead t opts => .ok (.builtin (.streamRead t (opts.map ToRef.canonOpt)))
  | .streamWrite t opts => .ok (.builtin (.streamWrite t (opts.map ToRef.canonOpt)))
  | .streamCancelRead t a => .ok (.builtin (.streamCancelRead t a))
  | .streamCancelWrite t a => .ok (.builtin (.streamCancelWrite t a))
  | .streamDropReadable t => .ok (.builtin (.streamDropReadable t))
  | .streamDropWritable t => .ok (.builtin (.streamDropWritable t))
  | .streamForward t => .ok (.builtin (.streamForward t))
  | .futureNew t => .ok (.builtin (.futureNew t))
  | .futureRead t opts => .ok (.builtin (.futureRead t (opts.map ToRef.canonOpt)))
  | .futureWrite t opts => .ok (.builtin (.futureWrite t (opts.map ToRef.canonOpt)))
  | .futureCancelRead t a => .ok (.builtin (.futureCancelRead t a))
  | .futureCancelWrite t a => .ok (.builtin (.futureCancelWrite t a))
  | .futureDropReadable t => .ok (.builtin (.futureDropReadable t))
  | .futureDropWritable t => .ok (.builtin (.futureDropWritable t))
  | .futureForward t => .ok (.builtin (.futureForward t))
  | .errorContextNew opts => .ok (.builtin (.errorContextNew (opts.map ToRef.canonOpt)))
  | .errorContextDebugMessage opts =>
    .ok (.builtin (.errorContextDebugMessage (opts.map ToRef.canonOpt)))
  | .errorContextDrop => .ok (.builtin .errorContextDrop)
  | .waitableSetNew => .ok (.builtin .waitableSetNew)
  | .waitableSetWait m => .ok (.builtin (.waitableSetWait m))
  | .waitableSetPoll m => .ok (.builtin (.waitableSetPoll m))
  | .waitableSetDrop => .ok (.builtin .waitableSetDrop)
  | .waitableJoin => .ok (.builtin .waitableJoin)
  | .threadIndex => .ok (.builtin .threadIndex)
  | .threadNewIndirect ft tbl => .ok (.builtin (.threadNewIndirect ft tbl))
  | .threadResumeLater => .ok (.builtin .threadResumeLater)
  | .threadSuspend => .ok (.builtin .threadSuspend)
  | .threadYield => .ok (.builtin .threadYield)
  | .threadSuspendThenResume => .ok (.builtin .threadSuspendThenResume)
  | .threadYieldThenResume => .ok (.builtin .threadYieldThenResume)
  | .threadSuspendThenPromote => .ok (.builtin .threadSuspendThenPromote)
  | .threadYieldThenPromote => .ok (.builtin .threadYieldThenPromote)
  | .threadSpawnRef .. => .error "thread.spawn-ref (🧵②) is not in the reference AST"
  | .threadSpawnIndirect .. => .error "thread.spawn-indirect (🧵②) is not in the reference AST"
  | .threadAvailableParallelism _ =>
    .error "thread.available-parallelism (🧵②) is not in the reference AST"

/-- A list of built-ins as definitions. -/
def canons : List BinaryP3.Canon → Except String (List (Syntax.Definition Silmaril.Wasm.Module))
  | [] => .ok []
  | c :: cs => do pure (.canon (← canonRef c) :: (← canons cs))

mutual

/-- The definitions of one section, in order. -/
def section_ : BinaryP3.Section → Except String (List (Syntax.Definition Silmaril.Wasm.Module))
  | .custom n d => ToRef.section_ (.custom n d)
  | .coreModule bs => ToRef.section_ (.coreModule bs)
  | .coreInstances xs => ToRef.section_ (.coreInstances xs)
  | .coreTypes xs => ToRef.section_ (.coreTypes xs)
  | .component c => do pure [.component (← ast c)]
  | .instances xs => ToRef.section_ (.instances xs)
  | .aliases xs => ToRef.section_ (.aliases xs)
  | .types xs => ToRef.section_ (.types xs)
  | .canons xs => canons xs
  | .start s => ToRef.section_ (.start s)
  | .imports xs => ToRef.section_ (.imports xs)
  | .exports xs => ToRef.section_ (.exports xs)
  | .values xs => ToRef.section_ (.values xs)

def sections : List BinaryP3.Section →
    Except String (List (Syntax.Definition Silmaril.Wasm.Module))
  | [] => .ok []
  | s :: ss => do pure ((← section_ s) ++ (← sections ss))

/-- A component: the definitions of its sections, in order. -/
def ast : BinaryP3.Ast → Except String (List (Syntax.Definition Silmaril.Wasm.Module))
  | .mk ss => sections ss

end

end ToRefP3

/-- **The reference syntax of a `BinaryP3` component AST.** -/
def toRefP3 (a : BinaryP3.Ast) : Except String RefComponent := ToRefP3.ast a

/-- **Decode a component binary into reference syntax** with the `BinaryP3` grammar. -/
def decodeP3 (bytes : ByteArray) : Except String RefComponent :=
  match BinaryP3.parse bytes with
  | .error e => .error s!"binary: {repr e}"
  | .ok a => toRefP3 a

/-- Two decodings agree: both fail, or both succeed with the same definitions once core
modules are erased (`Silmaril.Wasm.Module` has no decidable equality; core modules are
decoded by the same core decoder on the same bytes in both pipelines). -/
def sameDecoding (a b : Except String RefComponent) : Bool :=
  match a, b with
  | .ok x, .ok y =>
    decide (Syntax.Component.map (fun _ => ()) x = Syntax.Component.map (fun _ => ()) y)
  | .error _, .error _ => true
  | _, _ => false

end Silmaril.Wasm.Component.Conformance
