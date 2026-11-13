module

public import Silmaril.Wasm.Component.Reference.Runtime.Options.Defs
public import Silmaril.Wasm.Component.Reference.Syntax.Basic.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Predicates.Defs

/-!
# Resolved canonical built-ins and canon host code

* `ResolvedBuiltin E` mirrors `Syntax.Builtin` (the `canon` built-ins of `Binary.md` at
  component-model `a25fc0b`) constructor by constructor, with every immediate resolved to a
  runtime entity: resource type indices become `RtId`s, component type indices of
  `stream`/`future` built-ins become their element type `Option (WIT.ClosedType RtId)`,
  `task.return`'s result type becomes a closed type, `canonopt` lists become `CanonOpts E`,
  core memory indices become `E.MemAddr`, and `thread.new-indirect`'s core type and table
  indices become the expected flat function type `(func (param T))` and an `E.TableAddr`.
  Boolean `async_` flags (`subtask.cancel`, `*.cancel-read/write`) are kept as they are.
* `CanonHost E` is the host-code identifier type `H` of the shared core store
  (`E.Store (CanonHost E)`): one per lowering site. `lowered` is a `canon lower` of a component
  function, `builtin` a canon built-in (with the instance it was defined in), and `embedder` a
  host function supplied directly by the embedding.
* `CanonHost.coreType` is the flat core signature each site is allocated with
  (`E.allocHost` converts it with `E.ofFlatType`): for `lowered`, REF
  `flatten_functype(opts, ft, 'lower')` (`ABI.flattenFunc`, definitions.py L2169-2175); for
  built-ins, the "`$f` is given type" clauses of `CanonicalABI.md` §Canonical Definitions (lines
  3770-4760 at `a25fc0b`), where `T`/`A` is the address type of the relevant memory (or `i32`
  without one, deviation D-g) and `U` that of `thread.new-indirect`'s table. Address types come from
  an `AddrTypes E` argument because they live in the core store.

Design notes:
* `resourceNew`/`resourceRep` also carry the resource's `rep : AddrType` (`i32`, or `i64` under
  🐘), which their core types `[rep] → [i32]` / `[i32] → [rep]` need; REF reads it from the
  type definition.
* `CanonHost.embedder` also carries its flat signature `ft`, so that `coreType` is total.

Not modelled here: validation of built-ins, resolution from syntax (instantiation items), and
any built-in behaviour (canon items). No claim is made that the signatures are validated.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

open Engine

/-- A canon built-in with resolved immediates; one constructor per `Syntax.Builtin`
constructor, in the same order and with the same names. -/
inductive ResolvedBuiltin (E : CoreEngine) where
  | resourceNew (rt : RtId) (rep : AddrType)
  | resourceDrop (rt : RtId)
  | resourceRep (rt : RtId) (rep : AddrType)
  | backpressureInc
  | backpressureDec
  | taskReturn (result : Option (WIT.ClosedType RtId)) (opts : CanonOpts E)
  | taskCancel
  | contextGet (t : AddrType) (i : Nat)
  | contextSet (t : AddrType) (i : Nat)
  | subtaskCancel (async_ : Bool)
  | subtaskDrop
  | streamNew (t : Option (WIT.ClosedType RtId))
  | streamRead (t : Option (WIT.ClosedType RtId)) (opts : CanonOpts E)
  | streamWrite (t : Option (WIT.ClosedType RtId)) (opts : CanonOpts E)
  | streamCancelRead (t : Option (WIT.ClosedType RtId)) (async_ : Bool)
  | streamCancelWrite (t : Option (WIT.ClosedType RtId)) (async_ : Bool)
  | streamDropReadable (t : Option (WIT.ClosedType RtId))
  | streamDropWritable (t : Option (WIT.ClosedType RtId))
  | streamForward (t : Option (WIT.ClosedType RtId))
  | futureNew (t : Option (WIT.ClosedType RtId))
  | futureRead (t : Option (WIT.ClosedType RtId)) (opts : CanonOpts E)
  | futureWrite (t : Option (WIT.ClosedType RtId)) (opts : CanonOpts E)
  | futureCancelRead (t : Option (WIT.ClosedType RtId)) (async_ : Bool)
  | futureCancelWrite (t : Option (WIT.ClosedType RtId)) (async_ : Bool)
  | futureDropReadable (t : Option (WIT.ClosedType RtId))
  | futureDropWritable (t : Option (WIT.ClosedType RtId))
  | futureForward (t : Option (WIT.ClosedType RtId))
  | errorContextNew (opts : CanonOpts E)
  | errorContextDebugMessage (opts : CanonOpts E)
  | errorContextDrop
  | waitableSetNew
  | waitableSetWait (mem : E.MemAddr)
  | waitableSetPoll (mem : E.MemAddr)
  | waitableSetDrop
  | waitableJoin
  | threadIndex
  | threadNewIndirect (table : E.TableAddr) (ft : V1.FuncType)
  | threadResumeLater
  | threadSuspend
  | threadYield
  | threadSuspendThenResume
  | threadYieldThenResume
  | threadSuspendThenPromote
  | threadYieldThenPromote
  deriving DecidableEq

/-- Host code of the shared core store: the `H` parameter of `E.Store`. -/
inductive CanonHost (E : CoreEngine) where
  /-- `canon lower callee opts` in instance `inst`; `ft` is the callee's function type. -/
  | lowered (callee : FuncId) (ft : WIT.FuncType Empty RtId) (opts : CanonOpts E) (inst : InstId)
  /-- A canon built-in defined in instance `inst`. -/
  | builtin (b : ResolvedBuiltin E) (inst : InstId)
  /-- A host function supplied by the embedding, with its flat signature. -/
  | embedder (name : String) (ft : V1.FuncType)
  deriving DecidableEq

/-- Address types of core memories and tables (they live in the core store). -/
structure AddrTypes (E : CoreEngine) where
  /-- Address type of a memory. -/
  mem : E.MemAddr → AddrType
  /-- Address type of a table. -/
  table : E.TableAddr → AddrType

namespace ResolvedBuiltin

variable {E : CoreEngine}

/-- The core function type of a built-in (`CanonicalABI.md` §Canonical Definitions, "`$f` is
given type"). -/
def coreType (at_ : AddrTypes E) : ResolvedBuiltin E → V1.FuncType
  | .resourceNew _ rep => ⟨[ABI.pointerType rep], [.int .i32]⟩
  | .resourceDrop _ => ⟨[.int .i32], []⟩
  | .resourceRep _ rep => ⟨[.int .i32], [ABI.pointerType rep]⟩
  | .backpressureInc | .backpressureDec | .taskCancel => ⟨[], []⟩
  | .taskReturn result opts =>
    ABI.flattenFunc { memory := opts.ptrType at_.mem } .lower ⟨result.toList, []⟩
  | .contextGet t _ => ⟨[], [ABI.pointerType t]⟩
  | .contextSet t _ => ⟨[ABI.pointerType t], []⟩
  | .subtaskCancel _ => ⟨[.int .i32], [.int .i32]⟩
  | .subtaskDrop => ⟨[.int .i32], []⟩
  | .streamNew _ | .futureNew _ => ⟨[], [.int .i64]⟩
  | .streamRead _ opts | .streamWrite _ opts =>
    let p := ABI.pointerType (opts.ptrType at_.mem)
    ⟨[.int .i32, p, p], [p]⟩
  | .futureRead _ opts | .futureWrite _ opts =>
    ⟨[.int .i32, ABI.pointerType (opts.ptrType at_.mem)], [.int .i32]⟩
  | .streamCancelRead _ _ | .streamCancelWrite _ _
  | .futureCancelRead _ _ | .futureCancelWrite _ _ => ⟨[.int .i32], [.int .i32]⟩
  | .streamDropReadable _ | .streamDropWritable _
  | .futureDropReadable _ | .futureDropWritable _ => ⟨[.int .i32], []⟩
  | .streamForward _ | .futureForward _ => ⟨[.int .i32, .int .i32], []⟩
  | .errorContextNew opts =>
    let p := ABI.pointerType (opts.ptrType at_.mem)
    ⟨[p, p], [.int .i32]⟩
  | .errorContextDebugMessage opts =>
    ⟨[.int .i32, ABI.pointerType (opts.ptrType at_.mem)], []⟩
  | .errorContextDrop => ⟨[.int .i32], []⟩
  | .waitableSetNew => ⟨[], [.int .i32]⟩
  | .waitableSetWait mem | .waitableSetPoll mem =>
    ⟨[.int .i32, ABI.pointerType (at_.mem mem)], [.int .i32]⟩
  | .waitableSetDrop => ⟨[.int .i32], []⟩
  | .waitableJoin => ⟨[.int .i32, .int .i32], []⟩
  | .threadIndex => ⟨[], [.int .i32]⟩
  | .threadNewIndirect table ft =>
    ⟨ABI.pointerType (at_.table table) :: ft.params, [.int .i32]⟩
  | .threadResumeLater => ⟨[.int .i32], []⟩
  | .threadSuspend | .threadYield => ⟨[], [.int .i32]⟩
  | .threadSuspendThenResume | .threadYieldThenResume
  | .threadSuspendThenPromote | .threadYieldThenPromote => ⟨[.int .i32], [.int .i32]⟩

end ResolvedBuiltin

namespace CanonHost

variable {E : CoreEngine}

/-- The flat core signature of a canon host site: REF `flatten_functype(opts, ft, 'lower')` for
`canon lower`, the built-in signature for built-ins, and the given signature for embedder
functions. -/
def coreType (at_ : AddrTypes E) : CanonHost E → V1.FuncType
  | .lowered _ ft opts _ =>
    ABI.flattenFunc (opts.abiOptions at_.mem) .lower (ABI.FuncType.ofWIT ft)
  | .builtin b _ => b.coreType at_
  | .embedder _ ft => ft

end CanonHost

end Silmaril.Wasm.Component.Runtime
