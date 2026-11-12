module

public import Silmaril.Wasm.Jco.Async.XWorld.Defs

/-!
# Synchronous functions with stream or future results

`XSig.ofWit` (`Async/XWorld`) refuses a synchronous function whose result is `stream<T>` or
`future<T>`. In the Component Model such a function is lifted without `async`: it returns the
readable end as its result, and nothing of it runs after it returned. This module is a variant
that models them:

* `syncStreamCall R core sig vs`: the synchronous lift (`canonCall`, no task), then
  `stream.new` and a non-blocking `stream.write` of `M`'s values on the writable end (it stays
  pending until a reader reads), and the result is the readable end's handle.
* `syncFutureCall R core sig vs`: the same with a future: `M` must return exactly one value;
  `future.new`, `future.write` (pending), the readable end.
* `xcallExportS md name vs`: `xcallExport` of `Async/XWorld`, except that a **synchronous**
  function whose result kind is `stream` or `future` runs `syncStreamCall` or `syncFutureCall`.
* `XSig.ofWitS`, `XMeta.ofWorldS`: the metadata from WIT, accepting synchronous functions with
  `stream<T>` and `future<T>` results (`T` memory-free); on everything `XSig.ofWit` accepts, the
  same result.

The writable end stays in the callee's table and is never dropped: no thread of the callee runs
after the synchronous return. So after the caller read the values, a further read of the stream
waits for ever (it is pending), unlike the async stream function with `closeCb`.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat Val)

namespace Async

variable (M : CoreInst)

/-- **A synchronous function whose result is a stream**: `M`'s C convention, then `stream.new`,
`stream.write` of the values (pending), and the readable end. -/
def syncStreamCall (R core : List Flat → RM M.withStore.St (List Flat)) (sig : Sig)
    (vs : List PVal) : RM M.withStore.St Nat := do
  let v ← canonCall M.withStore R core sig vs
  let ws ← RM.ofOption (resVals v)
  let e ← builtin M .streamNew
  match e with
  | .ends r w => do
    let _ ← builtin M (.streamWrite w ws)
    pure r
  | _ => RM.fail

/-- **A synchronous function whose result is a future**: `M`'s C convention (one value), then
`future.new`, `future.write` of the value (pending), and the readable end. -/
def syncFutureCall (R core : List Flat → RM M.withStore.St (List Flat)) (sig : Sig)
    (vs : List PVal) : RM M.withStore.St Nat := do
  let v ← canonCall M.withStore R core sig vs
  let ws ← RM.ofOption (resVals v)
  match ws with
  | [y] => do
    let e ← builtin M .futureNew
    match e with
    | .ends r w => do
      let _ ← builtin M (.futureWrite w y)
      pure r
    | _ => RM.fail
  | _ => RM.fail

/-- **The wrapper with synchronous stream and future results**: as `xcallExport`, except for
synchronous functions whose result is a stream or a future. -/
def xcallExportS (md : XMeta) (name : String) (vs : List PVal) : RM M.withStore.St (Option PVal) :=
  match md.kindOf name, (awrap md.toAMeta).lifts.find? (·.lift.sig.name == name) with
  | some .stream, some ⟨l, none⟩ => do
    let h ← syncStreamCall M ((awrap md.toAMeta).base.callRef M.withStore l.realloc)
      ((awrap md.toAMeta).base.callRef M.withStore l.callee) l.sig vs
    pure (handleRes h)
  | some .future, some ⟨l, none⟩ => do
    let h ← syncFutureCall M ((awrap md.toAMeta).base.callRef M.withStore l.realloc)
      ((awrap md.toAMeta).base.callRef M.withStore l.callee) l.sig vs
    pure (handleRes h)
  | _, _ => xcallExport M md name vs

/-! ## From WIT -/

section ofWit

/-- The signature of a world function, accepting synchronous functions with stream and future
results: what `XSig.ofWit` gives, else the reading of the function as async, made synchronous. -/
def XSig.ofWitS (f : Silmaril.Wasm.Wit.Binary.Func) : Except String XSig :=
  match XSig.ofWit f with
  | .ok x => .ok x
  | .error e =>
    if f.async then .error e
    else (XSig.ofWit { f with async := true }).map fun x => { x with asig.async := none }

/-- The function of one exported world item. -/
def xexportSigS : Silmaril.Wasm.Wit.Binary.WorldItem → Except String XSig
  | .func f => XSig.ofWitS f
  | _ => throw "only exported functions (not interfaces or types) are in the fragment"

/-- Metadata from a resolved WIT world, with synchronous stream and future results. -/
def XMeta.ofWorldS (w : Silmaril.Wasm.Wit.Binary.World) (alloc : String := "alloc") :
    Except String XMeta := do
  if !w.imports.isEmpty then throw "imports are not in the fragment"
  let ss ← w.exports.mapM xexportSigS
  pure ⟨ss, alloc⟩

end ofWit

/-- A world with a synchronous function returning `future<u32>`. -/
def exSyncFutureWorld : Silmaril.Wasm.Wit.Binary.World where
  exports := [.func { name := "once", params := [], result := some (.future (some (.prim .u32))) }]

end Async

end Silmaril.Wasm.Jco
