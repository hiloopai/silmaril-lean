module

public import Silmaril.Wasm.Jco.Async.Future.Defs

/-!
# Stream and future results in the world syntax

`AMeta` (`Silmaril.Wasm.Jco.Async`) gives each world function an optional async style, and its
result is a value of the fragment. `Async/Early` and `Async/Future` model functions whose result
is `stream<T>` or `future<T>` one function at a time (`asyncCallS`, `asyncCallF`). This module
puts these result types into the metadata, as a new variant next to `AMeta`:

* `RKind`: the kind of a function's result: a plain value, `stream<T>` or `future<T>`, where `T`
  is the result type of the function's `Sig`.
* `XSig`, `XMeta`: an `ASig` with a result kind, and metadata of such functions.
  `XMeta.toAMeta` forgets the kinds; `XMeta.ofAMeta` declares every result plain.
* `xcallExport md name vs`: the component of `awrap md.toAMeta`, except that an async function
  whose result is a stream (a future) runs its shim's core function with `streamSplit`
  (`futureSplit`), and the caller receives the readable end's handle as a `u32` (`handleRes`).
* `XSig.ofWit`, `XMeta.ofWorld`: the metadata from a resolved WIT world, reading
  `stream<T>` and `future<T>` results of async functions (`T` memory-free). Async functions
  get the callback style (the stream and future bodies return `WAIT`).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat Val)

namespace Async

/-- The kind of a world function's result. -/
inductive RKind where
  /-- A value of the fragment. -/
  | plain
  /-- `stream<T>`, `T` the function's result type. -/
  | stream
  /-- `future<T>`, `T` the function's result type. -/
  | future
  deriving Repr, Inhabited, DecidableEq

/-- A world function with an optional async style and a result kind. -/
structure XSig where
  asig : ASig
  kind : RKind := .plain
  deriving Repr, Inhabited, DecidableEq

/-- Metadata with async styles and result kinds. -/
structure XMeta where
  world : List XSig
  alloc : String := "alloc"
  deriving Repr, Inhabited, DecidableEq

namespace XMeta

/-- Forget the result kinds. -/
def toAMeta (md : XMeta) : AMeta := ⟨md.world.map (·.asig), md.alloc⟩

/-- Every result plain. -/
def ofAMeta (md : AMeta) : XMeta := ⟨md.world.map fun s => ⟨s, .plain⟩, md.alloc⟩

/-- The result kind of the world function `name`. -/
def kindOf (md : XMeta) (name : String) : Option RKind :=
  (md.world.find? (·.asig.sig.name == name)).map (·.kind)

end XMeta

/-- A readable end's handle as the caller's result. -/
def handleRes (h : Nat) : Option PVal := some (.val (.u32 (BitVec.ofNat 32 h)))

variable (M : CoreInst)

/-- **The behaviour of calling the export `name` of the wrapper for `md`**: the lifts of
`awrap md.toAMeta`; an async function whose result is a stream or a future runs its shim's core
function with `streamSplit` or `futureSplit`, and returns the readable end. -/
def xcallExport (md : XMeta) (name : String) (vs : List PVal) : RM M.withStore.St (Option PVal) :=
  match md.kindOf name, (awrap md.toAMeta).lifts.find? (·.lift.sig.name == name) with
  | some .stream, some ⟨l, some _⟩ => do
    let h ← asyncCallS M ((awrap md.toAMeta).base.callRef M.withStore l.realloc)
      ((awrap md.toAMeta).base.callRef M.withStore l.callee) l.sig vs
    pure (handleRes h)
  | some .future, some ⟨l, some _⟩ => do
    let h ← asyncCallF M ((awrap md.toAMeta).base.callRef M.withStore l.realloc)
      ((awrap md.toAMeta).base.callRef M.withStore l.callee) l.sig vs
    pure (handleRes h)
  | _, _ => (awrap md.toAMeta).callExport M name vs

/-! ## From WIT -/

section ofWit
open Silmaril.Wasm.Wit.Binary (Ty)

/-- The result type and kind of a WIT result: `stream<T>` and `future<T>` with `T` memory-free,
or a result of the fragment. -/
def resultOfWit : Option Silmaril.Wasm.Wit.Binary.Ty → Option (Option PTy × RKind)
  | none => some (none, .plain)
  | some (.stream (some t)) => (valOfWit t).map fun v => (some (.val v), .stream)
  | some (.future (some t)) => (valOfWit t).map fun v => (some (.val v), .future)
  | some t => (PTy.ofWit t).map fun p => (some p, .plain)

/-- The signature of a freestanding world function, with its async style (callback, if async)
and result kind. Streams and futures are results of async functions only. -/
def XSig.ofWit (f : Silmaril.Wasm.Wit.Binary.Func) : Except String XSig := do
  if f.kind ≠ .freestanding then throw s!"{f.name}: resource functions are not in the fragment"
  let ps ← f.params.mapM fun (p, t) => match PTy.ofWit t with
    | some t' => pure t'
    | none => throw s!"{f.name}: parameter {p} is not in the fragment"
  let (r, k) ← match resultOfWit f.result with
    | some rk => pure rk
    | none => throw s!"{f.name}: the result is not in the fragment"
  if k ≠ .plain && !f.async then
    throw s!"{f.name}: stream and future results are only modelled for async functions"
  let s : Sig := ⟨f.name, ps, r⟩
  if s.Ok then pure ⟨⟨s, if f.async then some .callback else none⟩, k⟩
  else throw s!"{f.name}: too many flat parameters or a wide flat result"

/-- The function of one exported world item. -/
def xexportSig : Silmaril.Wasm.Wit.Binary.WorldItem → Except String XSig
  | .func f => XSig.ofWit f
  | _ => throw "only exported functions (not interfaces or types) are in the fragment"

/-- Metadata with result kinds from a resolved WIT world (no imports). -/
def XMeta.ofWorld (w : Silmaril.Wasm.Wit.Binary.World) (alloc : String := "alloc") :
    Except String XMeta := do
  if !w.imports.isEmpty then throw "imports are not in the fragment"
  let ss ← w.exports.mapM xexportSig
  pure ⟨ss, alloc⟩

end ofWit

/-! ## A litmus world -/

/-- A world with a plain function, an async function returning `stream<u32>` and an async
function returning `future<u32>`. -/
def exXWorld : Silmaril.Wasm.Wit.Binary.World where
  exports := [
    .func { name := "add", params := [("a", .prim .u32), ("b", .prim .u32)],
            result := some (.prim .u32) },
    .func { name := "count", async := true, params := [("n", .prim .u32)],
            result := some (.stream (some (.prim .u32))) },
    .func { name := "once", async := true, params := [],
            result := some (.future (some (.prim .u32))) }]

/-- A synchronous function returning a stream: not in the modelled fragment. -/
def exSyncStreamWorld : Silmaril.Wasm.Wit.Binary.World where
  exports := [.func { name := "count", params := [], result := some (.stream (some (.prim .u32))) }]

end Async

end Silmaril.Wasm.Jco
