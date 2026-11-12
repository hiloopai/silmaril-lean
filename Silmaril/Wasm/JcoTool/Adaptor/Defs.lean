module

public import Silmaril.Wasm.JcoTool.New.Defs
public import Silmaril.Wasm.Jco.Styles.Lime.Defs
public import Silmaril.Wasm.Binaryen.Exe.Encode
public import Silmaril.Wasm.Perf.CoreMod.Defs

/-!
# `wasm-jco new --adaptor`: the monadic direction with the verified adaptor

For a core module that follows the **C convention** of `Silmaril.Wasm.Jco.Meta` (an allocator
`alloc(size, align) -> ptr`, string and list results through an out-pointer), the component
needs adaptor code. `--adaptor` puts next to the module the adaptor of jco part (a) as it is
defined in Lean, **`Silmaril.Wasm.Jco.adaptorLime md`** (a Lime1 module), encoded by silmaril's
verified Core encoder (`Silmaril.Wasm.Binaryen.Exe.encodeModule?`, sound for the Core binary
grammar):

```
core module 0  the input module M (exports memory, alloc, the world's functions)
core module 1  adaptorLime md, instantiated with M's instance as "m"
canon lift     of each adaptor export, with M's memory and the adaptor's cabi_realloc
```

`md = Meta.ofWorld w alloc`: the world's exports (no imports), synchronous, of the first FFI
fragment (memory-free types, `string`, `list<u8>`; no spilling or wide results).
`planAdaptor` checks that `M` exports `memory`, the allocator at `(i32, i32) -> i32` and each
world function at the C-convention core type (`calleeCore`). Theorems: `Silmaril.Wasm.JcoTool.
Adaptor.Thms` (the adaptor in the output is the encoding of `adaptorLime md`, it validates, and
`wrap_correct` gives the behaviour at the world).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.Adaptor

open Silmaril.Wasm.Wit.Binary (World Func)
open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component (CoreFuncTy)
open Silmaril.Wasm.Jco (Meta Sig inMem)
open New (TS valType funcType expectExport require worldFuncs hasMemory mustEncode)

/-- The core type of the C-convention export of `s` (`Jco.calleeType`). -/
def calleeCore (s : Sig) : CoreFuncTy :=
  if inMem s.result then ⟨Silmaril.Wasm.Jco.flatParams s.params ++ [ti32], []⟩
  else ⟨Silmaril.Wasm.Jco.flatParams s.params, match s.result with
    | some t => t.flat
    | none => []⟩

/-- The adaptor's bytes. -/
def adaptorBytes (md : Meta) : Except String ByteArray := do
  let bs ← Silmaril.Wasm.Binaryen.Exe.encodeModule? (Silmaril.Wasm.Jco.adaptorLime md).toCore
  pure ⟨bs.toArray⟩

/-- The plan of adaptor mode: the metadata, the module's interface and the world's exports. -/
structure Plan where
  md : Meta
  mod : CoreMod
  exports : List Silmaril.Wasm.Wit.Binary.Func

/-- **The plan** of a C-convention module against a world. -/
def planAdaptor (core : ByteArray) (w : World) (alloc : String) : Except String Plan := do
  let md ← Meta.ofWorld w alloc
  let m ← Silmaril.Wasm.Perf.CoreMod.coreModF core
  let exps ← worldFuncs "world export" w.exports
  require m.imports.isEmpty "adaptor mode: the module must not import functions"
  require (hasMemory core) "adaptor mode: the module must export its memory as `memory`"
  expectExport m alloc ⟨[ti32, ti32], [ti32]⟩
  md.world.forM fun s => expectExport m s.name (calleeCore s)
  pure ⟨md, m, exps⟩

/-- Whether the canonical lift of `s` touches memory, and whether it allocates. -/
def sigMem (s : Sig) : Bool × Bool :=
  let pm := s.params.any fun t => match t with
    | .string | .bytes => true
    | .val _ => false
  (pm || inMem s.result, pm)

/-- **The component** of adaptor mode. -/
def emitAdaptor (core adaptor : ByteArray) (p : Plan) : Except String XAst := do
  let (tys, ts) ← (p.exports.mapM funcType : New.TyM (List Nat)).run {}
  let lifts : List XSection := ((p.md.world.zip tys).zipIdx).flatMap fun ((s, t), i) =>
    let (mem, ra) := sigMem s
    let opts := (if mem then [CanonOpt.memory 0] else []) ++ (if ra then [CanonOpt.realloc 0] else [])
    [.sec (.aliases [⟨.core .func, .coreExport 1 s.name⟩]),
     .sec (.canons [.lift (i + 1) opts t]),
     .sec (.exports [⟨s.name, ⟨.func, 2 * i⟩, none⟩])]
  pure ⟨[.sec (.coreModule core), .sec (.coreModule adaptor), .sec (.types ts.types.toList),
    .sec (.coreInstances [.instantiate 0 []]),
    .sec (.coreInstances [.instantiate 1 [("m", 0)]]),
    .sec (.aliases [⟨.core .memory, .coreExport 0 "memory"⟩]),
    .sec (.aliases [⟨.core .func, .coreExport 1 "cabi_realloc"⟩])] ++ lifts⟩

/-- The output of adaptor mode: the bytes, the syntax, and the plan. -/
structure Out where
  bytes : ByteArray
  ast : Option Ast
  adaptor : ByteArray
  plan : Plan

/-- **`wasm-jco new --adaptor`** with a world. -/
def newAdaptor (core : ByteArray) (w : World) (alloc : String := "alloc") : Except String Out := do
  let p ← planAdaptor core w alloc
  let a ← adaptorBytes p.md
  let c ← emitAdaptor core a p
  let b ← mustEncode "the component" c.encode
  pure ⟨b, c.toAst, a, p⟩

end Silmaril.Wasm.JcoTool.Adaptor
