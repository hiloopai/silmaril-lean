module

public import Silmaril.Wasm.JcoTool.Adaptor.Defs
public import Silmaril.Wasm.JcoTool.NewI.Defs
public import Silmaril.Wasm.JcoTool.Tool.Defs
public import Silmaril.Wasm.Perf.CoreMod.Defs

/-!
# `wasm-jco new --adaptor` with exported interfaces

Adaptor mode (`Silmaril.Wasm.JcoTool.Adaptor`) puts the verified adaptor `Jco.adaptorLime md` next
to a module that follows the C convention, for worlds of exported functions. This module adds
**exported interfaces** (`export ns:pkg/iface;`, `export x: interface { … }`), from the full
world (`WorldFull`):

* the metadata `mdOf wf alloc`: the world's exported functions (named `f`), then the
  functions of each exported interface, named `key#f` (wit-component's core names), each in the
  first FFI fragment of `Jco.Meta` (`Sig.ofWit`: synchronous, freestanding, memory-free types,
  `string`, `list<u8>`); the module must export each at its C-convention core type, the
  allocator and its memory, and import nothing (as in adaptor mode, imports are not in the
  fragment);
* the adaptor: `adaptorLime md`, encoded by silmaril's verified encoder (`Adaptor.adaptorBytes`);
* the component: the module and the adaptor instantiated as in adaptor mode, one `canon lift`
  per adaptor export (with the module's memory and the adaptor's `cabi_realloc` where the
  canonical ABI needs them), the world-level functions exported by name, and each exported
  interface exported as an instance (an inline instance of its lifted functions, by their
  plain names) under the interface's key.

Named types and resources are outside the fragment (the adaptor's metadata has no named
types); they are rejected with a message. Theorems: `AdaptorI.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.AdaptorI

open Silmaril.Wasm.Wit.Binary (WorldFull Func)
open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Jco (Meta Sig)
open Silmaril.Wasm.JcoTool.NewI (ifaces keyName fname worldFuncs)
open New (TS funcType expectExport require hasMemory mustEncode)

/-- An exported function of adaptor mode: its interface (`none`: world level), its function and
its signature (named by its core export). -/
structure AFn where
  iface : Option String
  f : Func
  s : Sig

/-- The exported functions: world-level, then each exported interface's. -/
def fnsOf (wf : WorldFull) : Except String (List AFn) := do
  if !wf.imports.isEmpty then throw "adaptor mode: imports are not in the fragment"
  let w ← (worldFuncs wf.exports).mapM fun f => do pure (AFn.mk none f (← Sig.ofWit f))
  let i ← ((ifaces wf).filter (!·.imported)).flatMapM fun i => do
    if !i.body.types.isEmpty then
      throw s!"adaptor mode: interface {keyName i.key} defines types (named types are not in the fragment)"
    i.body.funcs.mapM fun f => do
      let s ← Sig.ofWit f
      pure (AFn.mk (some (keyName i.key)) f { s with name := keyName i.key ++ "#" ++ fname f })
  pure (w ++ i)

/-- **The metadata** of adaptor mode with interfaces. -/
def mdOf (wf : WorldFull) (alloc : String) : Except String Meta := do
  pure ⟨(← fnsOf wf).map (·.s), alloc⟩

/-- The plan: the functions, the metadata, the module's interface. -/
structure Plan where
  fns : List AFn
  md : Meta
  mod : CoreMod

/-- **The plan** of a C-convention module against a full world. -/
def planI (core : ByteArray) (wf : WorldFull) (alloc : String) : Except String Plan := do
  let fns ← fnsOf wf
  let md : Meta := ⟨fns.map (·.s), alloc⟩
  let m ← Silmaril.Wasm.Perf.CoreMod.coreModF core
  require m.imports.isEmpty "adaptor mode: the module must not import functions"
  require (hasMemory core) "adaptor mode: the module must export its memory as `memory`"
  expectExport m alloc ⟨[ti32, ti32], [ti32]⟩
  md.world.forM fun s => expectExport m s.name (Adaptor.calleeCore s)
  pure ⟨fns, md, m⟩

/-- **The component** of adaptor mode with interfaces. -/
def emitI (core adaptor : ByteArray) (p : Plan) : Except String XAst := do
  let (tys, ts) ← (p.fns.mapM (fun x => funcType x.f) : New.TyM (List Nat)).run {}
  let lifts : List XSection := ((p.fns.zip tys).zipIdx).flatMap fun ((x, t), i) =>
    let (mem, ra) := Adaptor.sigMem x.s
    let opts := (if mem then [CanonOpt.memory 0] else []) ++ (if ra then [CanonOpt.realloc 0] else [])
    [.sec (.aliases [⟨.core .func, .coreExport 1 x.s.name⟩]),
     .sec (.canons [.lift (i + 1) opts t])]
  let worldExps : List XSection := (p.fns.zipIdx.filter (·.1.iface.isNone)).map fun (x, i) =>
    .sec (.exports [⟨⟨x.s.name, .plain0⟩, ⟨.func, i⟩, none⟩])
  let keys := (p.fns.filterMap (·.iface)).foldl (fun acc k => if acc.contains k then acc else acc ++ [k]) []
  let ifaceExps : List XSection := (keys.zipIdx).flatMap fun (k, j) =>
    let es := (p.fns.zipIdx.filter (·.1.iface == some k)).map fun (x, i) =>
      ((⟨fname x.f, .plain0⟩ : ExternName), (⟨.func, i⟩ : SortIdx))
    [.sec (.instances [.exports es]),
     .sec (.exports [⟨⟨k, .plain0⟩, ⟨.instance, 2 * j⟩, none⟩])]
  pure ⟨[.sec (.coreModule core), .sec (.coreModule adaptor), .sec (.types ts.types.toList),
    .sec (.coreInstances [.instantiate 0 []]),
    .sec (.coreInstances [.instantiate 1 [("m", 0)]]),
    .sec (.aliases [⟨.core .memory, .coreExport 0 "memory"⟩]),
    .sec (.aliases [⟨.core .func, .coreExport 1 "cabi_realloc"⟩])] ++ lifts ++ worldExps ++ ifaceExps⟩

/-- The output of adaptor mode with interfaces. -/
structure Out where
  bytes : ByteArray
  ast : Option Ast
  adaptor : ByteArray
  plan : Plan

/-- **`wasm-jco new --adaptor`** for a full world. -/
def newAdaptorI (core : ByteArray) (wf : WorldFull) (alloc : String := "alloc") : Except String Out := do
  let p ← planI core wf alloc
  let a ← Adaptor.adaptorBytes p.md
  let c ← emitI core a p
  let b ← mustEncode "the component" c.encode
  pure ⟨b, c.toAst, a, p⟩

/-- As a tool output (the summary names the theorem). -/
def toToolOut (o : Out) : Tool.Out :=
  ⟨o.bytes, o.ast, false,
    s!"adaptor (verified adaptorLime, interfaces included: AdaptorI.newAdaptorI_correct), {o.plan.md.world.length} functions" ::
      o.plan.fns.map (fun x => s!"export {x.s.name}: canon lift of the adaptor's {x.s.name}"),
    [o.adaptor]⟩

end Silmaril.Wasm.JcoTool.AdaptorI
