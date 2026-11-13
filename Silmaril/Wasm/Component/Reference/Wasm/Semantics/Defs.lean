module

public import Silmaril.Wasm.Component.Reference.Wasm.Semantics.Memory.Defs
public import Silmaril.Wasm.Component.Engine.Laws

/-!
# `WasmSemantics`: the core-level interface, with `CoreEngine` as a derived view

This is the interface of issue #846 (`WasmInterp`), in the shape issue #878 needs: one
core-level description of a WebAssembly semantics from which the component model's
`Component.Engine.CoreEngine` is **derived by a single adapter**, rather than a second,
parallel interface.

## Why not #846's five-field sketch

#846 proposes

```
structure WasmInterp where
  Module : Type ; Valid : Module → Prop ; Input : Type ; Behaviour : Type
  sem : Module → Input → Behaviour → Prop
```

That is a *behavioural* view: it says what a whole run of a whole module looks like. The
component model needs strictly more, because a component instance is not a closed program: the
canonical ABI reads and writes the instance's linear memory between calls, resolves funcrefs
out of its tables, allocates one host function per lowering site, and suspends an activation at
a host callout to let the component scheduler interleave it with others. None of that is
expressible as a predicate on `Module × Input × Behaviour`.

`WasmSemantics` is therefore the *configuration-level* interface -- modules and validity, a
host-indexed store, addresses, instantiation, invocation, a host-free step relation and an
observable status -- and #846's behavioural view is recovered from it as a definition
(`Silmaril/Wasm/Semantics/Interp.lean`), not assumed as a second primitive.

## Structure, not class

`WasmSemantics` is a `structure`, following `CoreEngine`. A semantics is a *value*, not a
canonical choice per type: `v2 o` and `v2Det o` are two semantics over the very same carriers,
as are `core3 o` and `core3Spec o`, so typeclass resolution has nothing to dispatch on. The
laws, by contrast, are a `class` on that value (`WasmSemantics.Lawful`, in
`Silmaril/Wasm/Semantics/Laws.lean`), exactly as `CoreEngine.Lawful` is.

## What is factored out

The one genuine sublanguage shared by every engine is linear memory: `MemoryView`
(`Silmaril/Wasm/Semantics/Memory.lean`) replaces the four byte-level accessors by a lookup/update
pair, and discharges eight of `CoreEngine.Lawful`'s twenty-three fields from four pointwise
coherence facts. Everything else `CoreEngine` asks for is genuinely semantics-level and is kept
here.

Not here: store extension and the laws (`Semantics/Laws.lean`), the behavioural view
(`Semantics/Interp.lean`), and any particular semantics.
-/

@[expose] public section

namespace Silmaril.Wasm.Semantics

open Silmaril.Wasm.Component.Engine

/-- A core-level WebAssembly semantics: syntax and validity, static types, a host-indexed
store with addresses and instances, instantiation, host-function allocation, linear memory
(through a `MemoryView`), funcref tables, and store-free activations with a host-free step
relation and an observable status. See the module docstring. -/
structure WasmSemantics where
  /-- Core modules. -/
  Module : Type
  /-- Module validity. -/
  Valid : Module → Prop
  /-- Function types of this semantics. -/
  FuncType : Type
  [decEqFuncType : DecidableEq FuncType]
  /-- External types of this semantics. -/
  ExternType : Type
  /-- Extern subtyping `a <: b`, used for import matching. -/
  ExternSub : ExternType → ExternType → Prop
  /-- Embedding of flat numeric signatures (the signatures host functions have). -/
  ofFlatType : V1.FuncType → FuncType
  /-- The flat numeric signature of a function type, if it has one. -/
  flatType? : FuncType → Option V1.FuncType
  /-- Imports of a module: module name, field name, expected type (positional order). -/
  importTypes : Module → List (String × String × ExternType)
  /-- Exports of a module and their types. -/
  exportTypes : Module → List (String × ExternType)
  /-- The store, indexed by the type `H` of host-code identifiers. -/
  Store : Type → Type
  /-- The empty store. -/
  empty : (H : Type) → Store H
  /-- Function addresses. -/
  FuncAddr : Type
  /-- Table addresses. -/
  TableAddr : Type
  /-- Global addresses. -/
  GlobalAddr : Type
  [decEqFuncAddr : DecidableEq FuncAddr]
  [decEqTableAddr : DecidableEq TableAddr]
  [decEqGlobalAddr : DecidableEq GlobalAddr]
  /-- Linear memory: addresses, instances, and the lookup/update pair they are accessed by.
  The four byte-level accessors the component runtime uses are derived from it. -/
  mem : MemoryView Store
  /-- External values (exports of instances, arguments of instantiation). -/
  ExternVal : Type
  /-- The function address of an external value, if it is a function. -/
  asFunc? : ExternVal → Option FuncAddr
  /-- The memory address of an external value, if it is a memory. -/
  asMemory? : ExternVal → Option mem.MemAddr
  /-- The table address of an external value, if it is a table. -/
  asTable? : ExternVal → Option TableAddr
  /-- The global address of an external value, if it is a global. -/
  asGlobal? : ExternVal → Option GlobalAddr
  /-- A function address as an external value. -/
  ofFunc : FuncAddr → ExternVal
  /-- Module instances. -/
  Inst : Type
  /-- The exports of a module instance. -/
  exports : Inst → List (String × ExternVal)
  /-- The type of an external value in a store. -/
  externType? : {H : Type} → Store H → ExternVal → Option ExternType
  /-- Instantiation: allocation plus segment initialization, with positional imports. The start
  function is returned, not run. -/
  prepare? : {H : Type} → Store H → Module → List ExternVal →
    Option (Store H × Inst × Option FuncAddr)
  /-- Allocate a host function with a flat signature and host code `h`. -/
  allocHost : {H : Type} → Store H → V1.FuncType → H → Store H × FuncAddr
  /-- The type of a function in a store. -/
  funcType? : {H : Type} → Store H → FuncAddr → Option FuncType
  /-- The address type of a table. -/
  tableAddrType? : {H : Type} → Store H → TableAddr → Option AddrType
  /-- Funcref table read: `none` when out of bounds, `some none` for a null entry. -/
  tableFunc? : {H : Type} → Store H → TableAddr → Nat → Option (Option FuncAddr)
  /-- Store-free activations. -/
  Thread : Type → Type
  /-- A fresh activation calling a function with arguments. -/
  invoke : {H : Type} → FuncAddr → List FlatValue → Thread H
  /-- The observable status of an activation in a store. -/
  status : {H : Type} → Store H → Thread H → Status H
  /-- The host-free step relation on configurations. -/
  Internal : {H : Type} → Store H × Thread H → Store H × Thread H → Prop
  /-- Resume a parked activation with a host result, observed at the given store. -/
  resume : {H : Type} → Store H → Thread H → CallResult → Thread H

attribute [instance] WasmSemantics.decEqFuncType WasmSemantics.decEqFuncAddr
  WasmSemantics.decEqTableAddr WasmSemantics.decEqGlobalAddr

namespace WasmSemantics

variable (S : WasmSemantics)

/-- Memory addresses of a semantics. -/
abbrev MemAddr : Type := S.mem.MemAddr

/-- A configuration: a store together with one activation. -/
abbrev Config (H : Type) : Type := S.Store H × S.Thread H

/-- The core engine the component model consumes, read off a semantics. Every field is either a
field of `S` or a derived field of its `MemoryView`; nothing is invented, so each projection of
`S.toCoreEngine` is *definitionally* the corresponding field of `S` (this is what lets the
existing engines be redefined through `WasmSemantics` without disturbing a single downstream
proof).

It is `@[reducible]` for the same reason the engines themselves are `abbrev`s: downstream
unification and instance search must be able to see through `(S.toCoreEngine).Store` to the
concrete store type. -/
@[reducible] def toCoreEngine : CoreEngine where
  Module := S.Module
  Valid := S.Valid
  FuncType := S.FuncType
  decEqFuncType := S.decEqFuncType
  ExternType := S.ExternType
  ExternSub := S.ExternSub
  ofFlatType := S.ofFlatType
  flatType? := S.flatType?
  importTypes := S.importTypes
  exportTypes := S.exportTypes
  Store := S.Store
  empty := S.empty
  FuncAddr := S.FuncAddr
  MemAddr := S.mem.MemAddr
  TableAddr := S.TableAddr
  GlobalAddr := S.GlobalAddr
  decEqFuncAddr := S.decEqFuncAddr
  decEqMemAddr := S.mem.decEqMemAddr
  decEqTableAddr := S.decEqTableAddr
  decEqGlobalAddr := S.decEqGlobalAddr
  ExternVal := S.ExternVal
  asFunc? := S.asFunc?
  asMemory? := S.asMemory?
  asTable? := S.asTable?
  asGlobal? := S.asGlobal?
  ofFunc := S.ofFunc
  Inst := S.Inst
  exports := S.exports
  externType? := S.externType?
  prepare? := S.prepare?
  allocHost := S.allocHost
  funcType? := S.funcType?
  memAddrType? := S.mem.addrType?
  memSize? := S.mem.size?
  memRead? := S.mem.read?
  memWrite? := S.mem.write?
  tableAddrType? := S.tableAddrType?
  tableFunc? := S.tableFunc?
  Thread := S.Thread
  invoke := S.invoke
  status := S.status
  Internal := S.Internal
  resume := S.resume

/-- Store extension of a semantics: that of its engine view. -/
abbrev Extends {H : Type} (s s' : S.Store H) : Prop := S.toCoreEngine.Extends s s'

/-- Finite host-free runs. -/
abbrev Steps {H : Type} : S.Config H → S.Config H → Prop := S.toCoreEngine.Steps

/-- An infinite host-free trace. -/
abbrev Diverges {H : Type} (c : S.Config H) : Prop := S.toCoreEngine.Diverges c

end WasmSemantics

end Silmaril.Wasm.Semantics
