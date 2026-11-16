module

public import Silmaril.Wasm.Component.Engine.Interface

/-!
# The static part of a core engine

A core engine (`CoreEngine`) has a static part, its module, type and address types, and a
store-dependent part, the store family and every operation that takes a store
(`Engine.Sim`). Component-level runtime data mentions only the static part: canonical options
hold memory and function addresses, tasks and callers hold options, item values hold modules
and extern values.

* `CoreEngine.Static`: the types such data uses, with decidable equality of addresses.
* `CoreEngine.toStatic E`: the static part of `E`, also a coercion. It is reducible, so
  `E.toStatic.FuncAddr` is `E.FuncAddr` for instance search and `simp`.

The data types of the component runtime (`Runtime.CanonOpts`, `CanonHost`, `Task`, `Caller`,
`Canon.Call`, `Canon.Ret`, `Instantiate.ItemVal`, …) are indexed by `CoreEngine.Static`. Two
engines with the same static part, such as `E` and `E.withStore I`, therefore have the same
types of such data by definition: `CanonHost (E.withStore I)` and `CanonHost E` are both
`CanonHost E.toStatic` up to unfolding. This is what lets a store map relate the component
stores of the two engines (`Machine.Transfer`).

* `CoreEngine.CoreView E H`: the read-only queries of a core store that component-level
  programs use (extern types, a function type test against a flat signature, memory and table
  address types, memory size, contents and write bounds, funcref table entries, and the results
  of host-function allocation and core instantiation), with results in the static part.
* `CoreEngine.view E s`: these queries on the store `s` of `E`. The reference machine answers the
  operation `Canon.Op.readCore` with `E.view` of its core store, so specification programs never
  see a store of `E` itself.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine

/-- The static part of a core engine that component-level data refers to. -/
structure CoreEngine.Static where
  /-- Core modules. -/
  Module : Type
  /-- Core extern types. -/
  ExternType : Type
  /-- Function addresses. -/
  FuncAddr : Type
  /-- Memory addresses. -/
  MemAddr : Type
  /-- Table addresses. -/
  TableAddr : Type
  [decEqFuncAddr : DecidableEq FuncAddr]
  [decEqMemAddr : DecidableEq MemAddr]
  [decEqTableAddr : DecidableEq TableAddr]
  /-- External values. -/
  ExternVal : Type

attribute [instance] CoreEngine.Static.decEqFuncAddr CoreEngine.Static.decEqMemAddr
  CoreEngine.Static.decEqTableAddr

/-- The static part of `E`. -/
@[reducible] def CoreEngine.toStatic (E : CoreEngine) : CoreEngine.Static where
  Module := E.Module
  ExternType := E.ExternType
  FuncAddr := E.FuncAddr
  MemAddr := E.MemAddr
  TableAddr := E.TableAddr
  ExternVal := E.ExternVal

instance : Coe CoreEngine CoreEngine.Static := ⟨CoreEngine.toStatic⟩

/-- The read-only queries of a core store over host code `H`, with results in the static part:
extern types, a function type test against a flat signature, memory and table address types,
memory size, contents and write bounds, funcref table entries, and the results (without the
new store) of host-function allocation and of core instantiation. -/
structure CoreEngine.CoreView (E : CoreEngine.Static) (H : Type) where
  /-- The type of an external value. -/
  externType? : E.ExternVal → Option E.ExternType
  /-- Whether a function has the core type of a flat signature. -/
  funcHasType : E.FuncAddr → V1.FuncType → Bool
  /-- Address type of a memory. -/
  memAddrType? : E.MemAddr → Option AddrType
  /-- Memory size in bytes. -/
  memSize? : E.MemAddr → Option Nat
  /-- Read `len` bytes at `start`. -/
  memRead? : E.MemAddr → (start len : Nat) → Option ByteArray
  /-- Whether writing `bytes` at `start` succeeds. -/
  memWriteOk : E.MemAddr → (start : Nat) → ByteArray → Bool
  /-- Address type of a table. -/
  tableAddrType? : E.TableAddr → Option AddrType
  /-- Funcref table read: `none` when out of bounds, `some none` for a null entry. -/
  tableFunc? : E.TableAddr → Nat → Option (Option E.FuncAddr)
  /-- The address a host-function allocation returns. -/
  allocAddr : V1.FuncType → H → E.FuncAddr
  /-- Core instantiation: the exports of the new instance and its start function. -/
  prepare? : E.Module → List E.ExternVal →
    Option (List (String × E.ExternVal) × Option E.FuncAddr)

/-- The queries of `E` on the store `s`. -/
def CoreEngine.view (E : CoreEngine) {H : Type} (s : E.Store H) : CoreEngine.CoreView E H where
  externType? := E.externType? s
  funcHasType f ft := E.funcType? s f == some (E.ofFlatType ft)
  memAddrType? := E.memAddrType? s
  memSize? := E.memSize? s
  memRead? := E.memRead? s
  memWriteOk m start bytes := (E.memWrite? s m start bytes).isSome
  tableAddrType? := E.tableAddrType? s
  tableFunc? := E.tableFunc? s
  allocAddr ty h := (E.allocHost s ty h).2
  prepare? m imports := (E.prepare? s m imports).map fun r => (E.exports r.2.1, r.2.2)

end Silmaril.Wasm.Component.Engine
