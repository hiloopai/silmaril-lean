module

public import Silmaril.Wasm.Component.Engine.Laws

/-!
# Engines that differ only in their store

A core engine (`CoreEngine`) has a static part (modules, types, addresses, instances, store-free
threads and `invoke`) and a store-dependent part (the store family and every operation that takes a
store). Two representations of the same engine, for example Core 3.0 with `ByteArray` memories and
with `KMem` trees (`Engine.Core3K`), share the static part and differ in the store.

* `CoreEngine.StoreImpl E`: the store-dependent part of an engine over the static part of `E`: a
  store family `Store`, `empty`, `externType?`, `prepare?`, `allocHost`, `funcType?`, the memory
  and table accessors, `status`, `Internal` and `resume`.
* `E.withStore I`: the engine with `E`'s static part and `I`'s stores. Every static field is
  `E`'s by definition, so the two engines have the same modules, types, addresses and threads.
* `CoreEngine.StoreSim E I`: a store map `φ : I.Store H → E.Store H` that commutes with every
  store-dependent operation, and a functional bisimulation for `Internal`: every internal step of
  `E.withStore I` maps to one of `E` (`internal`), and every internal step of `E` from a mapped
  configuration is the image of one of `E.withStore I` (`internal_lift`).
* `CoreEngine.ExecSim S X X'`: executable steppers of the two engines that commute with `φ`.

`Engine.Sim.Thms` carries runs, divergence, store extension, the engine laws and the fuel loop
across a `StoreSim`.

**Scope.** This is a simulation of core engines. The component machine (REF, `Component.Machine`)
is parametric in its engine, but its configurations hold specification programs whose
continuations receive the whole component store (`Canon.Op.get`, `Canon.Op.modify`), so a
`StoreSim` does not by itself carry REF runs from one engine to the other: that needs a relation
on programs, proved for every REF program (see `docs/projects/wasm-memrep.md`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine

namespace CoreEngine

/-- The store-dependent part of a core engine with `E`'s static part. -/
structure StoreImpl (E : CoreEngine) where
  /-- The store family. -/
  Store : Type → Type
  empty : (H : Type) → Store H
  externType? : {H : Type} → Store H → E.ExternVal → Option E.ExternType
  prepare? : {H : Type} → Store H → E.Module → List E.ExternVal →
    Option (Store H × E.Inst × Option E.FuncAddr)
  allocHost : {H : Type} → Store H → V1.FuncType → H → Store H × E.FuncAddr
  funcType? : {H : Type} → Store H → E.FuncAddr → Option E.FuncType
  memAddrType? : {H : Type} → Store H → E.MemAddr → Option AddrType
  memSize? : {H : Type} → Store H → E.MemAddr → Option Nat
  memRead? : {H : Type} → Store H → E.MemAddr → (start len : Nat) → Option ByteArray
  memWrite? : {H : Type} → Store H → E.MemAddr → (start : Nat) → ByteArray →
    Option (Store H)
  tableAddrType? : {H : Type} → Store H → E.TableAddr → Option AddrType
  tableFunc? : {H : Type} → Store H → E.TableAddr → Nat → Option (Option E.FuncAddr)
  status : {H : Type} → Store H → E.Thread H → Status H
  Internal : {H : Type} → Store H × E.Thread H → Store H × E.Thread H → Prop
  resume : {H : Type} → Store H → E.Thread H → CallResult → E.Thread H

/-- The engine with `E`'s static part and the stores of `I`. -/
abbrev withStore (E : CoreEngine) (I : E.StoreImpl) : CoreEngine :=
  { E with
    Store := I.Store
    empty := I.empty
    externType? := I.externType?
    prepare? := I.prepare?
    allocHost := I.allocHost
    funcType? := I.funcType?
    memAddrType? := I.memAddrType?
    memSize? := I.memSize?
    memRead? := I.memRead?
    memWrite? := I.memWrite?
    tableAddrType? := I.tableAddrType?
    tableFunc? := I.tableFunc?
    status := I.status
    Internal := I.Internal
    resume := I.resume }

/-- **An engine simulation**: a store map from `E.withStore I` to `E` commuting with every
store-dependent operation, and a functional bisimulation of the internal steps. -/
structure StoreSim (E : CoreEngine) (I : E.StoreImpl) where
  /-- The store map. -/
  φ : {H : Type} → I.Store H → E.Store H
  empty : ∀ H, φ (I.empty H) = E.empty H
  externType? : ∀ {H : Type} (s : I.Store H) v, E.externType? (φ s) v = I.externType? s v
  prepare? : ∀ {H : Type} (s : I.Store H) m vs,
    E.prepare? (φ s) m vs = (I.prepare? s m vs).map fun r => (φ r.1, r.2)
  allocHost : ∀ {H : Type} (s : I.Store H) ft h,
    E.allocHost (φ s) ft h = (φ (I.allocHost s ft h).1, (I.allocHost s ft h).2)
  funcType? : ∀ {H : Type} (s : I.Store H) a, E.funcType? (φ s) a = I.funcType? s a
  memAddrType? : ∀ {H : Type} (s : I.Store H) m, E.memAddrType? (φ s) m = I.memAddrType? s m
  memSize? : ∀ {H : Type} (s : I.Store H) m, E.memSize? (φ s) m = I.memSize? s m
  memRead? : ∀ {H : Type} (s : I.Store H) m st len,
    E.memRead? (φ s) m st len = I.memRead? s m st len
  memWrite? : ∀ {H : Type} (s : I.Store H) m st bs,
    E.memWrite? (φ s) m st bs = (I.memWrite? s m st bs).map φ
  tableAddrType? : ∀ {H : Type} (s : I.Store H) t,
    E.tableAddrType? (φ s) t = I.tableAddrType? s t
  tableFunc? : ∀ {H : Type} (s : I.Store H) t i, E.tableFunc? (φ s) t i = I.tableFunc? s t i
  status : ∀ {H : Type} (s : I.Store H) t, E.status (φ s) t = I.status s t
  /-- Internal steps map to internal steps. -/
  internal : ∀ {H : Type} {s s' : I.Store H} {t t'},
    I.Internal (s, t) (s', t') → E.Internal (φ s, t) (φ s', t')
  /-- Internal steps from a mapped configuration are images of internal steps. -/
  internal_lift : ∀ {H : Type} {s : I.Store H} {t c'},
    E.Internal (φ s, t) c' → ∃ s' t', I.Internal (s, t) (s', t') ∧ c' = (φ s', t')
  resume : ∀ {H : Type} (s : I.Store H) t r, E.resume (φ s) t r = I.resume s t r

namespace StoreSim

variable {E : CoreEngine} {I : E.StoreImpl} (S : E.StoreSim I)

/-- The configuration map. -/
def map {H : Type} (c : (E.withStore I).Config H) : E.Config H := (S.φ c.1, c.2)

end StoreSim

/-- **Executable steppers that commute with a simulation**: stepping a mapped configuration with
`X` is mapping the step of `X'`. -/
structure ExecSim {E : CoreEngine} {I : E.StoreImpl} (S : E.StoreSim I) (X : E.Exec)
    (X' : (E.withStore I).Exec) : Prop where
  step? : ∀ {H : Type} (c : (E.withStore I).Config H), X.step? (S.map c) = (X'.step? c).map S.map

end CoreEngine

end Silmaril.Wasm.Component.Engine
