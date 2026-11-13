module

public import Silmaril.Wasm.Resource.Handle.Defs
public import Silmaril.Wasm.Verify.Check.Defs

@[expose] public section

/-!
# A verified handle provider: a single-slot allocator

A real Core 3.0 module, `provSlot`, that **provides** handles (exports `alloc`, `use`, `free`)
from a single slot, the mutable global `used : i32` (initially `0`):

```wat
(module
  (global $used (mut i32) (i32.const 0))
  (func (export "alloc") (result i32)                     ;; function 0
    global.get $used  (if (then unreachable))             ;; the slot is taken: trap
    i32.const 1  global.set $used  i32.const 1)          ;; hand out handle 1
  (func (export "use") (param i32))                       ;; function 1
  (func (export "free") (param i32)                       ;; function 2
    i32.const 0  global.set $used))
```

The provider handle sentence (`providerSpec`) holds of it: `alloc` never hands out a live handle
(it traps instead). Its proof (`Silmaril.Wasm.Resource.ProviderExample.Thms`) goes through the
program logic: `slotInv` is the store invariant indexed by protocol states,

* protocol state `none` (the environment broke the protocol): no constraint on the slot;
* `some []` (no live handle): `used = 0`;
* `some [i32 1]` (handle `1` live): `used = 1`;

together with the shape of the store (the functions are those of the instance, and the global
exists).

A Silmaril addition.
-/

namespace Silmaril.Wasm.Resource

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm.Verify
open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core

/-! ## The module -/

/-- `[] → [i32]`. -/
def tySlotAlloc : RecType := ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩
/-- `[i32] → []`. -/
def tySlotHandle : RecType := ⟨[⟨true, [], .func ⟨[.i32], []⟩⟩]⟩

/-- The body of `alloc`: trap if the slot is taken, else take it and return handle `1`. -/
def slotAllocBody : List Instr :=
  [.globalGet ⟨0⟩, .if_ .empty [.unreachable] [], .intConst .i32 1, .globalSet ⟨0⟩,
    .intConst .i32 1]

/-- The body of `free`: release the slot. -/
def slotFreeBody : List Instr := [.intConst .i32 0, .globalSet ⟨0⟩]

/-- `alloc`. -/
def slotAllocFn : Func := ⟨⟨0⟩, [], slotAllocBody⟩
/-- `use` (does nothing). -/
def slotUseFn : Func := ⟨⟨1⟩, [], []⟩
/-- `free`. -/
def slotFreeFn : Func := ⟨⟨1⟩, [], slotFreeBody⟩

/-- **The single-slot handle provider.** -/
def provSlot : Module where
  types := [tySlotAlloc, tySlotHandle]
  globals := [⟨⟨.var, .i32⟩, [.intConst .i32 0]⟩]
  funcs := [slotAllocFn, slotUseFn, slotFreeFn]
  exports := [⟨"alloc", .func ⟨0⟩⟩, ⟨"use", .func ⟨1⟩⟩, ⟨"free", .func ⟨2⟩⟩]

/-- The instance of `provSlot` (computed by `instance?`). -/
def slotI : ScalarInstance := instOf provSlot

/-- Export `0` of `slotI`, `alloc`. -/
def slotAlloc : (ifaceOf slotI).Exp := ⟨0, by decide +kernel⟩
/-- Export `1` of `slotI`, `use`. -/
def slotUse : (ifaceOf slotI).Exp := ⟨1, by decide +kernel⟩
/-- Export `2` of `slotI`, `free`. -/
def slotFree : (ifaceOf slotI).Exp := ⟨2, by decide +kernel⟩

/-- The provider handle sentence with exports `0`, `1`, `2` as `alloc`, `use`, `free`, read on
the moves of an instance `I` (the protocol of `ProvSat`). -/
abbrev slotProto {I : ScalarInstance} (h0 : 0 < I.exports.length) (h1 : 1 < I.exports.length)
    (h2 : 2 < I.exports.length) : Protocol (Option (List Val)) (Move I.E I.F) :=
  (providerSpec (X := ifaceOf I) ⟨0, h0⟩ ⟨1, h1⟩ ⟨2, h2⟩).comap (moveEvent (X := ifaceOf I))

/-! ## The invariant -/

/-- The function at address `a` of `s` has code `c`, a function type with `np` parameters and
`nr` results, and its module's global `0` is at address `ga`. -/
def SlotFuncAt (s : Store Nat) (a : Nat) (c : Func) (np nr ga : Nat) : Prop :=
  ∃ fi : FuncInst Nat, s.funcs[a]? = some fi ∧ fi.code = .wasm c ∧
    fi.module.globals[0]? = some ga ∧
    ∃ ps rs : Ty (.list .val), Expand fi.type (.func ps rs) ∧ ps.length = np ∧ rs.length = nr

/-- The protocol state agrees with the slot value `c`. -/
def SlotState (q : Option (List Val)) (c : BitVec 32) : Prop :=
  q = none ∨ (q = some [] ∧ c = 0) ∨ (q = some [.i32 1] ∧ c = 1)

/-- **The store invariant** of the provider at protocol state `q`, for an instance whose
initial store is `s₀` and whose global `used` is at `ga`: the functions are those of `s₀`, and
the slot holds an `i32` agreeing with `q`. -/
def slotInv (s₀ : Store Nat) (ga : Nat) (q : Option (List Val)) (s : Store Nat) : Prop :=
  s.funcs = s₀.funcs ∧
    ∃ (g : GlobalInst) (c : BitVec 32), s.globals[ga]? = some g ∧ g.value = .i32 c ∧ SlotState q c

/-- **The shape of a single-slot provider instance** with its global `used` at `ga`: three
exports `alloc : [] → [i32]`, `use, free : [i32] → []` implemented by the three functions of
`provSlot`, all of whose global `0` is `ga`, and `used = 0` initially. `slotI` has this shape
(`slotI_shape`). -/
structure SlotShape (I : ScalarInstance) (ga : Nat) : Prop where
  params : I.exports.map FnType.params = [[], [.num (.int .i32)], [.num (.int .i32)]]
  alloc : SlotFuncAt I.store (I.addrs.getD 0 0) slotAllocFn 0 1 ga
  use : SlotFuncAt I.store (I.addrs.getD 1 0) slotUseFn 1 0 ga
  free : SlotFuncAt I.store (I.addrs.getD 2 0) slotFreeFn 1 0 ga
  init : slotInv I.store ga (some []) I.store

end Silmaril.Wasm.Resource
