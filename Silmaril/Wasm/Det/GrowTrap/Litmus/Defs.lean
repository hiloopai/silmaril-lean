module

public import Silmaril.Wasm.Det.GrowTrap.Defs
public import Silmaril.Wasm.Execution.Core.Exec.Prepare
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateInit

/-!
# Litmus module for subset 2 (allocation failure traps)

```wat
(module
  (memory 0 1)                                   ;; no page, at most one
  (func (export "guarded") (result i32) (local i32)                        ;; function 0
    i32.const 1  memory.grow 0  local.tee 0  i32.const -1  i32.eq
    if  unreachable  end
    local.get 0)
  (func (export "plain") (result i32)                                      ;; function 1
    i32.const 1  memory.grow 0  i32.const -1  i32.eq  if  unreachable  end
    memory.size 0)
  (func (export "unguarded") (result i32)                                  ;; function 2
    i32.const 1  memory.grow 0)
  (func (export "caller") (result i32)                                     ;; function 3
    call 0  drop  i32.const 0  i32.const 42  i32.store  i32.const 0  i32.load))
```

* functions `0`, `1` grow the memory behind the trap-on-failure guard (with and without
  `local.tee`); function `3` calls function `0` and then writes and reads the memory: they pass
  the check of subset 2 and are deterministic modulo traps and imports at every profile;
* function `2` returns the result of an unguarded `memory.grow`: at a profile where the grow may
  fail and may succeed (`Profile.spec`), it returns `0` (the old size) or `-1`, so it is not
  deterministic, and neither is the module;
* `growMod` is a silmaril-lean Core `Module`, `growStore` its allocation by `prepare?` into the
  empty store (no start function, no segments).

Theorems in `Silmaril.Wasm.Det.GrowTrap.Litmus.Thms`. New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.GrowTrap.Litmus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- `memarg 0 0`. -/
def ma0 : MemArg := ⟨0, 0⟩

/-- The trap-on-failure guard. -/
def guard : List Instr :=
  [.intConst .i32 (BitVec.allOnes 32), .intRelOp .i32 .eq, .if_ .empty [.unreachable] []]

/-- Body of function `0`: grow, `local.tee`, guard, return the old size. -/
def guardedBody : List Instr :=
  [.intConst .i32 1, .memoryGrow ⟨0⟩, .localTee ⟨0⟩] ++ guard ++ [.localGet ⟨0⟩]

/-- Body of function `1`: grow, guard, return the size. -/
def plainBody : List Instr := [.intConst .i32 1, .memoryGrow ⟨0⟩] ++ guard ++ [.memorySize ⟨0⟩]

/-- Body of function `2`: an unguarded grow. -/
def unguardedBody : List Instr := [.intConst .i32 1, .memoryGrow ⟨0⟩]

/-- Body of function `3`: call function `0`, then write and read memory. -/
def callerBody : List Instr :=
  [.call ⟨0⟩, .drop, .intConst .i32 0, .intConst .i32 42, .intStore .i32 none ⟨0⟩ ma0,
    .intConst .i32 0, .intLoad .i32 none ⟨0⟩ ma0]

/-- The litmus module. -/
def growMod : Module where
  types := [⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩]
  memories := [⟨.i32, ⟨0, some 1⟩⟩]
  funcs := [⟨⟨0⟩, [.i32], guardedBody⟩, ⟨⟨0⟩, [], plainBody⟩, ⟨⟨0⟩, [], unguardedBody⟩,
    ⟨⟨0⟩, [], callerBody⟩]
  exports := [⟨"guarded", .func ⟨0⟩⟩, ⟨"plain", .func ⟨1⟩⟩, ⟨"unguarded", .func ⟨2⟩⟩,
    ⟨"caller", .func ⟨3⟩⟩]

/-- The spec's allocation of `growMod` into the empty store. -/
def growPrep : Config Nat × Option FuncIdx :=
  (prepare? evalConst? ({} : Store Nat) growMod []).getD (⟨{}, {}, []⟩, none)

/-- The store of the instance of `growMod`. -/
def growStore : Store Nat := growPrep.1.store

/-- The entry functions of the instance: its four exports. -/
def growEntry (a : Nat) : Prop := a < 4

instance (a : Nat) : Decidable (growEntry a) := inferInstanceAs (Decidable (a < 4))

end Silmaril.Wasm.Det.GrowTrap.Litmus
