module

public import Silmaril.Wasm.Game.Shared.Defs
public import Silmaril.Wasm.Game.SpecInst.Defs

/-!
# A host that writes the module's memory

A worked example for `Silmaril.Wasm.Game.Shared`:

```wat
(module
  (type (func))
  (type (func (result i32)))
  (import "env" "mem" (memory 1))          ;; memory 0, imported
  (import "env" "log" (func (type 0)))     ;; function 0
  (func (type 1)                           ;; function 1
    call 0                                 ;; log
    i32.const 0
    i32.load8_u)                           ;; the byte at address 0
  (export "get" (func 1)))
```

* `exLog`, `exLogStore` (a one-page zero memory and a host function for `log`),
  `exLogPrep` (the spec's `prepare?`), `exLogI` (the scalar instance);
* `poke s`: the store `s` with byte `42` written at address `0` of memory `0`
  (by `Memory.store`, when in bounds);
* `logHost`: the Core host whose `log` returns `values []` **in the store
  `poke s`** (at stores whose host functions are the instance's imports; it
  diverges otherwise). It satisfies `HostOk`, so it is an environment through
  `SEnv.ofHost`;
* `getQ`: the export question `get` in the instantiated store.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Game.SharedExample

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation

/-- The memory type `i32 1` (one page). -/
def memTy1 : MemoryType := ⟨.i32, ⟨1, none⟩⟩

/-- The module: imports a memory and `log`, exports `get`, which calls `log` and returns the
byte at address `0`. -/
def exLog : Module where
  types := [⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[], [.num (.int .i32)]⟩⟩]⟩]
  imports := [⟨"env", "mem", .memory memTy1⟩, ⟨"env", "log", .func ⟨0⟩⟩]
  funcs := [⟨⟨1⟩, [], [.call ⟨0⟩, .intConst .i32 0,
    .intLoad .i32 (some (.i8, .unsigned)) ⟨0⟩ memarg0]⟩]
  exports := [⟨"get", .func ⟨1⟩⟩]

/-- The validated type of `exLog`. -/
def exLogMT : CModuleType := (validate? exLog).getD ⟨[], []⟩

/-- One zero page. -/
def zeroPage : ByteArray := ⟨Array.replicate 65536 0⟩

/-- The store providing the imports: a one-page memory and a host function for `log`. -/
def exLogStore : Store Nat :=
  { mems := [⟨memTy1, zeroPage⟩],
    funcs := (importStore (CExternType.funcs exLogMT.imports)).funcs }

/-- The external addresses of the imports. -/
def exLogXas : List ExternAddr := [.mem 0, .func 0]

/-- The spec's allocation of `exLog` into `exLogStore`. -/
def exLogPrep : Config Nat × Option FuncIdx :=
  (prepare? evalConst? exLogStore exLog exLogXas).getD (⟨{}, {}, []⟩, none)

/-- The configuration of `$instantiate` (no segments, no start function). -/
def exLogC₀ : Config Nat := exLogPrep.1.withStart exLogPrep.2

/-- The scalar instance of `exLog`. -/
def exLogI : ScalarInstance where
  imports := [⟨[], []⟩]
  exports := [⟨[], [.num (.int .i32)]⟩]
  addrs := exportFuncAddrs exLogPrep.1.frame.module
  store := exLogPrep.1.store

/-- Write byte `42` at address `0` (when in bounds). -/
def pokeMem (mi : MemInst) : MemInst :=
  match Silmaril.Wasm.Execution.Memory.store mi.bytes 0 (42 : BitVec (8 * 1)) with
  | some b => { mi with bytes := b }
  | none => mi

/-- The store with byte `42` written at address `0` of memory `0`. -/
def poke (s : Store Nat) : Store Nat :=
  match s.mems[0]? with
  | some mi => s.setMem 0 (pokeMem mi)
  | none => s

/-- **The host writing the module's memory**: `log` (host code `0`, no arguments) returns no
values in the store `poke s`, at stores whose host functions are the instance's imports;
every other call diverges. -/
def logHost : HostSemantics Nat := fun h s vs out =>
  (h = 0 ∧ vs = [] ∧ exLogI.HostsTyped s ∧ out = .returned (poke s) (.values [])) ∨
    (¬ (h = 0 ∧ vs = [] ∧ exLogI.HostsTyped s) ∧ out = .diverged)

/-- The export question `get` in the instantiated store. -/
def getQ : exLogI.shF.Op := ⟨⟨0, by decide⟩, (exLogI.store, ⟨[], .nil⟩)⟩

/-- The answer `i32 42`. -/
def ans42 : Answer (exLogI.exports.get getQ.1) :=
  .values ⟨[.num ⟨.int .i32, 42⟩], .cons ⟨42, rfl⟩ .nil⟩

end Silmaril.Wasm.Game.SharedExample
