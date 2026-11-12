module

public import Silmaril.Wasm.Component.Reference.Sound.Defs
public import Silmaril.Wasm.Component.Reference.Example.Defs
public import Silmaril.Wasm.Component.Reference.Link.Defs

/-!
# Litmus components for IR soundness

Three simple components over one-function Core 3.0 modules
`(func (param i32 i32) (result i32) local.get 0 local.get 1 i32.<op>)`:

* `adderS`: `add(a: u32, b: u32) -> u32` over `i32.add` (the adder);
* `recordS`: `sum(p: record { f: u32, fx: u32 }) -> u32` over `i32.add`: a record crosses the
  boundary, flattened to two `i32`s;
* `optionS`: `get-or-zero(p: option<u32>) -> u32` over `i32.mul`: a variant crosses the boundary,
  flattened to its discriminant and payload slot, so the result is the payload or `0`.

`binStore op` is the store of the module's instance, `binInst op` the instance.

`twoS` exports `add` and `sum` together; it checks that the second export of `toRef` names the
second lifted function.

Two components delimit the hypotheses of `RefToSpecAll`:

* `oobS`: `f() -> u32` over a module whose active data segment is out of bounds of its empty
  memory. The module validates but does not instantiate, so the module has no instance
  (`Simple.Inst` fails) and the reference machine traps during instantiation;
* `badNameS`: the adder exported under the name `a_b`, which is not a kebab-case name; the
  reference validator rejects it although the fragment conditions hold.

With an import: `fwdS` imports `g: func(u32) -> u32`, lowers it into the core module
`fwdCore3`, which imports it as `env.g` and re-exports it as `f`, and lifts `f` as its export
`f: func(u32) -> u32`. `fwdStore` is the store of the module's instance against one host
function, `fwdInst` the instance.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference.Litmus

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm (IntBinOp)

/-- `(type (func (param i32 i32) (result i32))) (func (export "f") (type 0) local.get 0
local.get 1 i32.<op>)`. -/
def binCore3 (op : IntBinOp) : Silmaril.Wasm.Module where
  types := [⟨[⟨true, [], .func ⟨[.i32, .i32], [.i32]⟩⟩]⟩]
  funcs := [⟨⟨0⟩, [], [.localGet ⟨0⟩, .localGet ⟨1⟩, .intBinOp .i32 op]⟩]
  exports := [⟨"f", .func ⟨0⟩⟩]

/-- The module with its export interface. -/
def binMod (op : IntBinOp) : NumModule :=
  ⟨binCore3 op, [("f", ⟨[.int .i32, .int .i32], [.int .i32]⟩)]⟩

/-- `add(a: u32, b: u32) -> u32`. -/
def adderS : Simple := ⟨binMod .add, [⟨"add", ⟨[.u32, .u32], [.u32]⟩, 0⟩]⟩

/-- `sum(p: record { f: u32, fx: u32 }) -> u32`. -/
def recordS : Simple := ⟨binMod .add, [⟨"sum", ⟨[.record [.u32, .u32]], [.u32]⟩, 0⟩]⟩

/-- `get-or-zero(p: option<u32>) -> u32`. -/
def optionS : Simple := ⟨binMod .mul, [⟨"get-or-zero", ⟨[.option .u32], [.u32]⟩, 0⟩]⟩

/-- The store of the instance of `binCore3 op` (instantiated against no imports). -/
def binStore (op : IntBinOp) : Silmaril.Wasm.Execution.Core.Store Nat :=
  match Silmaril.Wasm.Execution.Core.instantiateOnce? (Silmaril.Wasm.Game.importStore [])
      (binCore3 op) [] with
  | some (s, _, _) => s
  | none => {}

/-- The instance of `binCore3 op`. -/
def binInst (op : IntBinOp) : Silmaril.Wasm.Game.ScalarInstance where
  imports := []
  exports := [⟨[.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]⟩]
  addrs := [0]
  store := binStore op

/-- `add` and `sum` side by side: two exports over the same core function (a test of the function
indices of `toRef`). -/
def twoS : Simple :=
  ⟨binMod .add, [⟨"add", ⟨[.u32, .u32], [.u32]⟩, 0⟩, ⟨"sum", ⟨[.record [.u32, .u32]], [.u32]⟩, 0⟩]⟩

/-- `(type (func (result i32))) (memory 0 0) (func (export "f") (type 0) i32.const 0)
(data (i32.const 0) "\00")`: the data segment does not fit the empty memory. -/
def oobCore3 : Silmaril.Wasm.Module where
  types := [⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩]
  memories := [⟨.i32, ⟨0, some 0⟩⟩]
  funcs := [⟨⟨0⟩, [], [.intConst .i32 0]⟩]
  data := [⟨⟨#[0]⟩, .active ⟨0⟩ [.intConst .i32 0]⟩]
  exports := [⟨"f", .func ⟨0⟩⟩]

/-- `f() -> u32` over `oobCore3`. -/
def oobS : Simple := ⟨⟨oobCore3, [("f", ⟨[], [.int .i32]⟩)]⟩, [⟨"f", ⟨[], [.u32]⟩, 0⟩]⟩

/-- The adder exported as `a_b` (not a kebab-case name). -/
def badNameS : Simple := ⟨binMod .add, [⟨"a_b", ⟨[.u32, .u32], [.u32]⟩, 0⟩]⟩

/-! ## A component with an import -/

/-- `(type (func (param i32) (result i32))) (import "env" "g" (func (type 0)))
(export "f" (func 0))`: the import, re-exported. -/
def fwdCore3 : Silmaril.Wasm.Module where
  types := [⟨[⟨true, [], .func ⟨[.i32], [.i32]⟩⟩]⟩]
  imports := [⟨"env", "g", .func ⟨0⟩⟩]
  exports := [⟨"f", .func ⟨0⟩⟩]

/-- The module with its import and export interfaces. -/
def fwdMod : ImpModule :=
  ⟨fwdCore3, [("g", ⟨[.int .i32], [.int .i32]⟩)], [("f", ⟨[.int .i32], [.int .i32]⟩)]⟩

/-- `(import "g" (func (param u32) (result u32)))`, lowered into `fwdCore3`, whose export `f`
is lifted as `f: func(u32) -> u32`. -/
def fwdS : SimpleI := ⟨fwdMod, [("g", ⟨[.u32], [.u32]⟩)], [⟨"f", ⟨[.u32], [.u32]⟩, 0⟩]⟩

/-- The closed import types of `fwdCore3`. -/
def fwdImports : List Silmaril.Wasm.Validation.DefType :=
  match Silmaril.Wasm.Validation.validate? fwdCore3 with
  | some mt => Silmaril.Wasm.Validation.CExternType.funcs mt.imports
  | none => []

/-- The store of the instance of `fwdCore3` against one host function. -/
def fwdStore : Silmaril.Wasm.Execution.Core.Store Nat :=
  match Silmaril.Wasm.Execution.Core.instantiateOnce? (Silmaril.Wasm.Game.importStore fwdImports)
      fwdCore3 [.func 0] with
  | some (s, _, _) => s
  | none => {}

/-- The instance of `fwdCore3`. -/
def fwdInst : Silmaril.Wasm.Game.ScalarInstance where
  imports := [⟨[.num (.int .i32)], [.num (.int .i32)]⟩]
  exports := [⟨[.num (.int .i32)], [.num (.int .i32)]⟩]
  addrs := [0]
  store := fwdStore

section Host

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon

/-- The host's import `g(n) = n + 1`. -/
def fwdG : HostFuncId → List Value.Val → Option (List Value.Val)
  | _, [.int .u32 n] => some [.int .u32 ((n + 1) % 2 ^ 32)]
  | _, _ => none

/-- The specification embedder over `core3 neverFail` whose host answers by `fwdG`. -/
def embI : Embedder (core3 Silmaril.Wasm.SingleThreaded.neverFail) Unit :=
  { X := core3Exec Silmaril.Wasm.SingleThreaded.neverFail, hr := Silmaril.Wasm.Component.Reference.Core3Adder.noReady, host := answerImpl fwdG }

/-- A stateful host for the import: in host state `s` (a call counter), `g(n) = n + s`, moving to
state `s + 1`. -/
def fwdC (s : Nat) : HostFuncId → List Value.Val → Option (List Value.Val × Nat)
  | _, [.int .u32 n] => some ([.int .u32 ((n + s) % 2 ^ 32)], s + 1)
  | _, _ => none

/-- The specification embedder over `core3 neverFail` whose host answers by the stateful
`fwdC`, with host state `Nat`. -/
def embC : Embedder (core3 Silmaril.Wasm.SingleThreaded.neverFail) Nat :=
  { X := core3Exec Silmaril.Wasm.SingleThreaded.neverFail, hr := fun _ _ => false,
    host := answerImplS fwdC }

end Host

/-! ## Two components linked -/

/-- `(func (param i32) (result i32) local.get 0 local.get 0 i32.add)`, exported as `f`. -/
def dblCore3 : Silmaril.Wasm.Module where
  types := [⟨[⟨true, [], .func ⟨[.i32], [.i32]⟩⟩]⟩]
  funcs := [⟨⟨0⟩, [], [.localGet ⟨0⟩, .localGet ⟨0⟩, .intBinOp .i32 .add]⟩]
  exports := [⟨"f", .func ⟨0⟩⟩]

/-- The doubler `g(x: u32) -> u32`, `g(x) = 2x`. -/
def dblS : Simple := ⟨⟨dblCore3, [("f", ⟨[.int .i32], [.int .i32]⟩)]⟩, [⟨"g", ⟨[.u32], [.u32]⟩, 0⟩]⟩

/-- `fwdS` with its import `g` answered by the doubler's export `g`: `f(x) = 2x`. -/
def dblFwdL : Linked2 := ⟨dblS, fwdS, [0]⟩

end Silmaril.Wasm.Component.Reference.Litmus
