module

public import Silmaril.Wasm.Det.Core.Defs
public import Silmaril.Wasm.SSA.CoreCert.Defs
public import Silmaril.Wasm.Interp.Defs
public import Silmaril.Wasm.Execution.Core.Exec.Prepare
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateInit
public import Silmaril.Wasm.Validation.Check.Validate

/-!
# Litmus module for determinism and statelessness

```wat
(module
  (global $g (mut i32) (i32.const 0))
  (func (export "one") (result i32) i32.const 1)                      ;; function 0
  (func (export "nan") (result f32)                                   ;; function 1
    f32.const nan  f32.const nan  f32.add)
  (func (export "set") i32.const 5  global.set $g)                    ;; function 2
  (func (export "get") (result i32) global.get $g))                   ;; function 3
```

* function `0` is deterministic and stateless at every profile, although the module is
  neither: function `1` adds two canonical NaNs, whose sum the specification profile may return
  as a NaN of either sign, and functions `2`/`3` write and read a global;
* `litMod` is a silmaril-lean Core `Module`, `litPrep` its allocation by silmaril-lean's
  executable instantiation `prepare?` into the empty store, `litStore` the allocated store.

Theorems in `Silmaril.Wasm.Det.Core.Litmus.Thms`. New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.Core.Litmus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- The canonical positive `f32` NaN. -/
def nanP : BitVec 32 := 0x7fc00000
/-- The canonical negative `f32` NaN. -/
def nanN : BitVec 32 := 0xffc00000

/-- The litmus module. -/
def litMod : Module where
  types := [⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩, ⟨[⟨true, [], .func ⟨[], [.f32]⟩⟩]⟩,
    ⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩]
  globals := [⟨⟨.var, .i32⟩, [.intConst .i32 0]⟩]
  funcs := [⟨⟨0⟩, [], [.intConst .i32 1]⟩,
    ⟨⟨1⟩, [], [.floatConst .f32 nanP, .floatConst .f32 nanP, .floatBinOp .f32 .add]⟩,
    ⟨⟨2⟩, [], [.intConst .i32 5, .globalSet ⟨0⟩]⟩,
    ⟨⟨0⟩, [], [.globalGet ⟨0⟩]⟩]
  exports := [⟨"one", .func ⟨0⟩⟩, ⟨"nan", .func ⟨1⟩⟩, ⟨"set", .func ⟨2⟩⟩, ⟨"get", .func ⟨3⟩⟩]

/-- The spec's allocation of `litMod` into the empty store. -/
def litPrep : Config Nat × Option FuncIdx :=
  (prepare? evalConst? ({} : Store Nat) litMod []).getD (⟨{}, {}, []⟩, none)

/-- The store of the instance of `litMod`. -/
def litStore : Store Nat := litPrep.1.store

/-- The entry functions of the instance: its four exports. -/
def litEntry (a : Nat) : Prop := a < 4

/-! ## The executable leaf check -/

/-- A numeric parameter type. -/
def numParam : Validation.CValType → Bool
  | .num _ => true
  | _ => false

/-- Wasm code of a store-free leaf function (`Silmaril.Wasm.SSA.leafFunc`). -/
def leafCode : FuncCode Nat → Bool
  | .wasm fn => Silmaril.Wasm.SSA.leafFunc fn
  | .host _ => false

/-- A function type with numeric parameters. -/
def numParams (d : Validation.DefType) : Bool :=
  match d.funcType? with
  | some (ps, _) => ps.all numParam
  | none => false

/-- The function at `a` is a store-free leaf function (`Silmaril.Wasm.SSA.leafFunc`) with a
native-profile body (`Silmaril.Wasm.Interp.nativeFuncsB`) and numeric parameters. Such functions
are deterministic and stateless at every profile (`detFn_of_leafCheck`,
`statelessFn_of_leafCheck`; tactic `det_leaf`). -/
def leafCheck (s : Store Nat) (a : Nat) : Bool :=
  match s.funcs[a]? with
  | some fi => leafCode fi.code && Silmaril.Wasm.Interp.nativeFuncsB [fi] && numParams fi.type
  | none => false

end Silmaril.Wasm.Det.Core.Litmus
