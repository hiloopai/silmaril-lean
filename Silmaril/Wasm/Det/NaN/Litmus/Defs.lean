module

public import Silmaril.Wasm.Det.NaN.Defs
public import Silmaril.Wasm.Execution.Core.Exec.Prepare
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateInit

/-!
# Litmus module for determinism up to NaN payloads

```wat
(module
  (func (export "raw") (param f32 f32) (result f32)        ;; function 0
    local.get 0  local.get 1  f32.add)
  (func (export "guard") (param f32 f32) (result f32)      ;; function 1
    (local f32)
    local.get 0  local.get 1  f32.add  local.tee 2
    f32.const 0  local.get 2  local.get 2  f32.eq  select)  ;; x == x ? x : 0
  (func (export "cmp") (param f32 f32) (result i32)        ;; function 2
    local.get 0  local.get 1  f32.add  f32.const 1  f32.lt))
```

* `raw` returns the sum directly: a NaN result reaches the output, and the specification's
  profile may return `+nan` or `-nan` for `nan + nan`;
* `guard` checks the sum for NaN (`x == x` is false exactly for NaNs) and returns the constant
  `0` instead: the NaN payload never reaches the output;
* `cmp` uses floats only for a comparison, whose `i32` result does not depend on payloads.

All three pass the fragment check `nanCheck false` (no `global.set`, no bit sink), so each is
deterministic up to NaN payloads at every profile; `guard` and `cmp` are deterministic modulo
traps and imports (`DetFn`) at every profile, while `raw`, and hence the module, is not at
specification profiles. `bitsBody` (`i32.reinterpret_f32` of the sum) is rejected by the check.

`nanMod` is a silmaril-lean Core `Module`, `nanStore` its allocation by `prepare?` into the
empty store. Theorems in `Silmaril.Wasm.Det.NaN.Litmus.Thms`. New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.NaN.Litmus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- The `f32` value with bits `b`. -/
def f32v (b : BitVec 32) : Val := .num ⟨.float .f32, b⟩

/-- The canonical positive `f32` NaN. -/
def nanP : BitVec 32 := 0x7fc00000

/-- The canonical negative `f32` NaN. -/
def nanN : BitVec 32 := 0xffc00000

/-- The bits of `1.0f32`. -/
def one32 : BitVec 32 := 0x3f800000

/-- `raw`: `local.get 0; local.get 1; f32.add`. -/
def rawBody : List Instr := [.localGet ⟨0⟩, .localGet ⟨1⟩, .floatBinOp .f32 .add]

/-- `guard`: the sum, or `0` if it is a NaN. -/
def guardBody : List Instr :=
  [.localGet ⟨0⟩, .localGet ⟨1⟩, .floatBinOp .f32 .add, .localTee ⟨2⟩, .floatConst .f32 0,
    .localGet ⟨2⟩, .localGet ⟨2⟩, .floatRelOp .f32 .eq, .select none]

/-- `cmp`: is the sum below `1`? -/
def cmpBody : List Instr :=
  [.localGet ⟨0⟩, .localGet ⟨1⟩, .floatBinOp .f32 .add, .floatConst .f32 one32,
    .floatRelOp .f32 .lt]

/-- A bit sink: the bits of the sum as an `i32` (rejected by the fragment check). -/
def bitsBody : List Instr :=
  [.localGet ⟨0⟩, .localGet ⟨1⟩, .floatBinOp .f32 .add, .convert (.reinterpretInt .f32)]

/-- The litmus module. -/
def nanMod : Module where
  types := [⟨[⟨true, [], .func ⟨[.f32, .f32], [.f32]⟩⟩]⟩,
    ⟨[⟨true, [], .func ⟨[.f32, .f32], [.i32]⟩⟩]⟩]
  funcs := [⟨⟨0⟩, [], rawBody⟩, ⟨⟨0⟩, [.f32], guardBody⟩, ⟨⟨1⟩, [], cmpBody⟩]
  exports := [⟨"raw", .func ⟨0⟩⟩, ⟨"guard", .func ⟨1⟩⟩, ⟨"cmp", .func ⟨2⟩⟩]

/-- The spec's allocation of `nanMod` into the empty store. -/
def nanPrep : Config Nat × Option FuncIdx :=
  (prepare? evalConst? ({} : Store Nat) nanMod []).getD (⟨{}, {}, []⟩, none)

/-- The store of the instance of `nanMod`. -/
def nanStore : Store Nat := nanPrep.1.store

/-- The entry functions: the three exports. -/
def nanEntry (a : Nat) : Prop := a < 3

/-- Recognise `rawBody`. -/
def rawB : List Instr → Bool
  | [.localGet a, .localGet b, .floatBinOp .f32 .add] => decide (a = ⟨0⟩ ∧ b = ⟨1⟩)
  | _ => false

/-- Recognise `guardBody`. -/
def guardB : List Instr → Bool
  | [.localGet a, .localGet b, .floatBinOp .f32 .add, .localTee c, .floatConst .f32 z,
      .localGet d, .localGet e, .floatRelOp .f32 .eq, .select none] =>
    decide (a = ⟨0⟩ ∧ b = ⟨1⟩ ∧ c = ⟨2⟩ ∧ z.toNat = 0 ∧ d = ⟨2⟩ ∧ e = ⟨2⟩)
  | _ => false

/-- Recognise `cmpBody`. -/
def cmpB : List Instr → Bool
  | [.localGet a, .localGet b, .floatBinOp .f32 .add, .floatConst .f32 z, .floatRelOp .f32 .lt] =>
    decide (a = ⟨0⟩ ∧ b = ⟨1⟩ ∧ z.toNat = one32.toNat)
  | _ => false

/-- The shape of an allocated function: its body, its locals and its function type. -/
def shapeOk (body : List Instr → Bool) (locals : List ValType)
    (ty : List Validation.CValType × List Validation.CValType) (fi : FuncInst Nat) : Bool :=
  (match fi.code with
    | .wasm fn => body fn.body && decide (fn.locals = locals)
    | .host _ => false) && decide (fi.type.funcType? = some ty)

/-- The function type of `raw` and `guard`. -/
def tyFF : List Validation.CValType × List Validation.CValType :=
  ([.num (.float .f32), .num (.float .f32)], [.num (.float .f32)])

/-- The function type of `cmp`. -/
def tyFI : List Validation.CValType × List Validation.CValType :=
  ([.num (.float .f32), .num (.float .f32)], [.num (.int .i32)])

end Silmaril.Wasm.Det.NaN.Litmus
