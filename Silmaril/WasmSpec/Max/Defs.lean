module

public import Silmaril.WasmSpec.Common.Defs

/-!
# Wasm specification library: `Max` v1

The program (`max.wat`): `max x y` returns the larger of two `i32`s read as
signed integers, by an `if` on `i32.gt_s`.

Specification: `Spec`.
-/

@[expose] public section

namespace Silmaril.WasmSpec.Max

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

/-- The program, quoted from `max.wat`. -/
def program := wat3! r#"
(module
  ;; @requires true
  ;; @ensures (= result (ite (bvsgt x y) x y))
  (func $max (export "max") (param $x i32) (param $y i32) (result i32)
    (if (result i32) (i32.gt_s (local.get $x) (local.get $y))
      (then (local.get $x))
      (else (local.get $y)))))
"#

/-- The function `$max`. -/
def maxFunc : Func := program.funcs[0]

/-- Signed maximum. -/
def smax (x y : BitVec 32) : BitVec 32 := if y.slt x then x else y

/-- **Specification**: `$max x y` returns the signed maximum. -/
def Spec : Prop := ∀ x y : BitVec 32, Computes maxFunc [.i32 x, .i32 y] [.i32 (smax x y)]

end Silmaril.WasmSpec.Max
