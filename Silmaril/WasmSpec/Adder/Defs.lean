module

public import Silmaril.WasmSpec.Common.Defs

/-!
# Wasm specification library: `Adder` v1

The program (`adder.wat` beside this file; `make check` compares the two texts):
a module exporting `add`, which returns the wrapping sum of its two `i32`
parameters. The annotations (`;; @requires`, `;; @ensures`) are WAT comments,
read by `tools/wasm-vc` and ignored by the quotation.

Specification: `Spec` (body level) and `CallSpec` (call level, for callers such
as the `Add3` entry). Solutions: `Silmaril.WasmSpec.Adder.Thms` and `manifest.toml`.
-/

@[expose] public section

namespace Silmaril.WasmSpec.Adder

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

/-- The program, quoted from `adder.wat`. -/
def program := wat3! r#"
(module
  ;; @requires true
  ;; @ensures (= result (bvadd x y))
  (func $add (export "add") (param $x i32) (param $y i32) (result i32)
    (i32.add (local.get $x) (local.get $y))))
"#

/-- The function `$add`. -/
def addFunc : Func := program.funcs[0]

/-- Arguments of a call: two `i32`s. -/
def args (xy : BitVec 32 × BitVec 32) : List Val := [.i32 xy.1, .i32 xy.2]

/-- Results of a call: their wrapping sum. -/
def res (xy : BitVec 32 × BitVec 32) : List Val := [.i32 (xy.1 + xy.2)]

/-- **Specification** (body level): `$add` returns `x + y` (modulo `2^32`). -/
def Spec : Prop := ∀ x y : BitVec 32, Computes addFunc (args (x, y)) (res (x, y))

/-- **Specification** (call level): the function at address `a` behaves as `$add`
in every store satisfying `Inv`. -/
def CallSpec {H : Type} (P : Profile) (host : HostSemantics H) (a : Nat)
    (Inv : Store H → Prop) : Prop :=
  PureSpec P host a Inv args res

end Silmaril.WasmSpec.Adder
