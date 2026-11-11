module

public import Silmaril.Wasm.Auto2.VCGen.Defs
public import tests.wasm.auto.FrontBench.Defs

/-!
# Contracts of the VC library: specifications

Annotated total-correctness specifications for VC generator 4 (`Silmaril.Wasm.Auto2.VCGen`) of the
front-end benchmark's reference functions (`Silmaril.Wasm.Auto.FrontBench`): `sum` (a loop: the
`sum-ref` case, which round 3 of the front end left unknown), `max` and `add`. The proved
contracts (`Silmaril.Wasm.Auto2.VCBridge.VcEntry`) and the `ModMeets` theorems are in
`Silmaril.Wasm.Auto2.VCLib.Thms`.

* `sumSpec`: `sum n = triBV n`, loop invariant `acc + triBV n = triBV n₀`, variant `n`;
* `maxSpec`: the signed maximum (`select` on `x >s y`);
* `addSpec`: `x + y`;
* `div10Spec`: `x / 10` on `i64`, for the multiply-high kernel `div10MulhiFunc`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCLib

open Silmaril.Wasm
open Silmaril.Wasm.Auto2.VCGen

/-- Parameter `i` and local `j` as `i32` terms. -/
abbrev P32 (i : Nat) : Tm .i32 := .var .i32 i
abbrev L32 (j : Nat) : Tm .i32 := .loc .i32 j

/-! ## `sum` -/

/-- Specification function `0` (`i32`) is `triBV` (`Silmaril.WasmSpec.SumTo.triBV`). -/
def sumFns : Fns where
  f32 _ x := Silmaril.WasmSpec.SumTo.triBV x

/-- `sum n = triBV n`, total: invariant `acc + triBV n = triBV n₀`, variant `n`. -/
def sumSpec : FnSpec where
  params := [.i32]
  results := [.i32]
  post := .rel .eq (L32 0) (.fn 0 (P32 0))
  inv := [.rel .eq (.bin .add (L32 1) (.fn 0 (L32 0))) (.fn 0 (P32 0))]
  var := [L32 0]
  total := true

/-! ## `max` -/

/-- `max x y` is `x` if `x > y` (signed), else `y`; total. -/
def maxSpec : FnSpec where
  params := [.i32, .i32]
  results := [.i32]
  post := .rel .eq (L32 0) (.ite (.rel (.gt .signed) (P32 0) (P32 1)) (P32 0) (P32 1))
  total := true

/-! ## `add` -/

/-- `add x y = x + y`; total. -/
def addSpec : FnSpec where
  params := [.i32, .i32]
  results := [.i32]
  post := .rel .eq (L32 0) (.bin .add (P32 0) (P32 1))
  total := true

/-! ## `div10` -/

/-- The `div10` kernel as hand-written for the front-end benchmark
(`Silmaril.Wasm.Auto.FrontBench.div10Mulhi`: multiply-high by four `32 × 32 → 64` products). -/
def div10MulhiFunc : Func := Silmaril.Wasm.Auto.FrontBench.div10Mulhi.funcs[0]

/-- `div10 x = x / 10` (unsigned, `i64`); total. -/
def div10Spec : FnSpec where
  params := [.i64]
  results := [.i64]
  post := .rel .eq (.loc .i64 0) (.bin (.div .unsigned) (.var .i64 0) (.lit .i64 10))
  total := true

/-- The fuel of the library's contracts. -/
def libFuel : Nat := 100

end Silmaril.Wasm.Auto2.VCLib
