module

public import Silmaril.WasmSpec.Common.Defs

/-!
# Wasm specification library: `SumTo` v1

The program (`sum_to.wat`): `sum n` adds `n, n-1, …, 1` into an accumulator by a
count-down loop and returns it, so it computes the triangular number
`n (n + 1) / 2` modulo `2^32`. The annotations give the loop invariant
`acc + tri n = tri (old n)` and the measure `n`.

Specification: `Spec`, with `tri`/`triBV` the triangular numbers on `Nat` and
their `i32` image.
-/

@[expose] public section

namespace Silmaril.WasmSpec.SumTo

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

/-- The program, quoted from `sum_to.wat`. -/
def program := wat3! r#"
(module
  ;; @requires true
  ;; @ensures (= result (tri n))
  (func $sum (export "sum") (param $n i32) (result i32) (local $acc i32)
    (block $done
      (loop $again
        ;; @invariant (= (bvadd acc (tri n)) (tri (old n)))
        ;; @decreases n
        (br_if $done (i32.eqz (local.get $n)))
        (local.set $acc (i32.add (local.get $acc) (local.get $n)))
        (local.set $n (i32.sub (local.get $n) (i32.const 1)))
        (br $again)))
    (local.get $acc)))
"#

/-- The function `$sum`. -/
def sumFunc : Func := program.funcs[0]

/-- The triangular numbers `0 + 1 + ⋯ + k`. -/
def tri (k : Nat) : Nat := k * (k + 1) / 2

/-- The triangular number of an `i32` (read unsigned), modulo `2^32`. -/
def triBV (x : BitVec 32) : BitVec 32 := BitVec.ofNat 32 (tri x.toNat)

/-- **Specification**: `$sum n` returns `tri n` modulo `2^32`. -/
def Spec : Prop := ∀ n : BitVec 32, Computes sumFunc [.i32 n] [.i32 (triBV n)]

end Silmaril.WasmSpec.SumTo
