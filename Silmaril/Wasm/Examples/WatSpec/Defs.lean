module

public import Silmaril.Wasm.WatSpec.Defs
public import Silmaril.Wasm.Examples.Wat.Defs

/-!
# Annotated WAT examples

Functions written with `wat_spec!` (`Silmaril.Wasm.WatSpec`): WAT with `requires`, `ensures` and
`invariant` annotations. Each elaborates to the plain module and its specification; the
verification conditions are proved in `Silmaril.Proofs.Wasm.Examples.WatSpec`. `addStore` is the
store after instantiating `addS.module` against no imports. A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.WatSpec

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.WatSpec
open Silmaril.Wasm.Examples.Wat (triangle)

/-- `add`: the sum. -/
def addS : Annotated := wat_spec! r#"
(func $add (export "add") (param $x i32) (param $y i32) (result i32)
  (ensures (result = x + y))
  local.get $x
  local.get $y
  i32.add)
"#

/-- `abs`: `|x|` for every `x` but the most negative one. -/
def absS : Annotated := wat_spec! r#"
(func $abs (export "abs") (param $x i32) (result i32)
  (requires (x ≠ BitVec.intMin 32))
  (ensures (result.toInt = x.toInt.natAbs))
  (if (result i32) (i32.lt_s (local.get $x) (i32.const 0))
    (then (i32.sub (i32.const 0) (local.get $x)))
    (else (local.get $x))))
"#

/-- `max`: the signed maximum. -/
def maxS : Annotated := wat_spec! r#"
(func $max (export "max") (param $x i32) (param $y i32) (result i32)
  (ensures (result.toInt = max x.toInt y.toInt))
  (select (local.get $x) (local.get $y) (i32.gt_s (local.get $x) (local.get $y))))
"#

/-- `square`: an `i64` product. -/
def squareS : Annotated := wat_spec! r#"
(func $square (export "square") (param $x i64) (result i64)
  (ensures (result = x * x))
  local.get $x
  local.get $x
  i64.mul)
"#

/-- `sum`: `0 + 1 + ⋯ + n` (modulo `2³²`), by a loop with an invariant. -/
def sumS : Annotated := wat_spec! r#"
(func $sum (export "sum") (param $n i32) (result i32) (local $i i32) (local $acc i32)
  (ensures (result = BitVec.ofNat 32 (triangle n.toNat)))
  (block $done
    (loop $next
      (invariant (i.toNat ≤ n.toNat ∧ acc = BitVec.ofNat 32 (triangle i.toNat)))
      (br_if $done (i32.eq (local.get $i) (local.get $n)))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (local.set $acc (i32.add (local.get $acc) (local.get $i)))
      (br $next)))
  (local.get $acc))
"#

/-- `countdown`: a loop that writes its parameter; the invariant uses `old_n`. -/
def countdownS : Annotated := wat_spec! r#"
(func $countdown (export "countdown") (param $n i32) (result i32) (local $steps i32)
  (ensures (result = n))
  (block $done
    (loop $next
      (invariant (steps + n = old_n))
      (br_if $done (i32.eqz (local.get $n)))
      (local.set $n (i32.sub (local.get $n) (i32.const 1)))
      (local.set $steps (i32.add (local.get $steps) (i32.const 1)))
      (br $next)))
  (local.get $steps))
"#

/-- The instantiation of `addS.module` against no imports. -/
def addStore : Store Nat :=
  match instantiateOnce? (importStore []) addS.module [] with
  | some (s, _, _) => s
  | none => {}

end Silmaril.Wasm.Examples.WatSpec
