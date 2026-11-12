module

public import Silmaril.Wasm.Auto.Front.Defs
public import Silmaril.WasmSpec.Max.Defs
public import Silmaril.WasmSpec.Adder.Defs
public import Silmaril.WasmSpec.SumTo.Defs

/-!
# Pinned inputs of the front-end benchmark

The module pairs and reference functions of the front-end benchmark
(`docs/projects/wasm-binaryen-tooling.md`; `tools/wasm-check/tests/bench.sh` runs the tool
on their binary encodings, written by `wasm-check-gen`). Each `Case` names an
implementation, a specification module (or a reference function) and the expected verdict of
the current front end.

* `Max`, `Adder`, `SumTo`: the Wasm specification library programs (`Silmaril.WasmSpec.*`), with
  reference functions and mutants;
* `div10`: unsigned 64-bit division by ten, the kernel
  (`the div10 benchmark kernel`, Granlund-Montgomery multiply-high), written
  here as WAT by hand from the C source, against `i64.div_u`; and a mutant whose magic constant
  is wrong in its low word (wrong only for large arguments);
* `requant`: the int8 requantisation kernel (`…/requant/start.c`, with its fixed
  output stage, the zero point added in 64 bits) against the earlier version `v0` (the zero
  point added in 32 bits, which wraps for a saturated product).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.FrontBench

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-! ## `max` -/

/-- `Max`'s program (`Silmaril.WasmSpec.Max.program`). -/
def maxProg : Module := Silmaril.WasmSpec.Max.program

/-- `max` with `select` instead of `if`: equivalent. -/
def maxSelect := wat3! r#"
(module
  (func $max (export "max") (param $x i32) (param $y i32) (result i32)
    (select (local.get $x) (local.get $y) (i32.gt_s (local.get $x) (local.get $y)))))
"#

/-- A mutant: unsigned comparison. -/
def maxUnsigned := wat3! r#"
(module
  (func $max (export "max") (param $x i32) (param $y i32) (result i32)
    (if (result i32) (i32.gt_u (local.get $x) (local.get $y))
      (then (local.get $x))
      (else (local.get $y)))))
"#

/-- The reference function of `max`: the signed maximum. -/
def maxRef : List Val → Option Result
  | [.num ⟨.int .i32, x⟩, .num ⟨.int .i32, y⟩] =>
    some (.values [.i32 (Silmaril.WasmSpec.Max.smax x y)])
  | _ => none

/-! ## `add` -/

/-- `Adder`'s program. -/
def addProg : Module := Silmaril.WasmSpec.Adder.program

/-- `add` with swapped operands: equivalent. -/
def addSwap := wat3! r#"
(module
  (func $add (export "add") (param $x i32) (param $y i32) (result i32)
    (i32.add (local.get $y) (local.get $x))))
"#

/-- A mutant: subtraction. -/
def addSub := wat3! r#"
(module
  (func $add (export "add") (param $x i32) (param $y i32) (result i32)
    (i32.sub (local.get $x) (local.get $y))))
"#

/-- The reference function of `add`. -/
def addRef : List Val → Option Result
  | [.num ⟨.int .i32, x⟩, .num ⟨.int .i32, y⟩] => some (.values [.i32 (x + y)])
  | _ => none

/-! ## `sum` -/

/-- `SumTo`'s program (a count-down loop). -/
def sumProg : Module := Silmaril.WasmSpec.SumTo.program

/-- A mutant: the loop stops at `1` (it omits the last addition, of `1`). -/
def sumOffByOne := wat3! r#"
(module
  (func $sum (export "sum") (param $n i32) (result i32) (local $acc i32)
    (block $done
      (loop $again
        (br_if $done (i32.le_u (local.get $n) (i32.const 1)))
        (local.set $acc (i32.add (local.get $acc) (local.get $n)))
        (local.set $n (i32.sub (local.get $n) (i32.const 1)))
        (br $again)))
    (local.get $acc)))
"#

/-- The reference function of `sum`: the triangular number modulo `2^32`. -/
def sumRef : List Val → Option Result
  | [.num ⟨.int .i32, n⟩] => some (.values [.i32 (Silmaril.WasmSpec.SumTo.triBV n)])
  | _ => none

/-! ## `div10` -/

/-- `x / 10` by `i64.div_u`. -/
def div10Ref := wat3! r#"
(module
  (func $div10 (export "div10") (param $x i64) (result i64)
    (i64.div_u (local.get $x) (i64.const 10))))
"#

/-- `div10` of a division benchmark kernel: the high 64 bits of `x * 0xCCCCCCCCCCCCCCCD` from four 32 × 32 → 64
products, shifted right by 3. -/
def div10Mulhi := wat3! r#"
(module
  (func $div10 (export "div10") (param $x i64) (result i64)
    (local $alo i64) (local $ahi i64) (local $p0 i64) (local $p1 i64) (local $p2 i64)
    (local $p3 i64) (local $mid i64)
    (local.set $alo (i64.and (local.get $x) (i64.const 0xffffffff)))
    (local.set $ahi (i64.shr_u (local.get $x) (i64.const 32)))
    (local.set $p0 (i64.mul (local.get $alo) (i64.const 0xcccccccd)))
    (local.set $p1 (i64.mul (local.get $alo) (i64.const 0xcccccccc)))
    (local.set $p2 (i64.mul (local.get $ahi) (i64.const 0xcccccccd)))
    (local.set $p3 (i64.mul (local.get $ahi) (i64.const 0xcccccccc)))
    (local.set $mid
      (i64.add
        (i64.add (i64.shr_u (local.get $p0) (i64.const 32))
          (i64.and (local.get $p1) (i64.const 0xffffffff)))
        (i64.and (local.get $p2) (i64.const 0xffffffff))))
    (i64.shr_u
      (i64.add
        (i64.add
          (i64.add (local.get $p3) (i64.shr_u (local.get $p1) (i64.const 32)))
          (i64.shr_u (local.get $p2) (i64.const 32)))
        (i64.shr_u (local.get $mid) (i64.const 32)))
      (i64.const 3))))
"#

/-- A mutant of `div10Mulhi`: the low word of the magic constant is `0xcccccccc` (the constant
is `0xCCCCCCCCCCCCCCCC`); right for small arguments, wrong for some large ones. -/
def div10Mutant := wat3! r#"
(module
  (func $div10 (export "div10") (param $x i64) (result i64)
    (local $alo i64) (local $ahi i64) (local $p0 i64) (local $p1 i64) (local $p2 i64)
    (local $p3 i64) (local $mid i64)
    (local.set $alo (i64.and (local.get $x) (i64.const 0xffffffff)))
    (local.set $ahi (i64.shr_u (local.get $x) (i64.const 32)))
    (local.set $p0 (i64.mul (local.get $alo) (i64.const 0xcccccccc)))
    (local.set $p1 (i64.mul (local.get $alo) (i64.const 0xcccccccc)))
    (local.set $p2 (i64.mul (local.get $ahi) (i64.const 0xcccccccc)))
    (local.set $p3 (i64.mul (local.get $ahi) (i64.const 0xcccccccc)))
    (local.set $mid
      (i64.add
        (i64.add (i64.shr_u (local.get $p0) (i64.const 32))
          (i64.and (local.get $p1) (i64.const 0xffffffff)))
        (i64.and (local.get $p2) (i64.const 0xffffffff))))
    (i64.shr_u
      (i64.add
        (i64.add
          (i64.add (local.get $p3) (i64.shr_u (local.get $p1) (i64.const 32)))
          (i64.shr_u (local.get $p2) (i64.const 32)))
        (i64.shr_u (local.get $mid) (i64.const 32)))
      (i64.const 3))))
"#

/-- The reference function of `div10`. -/
def div10RefFn : List Val → Option Result
  | [.num ⟨.int .i64, x⟩] => some (.values [.i64 ((show BitVec 64 from x) / 10)])
  | _ => none

/-! ## `requant` -/

/-- `requant` of (fixed output stage: the zero point is added in 64 bits). -/
def requantFixed := wat3! r#"
(module
  (func $requant (export "requant")
    (param $acc i32) (param $mult i32) (param $rshift i32) (param $zp i32) (result i32)
    (local $ab i64) (local $hi i32) (local $x i32) (local $mask i32) (local $q i32)
    (local $r i64)
    (local.set $ab
      (i64.mul (i64.extend_i32_s (local.get $acc)) (i64.extend_i32_s (local.get $mult))))
    (local.set $hi
      (i32.wrap_i64
        (i64.div_s
          (i64.add (local.get $ab)
            (select (i64.const 1073741824) (i64.const -1073741823)
              (i64.ge_s (local.get $ab) (i64.const 0))))
          (i64.const 2147483648))))
    (local.set $x
      (select (i32.const 2147483647) (local.get $hi)
        (i32.and (i32.eq (local.get $acc) (local.get $mult))
          (i32.eq (local.get $acc) (i32.const -2147483648)))))
    (local.set $mask
      (i32.wrap_i64
        (i64.sub (i64.shl (i64.const 1) (i64.extend_i32_s (local.get $rshift))) (i64.const 1))))
    (local.set $q
      (i32.add (i32.shr_s (local.get $x) (local.get $rshift))
        (i32.gt_s (i32.and (local.get $x) (local.get $mask))
          (i32.add (i32.shr_s (local.get $mask) (i32.const 1))
            (i32.lt_s (local.get $x) (i32.const 0))))))
    (local.set $r (i64.add (i64.extend_i32_s (local.get $q)) (i64.extend_i32_s (local.get $zp))))
    (local.set $r (select (i64.const -128) (local.get $r) (i64.lt_s (local.get $r) (i64.const -128))))
    (local.set $r (select (i64.const 127) (local.get $r) (i64.gt_s (local.get $r) (i64.const 127))))
    (i32.wrap_i64 (local.get $r))))
"#

/-- `requant` v0: the zero point is added in 32 bits (it wraps for a saturated product). -/
def requantV0 := wat3! r#"
(module
  (func $requant (export "requant")
    (param $acc i32) (param $mult i32) (param $rshift i32) (param $zp i32) (result i32)
    (local $ab i64) (local $hi i32) (local $x i32) (local $mask i32) (local $q i32)
    (local $r i64)
    (local.set $ab
      (i64.mul (i64.extend_i32_s (local.get $acc)) (i64.extend_i32_s (local.get $mult))))
    (local.set $hi
      (i32.wrap_i64
        (i64.div_s
          (i64.add (local.get $ab)
            (select (i64.const 1073741824) (i64.const -1073741823)
              (i64.ge_s (local.get $ab) (i64.const 0))))
          (i64.const 2147483648))))
    (local.set $x
      (select (i32.const 2147483647) (local.get $hi)
        (i32.and (i32.eq (local.get $acc) (local.get $mult))
          (i32.eq (local.get $acc) (i32.const -2147483648)))))
    (local.set $mask
      (i32.wrap_i64
        (i64.sub (i64.shl (i64.const 1) (i64.extend_i32_s (local.get $rshift))) (i64.const 1))))
    (local.set $q
      (i32.add (i32.shr_s (local.get $x) (local.get $rshift))
        (i32.gt_s (i32.and (local.get $x) (local.get $mask))
          (i32.add (i32.shr_s (local.get $mask) (i32.const 1))
            (i32.lt_s (local.get $x) (i32.const 0))))))
    (local.set $r (i64.extend_i32_s (i32.add (local.get $q) (local.get $zp))))
    (local.set $r (select (i64.const -128) (local.get $r) (i64.lt_s (local.get $r) (i64.const -128))))
    (local.set $r (select (i64.const 127) (local.get $r) (i64.gt_s (local.get $r) (i64.const 127))))
    (i32.wrap_i64 (local.get $r))))
"#

/-! ## Cases -/

/-- What a case compares. -/
inductive Against where
  /-- A specification module (refinement, or equivalence). -/
  | module (spec : Module)
  /-- A reference function. -/
  | refFn (f : List Val → Option Result)

/-- A benchmark case. -/
structure Case where
  /-- The name (also the stem of the `.wasm` files). -/
  name : String
  /-- The implementation. -/
  impl : Module
  /-- What it is compared with. -/
  against : Against
  /-- The expected verdict of the current front end. -/
  expect : Silmaril.Wasm.Spec.Verdict

/-- The cases (export `0` throughout). -/
def cases : List Case := [
  ⟨"max-select", maxSelect, .module maxProg, .proved⟩,
  ⟨"max-unsigned", maxUnsigned, .module maxProg, .refuted⟩,
  ⟨"max-ref", maxProg, .refFn maxRef, .unknown⟩,
  ⟨"max-unsigned-ref", maxUnsigned, .refFn maxRef, .refuted⟩,
  ⟨"add-swap", addSwap, .module addProg, .proved⟩,
  ⟨"add-sub", addSub, .module addProg, .refuted⟩,
  ⟨"add-ref", addProg, .refFn addRef, .unknown⟩,
  ⟨"sum-ref", sumProg, .refFn sumRef, .unknown⟩,
  ⟨"sum-offbyone-ref", sumOffByOne, .refFn sumRef, .refuted⟩,
  ⟨"div10-mulhi", div10Mulhi, .module div10Ref, .proved⟩,
  ⟨"div10-mutant", div10Mutant, .module div10Ref, .refuted⟩,
  ⟨"div10-mulhi-ref", div10Mulhi, .refFn div10RefFn, .unknown⟩,
  ⟨"requant-v0", requantV0, .module requantFixed, .refuted⟩]

end Silmaril.Wasm.Auto.FrontBench
