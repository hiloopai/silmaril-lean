module

public import Silmaril.Wasm.Auto2.VCLib.Defs
public import Silmaril.Wasm.Auto2.VCSort.Defs
public import Silmaril.Wasm.Auto2.VCBTree.Defs
public import Silmaril.Wasm.Wat

/-!
# Contracts with memory and callees (VC library, pass 2): programs and specifications

Programs and annotated specifications for the VC stage with memory and callees
(`Silmaril.Wasm.Auto2.VCCheck`). The proved contracts and the kernel-checked checks are in
`Silmaril.Wasm.Auto2.VCLib2.Thms`.

* `doubleProg`: `double x = add x x` by a **call** to `add` (function `0` of the module), against
  `doubleSpec` (`x + x`) with the callee specification `addSpec` (`x + y`);
  `doubleSwapProg` has a callee computing `y + x` (another code, the same callee contract);
* `load2Prog`: `load2 p = mem[p] + mem[p + 4]` (two `i32` loads from **memory** `0`), against
  `load2Spec` (precondition `p + 8 ≤ size`, memory unchanged); `load2SwapProg` adds the words in
  the other order (accepted by normalisation: `add` is commutative).

* globals (generator 4's `FnSpec.globals`): `bumpProg` (`global.set`/`global.get`),
  `addnProg` (a global written in a loop), `frameProg` (a stack pointer moved down and restored),
  with the mutants `bumpLostProg` and `frameLeakProg`.

The binaries of these modules (`wasm-check vc-emit`) are the inputs of
`tools/wasm-check/tests/vc.sh`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCLib2

open Silmaril.Wasm
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Auto2.VCLib (P32 L32)

/-! ## `double` (a callee) -/

/-- `double x = add x x`. -/
def doubleProg := wat3! r#"
(module
  (func $add (param $x i32) (param $y i32) (result i32)
    (i32.add (local.get $x) (local.get $y)))
  (func $double (export "double") (param $x i32) (result i32)
    (call $add (local.get $x) (local.get $x))))
"#

/-- `double` with a callee computing `y + x`. -/
def doubleSwapProg := wat3! r#"
(module
  (func $add (param $x i32) (param $y i32) (result i32)
    (i32.add (local.get $y) (local.get $x)))
  (func $double (export "double") (param $x i32) (result i32)
    (call $add (local.get $x) (local.get $x))))
"#

/-- A mutant: the callee computes `x - y` (its condition is not accepted). -/
def doubleSubProg := wat3! r#"
(module
  (func $add (param $x i32) (param $y i32) (result i32)
    (i32.sub (local.get $x) (local.get $y)))
  (func $double (export "double") (param $x i32) (result i32)
    (call $add (local.get $x) (local.get $x))))
"#

/-- `double x = x + x`, total, calling function `0` with the specification `addSpec`. -/
def doubleSpec : FnSpec where
  params := [.i32]
  results := [.i32]
  post := .rel .eq (L32 0) (.bin .add (P32 0) (P32 0))
  total := true

/-- The specification with the callee (its code is only used by `fspec`'s `Callees`, not by the
generator). -/
def doubleSpecC (code : Func) : FnSpec := { doubleSpec with calls := [(0, VCLib.addSpec, code)] }

/-- The function `double` of `doubleProg`. -/
def doubleFunc : Func := doubleProg.funcs[1]

/-- The callee `add` of `doubleProg`. -/
def addFunc' : Func := doubleProg.funcs[0]

/-! ## `load2` (memory) -/

/-- `load2 p = mem[p] + mem[p + 4]`. -/
def load2Prog := wat3! r#"
(module
  (memory (export "memory") 1)
  (func $load2 (export "load2") (param $p i32) (result i32)
    (i32.add (i32.load (local.get $p)) (i32.load offset=4 (local.get $p)))))
"#

/-- `load2` adding in the other order. -/
def load2SwapProg := wat3! r#"
(module
  (memory (export "memory") 1)
  (func $load2 (export "load2") (param $p i32) (result i32)
    (i32.add (i32.load offset=4 (local.get $p)) (i32.load (local.get $p)))))
"#

/-- A mutant: the second load reads `p + 8`. -/
def load2OffProg := wat3! r#"
(module
  (memory (export "memory") 1)
  (func $load2 (export "load2") (param $p i32) (result i32)
    (i32.add (i32.load (local.get $p)) (i32.load offset=8 (local.get $p)))))
"#

/-- The word at `p + off` of the memory at entry. -/
abbrev word (off : Nat) : Tm .i32 := .load .i32 4 .unsigned (.v 0) (P32 0) off

/-- `load2 p` is the sum of the words at `p` and `p + 4` (which must be in memory); memory is
unchanged; total. -/
def load2Spec : FnSpec where
  params := [.i32]
  results := [.i32]
  pre := .inb (.v 0) (P32 0) 8
  post := .and (.rel .eq (L32 0) (.bin .add (word 0) (word 4))) (.meq .cur (.v 0))
  mem := true
  total := true

/-- The function `load2` of `load2Prog`. -/
def load2Func : Func := load2Prog.funcs[0]

/-! ## Globals -/

/-- `bump x` adds `x` to the global `g` and returns its new value. -/
def bumpProg := wat3! r#"
(module
  (global $g (mut i32) (i32.const 0))
  (func $bump (export "bump") (param $x i32) (result i32)
    (global.set $g (i32.add (global.get $g) (local.get $x)))
    (global.get $g)))
"#

/-- A mutant: the global is not written. -/
def bumpLostProg := wat3! r#"
(module
  (global $g (mut i32) (i32.const 0))
  (func $bump (export "bump") (param $x i32) (result i32)
    (i32.add (global.get $g) (local.get $x))))
"#

/-- The entry value of global `0` for a function with one parameter. -/
abbrev G0 : Tm .i32 := .var .i32 1

/-- `bump x`: the result and the final value of global `0` (placeholder `loc 1`, after the one
result) are `g + x`; total. -/
def bumpSpec : FnSpec where
  params := [.i32]
  results := [.i32]
  globals := [.i32]
  post := .and (.rel .eq (L32 0) (.bin .add G0 (P32 0))) (.rel .eq (L32 1) (.bin .add G0 (P32 0)))
  total := true

/-- `addn n` adds `1` to the global `acc`, `n` times (a loop: the global is havocked at the loop
head like a local). -/
def addnProg := wat3! r#"
(module
  (global $acc (mut i32) (i32.const 0))
  (func $addn (export "addn") (param $n i32)
    (block $d
      (loop $l
        (br_if $d (i32.eqz (local.get $n)))
        (global.set $acc (i32.add (global.get $acc) (i32.const 1)))
        (local.set $n (i32.sub (local.get $n) (i32.const 1)))
        (br $l)))))
"#

/-- `addn n`: the final value of `acc` (placeholder `loc 0`: no results) is `acc + n`; invariant
`acc' + n' = acc + n` (`loc 1` is the global, after the parameter), variant `n'`; total. -/
def addnSpec : FnSpec where
  params := [.i32]
  results := []
  globals := [.i32]
  post := .rel .eq (L32 0) (.bin .add G0 (P32 0))
  inv := [.rel .eq (.bin .add (L32 1) (L32 0)) (.bin .add G0 (P32 0))]
  var := [L32 0]
  total := true

/-- A function with a stack frame: it moves the stack pointer (global `0`) down by 16 and back,
and returns `x + 1`. -/
def frameProg := wat3! r#"
(module
  (global $sp (mut i32) (i32.const 1024))
  (func $frame (export "frame") (param $x i32) (result i32)
    (global.set $sp (i32.sub (global.get $sp) (i32.const 16)))
    (i32.add (local.get $x) (i32.const 1))
    (global.set $sp (i32.add (global.get $sp) (i32.const 16)))))
"#

/-- A mutant: the stack pointer is not restored. -/
def frameLeakProg := wat3! r#"
(module
  (global $sp (mut i32) (i32.const 1024))
  (func $frame (export "frame") (param $x i32) (result i32)
    (global.set $sp (i32.sub (global.get $sp) (i32.const 16)))
    (i32.add (local.get $x) (i32.const 1))))
"#

/-- `frame x = x + 1`, and the stack pointer is restored; total. -/
def frameSpec : FnSpec where
  params := [.i32]
  results := [.i32]
  globals := [.i32]
  post := .and (.rel .eq (L32 0) (.bin .add (P32 0) (.lit .i32 1))) (.rel .eq (L32 1) G0)
  total := true

/-! ## Insertion sort (two-memory invariants, `Silmaril.Wasm.Auto2.VCSort`) -/

/-- A mutant of insertion sort: the inner comparison is unsigned (`i32.le_u`), so the words are
not sorted in signed order. -/
def isortUnsignedProg := wat3! r#"
(module
  (memory (export "memory") 1)
  (func $insertion_sort (export "insertion_sort") (param $p i32) (param $n i32)
    (local $i i32) (local $j i32) (local $key i32)
    (local.set $i (i32.const 1))
    (block $done
      (loop $outer
        (br_if $done (i32.ge_u (local.get $i) (local.get $n)))
        (local.set $key
          (i32.load (i32.add (local.get $p) (i32.mul (local.get $i) (i32.const 4)))))
        (local.set $j (local.get $i))
        (block $placed
          (loop $inner
            (br_if $placed (i32.eqz (local.get $j)))
            (br_if $placed (i32.le_u
              (i32.load (i32.add (local.get $p)
                (i32.mul (i32.sub (local.get $j) (i32.const 1)) (i32.const 4))))
              (local.get $key)))
            (i32.store (i32.add (local.get $p) (i32.mul (local.get $j) (i32.const 4)))
              (i32.load (i32.add (local.get $p)
                (i32.mul (i32.sub (local.get $j) (i32.const 1)) (i32.const 4)))))
            (local.set $j (i32.sub (local.get $j) (i32.const 1)))
            (br $inner)))
        (i32.store (i32.add (local.get $p) (i32.mul (local.get $j) (i32.const 4)))
          (local.get $key))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $outer)))))
"#

/-- The modules whose binaries `wasm-check vc-emit` writes (file name, module). -/
def demoModules : List (String × Module) :=
  [("double-call", doubleProg), ("double-call-swap", doubleSwapProg),
   ("double-call-sub", doubleSubProg), ("load2-mem", load2Prog), ("load2-mem-swap", load2SwapProg),
   ("load2-mem-off", load2OffProg), ("bump-glob", bumpProg), ("bump-glob-lost", bumpLostProg),
   ("addn-glob", addnProg), ("frame-glob", frameProg), ("frame-glob-leak", frameLeakProg),
   ("isort", Silmaril.WasmSpec.InsertionSort.program), ("isort-unsigned", isortUnsignedProg),
   ("btree", Silmaril.WasmSpec.BTree.program)]

end Silmaril.Wasm.Auto2.VCLib2
