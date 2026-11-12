module

public import Silmaril.Wasm.Auto2.VCLib2.Defs

/-!
# VC library with linear arithmetic and recursion: programs and specifications

Programs and annotated
specifications for the VC stage of `wasm-check` (`Silmaril.Wasm.Auto2.VCCheck.vcCheckM`); the
proved contracts and the kernel-checked checks are in `Silmaril.Wasm.Auto2.VCLib3.Thms`.

* **Linear arithmetic** (the normaliser's `Tm.lin`): `dblAddProg` (`x + x`, whose conditions are
  the contract `dbl`), `dblShlProg` (`x << 1`), `dblMulProg` (`2 * x`), and the mutant
  `dblShl2Prog` (`x << 2`); `add3Prog` (`(a + b) + c`, contract `add3`), `add3AssocProg`
  (`(c + a) + b`), `add3SubProg` (`a - (0 - b) + c`), and the mutant `add3MutProg` (`a - b + c`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCLib3

open Silmaril.Wasm
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Auto2.VCLib (P32 L32)

/-! ## Linear arithmetic -/

/-- `dbl x = x + x`. -/
def dblAddProg := wat3! r#"
(module
  (func $dbl (export "dbl") (param $x i32) (result i32)
    (i32.add (local.get $x) (local.get $x))))
"#

/-- `dbl x = x << 1`. -/
def dblShlProg := wat3! r#"
(module
  (func $dbl (export "dbl") (param $x i32) (result i32)
    (i32.shl (local.get $x) (i32.const 1))))
"#

/-- `dbl x = 2 * x`. -/
def dblMulProg := wat3! r#"
(module
  (func $dbl (export "dbl") (param $x i32) (result i32)
    (i32.mul (i32.const 2) (local.get $x))))
"#

/-- A mutant: `x << 2`. -/
def dblShl2Prog := wat3! r#"
(module
  (func $dbl (export "dbl") (param $x i32) (result i32)
    (i32.shl (local.get $x) (i32.const 2))))
"#

/-- `dbl x = x + x`, total. -/
def dblSpec : FnSpec where
  params := [.i32]
  results := [.i32]
  post := .rel .eq (L32 0) (.bin .add (P32 0) (P32 0))
  total := true

/-- `add3 a b c = (a + b) + c`. -/
def add3Prog := wat3! r#"
(module
  (func $add3 (export "add3") (param $a i32) (param $b i32) (param $c i32) (result i32)
    (i32.add (i32.add (local.get $a) (local.get $b)) (local.get $c))))
"#

/-- `add3` reassociated: `(c + a) + b`. -/
def add3AssocProg := wat3! r#"
(module
  (func $add3 (export "add3") (param $a i32) (param $b i32) (param $c i32) (result i32)
    (i32.add (i32.add (local.get $c) (local.get $a)) (local.get $b))))
"#

/-- `add3` through subtractions: `a - (0 - b) + c`. -/
def add3SubProg := wat3! r#"
(module
  (func $add3 (export "add3") (param $a i32) (param $b i32) (param $c i32) (result i32)
    (i32.add (i32.sub (local.get $a) (i32.sub (i32.const 0) (local.get $b))) (local.get $c))))
"#

/-- A mutant: `a - b + c`. -/
def add3MutProg := wat3! r#"
(module
  (func $add3 (export "add3") (param $a i32) (param $b i32) (param $c i32) (result i32)
    (i32.add (i32.sub (local.get $a) (local.get $b)) (local.get $c))))
"#

/-- `add3 a b c = (a + b) + c`, total. -/
def add3Spec : FnSpec where
  params := [.i32, .i32, .i32]
  results := [.i32]
  post := .rel .eq (L32 0) (.bin .add (.bin .add (P32 0) (P32 1)) (P32 2))
  total := true

/-- The modules whose binaries `wasm-check vc-emit` adds (file name, module). -/
def demoModules3 : List (String × Module) :=
  [("dbl-add", dblAddProg), ("dbl-shl", dblShlProg), ("dbl-mul", dblMulProg),
   ("dbl-shl2", dblShl2Prog), ("add3", add3Prog), ("add3-assoc", add3AssocProg),
   ("add3-sub", add3SubProg), ("add3-mut", add3MutProg)]

/-! ## Callees with globals, variants over globals -/

/-- `incr2` calls `incr` (`g := g + 1`) twice. -/
def incr2Prog := wat3! r#"
(module
  (global $g (mut i32) (i32.const 0))
  (func $incr
    (global.set $g (i32.add (global.get $g) (i32.const 1))))
  (func $incr2 (export "incr2")
    (call $incr)
    (call $incr)))
"#

/-- A mutant: the callee subtracts. -/
def incr2SubProg := wat3! r#"
(module
  (global $g (mut i32) (i32.const 0))
  (func $incr
    (global.set $g (i32.sub (global.get $g) (i32.const 1))))
  (func $incr2 (export "incr2")
    (call $incr)
    (call $incr)))
"#

/-- A mutant: one call only. -/
def incr1Prog := wat3! r#"
(module
  (global $g (mut i32) (i32.const 0))
  (func $incr
    (global.set $g (i32.add (global.get $g) (i32.const 1))))
  (func $incr2 (export "incr2")
    (call $incr)))
"#

/-- The entry value of global `0` for a function without parameters. -/
abbrev G0' : Tm .i32 := .var .i32 0

/-- `incr`: the final value of global `0` (placeholder `loc 0`: no results) is `g + 1`; total. -/
def incrSpec : FnSpec where
  params := []
  results := []
  globals := [.i32]
  post := .rel .eq (L32 0) (.bin .add G0' (.lit .i32 1))
  total := true

/-- `incr2`: the final value of global `0` is `g + 2`; total. -/
def incr2Spec : FnSpec where
  params := []
  results := []
  globals := [.i32]
  post := .rel .eq (L32 0) (.bin .add G0' (.lit .i32 2))
  total := true

/-- `drain` counts global `0` down to `0` by calls to `dec`; the loop's variant is the global
(`loc 0`: `drain` has no parameters or locals), which only the callee writes. -/
def drainProg := wat3! r#"
(module
  (global $g (mut i32) (i32.const 10))
  (func $dec
    (global.set $g (i32.sub (global.get $g) (i32.const 1))))
  (func $drain (export "drain")
    (block $d
      (loop $l
        (br_if $d (i32.eqz (global.get $g)))
        (call $dec)
        (br $l)))))
"#

/-- `countdown` counts global `0` down to `0` itself (a variant over a global, no call). -/
def countdownProg := wat3! r#"
(module
  (global $g (mut i32) (i32.const 10))
  (func $countdown (export "countdown")
    (block $d
      (loop $l
        (br_if $d (i32.eqz (global.get $g)))
        (global.set $g (i32.sub (global.get $g) (i32.const 1)))
        (br $l)))))
"#

/-- `dec`: if global `0` is nonzero, its final value is `g - 1`; total. -/
def decSpec : FnSpec where
  params := []
  results := []
  globals := [.i32]
  pre := .rel .ne G0' (.lit .i32 0)
  post := .rel .eq (L32 0) (.bin .sub G0' (.lit .i32 1))
  total := true

/-- `drain` and `countdown`: the final value of global `0` is `0`; variant: the global. -/
def drainSpec : FnSpec where
  params := []
  results := []
  globals := [.i32]
  post := .rel .eq (L32 0) (.lit .i32 0)
  var := [L32 0]
  total := true

/-- The modules whose binaries `wasm-check vc-emit` adds (file name, module). -/
def demoModules3G : List (String × Module) :=
  [("incr2-glob-call", incr2Prog), ("incr2-glob-call-sub", incr2SubProg),
   ("incr1-glob-call", incr1Prog), ("drain-glob-call", drainProg),
   ("countdown-glob-var", countdownProg)]

/-! ## The VC cases of `wasm-check bench --vc` -/

/-- The cases of `wasm-check bench --vc`: (name, module, function export, contract,
expected `proved`). Contracts with memory, callees, globals (callees that write globals, variants
over globals) and arithmetic normalisation, against their demonstration modules and mutants. -/
def vcBench : List (String × Module × Nat × String × Bool) :=
  [("double-call", VCLib2.doubleProg, 0, "double", true),
   ("double-call-swap", VCLib2.doubleSwapProg, 0, "double", true),
   ("double-call-sub", VCLib2.doubleSubProg, 0, "double", false),
   ("load2-mem", VCLib2.load2Prog, 0, "load2", true),
   ("load2-mem-off", VCLib2.load2OffProg, 0, "load2", false),
   ("bump-glob", VCLib2.bumpProg, 0, "bump", true),
   ("bump-glob-lost", VCLib2.bumpLostProg, 0, "bump", false),
   ("addn-glob", VCLib2.addnProg, 0, "addn", true),
   ("frame-glob", VCLib2.frameProg, 0, "frame", true),
   ("frame-glob-leak", VCLib2.frameLeakProg, 0, "frame", false),
   ("incr2-glob-call", incr2Prog, 0, "incr2", true),
   ("incr2-glob-call-sub", incr2SubProg, 0, "incr2", false),
   ("incr1-glob-call", incr1Prog, 0, "incr2", false),
   ("drain-glob-call", drainProg, 0, "drain", true),
   ("countdown-glob-var", countdownProg, 0, "countdown", true),
   ("dbl-shl", dblShlProg, 0, "dbl", true),
   ("dbl-mul", dblMulProg, 0, "dbl", true),
   ("dbl-shl2", dblShl2Prog, 0, "dbl", false),
   ("add3-assoc", add3AssocProg, 0, "add3", true),
   ("add3-sub", add3SubProg, 0, "add3", true),
   ("add3-mut", add3MutProg, 0, "add3", false),
   ("isort", Silmaril.WasmSpec.InsertionSort.program, 0, "isort", true),
   ("isort-unsigned", VCLib2.isortUnsignedProg, 0, "isort", false),
   ("oba_find", Silmaril.WasmSpec.BTree.program, 1, "oba_find", true)]

end Silmaril.Wasm.Auto2.VCLib3
