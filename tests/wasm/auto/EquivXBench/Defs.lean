module

public import Silmaril.Wasm.Auto.Equiv.Defs
public import tests.wasm.auto.FrontBench.Defs

/-!
# Pinned inputs of the extended equivalence benchmark

Copies of the files in `benchmarks/wasm-auto-verify/equiv/` (`check-inputs.sh` keeps them
equal), parsed by `wat3!`:

* `requant`: the int8 requantisation kernel (`Silmaril.Wasm.Auto.FrontBench.requantFixed`)
  and its Binaryen `version_123` `-O2` output (`requant.binaryen-O2.wat`; `-O3` gives the same
  text): Binaryen merges the six scratch locals into one `i64` local and reuses two parameters,
  folds the code into one expression with `local.tee`, and reorients a comparison;
* `adler8`: one iteration of the 8-way unrolled inner loop of the Adler-32 kernel
  (`a += p[k]; b += a` for `k = 0..7`, sums in globals, loads `i32.load8_u offset=k`), and its
  Binaryen `-O2` output;
* `adler1x8`: the rolled byte loop body (`a += *p++; b += a`) unrolled eight times (pointer
  increments, loads at offset 0), and its Binaryen `-O2` output.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.EquivXBench

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- The body of the first function of a module. -/
def bodyOf (m : Module) : List Instr :=
  match m.funcs with
  | f :: _ => f.body
  | [] => []

/-- `requant`, Binaryen `-O2` (`benchmarks/wasm-auto-verify/equiv/requant.binaryen-O2.wat`). -/
def requantO2 := wat3! r#"
(module
 (type $0 (func (param i32 i32 i32 i32) (result i32)))
 (export "requant" (func $requant))
 (func $requant (param $0 i32) (param $1 i32) (param $2 i32) (param $3 i32) (result i32)
  (local $4 i64)
  (i32.wrap_i64
   (select
    (i64.const 127)
    (local.tee $4
     (select
      (i64.const -128)
      (local.tee $4
       (i64.add
        (i64.extend_i32_s
         (i32.add
          (i32.shr_s
           (local.tee $0
            (select
             (i32.const 2147483647)
             (i32.wrap_i64
              (i64.div_s
               (i64.add
                (select
                 (i64.const 1073741824)
                 (i64.const -1073741823)
                 (i64.ge_s
                  (local.tee $4
                   (i64.mul
                    (i64.extend_i32_s
                     (local.get $0)
                    )
                    (i64.extend_i32_s
                     (local.get $1)
                    )
                   )
                  )
                  (i64.const 0)
                 )
                )
                (local.get $4)
               )
               (i64.const 2147483648)
              )
             )
             (i32.and
              (i32.eq
               (local.get $0)
               (local.get $1)
              )
              (i32.eq
               (local.get $0)
               (i32.const -2147483648)
              )
             )
            )
           )
           (local.get $2)
          )
          (i32.lt_s
           (i32.add
            (i32.shr_s
             (local.tee $1
              (i32.wrap_i64
               (i64.sub
                (i64.shl
                 (i64.const 1)
                 (i64.extend_i32_s
                  (local.get $2)
                 )
                )
                (i64.const 1)
               )
              )
             )
             (i32.const 1)
            )
            (i32.lt_s
             (local.get $0)
             (i32.const 0)
            )
           )
           (i32.and
            (local.get $0)
            (local.get $1)
           )
          )
         )
        )
        (i64.extend_i32_s
         (local.get $3)
        )
       )
      )
      (i64.lt_s
       (local.get $4)
       (i64.const -128)
      )
     )
    )
    (i64.gt_s
     (local.get $4)
     (i64.const 127)
    )
   )
  )
 )
)
"#

/-- The local types of `requant` (four parameters, six locals). -/
def requantLocals : List IntType := [.i32, .i32, .i32, .i32, .i64, .i32, .i32, .i32, .i32, .i64]

/-- `adler8` (`benchmarks/wasm-auto-verify/equiv/adler8.wat`). -/
def adler8 := wat3! r#"
(module
  (memory 1)
  (global $a (mut i32) (i32.const 1))
  (global $b (mut i32) (i32.const 0))
  (func $adler8 (export "adler8") (param $p i32) (result i32)
    ;; one iteration of the 8-way unrolled inner loop of adler/start.c:
    ;; a += p[k]; b += a for k = 0..7, with the sums in globals; returns p + 8
    (global.set $a (i32.add (global.get $a) (i32.load8_u offset=0 (local.get $p))))
    (global.set $b (i32.add (global.get $b) (global.get $a)))
    (global.set $a (i32.add (global.get $a) (i32.load8_u offset=1 (local.get $p))))
    (global.set $b (i32.add (global.get $b) (global.get $a)))
    (global.set $a (i32.add (global.get $a) (i32.load8_u offset=2 (local.get $p))))
    (global.set $b (i32.add (global.get $b) (global.get $a)))
    (global.set $a (i32.add (global.get $a) (i32.load8_u offset=3 (local.get $p))))
    (global.set $b (i32.add (global.get $b) (global.get $a)))
    (global.set $a (i32.add (global.get $a) (i32.load8_u offset=4 (local.get $p))))
    (global.set $b (i32.add (global.get $b) (global.get $a)))
    (global.set $a (i32.add (global.get $a) (i32.load8_u offset=5 (local.get $p))))
    (global.set $b (i32.add (global.get $b) (global.get $a)))
    (global.set $a (i32.add (global.get $a) (i32.load8_u offset=6 (local.get $p))))
    (global.set $b (i32.add (global.get $b) (global.get $a)))
    (global.set $a (i32.add (global.get $a) (i32.load8_u offset=7 (local.get $p))))
    (global.set $b (i32.add (global.get $b) (global.get $a)))
    (i32.add (local.get $p) (i32.const 8))))
"#

/-- `adler8`, Binaryen `-O2`. -/
def adler8O2 := wat3! r#"
(module
 (type $0 (func (param i32) (result i32)))
 (global $a (mut i32) (i32.const 1))
 (global $b (mut i32) (i32.const 0))
 (memory $0 1)
 (export "adler8" (func $adler8))
 (func $adler8 (param $0 i32) (result i32)
  (global.set $a
   (i32.add
    (global.get $a)
    (i32.load8_u
     (local.get $0)
    )
   )
  )
  (global.set $b
   (i32.add
    (global.get $b)
    (global.get $a)
   )
  )
  (global.set $a
   (i32.add
    (global.get $a)
    (i32.load8_u offset=1
     (local.get $0)
    )
   )
  )
  (global.set $b
   (i32.add
    (global.get $b)
    (global.get $a)
   )
  )
  (global.set $a
   (i32.add
    (global.get $a)
    (i32.load8_u offset=2
     (local.get $0)
    )
   )
  )
  (global.set $b
   (i32.add
    (global.get $b)
    (global.get $a)
   )
  )
  (global.set $a
   (i32.add
    (global.get $a)
    (i32.load8_u offset=3
     (local.get $0)
    )
   )
  )
  (global.set $b
   (i32.add
    (global.get $b)
    (global.get $a)
   )
  )
  (global.set $a
   (i32.add
    (global.get $a)
    (i32.load8_u offset=4
     (local.get $0)
    )
   )
  )
  (global.set $b
   (i32.add
    (global.get $b)
    (global.get $a)
   )
  )
  (global.set $a
   (i32.add
    (global.get $a)
    (i32.load8_u offset=5
     (local.get $0)
    )
   )
  )
  (global.set $b
   (i32.add
    (global.get $b)
    (global.get $a)
   )
  )
  (global.set $a
   (i32.add
    (global.get $a)
    (i32.load8_u offset=6
     (local.get $0)
    )
   )
  )
  (global.set $b
   (i32.add
    (global.get $b)
    (global.get $a)
   )
  )
  (global.set $a
   (i32.add
    (global.get $a)
    (i32.load8_u offset=7
     (local.get $0)
    )
   )
  )
  (global.set $b
   (i32.add
    (global.get $b)
    (global.get $a)
   )
  )
  (i32.add
   (local.get $0)
   (i32.const 8)
  )
 )
)
"#

/-- `adler1x8` (`benchmarks/wasm-auto-verify/equiv/adler1x8.wat`). -/
def adler1x8 := wat3! r#"
(module
  (memory 1)
  (global $a (mut i32) (i32.const 1))
  (global $b (mut i32) (i32.const 0))
  (func $adler1x8 (export "adler8") (param $p i32) (result i32)
    ;; the rolled byte loop body of adler/start.c (a += *p++; b += a), unrolled 8 times
    (global.set $a (i32.add (global.get $a) (i32.load8_u (local.get $p))))
    (local.set $p (i32.add (local.get $p) (i32.const 1)))
    (global.set $b (i32.add (global.get $b) (global.get $a)))
    (global.set $a (i32.add (global.get $a) (i32.load8_u (local.get $p))))
    (local.set $p (i32.add (local.get $p) (i32.const 1)))
    (global.set $b (i32.add (global.get $b) (global.get $a)))
    (global.set $a (i32.add (global.get $a) (i32.load8_u (local.get $p))))
    (local.set $p (i32.add (local.get $p) (i32.const 1)))
    (global.set $b (i32.add (global.get $b) (global.get $a)))
    (global.set $a (i32.add (global.get $a) (i32.load8_u (local.get $p))))
    (local.set $p (i32.add (local.get $p) (i32.const 1)))
    (global.set $b (i32.add (global.get $b) (global.get $a)))
    (global.set $a (i32.add (global.get $a) (i32.load8_u (local.get $p))))
    (local.set $p (i32.add (local.get $p) (i32.const 1)))
    (global.set $b (i32.add (global.get $b) (global.get $a)))
    (global.set $a (i32.add (global.get $a) (i32.load8_u (local.get $p))))
    (local.set $p (i32.add (local.get $p) (i32.const 1)))
    (global.set $b (i32.add (global.get $b) (global.get $a)))
    (global.set $a (i32.add (global.get $a) (i32.load8_u (local.get $p))))
    (local.set $p (i32.add (local.get $p) (i32.const 1)))
    (global.set $b (i32.add (global.get $b) (global.get $a)))
    (global.set $a (i32.add (global.get $a) (i32.load8_u (local.get $p))))
    (local.set $p (i32.add (local.get $p) (i32.const 1)))
    (global.set $b (i32.add (global.get $b) (global.get $a)))
    (local.get $p)))
"#

/-- `adler1x8`, Binaryen `-O2`. -/
def adler1x8O2 := wat3! r#"
(module
 (type $0 (func (param i32) (result i32)))
 (global $a (mut i32) (i32.const 1))
 (global $b (mut i32) (i32.const 0))
 (memory $0 1)
 (export "adler8" (func $adler1x8))
 (func $adler1x8 (param $0 i32) (result i32)
  (global.set $a
   (i32.add
    (global.get $a)
    (i32.load8_u
     (local.get $0)
    )
   )
  )
  (global.set $b
   (i32.add
    (global.get $b)
    (global.get $a)
   )
  )
  (global.set $a
   (i32.add
    (global.get $a)
    (i32.load8_u
     (local.tee $0
      (i32.add
       (local.get $0)
       (i32.const 1)
      )
     )
    )
   )
  )
  (global.set $b
   (i32.add
    (global.get $b)
    (global.get $a)
   )
  )
  (global.set $a
   (i32.add
    (global.get $a)
    (i32.load8_u
     (local.tee $0
      (i32.add
       (local.get $0)
       (i32.const 1)
      )
     )
    )
   )
  )
  (global.set $b
   (i32.add
    (global.get $b)
    (global.get $a)
   )
  )
  (global.set $a
   (i32.add
    (global.get $a)
    (i32.load8_u
     (local.tee $0
      (i32.add
       (local.get $0)
       (i32.const 1)
      )
     )
    )
   )
  )
  (global.set $b
   (i32.add
    (global.get $b)
    (global.get $a)
   )
  )
  (global.set $a
   (i32.add
    (global.get $a)
    (i32.load8_u
     (local.tee $0
      (i32.add
       (local.get $0)
       (i32.const 1)
      )
     )
    )
   )
  )
  (global.set $b
   (i32.add
    (global.get $b)
    (global.get $a)
   )
  )
  (global.set $a
   (i32.add
    (global.get $a)
    (i32.load8_u
     (local.tee $0
      (i32.add
       (local.get $0)
       (i32.const 1)
      )
     )
    )
   )
  )
  (global.set $b
   (i32.add
    (global.get $b)
    (global.get $a)
   )
  )
  (global.set $a
   (i32.add
    (global.get $a)
    (i32.load8_u
     (local.tee $0
      (i32.add
       (local.get $0)
       (i32.const 1)
      )
     )
    )
   )
  )
  (global.set $b
   (i32.add
    (global.get $b)
    (global.get $a)
   )
  )
  (global.set $a
   (i32.add
    (global.get $a)
    (i32.load8_u
     (local.tee $0
      (i32.add
       (local.get $0)
       (i32.const 1)
      )
     )
    )
   )
  )
  (global.set $b
   (i32.add
    (global.get $b)
    (global.get $a)
   )
  )
  (i32.add
   (local.get $0)
   (i32.const 1)
  )
 )
)
"#

end Silmaril.Wasm.Auto.EquivXBench
