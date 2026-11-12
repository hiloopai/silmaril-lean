module

public import tests.wasm.auto.FrontBench.Defs
public import tests.wasm.auto.EquivXBench.Defs

/-!
# Pinned inputs of the front-end benchmark, extended set

Cases for the extended summaries (`Silmaril.Wasm.Auto.Bridge`: memory, globals, conversions, trap
guards), copies of the files in `benchmarks/wasm-auto-verify/front/` (`check-inputs.sh` keeps
them equal; `gen.sh` regenerates the Binaryen outputs with the pinned `version_123`):

* `requant`: the kernel (`Silmaril.Wasm.Auto.FrontBench.requantFixed`) against its
  Binaryen `-O2` output (`Silmaril.Wasm.Auto.EquivXBench.requantO2`, the same as `-O3`): `i64`
  arithmetic, `i32.wrap_i64`, `i64.extend_i32_s`, `select`, signed division by `2^31`;
* `adlerSum8`: one 8-way step of the Adler-32 inner loop (byte loads from memory
  `0` with a data segment, the sums in globals), returning both sums so that the comparison
  observes them; its Binaryen `-O2` output and a mutant that reads one byte twice;
* `divRem`: `(x / y) * y + x % y`, with two trap guards; Binaryen `-O2`, the same code written in
  the other order (proved), and a signed mutant (refuted);
* `counter`: a 64-bit counter in a global (`i64.extend_i32_s/u`, `i32.wrap_i64`) and its Binaryen
  `-O2` output.

All cases compare export `0` (`Rel.eq`). The statements observe one invocation from the
instantiated store (its result or trap), so the data segment fixes the memory that the loads
read.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.FrontBenchX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Auto.FrontBench (Case Against requantFixed requantV0)

/-- One 8-way step of the Adler-32 inner loop, returning both sums (`benchmarks/wasm-auto-verify/front/adlersum8.wat`). -/
def adlerSum8 := wat3! r#"
(module
  (memory 1)
  (data (i32.const 0) "\01\02\03\04\05\06\07\08\09\0a\0b\0c\0d\0e\0f\10\ff\fe\fd\fc\fb\fa\f9\f8")
  (global $a (mut i32) (i32.const 1))
  (global $b (mut i32) (i32.const 0))
  (func $adlersum8 (export "adlersum8") (param $p i32) (result i32)
    ;; one 8-way step of the Adler-32 inner loop (benchmarks/wasm-auto-verify/equiv/
    ;; adler8.wat), returning both sums: (b << 16) | (a & 0xffff)
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
    (i32.or (i32.shl (global.get $b) (i32.const 16))
      (i32.and (global.get $a) (i32.const 65535)))))
"#

/-- `adlerSum8`, Binaryen `version_123` `-O2` (`benchmarks/wasm-auto-verify/front/adlersum8.binaryen-O2.wat`). -/
def adlerSum8O2 := wat3! r#"
(module
 (type $0 (func (param i32) (result i32)))
 (global $a (mut i32) (i32.const 1))
 (global $b (mut i32) (i32.const 0))
 (memory $0 1)
 (data $0 (i32.const 0) "\01\02\03\04\05\06\07\08\t\n\0b\0c\r\0e\0f\10\ff\fe\fd\fc\fb\fa\f9\f8")
 (export "adlersum8" (func $adlersum8))
 (func $adlersum8 (param $0 i32) (result i32)
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
  (i32.or
   (i32.and
    (global.get $a)
    (i32.const 65535)
   )
   (i32.shl
    (global.get $b)
    (i32.const 16)
   )
  )
 )
)
"#

/-- A mutant of `adlerSum8`: the last byte is read at offset `6` again (`benchmarks/wasm-auto-verify/front/adlersum8-mutant.wat`). -/
def adlerSum8Mutant := wat3! r#"
(module
  (memory 1)
  (data (i32.const 0) "\01\02\03\04\05\06\07\08\09\0a\0b\0c\0d\0e\0f\10\ff\fe\fd\fc\fb\fa\f9\f8")
  (global $a (mut i32) (i32.const 1))
  (global $b (mut i32) (i32.const 0))
  (func $adlersum8 (export "adlersum8") (param $p i32) (result i32)
    ;; one 8-way step of the Adler-32 inner loop (benchmarks/wasm-auto-verify/equiv/
    ;; adler8.wat), returning both sums: (b << 16) | (a & 0xffff)
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
    (global.set $a (i32.add (global.get $a) (i32.load8_u offset=6 (local.get $p))))
    (global.set $b (i32.add (global.get $b) (global.get $a)))
    (i32.or (i32.shl (global.get $b) (i32.const 16))
      (i32.and (global.get $a) (i32.const 65535)))))
"#

/-- `(x / y) * y + x % y` (unsigned, both trap on `y = 0`) (`benchmarks/wasm-auto-verify/front/divrem.wat`). -/
def divRem := wat3! r#"
(module
  (func $divrem (export "divrem") (param $x i32) (param $y i32) (result i32)
    ;; x = (x / y) * y + x % y, with both traps on y = 0
    (local $q i32)
    (local.set $q (i32.div_u (local.get $x) (local.get $y)))
    (i32.add (i32.mul (local.get $q) (local.get $y)) (i32.rem_u (local.get $x) (local.get $y)))))
"#

/-- `divRem`, Binaryen `version_123` `-O2` (`benchmarks/wasm-auto-verify/front/divrem.binaryen-O2.wat`). -/
def divRemO2 := wat3! r#"
(module
 (type $0 (func (param i32 i32) (result i32)))
 (export "divrem" (func $divrem))
 (func $divrem (param $0 i32) (param $1 i32) (result i32)
  (i32.add
   (i32.mul
    (i32.div_u
     (local.get $0)
     (local.get $1)
    )
    (local.get $1)
   )
   (i32.rem_u
    (local.get $0)
    (local.get $1)
   )
  )
 )
)
"#

/-- `divRem` written in the other order (`benchmarks/wasm-auto-verify/front/divrem-ref.wat`). -/
def divRemRef := wat3! r#"
(module
  (func $divrem (export "divrem") (param $x i32) (param $y i32) (result i32)
    ;; the same, written in the other order: the same guards, the same result
    (i32.add (i32.rem_u (local.get $x) (local.get $y))
      (i32.mul (local.get $y) (i32.div_u (local.get $x) (local.get $y))))))
"#

/-- A mutant of `divRem`: signed division and remainder (`benchmarks/wasm-auto-verify/front/divrem-signed.wat`). -/
def divRemSigned := wat3! r#"
(module
  (func $divrem (export "divrem") (param $x i32) (param $y i32) (result i32)
    ;; a mutant: signed division and remainder (also traps on overflow)
    (i32.add (i32.rem_s (local.get $x) (local.get $y))
      (i32.mul (local.get $y) (i32.div_s (local.get $x) (local.get $y))))))
"#

/-- A 64-bit counter in a global, returning its low half (`benchmarks/wasm-auto-verify/front/counter.wat`). -/
def counter := wat3! r#"
(module
  (global $n (mut i64) (i64.const 41))
  (func $next (export "next") (param $k i32) (result i64)
    ;; add k (sign-extended) to a 64-bit counter and return its low half, zero-extended
    (global.set $n (i64.add (global.get $n) (i64.extend_i32_s (local.get $k))))
    (i64.extend_i32_u (i32.wrap_i64 (global.get $n)))))
"#

/-- `counter`, Binaryen `version_123` `-O2` (`benchmarks/wasm-auto-verify/front/counter.binaryen-O2.wat`). -/
def counterO2 := wat3! r#"
(module
 (type $0 (func (param i32) (result i64)))
 (global $n (mut i64) (i64.const 41))
 (export "next" (func $next))
 (func $next (param $0 i32) (result i64)
  (global.set $n
   (i64.add
    (global.get $n)
    (i64.extend_i32_s
     (local.get $0)
    )
   )
  )
  (i64.extend_i32_u
   (i32.wrap_i64
    (global.get $n)
   )
  )
 )
)
"#

/-- The round-3 cases (export `0`, `Rel.eq`). -/
def casesX : List Case := [
  ⟨"requant-O2", Silmaril.Wasm.Auto.EquivXBench.requantO2, .module requantFixed, .proved⟩,
  ⟨"requant-O2-v0", Silmaril.Wasm.Auto.EquivXBench.requantO2, .module requantV0, .refuted⟩,
  ⟨"adlersum8-O2", adlerSum8O2, .module adlerSum8, .proved⟩,
  ⟨"adlersum8-mutant", adlerSum8Mutant, .module adlerSum8, .refuted⟩,
  ⟨"divrem-O2", divRemO2, .module divRem, .proved⟩,
  ⟨"divrem-ref", divRemRef, .module divRem, .proved⟩,
  ⟨"divrem-signed", divRemSigned, .module divRem, .refuted⟩,
  ⟨"counter-O2", counterO2, .module counter, .proved⟩]

/-- Every case of the front-end benchmark: the first set and the extended set. -/
def allCases : List Case := Silmaril.Wasm.Auto.FrontBench.cases ++ casesX

end Silmaril.Wasm.Auto.FrontBenchX
