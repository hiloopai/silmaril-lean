;; `gen.py regress`: the control of wrong-spectest-shared.wast, with the right expectation (42) on
;; the third assertion. wasmtime must accept this file. The same script is kernel-checked against
;; the typed spectest host as the rows silmaril.wasm_wast.spectest_host.*
;; (Silmaril.Project.WasmWast.SpectestHost).
(module $W
  (import "spectest" "memory" (memory 1))
  (import "spectest" "print_i32" (func $print (param i32)))
  (import "spectest" "global_i32" (global $g1 i32))
  (import "spectest" "global_i32" (global $g2 i32))
  (func (export "store") (i32.store (i32.const 0) (i32.const 42)) (call $print (i32.const 42)))
  (func (export "g") (result i32) (i32.add (global.get $g1) (global.get $g2))))
(module $R
  (import "spectest" "memory" (memory 1))
  (func (export "load") (result i32) (i32.load (i32.const 0))))
(assert_return (invoke $R "load") (i32.const 0))
(assert_return (invoke $W "store"))
(assert_return (invoke $R "load") (i32.const 42))
(assert_return (invoke $W "g") (i32.const 1332))
