;; `gen.py regress`: a deliberately wrong expectation about spectest's identity semantics. $W and
;; $R import spectest's `memory` separately; in the reference interpreter it is one memory
;; (interpreter/host/spectest.ml: a top-level value), so $R sees the 42 that $W stores. The line
;; marked WRONG expects 0, what a registry allocating one memory per import would give. wasmtime
;; must reject this file, on that line.
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
(assert_return (invoke $R "load") (i32.const 0)) ;; WRONG
(assert_return (invoke $W "g") (i32.const 1332))
