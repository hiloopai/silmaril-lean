;; `gen.py regress`: a deliberately wrong `assert_trap` (6 / 3 does not trap). wasmtime must reject
;; this file, on the line marked WRONG.
(module
  (func (export "div") (param i32 i32) (result i32) (i32.div_u (local.get 0) (local.get 1))))
(assert_trap (invoke "div" (i32.const 1) (i32.const 0)) "integer divide by zero")
(assert_trap (invoke "div" (i32.const 6) (i32.const 3)) "integer divide by zero") ;; WRONG
