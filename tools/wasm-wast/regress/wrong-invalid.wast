;; `gen.py regress`: a deliberately wrong `assert_invalid` (the module is valid). wasmtime must
;; reject this file, on the line marked WRONG.
(assert_invalid (module (func (result i32) (i64.const 0))) "type mismatch")
(assert_invalid (module (func (result i32) (i32.const 0))) "type mismatch") ;; WRONG
