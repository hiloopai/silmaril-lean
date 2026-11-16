;; `gen.py regress`: a deliberately wrong `assert_return` (the function returns 1). wasmtime must
;; reject this file, on the line marked WRONG.
(module (func (export "one") (result i32) (i32.const 1)))
(assert_return (invoke "one") (i32.const 1))
(assert_return (invoke "one") (i32.const 2)) ;; WRONG
