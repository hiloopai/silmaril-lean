;; `gen.py regress`: a deliberately wrong expectation about a host reference. `(ref.extern n)` is
;; the host reference n converted to `extern` (the reference interpreter at WebAssembly/spec
;; 608711107b: `Extern.ExternRef (Script.HostRef n)`, interpreter/text/parser.mly l. 1509); as a
;; result pattern it holds only for that same reference (interpreter/script/runner.ml l. 464-477,
;; `Value.eq_ref`). The module stores the argument in a mutable `externref` global and in a table
;; and reads them back. wasmtime must reject this file, on the line marked WRONG (the stored
;; reference is `(ref.extern 1)`, not `(ref.extern 2)`).
(module
  (global $g (mut externref) (ref.null extern))
  (table $t 2 externref)
  (func (export "set") (param externref) (global.set $g (local.get 0)) (table.set $t (i32.const 1) (local.get 0)))
  (func (export "get") (result externref) (global.get $g))
  (func (export "get-t") (param i32) (result externref) (table.get $t (local.get 0))))
(assert_return (invoke "get") (ref.null extern))
(assert_return (invoke "set" (ref.extern 1)))
(assert_return (invoke "get-t" (i32.const 0)) (ref.null extern))
(assert_return (invoke "get-t" (i32.const 1)) (ref.extern 1))
(assert_return (invoke "get") (ref.extern 2)) ;; WRONG
