;; `gen.py regress`: a deliberately wrong expectation about cross-module state. $Mem exports a
;; memory and a mutable global; $Writer imports both (and spectest's `print_i32`), stores 42 at
;; address 0 and sets the global to 7; $Reader imports the same memory and global from the
;; registered names and reads them. Both values are written by one module and read by another.
;; wasmtime must reject this file, on the line marked WRONG (the stored value is 42, not 43).
(module $Mem
  (memory (export "mem") 1)
  (global (export "g") (mut i32) (i32.const 0)))
(register "Mem" $Mem)
(module $Writer
  (import "spectest" "print_i32" (func $print (param i32)))
  (import "Mem" "mem" (memory 1))
  (import "Mem" "g" (global $g (mut i32)))
  (func (export "write") (i32.store (i32.const 0) (i32.const 42)) (global.set $g (i32.const 7))
    (call $print (i32.const 42))))
(module $Reader
  (import "Mem" "mem" (memory 1))
  (import "Mem" "g" (global $g (mut i32)))
  (func (export "load") (param i32) (result i32) (i32.load (local.get 0)))
  (func (export "g") (result i32) (global.get $g)))
(invoke $Writer "write")
(assert_return (invoke $Reader "g") (i32.const 7))
(assert_return (get $Mem "g") (i32.const 7))
(assert_return (invoke $Reader "load" (i32.const 0)) (i32.const 43)) ;; WRONG
