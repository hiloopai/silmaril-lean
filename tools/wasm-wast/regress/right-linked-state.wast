;; `gen.py regress`: the control of wrong-linked-state.wast: the same modules and commands,
;; with the right expectation (42) on the last line. wasmtime must accept this file.
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
(assert_return (invoke $Reader "load" (i32.const 0)) (i32.const 42))
