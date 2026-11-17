;; `gen.py regress`: a deliberately wrong expectation about the state left by a failed
;; instantiation. $Shared exports a table and a memory and is registered. The module in `assert_trap` imports both; by Wasm 3.0 §4.4
;; ($instantiate: element segments, then data segments, then the start call) its element segment
;; stores $seven at table index 0, its first data segment writes 42 at address 0, and its second
;; data segment is out of bounds and traps. The trap aborts the instantiation, but the earlier
;; writes stay in the shared store (nothing is rolled back), and the failed module is not
;; registered or current. $Reader imports the same table and memory and observes them.
;; wasmtime must reject this file, on the line marked WRONG (a rolled-back memory would read 0).
(module $Shared
  (table (export "tab") 2 funcref)
  (memory (export "mem") 1))
(register "Shared" $Shared)
(assert_trap
  (module
    (import "Shared" "tab" (table 2 funcref))
    (import "Shared" "mem" (memory 1))
    (func $seven (result i32) (i32.const 7))
    (elem (i32.const 0) $seven)
    (data (i32.const 0) "\2a")
    (data (i32.const 65536) "\01"))
  "out of bounds memory access")
(module $Reader
  (type $r (func (result i32)))
  (import "Shared" "tab" (table 2 funcref))
  (import "Shared" "mem" (memory 1))
  (func (export "load0") (result i32) (i32.load8_u (i32.const 0)))
  (func (export "call") (param i32) (result i32) (call_indirect (type $r) (local.get 0))))
(assert_return (invoke $Reader "call" (i32.const 0)) (i32.const 7))
(assert_trap (invoke $Reader "call" (i32.const 1)) "uninitialized element")
(assert_return (invoke $Reader "load0") (i32.const 0)) ;; WRONG: the write before the trap persists (42)
