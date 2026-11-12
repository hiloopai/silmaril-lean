;; A module in the C convention of Silmaril.Wasm.Jco.Meta exporting an interface's functions under
;; wit-component's core names (`test:ai/greet#f`): an allocator alloc(size, align) -> ptr, and
;; string results written as (ptr, len) to an out-pointer passed as the last argument.
(module
  (memory (export "memory") 1)
  (global $bump (mut i32) (i32.const 1024))
  (func $alloc (export "alloc") (param $size i32) (param $align i32) (result i32)
    (local $p i32)
    (local.set $p (i32.and (i32.add (global.get $bump) (i32.const 7)) (i32.const -8)))
    (global.set $bump (i32.add (local.get $p) (local.get $size)))
    (local.get $p))
  (func (export "test:ai/greet#add") (param i32 i32) (result i32) local.get 0 local.get 1 i32.add)
  (data (i32.const 64) "hello, ")
  (func (export "test:ai/greet#hello") (param $p i32) (param $n i32) (param $out i32)
    (local $o i32)
    (local.set $o (call $alloc (i32.add (local.get $n) (i32.const 7)) (i32.const 1)))
    (memory.copy (local.get $o) (i32.const 64) (i32.const 7))
    (memory.copy (i32.add (local.get $o) (i32.const 7)) (local.get $p) (local.get $n))
    (i32.store (local.get $out) (local.get $o))
    (i32.store offset=4 (local.get $out) (i32.add (local.get $n) (i32.const 7))))
  (func (export "count") (param i32 i32) (result i32) local.get 1)
)
