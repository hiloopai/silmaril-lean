(module
  (memory (export "memory") 1)
  (global $bump (mut i32) (i32.const 1024))
  (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
    (local $p i32)
    (local.set $p (i32.and (i32.add (global.get $bump) (i32.const 7)) (i32.const -8)))
    (global.set $bump (i32.add (local.get $p) (local.get 3)))
    (local.get $p))
  ;; 17 flat parameters spill: one pointer to 17 u32s
  (func (export "sum17") (param $p i32) (result i32)
    (local $i i32) (local $s i32)
    (block $d (loop $l
      (br_if $d (i32.ge_u (local.get $i) (i32.const 17)))
      (local.set $s (i32.add (local.get $s) (i32.load (i32.add (local.get $p) (i32.shl (local.get $i) (i32.const 2))))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $l)))
    (local.get $s))
  ;; two flat results: returned through a pointer
  (func (export "divmod") (param $a i32) (param $b i32) (result i32)
    (i32.store (i32.const 16) (i32.div_u (local.get $a) (local.get $b)))
    (i32.store (i32.const 20) (i32.rem_u (local.get $a) (local.get $b)))
    (i32.const 16))
)
