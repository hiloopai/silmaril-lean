;; A small spec-style script: a module, assertions on its exports, an invalid and a
;; malformed module.
(module
  (func (export "add") (param $x i32) (param $y i32) (result i32)
    (i32.add (local.get $x) (local.get $y)))
  (func (export "div_s") (param $x i32) (param $y i32) (result i32)
    (i32.div_s (local.get $x) (local.get $y)))
  (func (export "eqz") (param $x i64) (result i32) (i64.eqz (local.get $x))))
(assert_return (invoke "add" (i32.const 1) (i32.const 2)) (i32.const 3))
(assert_return (invoke "add" (i32.const 0x7fffffff) (i32.const 1)) (i32.const 0x80000000))
(assert_trap (invoke "div_s" (i32.const 1) (i32.const 0)) "integer divide by zero")
(assert_return (invoke "eqz" (i64.const 0)) (i32.const 1))
(assert_invalid (module (func (result i32) (i64.const 0))) "type mismatch")
(assert_malformed (module quote "(func (i32.const 0x))") "unknown operator")
(module binary "\00asm" "\01\00\00\00")
