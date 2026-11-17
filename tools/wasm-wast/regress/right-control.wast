;; The controls of `gen.py regress`: the modules of the `wrong-*.wast` scripts with the right
;; expectations. wasmtime must accept this file, so that the failures of the wrong scripts are
;; their wrong expectations and not a broken wasmtime.
(module
  (func (export "one") (result i32) (i32.const 1))
  (func (export "div") (param i32 i32) (result i32) (i32.div_u (local.get 0) (local.get 1))))
(assert_return (invoke "one") (i32.const 1))
(assert_return (invoke "div" (i32.const 6) (i32.const 3)) (i32.const 2))
(assert_trap (invoke "div" (i32.const 1) (i32.const 0)) "integer divide by zero")
(assert_invalid (module (func (result i32) (i64.const 0))) "type mismatch")
(assert_malformed (module binary "\00asm" "\02\00\00\00") "unknown binary version")
(module
  (func (export "add") (param f32 f32) (result f32) (f32.add (local.get 0) (local.get 1)))
  (func (export "neg") (param f32) (result f32) (f32.neg (local.get 0))))
(assert_return (invoke "add" (f32.const nan:0x200000) (f32.const 0)) (f32.const nan:arithmetic))
(assert_return (invoke "add" (f32.const nan) (f32.const 0)) (f32.const nan:canonical))
(assert_return (invoke "neg" (f32.const 0)) (f32.const -0))
