(module
  (type (func (param i32) (result i32)))
  (type (func (param) (result i32)))
  (type (func (param i64) (result i64)))
  (memory 1 2)
  (func (type 0) (local)
    i32.const 0 local.get 0 i32.store 0 offset=4 align=4
    i32.const 0 i32.load 0 offset=4 align=4)
  (func (type 1) (local) memory.size 0)
  (func (type 0) (local) local.get 0 memory.grow 0)
  (func (type 0) (local)
    i32.const 0 local.get 0 i32.store8 0 offset=1 align=1
    i32.const 0 i32.load8_s 0 offset=1 align=1)
  (func (type 2) (local)
    i32.const 0 local.get 0 i64.store 0 offset=8 align=8
    i32.const 0 i64.load 0 offset=8 align=8)
  (func (type 0) (local) local.get 0 i32.load 0 offset=0 align=4)
  (export "run" (func 0))
  (export "pages" (func 1))
  (export "grow" (func 2))
  (export "narrow" (func 3))
  (export "wide" (func 4))
  (export "peek" (func 5))
  (export "memory" (memory 0)))
