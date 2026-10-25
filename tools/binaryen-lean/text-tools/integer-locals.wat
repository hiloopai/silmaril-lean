(module
  (type (func (param i32) (result i32)))
  (func (type 0) (local i32)
    local.get 0
    i32.const 2
    i32.mul
    local.set 1
    local.get 1
    i32.const 2
    i32.add)
  (export "run" (func 0)))
