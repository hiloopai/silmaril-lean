(module
  (type (func (param i32) (result i32)))
  (import "env" "twice" (func (type 0)))
  (func (type 0) (local)
    local.get 0 call 0 i32.const 2 i32.add)
  (export "host" (func 0))
  (export "run" (func 1)))
