(module
  (type (func (param i32) (result i32)))
  (func (type 0) (local) local.get 0
    (if (result i32)
      (then (block (result i32) i32.const 7))
      (else (loop (result i32) i32.const 9))))
  (func (type 0) (local)
    (block (result)
      (loop (result)
        local.get 0 i32.eqz br_if 1
        local.get 0 i32.const 1 i32.sub local.set 0 br 0))
    local.get 0)
  (export "choose" (func 0))
  (export "countdown" (func 1)))
