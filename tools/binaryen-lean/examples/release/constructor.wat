(module
  (type (func))
  (type (func (result i32)))
  (global $state (mut i32) (i32.const 3))
  (func $initialize (type 0)
    i32.const 9
    global.set $state)
  (func $get (type 1)
    global.get $state)
  (export "get" (func $get))
  (export "state" (global $state))
  (start $initialize))
