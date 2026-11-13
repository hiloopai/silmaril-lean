;; `_initialize` under a task hook: wit-component calls it once every module is instantiated,
;; between `__wasm_task_hook(6)` and `__wasm_task_hook(7)`. Each event is one hex digit
;; (code + 1) of `$events`; `_initialize` adds the digit `a`.
(module
  (memory (export "memory") 1)
  (global $events (mut i64) (i64.const 0))
  (func $push (param i64)
    global.get $events
    i64.const 16
    i64.mul
    local.get 0
    i64.add
    global.set $events)
  (func (export "__wasm_task_hook") (param i32)
    local.get 0
    i64.extend_i32_u
    i64.const 1
    i64.add
    call $push)
  (func (export "_initialize")
    i64.const 10
    call $push)
  (func (export "events") (result i64)
    global.get $events)
)
