;; The task hook (`__wasm_task_hook`) records each event code as one hex digit (code + 1) in
;; `$events`; `greet` returns the record: the string parameter is lowered with the export
;; allocator (codes 12/13), then the export is entered (code 0).
(module
  (memory (export "memory") 1)
  (global $events (mut i64) (i64.const 0))
  (global $bump (mut i32) (i32.const 1024))
  (func (export "__wasm_task_hook") (param i32)
    global.get $events
    i64.const 16
    i64.mul
    local.get 0
    i64.extend_i32_u
    i64.const 1
    i64.add
    i64.add
    global.set $events)
  (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
    (local $p i32)
    global.get $bump
    local.set $p
    global.get $bump
    local.get 3
    i32.add
    global.set $bump
    local.get $p)
  (func (export "greet") (param i32 i32) (result i64)
    global.get $events
    local.get 1
    i64.extend_i32_u
    i64.const 4096
    i64.mul
    i64.add)
  (func (export "add") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.add)
  (func (export "events") (result i64)
    global.get $events)
)
