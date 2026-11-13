;; A module that imports its memory (`env.memory`, wit-component's import-memory layout: the
;; component defines it) and returns strings and lists from it.
(module
  (import "env" "memory" (memory 1))
  (global $bump (mut i32) (i32.const 2048))
  (data (i32.const 16) "hello")
  (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
    (local $p i32)
    global.get $bump
    local.set $p
    global.get $bump
    local.get 3
    i32.add
    global.set $bump
    local.get $p)
  ;; name: the constant "hello" followed by nothing
  (func (export "name") (result i32)
    i32.const 512
    i32.const 16
    i32.store
    i32.const 516
    i32.const 5
    i32.store
    i32.const 512)
  ;; echo: returns its string argument (pointer and length as given)
  (func (export "echo") (param i32 i32) (result i32)
    i32.const 520
    local.get 0
    i32.store
    i32.const 524
    local.get 1
    i32.store
    i32.const 520)
  ;; total: the sum of a list<u32>
  (func (export "total") (param i32 i32) (result i32)
    (local $s i32)
    block
      loop
        local.get 1
        i32.eqz
        br_if 1
        local.get $s
        local.get 0
        i32.load
        i32.add
        local.set $s
        local.get 0
        i32.const 4
        i32.add
        local.set 0
        local.get 1
        i32.const 1
        i32.sub
        local.set 1
        br 0
      end
    end
    local.get $s)
)
