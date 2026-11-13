(module
  (import "[export]$root" "[task-return]gen" (func $task_return (param i32)))
  (import "[export]$root" "[stream-new-0]gen" (func $stream_new (result i64)))
  (import "[export]$root" "[async-lower][stream-write-0]gen" (func $stream_write (param i32 i32 i32) (result i32)))
  (import "[export]$root" "[stream-drop-writable-0]gen" (func $drop_w (param i32)))
  (import "$root" "[waitable-set-new]" (func $ws_new (result i32)))
  (import "$root" "[waitable-join]" (func $join (param i32 i32)))
  (import "$root" "[waitable-set-wait]" (func $wait (param i32 i32) (result i32)))
  (memory (export "memory") 1)
  (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32) i32.const 4096)
  (func (export "[async-lift-stackful]gen") (param $n i32)
    (local $p i64) (local $w i32) (local $i i32) (local $ws i32) (local $res i32)
    call $stream_new
    local.set $p
    local.get $p
    i32.wrap_i64
    call $task_return
    local.get $p
    i64.const 32
    i64.shr_u
    i32.wrap_i64
    local.set $w
    ;; fill bytes 'a' + i % 26
    (block $done (loop $l
      local.get $i local.get $n i32.ge_u br_if $done
      i32.const 100 local.get $i i32.add
      i32.const 97 local.get $i i32.const 26 i32.rem_u i32.add
      i32.store8
      local.get $i i32.const 1 i32.add local.set $i
      br $l))
    i32.const 0 local.set $i
    ;; write all n bytes: an async write may take only part of them
    call $ws_new local.set $ws
    local.get $w local.get $ws call $join
    (block $wd (loop $wl
      local.get $i local.get $n i32.ge_u br_if $wd
      local.get $w i32.const 100 local.get $i i32.add local.get $n local.get $i i32.sub call $stream_write
      local.set $res
      (if (i32.eq (local.get $res) (i32.const -1))
        (then
          local.get $ws i32.const 200 call $wait drop
          i32.const 204 i32.load local.set $res))
      local.get $i local.get $res i32.const 4 i32.shr_u i32.add local.set $i
      ;; stop if the reader dropped its end
      local.get $res i32.const 15 i32.and i32.const 1 i32.eq br_if $wd
      br $wl))
    local.get $w i32.const 0 call $join
    local.get $w call $drop_w)
)
