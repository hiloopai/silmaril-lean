  ;; Negative case (c), after common.wat: the core module's start function traps, so no
  ;; instance is ever initialised (`initFail`). The handler would answer `200 hello`.
  (data (i32.const 0x100) "hello")
  (func $boom unreachable)
  (start $boom)
  (func (export "wasi:http/incoming-handler@0.2.12#handle") (param $r i32) (param $o i32)
    (call $answer (local.get $o) (i32.const 200) (i32.const 0) (i32.const 0)
      (i32.const 0x100) (i32.const 5)))
