  ;; `hello`: every request is answered `200 hello` (`helloResp`).
  (data (i32.const 0x100) "hello")
  (func (export "wasi:http/incoming-handler@0.2.12#handle") (param $r i32) (param $o i32)
    (call $answer (local.get $o) (i32.const 200) (i32.const 0x100) (i32.const 5)))
