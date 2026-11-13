  ;; `hello`: every request is answered `200 hello` with `content-type: text/plain`
  ;; (`helloResp`).
  (data (i32.const 0x100) "hello")
  (data (i32.const 0x110) "content-type")
  (data (i32.const 0x120) "text/plain")
  ;; the header lines of `helloResp`: one line, name and value
  (data (i32.const 0x130) "\10\01\00\00\0c\00\00\00\20\01\00\00\0a\00\00\00")
  (func (export "wasi:http/incoming-handler@0.2.12#handle") (param $r i32) (param $o i32)
    (call $answer (local.get $o) (i32.const 200) (i32.const 0x130) (i32.const 1)
      (i32.const 0x100) (i32.const 5)))
