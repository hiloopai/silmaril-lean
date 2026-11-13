;; `greet`: read the values of `x-name` from the request's headers and answer
  ;; `200 hello <first value>` (`200 hello world` without one) (`greet`).
  (data (i32.const 0x100) "x-name")
  (data (i32.const 0x110) "hello ")
  (data (i32.const 0x120) "world")

  (func (export "wasi:http/incoming-handler@0.2.12#handle") (param $r i32) (param $o i32)
    (local $h i32) (local $vp i32) (local $p i32) (local $n i32)
    (local.set $h (call $req_headers (local.get $r)))
    (call $fields_get (local.get $h) (i32.const 0x100) (i32.const 6) (global.get $ret))
    ;; the list<field-value> in the return area: its pointer and its length
    (local.set $vp (i32.load (global.get $ret)))
    (if (i32.load offset=4 (global.get $ret))
      (then
        (local.set $p (i32.load (local.get $vp)))
        (local.set $n (i32.load offset=4 (local.get $vp))))
      (else
        (local.set $p (i32.const 0x120))
        (local.set $n (i32.const 5))))
    ;; `hello ` and the name, in the buffer at 0x10000
    (memory.copy (i32.const 0x10000) (i32.const 0x110) (i32.const 6))
    (memory.copy (i32.const 0x10006) (local.get $p) (local.get $n))
    (call $answer (local.get $o) (i32.const 200) (i32.const 0) (i32.const 0) (i32.const 0x10000)
      (i32.add (local.get $n) (i32.const 6))))
