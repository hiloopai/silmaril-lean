  ;; `echo`: answer `200` with the request's content, read in at most `echoFuel` (16) reads of
  ;; `readLen` (65536) bytes; `500` when an answer has an unexpected shape or the reads run out.
  (func $fail (param $o i32)
    (call $answer (local.get $o) (i32.const 500) (i32.const 0) (i32.const 0) (i32.const 0) (i32.const 0)))

  (func (export "wasi:http/incoming-handler@0.2.12#handle") (param $r i32) (param $o i32)
    (local $s i32) (local $fuel i32) (local $acc i32) (local $n i32)
    (call $req_consume (local.get $r) (global.get $ret))
    (if (i32.load8_u (global.get $ret)) (then (return (call $fail (local.get $o)))))
    (call $in_stream (i32.load (i32.add (global.get $ret) (i32.const 4))) (global.get $ret))
    (if (i32.load8_u (global.get $ret)) (then (return (call $fail (local.get $o)))))
    (local.set $s (i32.load (i32.add (global.get $ret) (i32.const 4))))
    (local.set $fuel (i32.const 16))
    (loop $l
      (if (i32.eqz (local.get $fuel)) (then (return (call $fail (local.get $o)))))
      (local.set $fuel (i32.sub (local.get $fuel) (i32.const 1)))
      (call $in_read (local.get $s) (i64.const 65536) (global.get $ret))
      (if (i32.eqz (i32.load8_u (global.get $ret)))
        (then
          ;; ok(bytes): append them to the buffer
          (local.set $n (i32.load (i32.add (global.get $ret) (i32.const 8))))
          (memory.copy (i32.add (i32.const 0x10000) (local.get $acc))
            (i32.load (i32.add (global.get $ret) (i32.const 4))) (local.get $n))
          (local.set $acc (i32.add (local.get $acc) (local.get $n)))
          (br $l)))
      ;; err(closed): the whole content was read
      (if (i32.eq (i32.load8_u (i32.add (global.get $ret) (i32.const 4))) (i32.const 1))
        (then (return (call $answer (local.get $o) (i32.const 200) (i32.const 0) (i32.const 0)
            (i32.const 0x10000)
          (local.get $acc))))))
    (call $fail (local.get $o)))
