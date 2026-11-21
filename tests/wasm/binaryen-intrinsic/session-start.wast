(module $host
  (func (export "transform") (param i32 i64) (result i32)
    (if (result i32) (i64.eqz (local.get 1))
      (then (unreachable))
      (else (i32.wrap_i64 (local.get 1))))))
(register "host" $host)
