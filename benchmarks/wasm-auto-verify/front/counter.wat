(module
  (global $n (mut i64) (i64.const 41))
  (func $next (export "next") (param $k i32) (result i64)
    ;; add k (sign-extended) to a 64-bit counter and return its low half, zero-extended
    (global.set $n (i64.add (global.get $n) (i64.extend_i32_s (local.get $k))))
    (i64.extend_i32_u (i32.wrap_i64 (global.get $n)))))
