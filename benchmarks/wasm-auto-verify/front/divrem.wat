(module
  (func $divrem (export "divrem") (param $x i32) (param $y i32) (result i32)
    ;; x = (x / y) * y + x % y, with both traps on y = 0
    (local $q i32)
    (local.set $q (i32.div_u (local.get $x) (local.get $y)))
    (i32.add (i32.mul (local.get $q) (local.get $y)) (i32.rem_u (local.get $x) (local.get $y)))))
