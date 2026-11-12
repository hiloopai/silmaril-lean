(module
  (func $divrem (export "divrem") (param $x i32) (param $y i32) (result i32)
    ;; the same, written in the other order: the same guards, the same result
    (i32.add (i32.rem_u (local.get $x) (local.get $y))
      (i32.mul (local.get $y) (i32.div_u (local.get $x) (local.get $y))))))
