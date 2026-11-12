(module
  (func $divrem (export "divrem") (param $x i32) (param $y i32) (result i32)
    ;; a mutant: signed division and remainder (also traps on overflow)
    (i32.add (i32.rem_s (local.get $x) (local.get $y))
      (i32.mul (local.get $y) (i32.div_s (local.get $x) (local.get $y))))))
