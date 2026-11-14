  ;; `dice` (Silmaril.Servers.Examples.Dice): every face is `(x % 6) + 1`.
  (func $roll_face (result i32) (call $face (i64.const 6)))
  (func $pair_face (result i32) (call $face (i64.const 6)))
