  ;; `dice-buggy`: dice with a planted bug, `/roll` is `(x % 7) + 1`. Only draws with
  ;; `x % 7 == 6` reveal it (a roll of 7); `/pair` is as in dice.
  (func $roll_face (result i32) (call $face (i64.const 7)))
  (func $pair_face (result i32) (call $face (i64.const 6)))
