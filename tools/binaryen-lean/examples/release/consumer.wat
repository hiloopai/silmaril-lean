(module
  (import "Provider" "answer" (func $answer (result i32)))
  (func (export "run") (result i32)
    (i32.add (call $answer) (i32.const 1))))
