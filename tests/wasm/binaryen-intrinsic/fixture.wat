(module
  (import "host" "transform" (func $transform (param i32 i64) (result i32)))
  (func (export "choose") (param i32 i64) (result i32)
    (if (result i32) (local.get 0)
      (then (call $transform (local.get 0) (local.get 1)))
      (else (i32.const 7))))
  (func (export "branch") (param i32)
    (block $done (br_if $done (local.get 0)))))
