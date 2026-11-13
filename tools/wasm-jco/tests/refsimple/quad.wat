;; A core module importing `double` from "env" (the wiring of SimpleI.toRef).
(module
  (import "env" "double" (func $d (param i32) (result i32)))
  (import "env" "is-odd" (func $o (param i32) (result i32)))
  (func (export "quad") (param i32) (result i32) local.get 0 call $d call $d)
  (func (export "odd-double") (param i32) (result i32) local.get 0 call $d call $o)
)
