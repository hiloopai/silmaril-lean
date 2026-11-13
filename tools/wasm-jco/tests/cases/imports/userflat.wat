(module
  (import "$root" "double" (func $double (param i32) (result i32)))
  (func (export "run") (param i32) (result i32) (i32.add (call $double (local.get 0)) (i32.const 1)))
)
