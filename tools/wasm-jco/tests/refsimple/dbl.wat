(module
  (func (export "double") (param i32) (result i32) local.get 0 i32.const 1 i32.shl)
  (func (export "is-odd") (param i32) (result i32) local.get 0 i32.const 1 i32.and)
)
