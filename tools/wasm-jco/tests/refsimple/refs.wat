;; A core module without imports whose exports follow the canonical ABI's flat types.
(module
  (func (export "add") (param i32 i32) (result i32) local.get 0 local.get 1 i32.add)
  (func (export "sub") (param i32 i32) (result i32) local.get 0 local.get 1 i32.sub)
  (func (export "neg") (param i64) (result i64) i64.const 0 local.get 0 i64.sub)
  (func (export "is-zero") (param i32) (result i32) local.get 0 i32.eqz)
  (func (export "next") (param i32) (result i32) local.get 0 i32.const 1 i32.add)
  (global $n (mut i32) (i32.const 0))
  (func (export "count") (result i32) global.get $n i32.const 1 i32.add global.set $n global.get $n)
  (func (export "tick"))
  (func (export "boom") (param i32) (result i32) unreachable)
)
