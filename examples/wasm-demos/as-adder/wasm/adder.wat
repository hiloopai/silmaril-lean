(module
 (type $0 (func (param i32 i32) (result i32)))
 (type $1 (func (param i32) (result i32)))
 (memory $0 0)
 (export "add" (func $assembly/index/add))
 (export "mul" (func $assembly/index/mul))
 (export "max" (func $assembly/index/max))
 (export "odd" (func $assembly/index/odd))
 (export "memory" (memory $0))
 (func $assembly/index/odd (param $0 i32) (result i32)
  local.get $0
  i32.const 1
  i32.shl
  i32.const 1
  i32.add
 )
 (func $assembly/index/mul (param $0 i32) (param $1 i32) (result i32)
  local.get $0
  local.get $1
  i32.mul
 )
 (func $assembly/index/max (param $0 i32) (param $1 i32) (result i32)
  local.get $1
  local.get $0
  local.get $0
  local.get $1
  i32.lt_s
  select
 )
 (func $assembly/index/add (param $0 i32) (param $1 i32) (result i32)
  local.get $0
  local.get $1
  i32.add
 )
)
