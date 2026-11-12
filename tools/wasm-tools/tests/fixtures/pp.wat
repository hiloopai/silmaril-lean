(module $m
  (type $t (func (param i32) (result i32)))
  (memory 1)
  (func $f (export "f") (type $t) (param $x i32) (result i32)
    (local $y i32)
    block $b
      local.get $x
      br_if $b
    end
    (i32.add (local.get $x) (i32.const 1)))
  (data (i32.const 8) "hi"))
