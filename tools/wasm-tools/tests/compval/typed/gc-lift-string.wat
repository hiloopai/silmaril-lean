(component
  (core module $m
    (type $s (array i8))
    (func (export "f") (param (ref $s)) (result i32) unreachable))
  (core instance $i (instantiate $m))
  (func (param "x" string) (result u32) (canon lift (core func $i "f") gc string-encoding=utf8)))
