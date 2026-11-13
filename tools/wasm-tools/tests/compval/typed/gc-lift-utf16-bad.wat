(component
  (core module $m
    (type $s (array i8))
    (func (export "f") (param (ref $s)) unreachable))
  (core instance $i (instantiate $m))
  (func (param "x" string) (canon lift (core func $i "f") gc string-encoding=utf16)))
