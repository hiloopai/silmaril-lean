(component
  (core type $l (array (mut i64)))
  (core type $ty (func (param (ref null $l)) (result i32)))
  (import "f" (func $f (param "x" (list u64)) (result char)))
  (core func (canon lower (func $f) gc (core-type $ty))))
