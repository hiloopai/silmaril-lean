(component
  (core type $ty (func (param i32 i32)))
  (import "f" (func $f (param "x" u32)))
  (core func (canon lower (func $f) gc (core-type $ty))))
