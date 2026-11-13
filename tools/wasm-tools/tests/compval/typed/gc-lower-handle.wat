(component
  (import "r" (type $r (sub resource)))
  (core type $ty (func (param externref) (result (ref extern))))
  (import "f" (func $f (param "x" (borrow $r)) (result (own $r))))
  (core func (canon lower (func $f) gc (core-type $ty))))
