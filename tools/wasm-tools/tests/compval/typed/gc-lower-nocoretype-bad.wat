(component
  (import "f" (func $f (param "x" u32)))
  (core func (canon lower (func $f) gc)))
