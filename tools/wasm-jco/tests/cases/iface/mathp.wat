;; Exports the interface test:iface/math: a record parameter (point, two flat u32) and an
;; enum (color, one i32).
(module
  (func (export "test:iface/math#add") (param i32 i32) (result i32) (i32.add (local.get 0) (local.get 1)))
  (func (export "test:iface/math#norm") (param i32 i32) (result i32) (i32.add (local.get 0) (local.get 1)))
  (func (export "test:iface/math#hue") (param i32) (result i32)
    (i32.rem_u (i32.add (local.get 0) (i32.const 1)) (i32.const 3)))
)
