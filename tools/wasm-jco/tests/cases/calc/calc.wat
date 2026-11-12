(module
  (func (export "add") (param i32 i32) (result i32) local.get 0 local.get 1 i32.add)
  (func (export "sub") (param i32 i32) (result i32) local.get 0 local.get 1 i32.sub)
  ;; pick(c, x): if c and x = some(v) then v else 0; option<u32> is (disc, payload)
  (func (export "pick") (param $c i32) (param $d i32) (param $v i32) (result i32)
    (select (local.get $v) (i32.const 0) (i32.and (local.get $c) (local.get $d))))
  (func (export "scale") (param i64 f64) (result f64) local.get 0 f64.convert_i64_u local.get 1 f64.mul)
)
