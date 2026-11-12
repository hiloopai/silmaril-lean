(module
 (type $0 (func (param i32) (result i64)))
 (global $n (mut i64) (i64.const 41))
 (export "next" (func $next))
 (func $next (param $0 i32) (result i64)
  (global.set $n
   (i64.add
    (global.get $n)
    (i64.extend_i32_s
     (local.get $0)
    )
   )
  )
  (i64.extend_i32_u
   (i32.wrap_i64
    (global.get $n)
   )
  )
 )
)
