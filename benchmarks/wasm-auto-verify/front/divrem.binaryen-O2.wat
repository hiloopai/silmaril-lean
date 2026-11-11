(module
 (type $0 (func (param i32 i32) (result i32)))
 (export "divrem" (func $divrem))
 (func $divrem (param $0 i32) (param $1 i32) (result i32)
  (i32.add
   (i32.mul
    (i32.div_u
     (local.get $0)
     (local.get $1)
    )
    (local.get $1)
   )
   (i32.rem_u
    (local.get $0)
    (local.get $1)
   )
  )
 )
)
