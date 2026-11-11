(module
 (type $0 (func (param i32) (result i32)))
 (global $a (mut i32) (i32.const 1))
 (global $b (mut i32) (i32.const 0))
 (memory $0 1)
 (data $0 (i32.const 0) "\01\02\03\04\05\06\07\08\t\n\0b\0c\r\0e\0f\10\ff\fe\fd\fc\fb\fa\f9\f8")
 (export "adlersum8" (func $adlersum8))
 (func $adlersum8 (param $0 i32) (result i32)
  (global.set $a
   (i32.add
    (global.get $a)
    (i32.load8_u
     (local.get $0)
    )
   )
  )
  (global.set $b
   (i32.add
    (global.get $b)
    (global.get $a)
   )
  )
  (global.set $a
   (i32.add
    (global.get $a)
    (i32.load8_u offset=1
     (local.get $0)
    )
   )
  )
  (global.set $b
   (i32.add
    (global.get $b)
    (global.get $a)
   )
  )
  (global.set $a
   (i32.add
    (global.get $a)
    (i32.load8_u offset=2
     (local.get $0)
    )
   )
  )
  (global.set $b
   (i32.add
    (global.get $b)
    (global.get $a)
   )
  )
  (global.set $a
   (i32.add
    (global.get $a)
    (i32.load8_u offset=3
     (local.get $0)
    )
   )
  )
  (global.set $b
   (i32.add
    (global.get $b)
    (global.get $a)
   )
  )
  (global.set $a
   (i32.add
    (global.get $a)
    (i32.load8_u offset=4
     (local.get $0)
    )
   )
  )
  (global.set $b
   (i32.add
    (global.get $b)
    (global.get $a)
   )
  )
  (global.set $a
   (i32.add
    (global.get $a)
    (i32.load8_u offset=5
     (local.get $0)
    )
   )
  )
  (global.set $b
   (i32.add
    (global.get $b)
    (global.get $a)
   )
  )
  (global.set $a
   (i32.add
    (global.get $a)
    (i32.load8_u offset=6
     (local.get $0)
    )
   )
  )
  (global.set $b
   (i32.add
    (global.get $b)
    (global.get $a)
   )
  )
  (global.set $a
   (i32.add
    (global.get $a)
    (i32.load8_u offset=7
     (local.get $0)
    )
   )
  )
  (global.set $b
   (i32.add
    (global.get $b)
    (global.get $a)
   )
  )
  (i32.or
   (i32.and
    (global.get $a)
    (i32.const 65535)
   )
   (i32.shl
    (global.get $b)
    (i32.const 16)
   )
  )
 )
)
