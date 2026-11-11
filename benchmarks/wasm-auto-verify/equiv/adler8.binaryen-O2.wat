(module
 (type $0 (func (param i32) (result i32)))
 (global $a (mut i32) (i32.const 1))
 (global $b (mut i32) (i32.const 0))
 (memory $0 1)
 (export "adler8" (func $adler8))
 (func $adler8 (param $0 i32) (result i32)
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
  (i32.add
   (local.get $0)
   (i32.const 8)
  )
 )
)
