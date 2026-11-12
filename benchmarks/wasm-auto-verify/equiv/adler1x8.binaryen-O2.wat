(module
 (type $0 (func (param i32) (result i32)))
 (global $a (mut i32) (i32.const 1))
 (global $b (mut i32) (i32.const 0))
 (memory $0 1)
 (export "adler8" (func $adler1x8))
 (func $adler1x8 (param $0 i32) (result i32)
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
    (i32.load8_u
     (local.tee $0
      (i32.add
       (local.get $0)
       (i32.const 1)
      )
     )
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
    (i32.load8_u
     (local.tee $0
      (i32.add
       (local.get $0)
       (i32.const 1)
      )
     )
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
    (i32.load8_u
     (local.tee $0
      (i32.add
       (local.get $0)
       (i32.const 1)
      )
     )
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
    (i32.load8_u
     (local.tee $0
      (i32.add
       (local.get $0)
       (i32.const 1)
      )
     )
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
    (i32.load8_u
     (local.tee $0
      (i32.add
       (local.get $0)
       (i32.const 1)
      )
     )
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
    (i32.load8_u
     (local.tee $0
      (i32.add
       (local.get $0)
       (i32.const 1)
      )
     )
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
    (i32.load8_u
     (local.tee $0
      (i32.add
       (local.get $0)
       (i32.const 1)
      )
     )
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
   (i32.const 1)
  )
 )
)
