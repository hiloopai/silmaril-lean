(module
 (type $0 (func (param i32) (result i32)))
 (type $1 (func (param i32 i32 i32) (result i32)))
 (type $2 (func (param i32 i32) (result i32)))
 (type $3 (func (param i32 i64 i32) (result i32)))
 (type $4 (func (param i64 i32) (result i32)))
 (type $5 (func (param i64) (result i32)))
 (type $6 (func (param i64 i64 i32) (result i64)))
 (type $7 (func (param i32) (result i64)))
 (type $8 (func (param i64 i64) (result i32)))
 (type $9 (func (param i32 i64 i32) (result i64)))
 (type $10 (func (param i32 i64 i64) (result i32)))
 (type $11 (func (param i32 i64) (result i32)))
 (type $12 (func (param i32 i32 i64) (result i32)))
 (type $13 (func (param i64) (result i64)))
 (type $14 (func (param i64 i32 i32) (result i32)))
 (type $15 (func (param i64 i32 i32) (result i64)))
 (type $16 (func (param i32 i32 i64) (result i64)))
 (type $17 (func (param i64 i64 i32) (result i32)))
 (type $18 (func (param i32 i32) (result i64)))
 (export "f0" (func $0))
 (export "f1" (func $1))
 (export "f2" (func $2))
 (export "f3" (func $3))
 (export "f4" (func $4))
 (export "f5" (func $5))
 (export "f6" (func $6))
 (export "f7" (func $7))
 (export "f8" (func $8))
 (export "f9" (func $9))
 (export "f10" (func $10))
 (export "f11" (func $11))
 (export "f12" (func $12))
 (export "f13" (func $13))
 (export "f14" (func $14))
 (export "f15" (func $15))
 (export "f16" (func $16))
 (export "f17" (func $17))
 (export "f18" (func $18))
 (export "f19" (func $12))
 (export "f20" (func $19))
 (export "f21" (func $20))
 (export "f22" (func $21))
 (export "f23" (func $22))
 (export "f24" (func $23))
 (export "f25" (func $12))
 (export "f26" (func $24))
 (export "f27" (func $25))
 (export "f28" (func $26))
 (export "f29" (func $27))
 (export "f30" (func $28))
 (export "f31" (func $7))
 (export "f32" (func $29))
 (export "f33" (func $30))
 (export "f34" (func $31))
 (export "f35" (func $32))
 (export "f36" (func $33))
 (export "f37" (func $34))
 (export "f38" (func $35))
 (export "f39" (func $36))
 (export "f40" (func $37))
 (export "f41" (func $38))
 (export "f42" (func $39))
 (export "f43" (func $40))
 (export "f44" (func $41))
 (export "f45" (func $42))
 (export "f46" (func $43))
 (export "f47" (func $44))
 (export "f48" (func $45))
 (export "f49" (func $46))
 (export "f50" (func $47))
 (export "f51" (func $48))
 (export "f52" (func $49))
 (export "f53" (func $50))
 (export "f54" (func $51))
 (export "f55" (func $52))
 (export "f56" (func $53))
 (export "f57" (func $54))
 (export "f58" (func $55))
 (export "f59" (func $56))
 (func $0 (param $0 i32) (param $1 i64) (param $2 i32) (result i32)
  (local.get $0)
 )
 (func $1 (param $0 i32) (result i32)
  (i32.mul
   (i32.lt_u
    (i32.shr_s
     (i32.const 63)
     (i32.or
      (local.get $0)
      (i32.const 32)
     )
    )
    (i32.ne
     (i32.sub
      (local.get $0)
      (i32.const 2)
     )
     (i32.shl
      (local.get $0)
      (i32.const 30)
     )
    )
   )
   (local.get $0)
  )
 )
 (func $2 (param $0 i32) (result i32)
  (i32.const 0)
 )
 (func $3 (param $0 i32) (result i32)
  (i32.ge_s
   (i32.add
    (i32.div_u
     (i32.const 32)
     (i32.const 0)
    )
    (i32.rem_u
     (i32.shl
      (i32.const 1)
      (local.get $0)
     )
     (local.get $0)
    )
   )
   (i32.const 0)
  )
 )
 (func $4 (param $0 i32) (param $1 i64) (param $2 i32) (result i64)
  (i64.const -2)
 )
 (func $5 (param $0 i64) (param $1 i32) (param $2 i32) (result i32)
  (i32.or
   (i32.or
    (i32.add
     (i32.shr_u
      (local.get $1)
      (local.get $1)
     )
     (local.get $2)
    )
    (i64.ge_s
     (i64.div_u
      (local.get $0)
      (local.get $0)
     )
     (i64.shr_u
      (local.get $0)
      (i64.const 8)
     )
    )
   )
   (i32.const 7)
  )
 )
 (func $6 (param $0 i32) (param $1 i64) (param $2 i64) (result i32)
  (i32.rem_u
   (i32.div_u
    (i32.const 8)
    (local.get $0)
   )
   (i32.eqz
    (i32.shr_s
     (i32.and
      (local.get $0)
      (i32.const 1)
     )
     (i64.gt_s
      (local.get $2)
      (i64.const 8)
     )
    )
   )
  )
 )
 (func $7 (param $0 i32) (param $1 i64) (result i32)
  (local.get $0)
 )
 (func $8 (param $0 i32) (param $1 i32) (param $2 i32) (result i32)
  (local.get $2)
 )
 (func $9 (param $0 i64) (param $1 i32) (result i32)
  (i32.div_u
   (i32.add
    (i32.rem_u
     (local.get $1)
     (i32.const 3)
    )
    (local.get $1)
   )
   (i32.and
    (i32.add
     (local.get $1)
     (i32.const 8)
    )
    (i32.const 23)
   )
  )
 )
 (func $10 (param $0 i32) (param $1 i32) (param $2 i64) (result i32)
  (local.get $0)
 )
 (func $11 (param $0 i64) (result i32)
  (i32.or
   (i32.rem_u
    (i32.const -4)
    (i32.rem_u
     (i32.const 0)
     (i32.const 0)
    )
   )
   (i32.const 32)
  )
 )
 (func $12 (param $0 i32) (result i32)
  (local.get $0)
 )
 (func $13 (param $0 i32) (param $1 i32) (param $2 i32) (result i32)
  (i32.mul
   (i32.mul
    (i32.rem_u
     (i32.xor
      (local.get $1)
      (i32.const 8)
     )
     (local.get $2)
    )
    (i32.and
     (local.get $1)
     (local.get $2)
    )
   )
   (i32.shl
    (i32.xor
     (local.get $0)
     (local.get $2)
    )
    (local.get $0)
   )
  )
 )
 (func $14 (param $0 i64) (param $1 i64) (param $2 i32) (result i64)
  (i64.const 0)
 )
 (func $15 (param $0 i32) (param $1 i32) (result i32)
  (i32.rem_u
   (i32.const 3)
   (i32.div_u
    (i32.const 1)
    (i32.shr_u
     (i32.const 0)
     (i32.rem_u
      (local.get $1)
      (local.get $0)
     )
    )
   )
  )
 )
 (func $16 (param $0 i32) (param $1 i32) (param $2 i32) (result i32)
  (i32.mul
   (i32.div_u
    (i32.sub
     (i32.shr_s
      (local.get $0)
      (local.get $0)
     )
     (local.get $0)
    )
    (i32.div_u
     (i32.add
      (local.get $0)
      (local.get $2)
     )
     (i32.const 0)
    )
   )
   (i32.const 0)
  )
 )
 (func $17 (param $0 i32) (param $1 i64) (param $2 i32) (result i32)
  (i32.or
   (i32.sub
    (i32.rem_u
     (i32.rem_u
      (i32.const 7)
      (local.get $2)
     )
     (local.get $0)
    )
    (i32.shl
     (i32.or
      (local.get $2)
      (i32.const 31)
     )
     (i32.sub
      (local.get $0)
      (i32.const 1)
     )
    )
   )
   (i32.shl
    (i32.sub
     (i32.or
      (local.get $0)
      (local.get $2)
     )
     (i32.const 32)
    )
    (i32.div_u
     (i32.xor
      (local.get $0)
      (i32.const 3)
     )
     (local.get $0)
    )
   )
  )
 )
 (func $18 (param $0 i64) (result i32)
  (i32.shr_u
   (i32.sub
    (i32.const 1)
    (i32.shr_s
     (i32.const 2)
     (i64.lt_u
      (local.get $0)
      (i64.const 31)
     )
    )
   )
   (i32.const 1)
  )
 )
 (func $19 (param $0 i64) (param $1 i32) (param $2 i32) (result i64)
  (i64.shr_s
   (i64.shr_s
    (i64.or
     (i64.rem_u
      (local.get $0)
      (local.get $0)
     )
     (i64.shr_u
      (i64.const 255)
      (local.get $0)
     )
    )
    (i64.add
     (i64.sub
      (i64.const 3)
      (local.get $0)
     )
     (i64.shr_s
      (i64.const -2)
      (local.get $0)
     )
    )
   )
   (i64.div_u
    (i64.const 2)
    (i64.sub
     (i64.const 0)
     (i64.shr_u
      (local.get $0)
      (local.get $0)
     )
    )
   )
  )
 )
 (func $20 (param $0 i32) (param $1 i32) (param $2 i64) (result i64)
  (i64.div_u
   (i64.rem_u
    (i64.and
     (local.get $2)
     (i64.shl
      (i64.const 2)
      (local.get $2)
     )
    )
    (i64.xor
     (local.get $2)
     (i64.shr_u
      (local.get $2)
      (local.get $2)
     )
    )
   )
   (i64.const 0)
  )
 )
 (func $21 (param $0 i64) (param $1 i64) (param $2 i32) (result i32)
  (i32.and
   (i32.rem_u
    (i32.shr_s
     (i32.const 3)
     (local.get $2)
    )
    (i64.lt_u
     (local.get $1)
     (i64.add
      (local.get $0)
      (i64.const 2)
     )
    )
   )
   (i32.or
    (i32.mul
     (i32.div_u
      (local.get $2)
      (i32.const 0)
     )
     (i32.shr_s
      (local.get $2)
      (local.get $2)
     )
    )
    (i64.gt_u
     (i64.shr_u
      (local.get $1)
      (i64.const 5)
     )
     (i64.shr_u
      (local.get $0)
      (local.get $1)
     )
    )
   )
  )
 )
 (func $22 (param $0 i32) (result i32)
  (i32.shl
   (local.get $0)
   (local.get $0)
  )
 )
 (func $23 (param $0 i32) (param $1 i32) (result i32)
  (i32.div_u
   (i32.const -2)
   (i32.const 0)
  )
 )
 (func $24 (param $0 i32) (param $1 i32) (result i32)
  (i32.add
   (i32.xor
    (local.get $0)
    (i32.const 1)
   )
   (i32.shr_s
    (i32.add
     (local.get $1)
     (i32.and
      (local.get $0)
      (i32.const 2)
     )
    )
    (i32.eq
     (local.get $0)
     (i32.const -2)
    )
   )
  )
 )
 (func $25 (param $0 i64) (param $1 i64) (param $2 i32) (result i64)
  (i64.and
   (local.get $0)
   (i64.shr_s
    (i64.mul
     (local.get $1)
     (i64.mul
      (local.get $1)
      (local.get $1)
     )
    )
    (local.get $0)
   )
  )
 )
 (func $26 (param $0 i64) (result i64)
  (i64.or
   (local.get $0)
   (i64.sub
    (i64.const 0)
    (i64.mul
     (local.get $0)
     (i64.add
      (i64.mul
       (local.get $0)
       (local.get $0)
      )
      (i64.shr_u
       (i64.const 3)
       (local.get $0)
      )
     )
    )
   )
  )
 )
 (func $27 (param $0 i32) (param $1 i64) (param $2 i32) (result i32)
  (i32.eqz
   (local.get $2)
  )
 )
 (func $28 (param $0 i64) (param $1 i64) (param $2 i32) (result i64)
  (i64.div_u
   (i64.mul
    (i64.xor
     (i64.mul
      (local.get $1)
      (i64.const 7)
     )
     (local.get $0)
    )
    (local.get $1)
   )
   (i64.and
    (i64.div_u
     (i64.and
      (local.get $0)
      (i64.const 255)
     )
     (i64.rem_u
      (i64.const 2)
      (local.get $1)
     )
    )
    (i64.rem_u
     (local.get $0)
     (i64.rem_u
      (local.get $1)
      (local.get $1)
     )
    )
   )
  )
 )
 (func $29 (param $0 i32) (result i64)
  (i64.const -5)
 )
 (func $30 (param $0 i32) (param $1 i32) (result i32)
  (i32.mul
   (local.get $0)
   (local.get $0)
  )
 )
 (func $31 (param $0 i32) (param $1 i64) (param $2 i32) (result i32)
  (i32.rem_u
   (i64.ge_s
    (local.get $1)
    (i64.shl
     (i64.shr_s
      (local.get $1)
      (local.get $1)
     )
     (local.get $1)
    )
   )
   (i32.mul
    (i32.rem_u
     (i32.const -2)
     (i32.const 0)
    )
    (i32.or
     (i32.add
      (local.get $0)
      (local.get $2)
     )
     (i32.div_u
      (local.get $2)
      (i32.const 255)
     )
    )
   )
  )
 )
 (func $32 (param $0 i64) (result i32)
  (i64.eqz
   (i64.add
    (i64.add
     (local.get $0)
     (i64.const 31)
    )
    (i64.or
     (i64.sub
      (i64.const 32)
      (local.get $0)
     )
     (i64.rem_u
      (local.get $0)
      (local.get $0)
     )
    )
   )
  )
 )
 (func $33 (param $0 i32) (param $1 i32) (result i32)
  (i32.div_u
   (i32.add
    (i32.sub
     (i32.const 2)
     (local.get $0)
    )
    (i32.rem_u
     (local.tee $0
      (i32.add
       (local.get $0)
       (local.get $1)
      )
     )
     (i32.shl
      (i32.const 255)
      (local.get $1)
     )
    )
   )
   (i32.div_u
    (i32.add
     (i32.mul
      (local.get $1)
      (i32.const 7)
     )
     (local.get $0)
    )
    (local.get $1)
   )
  )
 )
 (func $34 (param $0 i32) (param $1 i32) (param $2 i32) (result i32)
  (i32.const 7)
 )
 (func $35 (param $0 i32) (param $1 i32) (param $2 i32) (result i32)
  (i32.div_u
   (i32.mul
    (i32.mul
     (i32.sub
      (local.get $1)
      (local.get $2)
     )
     (i32.shr_u
      (local.get $1)
      (local.get $1)
     )
    )
    (i32.and
     (i32.add
      (local.get $1)
      (local.get $2)
     )
     (i32.add
      (local.get $0)
      (local.get $2)
     )
    )
   )
   (i32.rem_u
    (i32.ne
     (i32.and
      (local.get $1)
      (local.get $2)
     )
     (i32.const 8)
    )
    (i32.const 3)
   )
  )
 )
 (func $36 (param $0 i32) (param $1 i32) (param $2 i32) (result i32)
  (i32.const 1)
 )
 (func $37 (param $0 i32) (param $1 i32) (result i32)
  (local.get $0)
 )
 (func $38 (param $0 i32) (param $1 i64) (param $2 i32) (result i32)
  (i32.add
   (local.get $0)
   (i32.rem_u
    (local.get $2)
    (i32.shr_s
     (i32.const 1)
     (local.get $0)
    )
   )
  )
 )
 (func $39 (param $0 i32) (param $1 i64) (param $2 i64) (result i32)
  (i32.add
   (local.get $0)
   (i32.ne
    (local.get $0)
    (i32.rem_u
     (i32.rem_u
      (local.get $0)
      (i32.const 3)
     )
     (i32.const 0)
    )
   )
  )
 )
 (func $40 (param $0 i32) (param $1 i64) (param $2 i32) (result i64)
  (i64.const -1)
 )
 (func $41 (param $0 i32) (param $1 i32) (result i64)
  (i64.const 0)
 )
 (func $42 (param $0 i32) (result i32)
  (i32.ne
   (i32.shr_u
    (i32.const 7)
    (local.get $0)
   )
   (i32.const 0)
  )
 )
 (func $43 (param $0 i64) (result i64)
  (i64.const -1)
 )
 (func $44 (param $0 i32) (param $1 i32) (param $2 i32) (result i32)
  (i32.add
   (i32.shr_u
    (local.get $2)
    (i32.add
     (i32.add
      (local.get $1)
      (local.get $1)
     )
     (i32.rem_u
      (i32.const 2)
      (local.get $0)
     )
    )
   )
   (i32.lt_u
    (local.get $2)
    (i32.shr_u
     (i32.shr_u
      (local.get $0)
      (local.get $1)
     )
     (local.get $1)
    )
   )
  )
 )
 (func $45 (param $0 i32) (result i32)
  (i32.and
   (i32.rem_u
    (i32.shr_s
     (i32.sub
      (i32.const 32)
      (local.get $0)
     )
     (local.get $0)
    )
    (local.get $0)
   )
   (local.get $0)
  )
 )
 (func $46 (param $0 i32) (param $1 i64) (param $2 i32) (result i32)
  (local.get $2)
 )
 (func $47 (param $0 i32) (result i64)
  (i64.const 8)
 )
 (func $48 (param $0 i32) (param $1 i64) (result i32)
  (i32.const -1)
 )
 (func $49 (param $0 i64) (param $1 i64) (result i32)
  (i32.sub
   (i32.const 34)
   (i64.eqz
    (local.get $0)
   )
  )
 )
 (func $50 (param $0 i64) (param $1 i64) (result i32)
  (i32.const -18)
 )
 (func $51 (param $0 i64) (param $1 i64) (result i32)
  (i32.const -2)
 )
 (func $52 (param $0 i64) (param $1 i32) (result i32)
  (i32.shl
   (local.get $1)
   (i32.or
    (local.get $1)
    (i32.shr_s
     (i32.const 8)
     (local.get $1)
    )
   )
  )
 )
 (func $53 (param $0 i32) (param $1 i32) (param $2 i64) (result i32)
  (i32.div_u
   (local.get $0)
   (local.get $0)
  )
 )
 (func $54 (param $0 i64) (param $1 i32) (result i32)
  (i32.or
   (local.get $1)
   (i32.mul
    (local.get $1)
    (local.get $1)
   )
  )
 )
 (func $55 (param $0 i32) (result i64)
  (i64.const 0)
 )
 (func $56 (param $0 i32) (param $1 i32) (result i32)
  (i32.shr_s
   (i32.add
    (i32.add
     (i32.add
      (local.get $0)
      (local.get $0)
     )
     (i32.lt_u
      (local.get $0)
      (local.get $1)
     )
    )
    (local.get $1)
   )
   (i32.const 1)
  )
 )
)
