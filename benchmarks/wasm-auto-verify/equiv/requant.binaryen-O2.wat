(module
 (type $0 (func (param i32 i32 i32 i32) (result i32)))
 (export "requant" (func $requant))
 (func $requant (param $0 i32) (param $1 i32) (param $2 i32) (param $3 i32) (result i32)
  (local $4 i64)
  (i32.wrap_i64
   (select
    (i64.const 127)
    (local.tee $4
     (select
      (i64.const -128)
      (local.tee $4
       (i64.add
        (i64.extend_i32_s
         (i32.add
          (i32.shr_s
           (local.tee $0
            (select
             (i32.const 2147483647)
             (i32.wrap_i64
              (i64.div_s
               (i64.add
                (select
                 (i64.const 1073741824)
                 (i64.const -1073741823)
                 (i64.ge_s
                  (local.tee $4
                   (i64.mul
                    (i64.extend_i32_s
                     (local.get $0)
                    )
                    (i64.extend_i32_s
                     (local.get $1)
                    )
                   )
                  )
                  (i64.const 0)
                 )
                )
                (local.get $4)
               )
               (i64.const 2147483648)
              )
             )
             (i32.and
              (i32.eq
               (local.get $0)
               (local.get $1)
              )
              (i32.eq
               (local.get $0)
               (i32.const -2147483648)
              )
             )
            )
           )
           (local.get $2)
          )
          (i32.lt_s
           (i32.add
            (i32.shr_s
             (local.tee $1
              (i32.wrap_i64
               (i64.sub
                (i64.shl
                 (i64.const 1)
                 (i64.extend_i32_s
                  (local.get $2)
                 )
                )
                (i64.const 1)
               )
              )
             )
             (i32.const 1)
            )
            (i32.lt_s
             (local.get $0)
             (i32.const 0)
            )
           )
           (i32.and
            (local.get $0)
            (local.get $1)
           )
          )
         )
        )
        (i64.extend_i32_s
         (local.get $3)
        )
       )
      )
      (i64.lt_s
       (local.get $4)
       (i64.const -128)
      )
     )
    )
    (i64.gt_s
     (local.get $4)
     (i64.const 127)
    )
   )
  )
 )
)
