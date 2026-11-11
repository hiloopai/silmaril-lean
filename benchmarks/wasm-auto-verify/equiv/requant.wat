(module
  (func $requant (export "requant")
    (param $acc i32) (param $mult i32) (param $rshift i32) (param $zp i32) (result i32)
    (local $ab i64) (local $hi i32) (local $x i32) (local $mask i32) (local $q i32)
    (local $r i64)
    (local.set $ab
      (i64.mul (i64.extend_i32_s (local.get $acc)) (i64.extend_i32_s (local.get $mult))))
    (local.set $hi
      (i32.wrap_i64
        (i64.div_s
          (i64.add (local.get $ab)
            (select (i64.const 1073741824) (i64.const -1073741823)
              (i64.ge_s (local.get $ab) (i64.const 0))))
          (i64.const 2147483648))))
    (local.set $x
      (select (i32.const 2147483647) (local.get $hi)
        (i32.and (i32.eq (local.get $acc) (local.get $mult))
          (i32.eq (local.get $acc) (i32.const -2147483648)))))
    (local.set $mask
      (i32.wrap_i64
        (i64.sub (i64.shl (i64.const 1) (i64.extend_i32_s (local.get $rshift))) (i64.const 1))))
    (local.set $q
      (i32.add (i32.shr_s (local.get $x) (local.get $rshift))
        (i32.gt_s (i32.and (local.get $x) (local.get $mask))
          (i32.add (i32.shr_s (local.get $mask) (i32.const 1))
            (i32.lt_s (local.get $x) (i32.const 0))))))
    (local.set $r (i64.add (i64.extend_i32_s (local.get $q)) (i64.extend_i32_s (local.get $zp))))
    (local.set $r (select (i64.const -128) (local.get $r) (i64.lt_s (local.get $r) (i64.const -128))))
    (local.set $r (select (i64.const 127) (local.get $r) (i64.gt_s (local.get $r) (i64.const 127))))
    (i32.wrap_i64 (local.get $r))))
