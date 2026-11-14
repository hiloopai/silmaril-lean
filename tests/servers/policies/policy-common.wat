  ;; Shared part of the host policies (world `random-host`): memory, the splitmix64 finaliser
  ;; and `get-random-bytes`. The runner wraps it with one policy (zero.wat, or seeded.wat.in /
  ;; chaos.wat.in with the seed substituted) in a module.
  (memory (export "memory") 1)

  ;; `get-random-bytes` is outside the supported scope (the dice servers do not import it): it
  ;; traps. Core signature of the export: the length, the address of the (pointer, length) pair.
  (func (export "wasi:random/random@0.2.12#get-random-bytes") (param i64) (result i32)
    unreachable)

  ;; The splitmix64 finaliser (Steele, Lea, Flood 2014; the `mix64` variant 13 of Stafford):
  ;;   z := (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9
  ;;   z := (z ^ (z >> 27)) * 0x94D049BB133111EB
  ;;   z ^ (z >> 31)
  (func $mix (param $z i64) (result i64)
    (local.set $z (i64.mul (i64.xor (local.get $z) (i64.shr_u (local.get $z) (i64.const 30)))
      (i64.const 0xBF58476D1CE4E5B9)))
    (local.set $z (i64.mul (i64.xor (local.get $z) (i64.shr_u (local.get $z) (i64.const 27)))
      (i64.const 0x94D049BB133111EB)))
    (i64.xor (local.get $z) (i64.shr_u (local.get $z) (i64.const 31))))
