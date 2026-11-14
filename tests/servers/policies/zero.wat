  ;; Policy `zero`: every `get-random-u64` is 0 (a pure deterministic host).
  (func (export "wasi:random/random@0.2.12#get-random-u64") (result i64)
    (i64.const 0))
