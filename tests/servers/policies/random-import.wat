  ;; The import of the dice servers beyond common.wat: wasi:random/random `get-random-u64`
  ;; (core signature: no parameters, the u64 as an i64). The runner puts it before common.wat
  ;; (imports come first in a module).
  (import "wasi:random/random@0.2.12" "get-random-u64" (func $random_u64 (result i64)))
