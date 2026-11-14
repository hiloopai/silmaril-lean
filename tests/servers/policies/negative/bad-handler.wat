;; Negative case (b): a core module whose export has the name of wasi:http's `handle` with the
;; core signature of `handle: func(x: u32)` (bad-handler.wit). It answers nothing.
(module
  (func (export "wasi:http/incoming-handler@0.2.12#handle") (param i32)))
