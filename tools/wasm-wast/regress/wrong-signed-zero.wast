;; `gen.py regress`: a deliberately wrong signed zero. `f32.neg 0` is `-0`, whose bits differ
;; from `+0`; exact float expectations compare bits. wasmtime must reject this file, on the line
;; marked WRONG.
(module (func (export "neg") (param f32) (result f32) (f32.neg (local.get 0))))
(assert_return (invoke "neg" (f32.const 0)) (f32.const -0))
(assert_return (invoke "neg" (f32.const 0)) (f32.const 0)) ;; WRONG
