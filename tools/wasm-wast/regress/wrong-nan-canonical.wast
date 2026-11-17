;; `gen.py regress`: a deliberately wrong NaN pattern. The operand `nan:0x200000` is a
;; non-canonical NaN, so the specification allows any arithmetic NaN as the result of `f32.add`
;; (wasmtime returns the quieted operand, `nan:0x600000`): `nan:arithmetic` holds, `nan:canonical`
;; does not. wasmtime must reject this file, on the line marked WRONG.
(module (func (export "add") (param f32 f32) (result f32) (f32.add (local.get 0) (local.get 1))))
(assert_return (invoke "add" (f32.const nan:0x200000) (f32.const 0)) (f32.const nan:arithmetic))
(assert_return (invoke "add" (f32.const nan:0x200000) (f32.const 0)) (f32.const nan:canonical)) ;; WRONG
