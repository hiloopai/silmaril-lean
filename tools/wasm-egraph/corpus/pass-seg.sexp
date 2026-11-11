; Function pairs for `wasm-check pass --egraph-tv-seg` (tests/pass-seg.sh):
; `emit-seg` writes the lhs bodies as one module and the rhs bodies as another (export `f<k>`
; for the `k`-th case), `tv-seg --func` proves each pair from function entry, and
; `wasm-check pass` lifts the proofs of the exports its own stages leave unknown to
; module equivalence (`Silmaril.Wasm.Auto.BridgeSeg.modEquiv_of_funcEquiv`).
(case mul-shl-renumbered (locals i32) (mode func) (alocals i32) (blocals i64 i32)
  (lhs "local.get 0; i32.const 8; i32.mul; local.set 1; local.get 1; i32.const 1; i32.xor")
  (rhs "local.get 0; i32.const 3; i32.shl; local.set 2; local.get 2; i32.const 1; i32.xor"))
(case divu-pow2-merged (locals i32 i32) (mode func) (alocals i32 i32) (blocals i32)
  (lhs "local.get 0; i32.const 16; i32.div_u; local.set 2; local.get 1; i32.const 4; i32.rem_u; local.set 3; local.get 2; local.get 3; i32.or")
  (rhs "local.get 0; i32.const 4; i32.shr_u; local.set 2; local.get 1; i32.const 3; i32.and; local.get 2; i32.or"))
(case eqz-pair-reordered (locals i64) (mode func) (alocals i32 i64) (blocals i64 i32)
  (lhs "local.get 0; i64.eqz; i32.eqz; local.set 1; local.get 1")
  (rhs "local.get 0; i64.const 0; i64.ne; local.set 2; local.get 2"))
(case same-body (locals i32) (mode func) (alocals i32) (blocals i32)
  (lhs "local.get 0; i32.const 1; i32.add; local.set 1; local.get 1")
  (rhs "local.get 0; i32.const 1; i32.add; local.set 1; local.get 1"))
(case div-trap (locals i32 i32) (mode func) (alocals i32) (blocals)
  (lhs "local.get 0; local.get 1; i32.div_u; local.set 2; local.get 0; i32.const 2; i32.mul")
  (rhs "local.get 0; local.get 1; i32.div_u; drop; local.get 0; i32.const 1; i32.shl"))
