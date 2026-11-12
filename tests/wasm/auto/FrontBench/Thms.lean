module

public import tests.wasm.auto.FrontBench.Defs
public import Silmaril.Wasm.Auto.Front.Thms
public import tests.wasm.auto.FrontBench.Proofs.Proved

@[expose] public section

/-!
# The front-end benchmark: refutations and proofs

The refuted cases of `Silmaril.Wasm.Auto.FrontBench.cases`, as theorems: each counterexample (the
one `wasm-check` reports) is replayed on silmaril-lean's verified interpreter by kernel
evaluation (`wasm_diff_refute`). The `identical` verdict: `modEquiv_refl`.

The proved cases (first case set, `tests.wasm.auto.FrontBench.Proofs.Proved`), at every profile and for
both relations: `maxSelect_equiv`, `addSwap_equiv`, `div10Mulhi_equiv` (`wasm_prove_base`), and the
reference functions `max_meets`, `add_meets`, `div10Mulhi_meets`. Still open: `sum-ref` (a loop:
the summaries do not cover loops, and the VC generator proves partial correctness only).
-/

namespace Silmaril.Wasm.Auto.FrontBench

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Auto.Front
open Silmaril.Wasm.SingleThreaded (profile)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Verify (refOracle)

/-- Unsigned comparison does not refine `Max`: on `(0, 0x80000000)` it returns `0x80000000`,
`Max` returns `0`. -/
theorem maxUnsigned_not_refines :
    ¬ ModRefines Rel.eq.toProp (profile refOracle) maxUnsigned maxProg 0 := by
  wasm_diff_refute [Val.i32 0, Val.i32 0x80000000]

/-- The same against the reference function, at every specification profile. -/
theorem maxUnsigned_not_meets (nd : Bool) :
    ¬ ModMeets Rel.eq.toProp (Profile.spec nd {}) maxUnsigned 0 maxRef := by
  wasm_diff_refute [Val.i32 0, Val.i32 0x80000000]

/-- Subtraction is not addition (both directions of the equivalence fail). -/
theorem addSub_not_equiv : ¬ ModEquiv Rel.eq.toProp (profile refOracle) addSub addProg 0 := by
  wasm_diff_refute [Val.i32 0, Val.i32 1]

/-- The off-by-one loop misses `sum 1 = 1`, at every specification profile. -/
theorem sumOffByOne_not_meets (nd : Bool) :
    ¬ ModMeets Rel.eq.toProp (Profile.spec nd {}) sumOffByOne 0 sumRef := by
  wasm_diff_refute [Val.i32 1]

/-- The `div10` mutant (magic constant `0xCCCCCCCCCCCCCCCC`) gives `10 / 10 = 0`. -/
theorem div10Mutant_not_refines :
    ¬ ModRefines Rel.eq.toProp (profile refOracle) div10Mutant div10Ref 0 := by
  wasm_diff_refute [Val.i64 10]

/-- `requant` v0 does not refine the fixed kernel: with `acc = mult = 0`, `rshift = 2^31 - 1`,
`zp = 2^31 - 1` the 32-bit addition of the zero point wraps (`-128` instead of `127`). -/
theorem requantV0_not_refines :
    ¬ ModRefines Rel.eq.toProp (profile refOracle) requantV0 requantFixed 0 := by
  wasm_diff_refute [Val.i32 0, Val.i32 0, Val.i32 0x7fffffff, Val.i32 0x7fffffff]

/-- The same with the saturated product `acc = mult = -2^31`, `rshift = 0`, `zp = 1`. -/
theorem requantV0_not_refines' :
    ¬ ModRefines Rel.eq.toProp (profile refOracle) requantV0 requantFixed 0 := by
  wasm_diff_refute [Val.i32 0x80000000, Val.i32 0x80000000, Val.i32 0, Val.i32 1]

/-- `Max` is equivalent to itself (the `identical` verdict). -/
theorem max_equiv_self (P : Profile) : ModEquiv Rel.eq.toProp P maxProg maxProg 0 :=
  modEquiv_refl .eq P maxProg 0

end Silmaril.Wasm.Auto.FrontBench
