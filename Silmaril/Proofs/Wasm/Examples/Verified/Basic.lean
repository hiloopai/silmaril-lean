module

public import Silmaril.Wasm.Examples.Verified.Defs
public import Silmaril.Wasm.Verify.FnSpec.Thms
public import Silmaril.Wasm.Verify.Kernel.Defs
public import Silmaril.Wasm.Examples.Wat.Thms

/-!
# Verified Wasm functions: proofs

Each `…_vc` is `wasm_vc [spec, prog]`, plus one line of arithmetic for `abs` (the value of
`(-x).toInt`) and for `sum` (one loop iteration, `Silmaril.Wasm.Examples.Wat.triangle_step`).
`doubleBytes_decode`: silmaril-lean's decoder maps `double.wasm` to `doubleWat` (kernel
evaluation, `kernel_rfl`); `double_verified`: function `0` of the decoded binary meets
`doubleSpec`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.Verified

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Verify Silmaril.Wasm.Logic.Words
open Silmaril.Wasm.Examples.Wat (triangle triangle_step)

theorem double_vc : doubleSpec.vc prog.funcs[0] := by
  wasm_vc [doubleSpec, prog]

theorem abs_vc : absSpec.vc prog.funcs[1] := by
  wasm_vc [absSpec, prog]
  · rw [BitVec.toInt_neg_of_ne_intMin ‹_›, abs_of_neg ‹_›]
  · rw [abs_of_nonneg ‹_›]

theorem max_vc : maxSpec.vc prog.funcs[2] := by
  wasm_vc [maxSpec, prog]

theorem sum_vc : sumSpec.vc prog.funcs[3] := by
  wasm_vc [sumSpec, prog]
  exact triangle_step _ _ ‹_› ‹_›

theorem storeLoad_vc : storeLoadSpec.vc prog.funcs[4] := by
  wasm_vc [storeLoadSpec, prog]

theorem get_vc : getSpec.vc prog.funcs[5] := by
  wasm_vc [getSpec, prog]

/-- **`double.wasm` decodes to `doubleWat`** (silmaril-lean's binary decoder, kernel
evaluation). -/
theorem doubleBytes_decode : Binary.Core.decode? doubleBytes = some doubleWat := by
  kernel_rfl

theorem doubleWat_vc : doubleSpec.vc doubleWat.funcs[0] := by
  wasm_vc [doubleSpec, doubleWat]

/-- **Function `0` of the decoded `double.wasm` meets `doubleSpec`.** -/
theorem double_verified : ∀ m, Binary.Core.decode? doubleBytes = some m → Verified m 0 doubleSpec := by
  intro m hm
  rw [doubleBytes_decode] at hm
  cases hm
  exact ⟨_, rfl, doubleWat_vc⟩

end Silmaril.Wasm.Examples.Verified
