module

public import Silmaril.Wasm.Binaryen.Pass.RedundantSetLine

@[expose] public section

/-! # Self-store elimination (silmaril's `rse-line`): the verified stage

Silmaril's `RedundantSetLine.rseLine` (`Pass/RedundantSetLine.lean`) rewrites a store
of a local's own value:

  `local.get x; local.set x` ⟶ `local.get x; drop`,   `local.get x; local.tee x` ⟶ `local.get x`

in folded and flat form. Unoptimised-phi copies of exactly this shape are frequent in
LLVM `-O1` output (C via clang, Rust via rustc). Silmaril proves one simulation
(`RedundantSetLineSim.rsBaseSim`) but never packages a soundness theorem or wires the
pass into its executable. This stage reuses silmaril's run function unchanged and
drops silmaril's coverage-only `exportsFunc` gate from `rseLineChecked`, keeping
the validator fallback.

The resulting `local.get x; drop` is removed by the `drop-get` stage
(`Silmaril.Wasm.Binaryen.DropGet`) and silmaril's `vacuum`.

**Profile.** The proof (`Silmaril.Wasm.Binaryen.RseLine.Thms`) holds at every
numerical profile. The original's intermediate state `v; local.set x` is related to
the result only through the frame (`v` is the current value of `x`), which runtime
base pairs cannot mention; the reverse simulation completes that store as a forced
step (`Silmaril.Wasm.Binaryen.Deferred`), which leaves the frame unchanged.
-/

namespace Silmaril.Wasm.Binaryen.RseLine

open Silmaril.Wasm.Binaryen

/-- **The self-store stage**: silmaril's rewrite, kept when the validator accepts it. -/
def rseLineChecked (m : BModule) : BModule :=
  let m' := RedundantSetLine.rseLine m
  if Exe.validOk m' then m' else m

end Silmaril.Wasm.Binaryen.RseLine
