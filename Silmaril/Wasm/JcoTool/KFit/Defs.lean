module

public import Silmaril.Wasm.JcoTool.KCore.Defs

/-!
# Kernels that always fit

`KLive.KFits k N`, the hypothesis of the liveness theorems, says the generated module of `k` never
overflows its fixed buffers. It holds for every kernel that does not use the buffer and emits at
most one byte per input byte and at its flush (`Small`): a module feeds at most `N ≤ 256` bytes
per read into an output region of `CAP` bytes. `kInc`, `kNoDigit` and `kTake n` are `Small`
(theorems in `KFit.Thms`); `kLines` and `kRechunk` use the buffer and are not covered.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KFit

open Silmaril.Wasm.Component.Streams.Kernel (KStmt KM)

/-- The statement does not touch the buffer. -/
def noBuf : KStmt → Bool
  | .skip | .emit _ | .set _ | .clear => true
  | .seq p q | .ite _ p q => noBuf p && noBuf q
  | .push _ | .emitBuf => false

/-- The most bytes the statement emits. -/
def maxEmit : KStmt → Nat
  | .skip | .set _ | .clear | .push _ | .emitBuf => 0
  | .emit _ => 1
  | .seq p q => maxEmit p + maxEmit q
  | .ite _ p q => max (maxEmit p) (maxEmit q)

/-- **A small kernel**: no buffer, at most one byte per step and at its flush. -/
def Small (k : KM) : Bool :=
  noBuf k.step && decide (maxEmit k.step ≤ 1) && noBuf k.flush && decide (maxEmit k.flush ≤ 1)

end Silmaril.Wasm.JcoTool.KFit
