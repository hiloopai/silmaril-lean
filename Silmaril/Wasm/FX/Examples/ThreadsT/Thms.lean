module

public import Silmaril.Proofs.Wasm.FX.Examples.ThreadsT.Static
public import Silmaril.Proofs.Wasm.FX.Examples.ThreadsT.Sync
public import Silmaril.Proofs.Wasm.FX.Examples.ThreadsT.Kt
public import Silmaril.Proofs.Wasm.FX.Examples.ThreadsT.Tk
public import Silmaril.Proofs.Wasm.FX.Examples.ThreadsT.Ykt
public import Silmaril.Proofs.Wasm.FX.Examples.ThreadsT.Ytk
public import Silmaril.Proofs.Wasm.FX.Examples.ThreadsT.Dyn

/-!
# The explainer's lightweight threads under `StepFXT`

The `StepFXL` programs of `Silmaril.Wasm.FX.Examples.Threads`, compiled to FX code over the
`StepFXT` intrinsics by `Silmaril.Wasm.Models.FXLComp` (locals as continuation cells, the queue and
`print_i32` as intrinsics), print their documented output under `StepFXT`, at every profile and
host. Each run is computed by the interpreter `Silmaril.Wasm.Models.FXTRun`, whose steps are proved
to be `StepFXT` steps, and checked by the kernel (`decide +kernel`); proofs in
`Silmaril.Proofs.Wasm.FX.Examples.ThreadsT` (namespace of the same name):

* **`static_fxt`**: static threads, `-1 10 20 30 11 21 31 12 22 32 -2`;
* **`dyn_fxt`**: the dynamic `run`, the five schedulers in sequence, `-1 … -6` (checked in
  five segments between the checkpoints `dynMid i` of `Silmaril.Wasm.FX.Examples.ThreadsT`);
* **`sync_fxt`**, **`kt_fxt`**, **`tk_fxt`**, **`ykt_fxt`**, **`ytk_fxt`**: each scheduler alone;
* `…_sim` for each: the only `StepFXL` behaviour of the source program is matched by this
  `StepFXT` behaviour of its compilation (a per-program check of the compiler, not a general
  simulation theorem).

Each is `ObsT.ret (logV log) (returns [])` **∈** the `StepFXT` behaviours: membership only.
That the compiled program has no other `StepFXT` behaviour (no other log, no divergence) is not
proved.

A Silmaril addition.
-/
