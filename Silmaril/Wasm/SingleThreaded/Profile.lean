module

public import Silmaril.Wasm.Execution.Core.Soundness

@[expose] public section

/-! # The single-threaded, component-facing presentation of Core 3.0: profile

Core 3.0 at the pinned revision has no threads, shared memory or atomics, so
"single-threaded Core 3.0" is Core 3.0 itself, *re-presented* for an embedder
that interleaves several activations cooperatively (the component model):

* the **deterministic profile** (`$ND = false`, canonical NaNs) with an explicit
  **grow oracle** deciding `memory.grow`/`table.grow` failure;
* host calls are not steps but **callouts**: a thread stops with
  `Status.callout h args` and the embedder `resume`s it with a result;
* threads are **store-free** values; one store is shared by all activations.

This file fixes the profile. `Thread.lean` defines threads, `status` and
`resume`; `Agreement.lean` proves the presentation agrees with `Core.Step`.
-/

namespace Silmaril.Wasm.SingleThreaded

open Silmaril.Wasm.Numerics

/-- Decides, for `(kind, address, current size, delta)`, whether a grow fails. -/
abbrev GrowOracle := GrowKind → Nat → Nat → Nat → Bool

/-- The single-threaded profile. -/
def profile (o : GrowOracle) : Profile := Profile.deterministic o

/-- The oracle under which growth only fails when impossible. -/
def neverFail : GrowOracle := fun _ _ _ _ => false

@[simp] theorem profile_nd (o : GrowOracle) : (profile o).nd = false := rfl
@[simp] theorem profile_nan (o : GrowOracle) : (profile o).nan = .canonical := rfl

end Silmaril.Wasm.SingleThreaded
