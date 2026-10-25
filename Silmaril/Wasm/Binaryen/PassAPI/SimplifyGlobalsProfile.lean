module

public import Silmaril.Wasm.Binaryen.Pass.SimplifyGlobalsProfile
public import Silmaril.Wasm.Binaryen.PassAPI.Instances

@[expose] public section

/-! # Immutable-global propagation as a pass for every numerical profile

The standard equivalence contract already accepts arbitrary profiles. The new
bidirectional proof lets the complete existing transformation inhabit that
contract directly, without an extra profile filter or identity fallback.
-/

namespace Silmaril.Wasm.Binaryen.PassAPI

open Silmaril.Wasm Execution.Core Numerics

/-- The unchanged SimplifyGlobals transform, preserving closed-host export equivalence
for all numerical profiles, including the nondeterministic specification profile. -/
def simplifyGlobalsProfileP (P : Profile) (H : Type) :
    Pass (equivContract P (closedHost (H := H))) where
  run := simplifyGlobals
  inv_run {m} hm := (SimplifyGlobals.simplifyGlobals_sound_profile m hm P H).1
  sound {m} hm := (SimplifyGlobals.simplifyGlobals_sound_profile m hm P H).2

theorem simplifyGlobalsProfileP_run (P : Profile) (H : Type) :
    (simplifyGlobalsProfileP P H).run = simplifyGlobals := rfl

end Silmaril.Wasm.Binaryen.PassAPI
