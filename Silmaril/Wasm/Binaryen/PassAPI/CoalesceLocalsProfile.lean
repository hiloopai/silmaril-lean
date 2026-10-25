module

public import Silmaril.Wasm.Binaryen.CoalesceLocalsProfile
public import Silmaril.Wasm.Binaryen.PassAPI.Instances

@[expose] public section

/-! # Overwrite-anchored CoalesceLocals as a pass at every numerical profile -/

namespace Silmaril.Wasm.Binaryen.PassAPI

open Silmaril.Wasm Execution.Core Numerics

/-- The existing dead-store transform, with its full arbitrary-profile contract. -/
def coalesceLocalsProfileP (P : Profile) (H : Type) :
    Pass (equivContract P (closedHost (H := H))) where
  run := CoalesceLocalsLite.deadSetLite
  inv_run {_m} hm := CoalesceLocalsLite.deadSetLite_ok hm
  sound {_m} hm := CoalesceLocalsLite.deadSetLite_sound_profile hm

theorem coalesceLocalsProfileP_run (P : Profile) (H : Type) :
    (coalesceLocalsProfileP P H).run = CoalesceLocalsLite.deadSetLite := rfl

end Silmaril.Wasm.Binaryen.PassAPI
