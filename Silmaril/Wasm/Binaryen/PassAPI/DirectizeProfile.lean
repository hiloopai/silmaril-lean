module

public import Silmaril.Wasm.Binaryen.Pass.DirectizeProfile
public import Silmaril.Wasm.Binaryen.PassAPI.Instances

@[expose] public section

/-! # Directize as a pass for every numerical profile -/

namespace Silmaril.Wasm.Binaryen.PassAPI

open Silmaril.Wasm Execution.Core Numerics

/-- The unchanged Directize transform as a closed-host export-equivalence pass on all
valid modules, including the nondeterministic WebAssembly specification profile. -/
def directizeProfileP (P : Profile) (H : Type) :
    Pass (equivContract P (closedHost (H := H))) where
  run := directize
  inv_run {m} hm := (Directize.directize_sound_profile m hm P H).1
  sound {m} hm := (Directize.directize_sound_profile m hm P H).2

theorem directizeProfileP_run (P : Profile) (H : Type) :
    (directizeProfileP P H).run = directize := rfl

end Silmaril.Wasm.Binaryen.PassAPI
