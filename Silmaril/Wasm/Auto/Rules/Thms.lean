module

public import Silmaril.Wasm.Auto.Rules.Defs
public import Silmaril.Wasm.Auto.EGraph.Thms
import Silmaril.Proofs.Wasm.Auto.Rules.Sound

/-! # The verified rewrite library: soundness

`library_sound`: every rule of `Silmaril.Wasm.Auto.Rules.library` satisfies `Rule.Sound`, so
`Silmaril.Wasm.Auto.EGraph.segEquiv_of_checkEqL` and `segRefines_of_checkRefL` turn any
certificate over the library that the kernel checks into a segment equivalence or
refinement. One theorem per schema (`addComm_sound` …) is in
`Silmaril.Proofs.Wasm.Auto.Rules.Sound`.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.Rules

open Silmaril.Wasm Silmaril.Wasm.Auto.EGraph

/-- **Every rule of the library is sound.** -/
theorem library_sound : ∀ r ∈ library, r.Sound := by
  intro r hr
  obtain ⟨sch, hs, hr⟩ := List.mem_flatMap.mp hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Silmaril.Proofs.Wasm.Auto.Rules.schemas_sound sch hs .i32
  · exact Silmaril.Proofs.Wasm.Auto.Rules.schemas_sound sch hs .i64

end Silmaril.Wasm.Auto.Rules
