module

public import Silmaril.Wasm.Validation.Check.AtomicBComplete

@[expose] public section

/-! # `Context.Wf` implies `ElemsOk`

`Context.Wf` carries an `elems` field (element types are valid), so every
well-formed context satisfies `ElemsOk`, the hypothesis of
`atomC_complete_elems` (`Check/AtomComplete.lean`). -/

namespace Silmaril.Wasm.Validation

theorem Context.Wf.elemsOk {C : Context} (hC : C.Wf) : ElemsOk C := hC.elems

theorem Context.wf_elemsOk : ∀ C : Context, C.Wf → ElemsOk C := fun _ hC => hC.elemsOk

end Silmaril.Wasm.Validation
