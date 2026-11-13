module

public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Defs

/-!
# `Runtime.Arena`: laws of the component reference

Theorems of the component reference copy `Runtime.Arena`, refined out of
`Silmaril.Raw.Wasm.Component.Runtime.Arena`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime

universe u

namespace Arena

variable {α : Type u}

theorem get?_isSome_iff (a : Arena α) (i : Nat) : (a.get? i).isSome ↔ i < a.length := by
  simp [get?_eq_getElem?]

end Arena

end Silmaril.Wasm.Component.Runtime
