module

@[expose] public section

/-! Shared `Except` proof plumbing, independent of encoder implementation and
proofs. Original fully qualified theorem names are preserved. -/

namespace Silmaril.Wasm.Binaryen.Exe

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

end Silmaril.Wasm.Binaryen.Exe
