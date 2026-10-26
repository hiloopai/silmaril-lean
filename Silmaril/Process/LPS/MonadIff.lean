module

public import Silmaril.Process.LPS.Monad

/-! # Deterministic reads in the specification monad, as equivalences

`input` and `getModel` answer exactly the call's input and model, so a bind after them is its
continuation at those values. Used to compare two specifications that differ only past such a
read (`SoundReference.sendmsgSpecWith_congr`, `NativeX86.All.sigaltstackSpecWith_congr`).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Sys

theorem bind_input_iff {β : Type} (k : SyscallInput → Sys β) (i : SyscallInput) (m : Model)
    (o : Outcome β) : (input >>= k) i m o ↔ k i i m o := by
  show Sys.bind input k i m o ↔ _
  cases o with
  | ok y m₂ evs =>
    constructor
    · rintro ⟨x, m₁, evs₁, evs₂, h₁, h₂, rfl⟩
      cases h₁; simpa using h₂
    · intro h; exact ⟨i, m, [], evs, rfl, h, by simp⟩
  | unmodeled =>
    constructor
    · rintro (h₁ | ⟨x, m₁, evs₁, h₁, h₂⟩)
      · cases h₁
      · cases h₁; exact h₂
    · intro h; exact .inr ⟨i, m, [], rfl, h⟩

theorem bind_getModel_iff {β : Type} (k : Model → Sys β) (i : SyscallInput) (m : Model)
    (o : Outcome β) : (getModel >>= k) i m o ↔ k m i m o := by
  show Sys.bind getModel k i m o ↔ _
  cases o with
  | ok y m₂ evs =>
    constructor
    · rintro ⟨x, m₁, evs₁, evs₂, h₁, h₂, rfl⟩
      cases h₁; simpa using h₂
    · intro h; exact ⟨m, m, [], evs, rfl, h, by simp⟩
  | unmodeled =>
    constructor
    · rintro (h₁ | ⟨x, m₁, evs₁, h₁, h₂⟩)
      · cases h₁
      · cases h₁; exact h₂
    · intro h; exact .inr ⟨m, m, [], rfl, h⟩

end Silmaril.Process.LPS.Sys
