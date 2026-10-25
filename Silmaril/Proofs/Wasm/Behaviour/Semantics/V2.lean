module

public import Silmaril.Wasm.Behaviour.Semantics.V2.Defs

/-! # Proofs of the WebAssembly 2.0 behaviour laws

The public statements are in `Silmaril.Wasm.Behaviour.Semantics.V2.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Behaviour.Semantics.V2

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

@[simp] theorem diverges_mem_behavioursOf_iff {P : Profile} {host : HostSemantics H}
    {c : Config H} :
    (Behaviour.diverges : Behaviour Val) ∈ behavioursOf P host c ↔ Diverges P host c := by
  constructor
  · rintro (⟨_, r, _, _, h⟩ | ⟨_, h⟩)
    · exact absurd h.symm (Result.toBehaviour_ne_diverges r)
    · exact h
  · exact fun h => Or.inr ⟨rfl, h⟩

theorem exists_result_of_mem {P : Profile} {host : HostSemantics H} {c : Config H}
    {b : Behaviour Val} (mem : b ∈ behavioursOf P host c) (ne : b ≠ .diverges) :
    ∃ (c' : Config H) (r : Result),
      Steps P host c c' ∧ c'.code = r.toAdmin ∧ b = r.toBehaviour := by
  rcases mem with h | ⟨h, _⟩
  · exact h
  · exact absurd h ne

theorem diverges_of_steps {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (steps : Steps P host c c') (div : Diverges P host c') : Diverges P host c := by
  induction steps with
  | refl => exact div
  | tail _ step ih => exact ih (InfiniteTrace.fold step div)

theorem behavioursOf_mono_steps {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (steps : Steps P host c c') : behavioursOf P host c' ⊆ behavioursOf P host c := by
  rintro b (⟨c'', r, hsteps, hfinal, rfl⟩ | ⟨rfl, hdiv⟩)
  · exact Or.inl ⟨c'', r, steps.trans hsteps, hfinal, rfl⟩
  · exact Or.inr ⟨rfl, diverges_of_steps steps hdiv⟩

theorem throws_not_mem_behavioursOf {P : Profile} {host : HostSemantics H} {c : Config H}
    (a : Nat) : (Behaviour.throws a : Behaviour Val) ∉ behavioursOf P host c := by
  rintro (⟨_, r, _, _, h⟩ | ⟨h, _⟩)
  · exact Result.toBehaviour_ne_throws r a h.symm
  · cases h

theorem mem_behavioursOf_cases {P : Profile} {host : HostSemantics H} {c : Config H}
    {b : Behaviour Val} (mem : b ∈ behavioursOf P host c) :
    (∃ vs, b = .returns vs) ∨ b = .traps ∨ b = .diverges := by
  rcases mem with ⟨_, r, _, _, rfl⟩ | ⟨rfl, _⟩
  · cases r with
    | values vs => exact Or.inl ⟨vs, rfl⟩
    | trap => exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)


end Silmaril.Proofs.Wasm.Behaviour.Semantics.V2
