module

public import Silmaril.Wasm.Behaviour.Semantics.V3.Defs

/-! # Proofs of the WebAssembly 3.0 behaviour laws

The public statements are in `Silmaril.Wasm.Behaviour.Semantics.V3.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Behaviour.Semantics.V3

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
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


end Silmaril.Proofs.Wasm.Behaviour.Semantics.V3
