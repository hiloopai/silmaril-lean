module

public import Silmaril.Wasm.Resource.Extern.Defs
public import Silmaril.Proofs.Wasm.Resource.Handle.Basic

/-!
# Handle protocols for `externref` handles: blame and soundness

Environment moves never break the reference sentences (`uClientSpec_oTotal`,
`uProviderSpec_oTotal`), and a protocol invariant of the untyped transition system makes every
play of the untyped strategy accepted (`untyped_accepts`, every profile).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

theorem allocOfResult_cases (r : Result) :
    (∃ h, HEv.allocOfResult r = .alloc h) ∨ HEv.allocOfResult r = .skip := by
  unfold HEv.allocOfResult; split <;> simp

/-- Environment moves never break the client sentence for references. -/
theorem uClientSpec_oTotal {ι : Type} (ha hu hf : Nat) :
    OTotal (uClientSpec (ι := ι) ha hu hf) := by
  intro q o ho
  rcases o with (e | ⟨e, a⟩) | (f | ⟨f, a⟩)
  · exact ho.elim
  · show (handleStep .client q (uClientEv ha hu hf (.inl (.ans e a)))).isSome
    rw [Option.isSome_iff_ne_none]
    simp only [uClientEv]
    split
    · rcases allocOfResult_cases a.result with ⟨h, hh⟩ | hh <;> rw [hh]
      · exact handleStep_client_alloc q h
      · rw [handleStep_skip]; simp
    · rw [handleStep_skip]; simp
  · show (handleStep .client q (uClientEv ha hu hf (.inr (.ask f)))).isSome
    simp only [uClientEv, handleStep_skip, Option.isSome_some]
  · exact ho.elim

/-- Environment moves never break the provider sentence for references. -/
theorem uProviderSpec_oTotal {ι : Type} [DecidableEq ι] (ja ju jf : ι) :
    OTotal (uProviderSpec ja ju jf) := by
  intro q o ho
  rcases o with (e | ⟨e, a⟩) | (f | ⟨f, a⟩)
  · exact ho.elim
  · show (handleStep .provider q (uProviderEv ja ju jf (.inl (.ans e a)))).isSome
    simp only [uProviderEv, handleStep_skip, Option.isSome_some]
  · show (handleStep .provider q (uProviderEv ja ju jf (.inr (.ask f)))).isSome
    rw [Option.isSome_iff_ne_none]
    simp only [uProviderEv]
    split
    · rcases useOf_cases f.args with ⟨h, hh⟩ | hh <;> rw [hh]
      · exact handleStep_provider_use q h
      · rw [handleStep_skip]; simp
    · split
      · rcases freeOf_cases f.args with ⟨h, hh⟩ | hh <;> rw [hh]
        · exact handleStep_provider_free q h
        · rw [handleStep_skip]; simp
      · rw [handleStep_skip]; simp
  · exact ho.elim

/-- **Plays of an untyped instance** are accepted given a protocol invariant of its transition
system (host-free Core steps silent, every profile). -/
theorem untyped_accepts {S : Type} {U : UInstance} {P : Profile}
    {π : Protocol S (Move U.E U.F)} (Φ : LTSInv (U.lts P) π) (hO : OTotal π) :
    ∀ p ∈ U.strategy P, π.Accepts p :=
  Φ.accepts hO

end Silmaril.Wasm.Resource
