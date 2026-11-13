module

public import Silmaril.Proofs.Wasm.Det.Game.Instance

/-!
# The converse after earlier activations: observable determinism of call states

If the strategy of an instance is deterministic modulo traps, then at every call state reached
by complete, trap-free activations (`ScalarInstance.Activation`), two Core runs of an export
invocation against the same typed trace that reach non-trapping stops visible in the game have
the same output (`obsModule_of_detMod`). The earlier activations are the history of the play,
so this is `obsAgree_of_detMod` after a prefix.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Game

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Game
  Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {I : ScalarInstance} {P : Profile}

theorem path_concat {q q' q'' : I.HState} {a b : List (Move I.E I.F)} (h₁ : I.Path P q a q')
    (h₂ : I.Path P q' b q'') : I.Path P q (a ++ b) q'' := by
  induction h₁ with
  | nil => exact h₂
  | cons t _ ih => exact .cons t (ih h₂)

/-- **A deterministic strategy gives observable determinism at every call state reached by
trap-free activations.** -/
theorem obsModule_of_detMod {s₀ : Store Nat}
    (hD : DetMod (wasmTraps I.exports) (I.strategy P s₀)) : ObsModule P I s₀ := by
  intro c s hc hcf f tr d₁ d₂ o₁ o₂ htr h₁ h₂ ho₁ ho₂ hg₁ hg₂
  obtain ⟨p₁, s₁, t₁, hp₁, hpath₁, hs₁⟩ := play_of_runs (f := f) (t := I.initThread f) h₁ rfl htr
  obtain ⟨p₂, s₂, t₂, hp₂, hpath₂, hs₂⟩ := play_of_runs (f := f) (t := I.initThread f) h₂ rfl htr
  have hpp : p₂ = p₁ := playOf_fun hp₂ hp₁
  subst hpp
  obtain ⟨m₁, q₁, ht₁, hm₁⟩ := last_move hs₁ ho₁ hg₁
  obtain ⟨m₂, q₂, ht₂, hm₂⟩ := last_move hs₂ ho₂ hg₂
  have hmem₁ : c ++ (.inr (.ask f) :: p₂) ++ [m₁] ∈ I.strategy P s₀ :=
    ScalarInstance.mem_strategy_iff.2
      ⟨q₁, by rw [List.append_assoc]; exact path_concat hc (.cons (.call s f) (path_snoc hpath₁ ht₁))⟩
  have hmem₂ : c ++ (.inr (.ask f) :: p₂) ++ [m₂] ∈ I.strategy P s₀ :=
    ScalarInstance.mem_strategy_iff.2
      ⟨q₂, by rw [List.append_assoc]; exact path_concat hc (.cons (.call s f) (path_snoc hpath₂ ht₂))⟩
  have hfree : TrapFree (wasmTraps I.exports) (c ++ (.inr (.ask f) :: p₂)) := by
    intro m hm
    rcases List.mem_append.1 hm with hm | hm
    · exact hcf m hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact id
    · exact playOf_trapFree hp₂ m hm
  rcases hD _ m₁ m₂ hmem₁ hmem₂ (trans_isP ht₁) (trans_isP ht₂) hfree with h | h | h
  · exact moveOf_inj hm₁ (h ▸ hm₂)
  · exact (moveOf_not_trap ho₁ hm₁ h).elim
  · exact (moveOf_not_trap ho₂ hm₂ h).elim

/-- **A stateless strategy gives observable statelessness**: export invocations agree on their
visible outputs at any two call states reached by activations (traps allowed in them). -/
theorem obsStateless_of_statelessMod {s₀ : Store Nat}
    (hD : StatelessMod (wasmTraps I.exports) (I.strategy P s₀)) : ObsStateless P I s₀ := by
  intro c₁ u₁ c₂ u₂ hc₁ hc₂ f tr d₁ d₂ o₁ o₂ htr h₁ h₂ ho₁ ho₂ hg₁ hg₂
  obtain ⟨p₁, s₁, t₁, hp₁, hpath₁, hs₁⟩ := play_of_runs (f := f) (t := I.initThread f) h₁ rfl htr
  obtain ⟨p₂, s₂, t₂, hp₂, hpath₂, hs₂⟩ := play_of_runs (f := f) (t := I.initThread f) h₂ rfl htr
  have hpp : p₂ = p₁ := playOf_fun hp₂ hp₁
  subst hpp
  obtain ⟨m₁, q₁, ht₁, hm₁⟩ := last_move hs₁ ho₁ hg₁
  obtain ⟨m₂, q₂, ht₂, hm₂⟩ := last_move hs₂ ho₂ hg₂
  have hmem₁ : c₁ ++ (.inr (.ask f) :: p₂) ++ [m₁] ∈ I.strategy P s₀ :=
    ScalarInstance.mem_strategy_iff.2 ⟨q₁, by
      rw [List.append_assoc]; exact path_concat hc₁ (.cons (.call u₁ f) (path_snoc hpath₁ ht₁))⟩
  have hmem₂ : c₂ ++ (.inr (.ask f) :: p₂) ++ [m₂] ∈ I.strategy P s₀ :=
    ScalarInstance.mem_strategy_iff.2 ⟨q₂, by
      rw [List.append_assoc]; exact path_concat hc₂ (.cons (.call u₂ f) (path_snoc hpath₂ ht₂))⟩
  have hfree : TrapFree (wasmTraps I.exports) (.inr (.ask f) :: p₂) := by
    intro m hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact id
    · exact playOf_trapFree hp₂ m hm
  have hA := hD c₁ c₂ (ScalarInstance.mem_strategy_iff.2 ⟨_, hc₁⟩)
    (ScalarInstance.mem_strategy_iff.2 ⟨_, hc₂⟩) (path_pos hc₁) (path_pos hc₂)
  rcases hA _ m₁ m₂ hmem₁ hmem₂ (trans_isP ht₁) (trans_isP ht₂) hfree with h | h | h
  · exact moveOf_inj hm₁ (h ▸ hm₂)
  · exact (moveOf_not_trap ho₁ hm₁ h).elim
  · exact (moveOf_not_trap ho₂ hm₂ h).elim

end Silmaril.Proofs.Wasm.Det.Game
