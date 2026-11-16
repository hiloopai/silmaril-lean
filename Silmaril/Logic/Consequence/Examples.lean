module

public import Silmaril.Logic.Consequence.Ax.Thms
public import Silmaril.Logic.Consequence.Accept.Thms
public import Silmaril.Logic.Consequence.Semantic.Thms

/-!
# Consequence systems: examples

* `memSystem`: a list context proves exactly its members. It is monotone along `List.Subset`
  (weakening), it is unchanged by pulling back through `ctxFinset`, and no context is
  inconsistent unless it contains every conclusion (`memSystem_consistent`).
* `dvdSat`: a satisfaction whose contexts and conclusions are both numbers but are satisfied
  differently: a model `m` satisfies the context `d` and the conclusion `c` when `d ∣ m` and
  `c ∣ m`. Its entailment is "`c` divides `d`"; the context is not a set of conclusions.
* `evenRefuted`: the acceptor lift `liftAxFF` of a Bool checker for even numbers.
-/

@[expose] public section

namespace Silmaril.Consequence.Examples

/-- A list context proves exactly its members. -/
def memSystem (C : Type) : ListSystem C := fun l c => c ∈ l

theorem memSystem_monoWrt (C : Type) : (memSystem C).MonoWrt (· ⊆ ·) :=
  fun _ _ h _ hc => h hc

/-- `memSystem` is the pullback of finite-set membership along `ctxFinset`. -/
theorem memSystem_eq_pullback (C : Type) [DecidableEq C] :
    memSystem C = System.pullback ctxFinset id (fun s c => c ∈ s) :=
  funext₂ fun l c => propext (by simp [memSystem, ctxFinset])

/-- `[true]` is consistent: it does not prove `false`. -/
theorem memSystem_consistent : (memSystem Bool).ContextConsistent [true] :=
  fun h => absurd (h false) (by simp [memSystem])

/-- Divisibility as satisfaction: `m` satisfies context `d` and conclusion `c` when they
divide it. -/
def dvdSat : Satisfaction.{0, 0, 0} ℕ ℕ := ⟨ℕ, fun m d => d ∣ m, fun m c => c ∣ m⟩

example : dvdSat.entails 6 3 := fun _ h => Nat.dvd_trans ⟨2, rfl⟩ h

example : ¬ dvdSat.entails 6 4 := fun h => by
  have h46 : (4 : ℕ) ∣ 6 := h (6 : ℕ) (Nat.dvd_refl 6)
  exact absurd h46 (by decide)

/-- `0` proves everything: its only model is `0`, which every number divides. -/
example : dvdSat.entails.ProvesAll 0 := fun _ _ h => by
  obtain ⟨k, rfl⟩ := h; exact ⟨0, by simp⟩

/-- Even numbers, refuted: an even context proves `False`, and proves nothing else. -/
def evenRefuted : System ℕ Prop := liftAxFF (Accept.ofBool fun n => n % 2 == 0) False

example : evenRefuted 4 False := by
  show liftAxFF _ False 4 False; rw [liftAxFF_ofBool]; rfl

example : ¬ evenRefuted 3 False := by
  show ¬ liftAxFF _ False 3 False; rw [liftAxFF_ofBool]; decide

example : ¬ evenRefuted.ProvesAll 4 := liftAxFF_not_explosive (c := True) (by simp)

end Silmaril.Consequence.Examples
