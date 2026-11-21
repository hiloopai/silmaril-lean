module

public import Silmaril.Logic.Consequence.Structural.Finitary.Thms
public import Silmaril.Logic.Consequence.Structural.Thms

/-!
# Examples: consequences of sets of premises

The Tarski closure of the successor steps `[n] ⊢ n + 1` gives, from the set `{0}`, every
natural number, through the closure operator `cnClosure`; and its finset reading does not
depend on the enumeration.
-/

@[expose] public section

namespace Silmaril.Consequence.Structural.Finitary.Examples

/-- `[n] ⊢ n + 1`. -/
def succ : Rel Nat := fun Γ c => ∃ n, Γ = [n] ∧ c = n + 1

/-- The Tarski closure of `succ`. -/
abbrev tsucc : Rel Nat := Derives tarskiRules succ

theorem tsucc_closed : Closed tarskiRules tsucc := derives_closed _ _

/-- The Tarski closure as a closure operator on sets of natural numbers. -/
def tsuccCn : ClosureOperator (Set Nat) :=
  cnClosure (tsucc_closed.refl trivial) (tsucc_closed.cut trivial)

theorem mem_cn_zero (n : Nat) : n ∈ tsuccCn {0} := by
  induction n with
  | zero => exact tsuccCn.le_closure _ rfl
  | succ n ih =>
    have h : n + 1 ∈ cn tsucc (cn tsucc {0}) :=
      ⟨[n], fun x hx => by rw [List.mem_singleton.1 hx]; exact ih, .base ⟨n, rfl, rfl⟩⟩
    exact cn_cn (tsucc_closed.cut trivial) _ h

/-- Through the enumeration of `[1, 0, 1].toFinset`, which `WeakSubset` makes irrelevant. -/
theorem onFinset_tsucc_enum : onFinset tsucc [1, 0, 1].toFinset 2 ↔ tsucc [1, 0, 1] 2 :=
  onFinset_toFinset tsucc_closed.weak _ _

/-- Order and multiplicity of premises do not matter in the Tarski closure. -/
theorem tsucc_set_like : tsucc [1, 0, 1] 2 ↔ tsucc [0, 1] 2 :=
  ⟨tsucc_closed.weak (show [1, 0, 1] ⊆ [0, 1] by decide),
    tsucc_closed.weak (show [0, 1] ⊆ [1, 0, 1] by decide)⟩

end Silmaril.Consequence.Structural.Finitary.Examples
