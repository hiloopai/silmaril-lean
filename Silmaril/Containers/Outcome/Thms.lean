module

public import Silmaril.Containers.Outcome.Defs
public import Mathlib.Order.Defs.PartialOrder
import Silmaril.Proofs.Containers.Outcome.Basic

public section
namespace Silmaril.Containers.Outcome
variable {U V : Type}

theorem mapUB_noUB (f : U → V) (s : Outcome U) : (s.mapUB f).NoUB ↔ s.NoUB := by
  cases s <;> rfl

theorem toEmpty_roundtrip (s : Outcome U) (h : s.NoUB) :
    (s.toEmpty h).mapUB (fun e => Empty.elim e) = s := by
  cases s <;> first | rfl | exact h.elim

theorem empty_noUB (s : Outcome Empty) : s.NoUB := by
  cases s <;> trivial

theorem approx_refl (s : Outcome U) : s.Approx s := .inl rfl

theorem approx_trans {a b c : Outcome U} (h : a.Approx b) (k : b.Approx c) : a.Approx c :=
  Silmaril.Proofs.Containers.Outcome.approx_trans h k

instance approximationPreorder : Preorder (Outcome U) where
  le := Approx
  le_refl := approx_refl
  le_trans := fun _ _ _ => approx_trans

/-- Mutual approximation is exactly equality after reason erasure. Reasons are identified by
the chosen top policy, not merely because there is more than one of them. -/
theorem mutual_iff_erase (a b : Outcome U) :
    (a.Approx b ∧ b.Approx a) ↔ a.erase = b.erase :=
  Silmaril.Proofs.Containers.Outcome.mutual_iff_erase a b

instance approximationSetoid : Setoid (Outcome U) where
  r a b := a.erase = b.erase
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- The quotient's antisymmetry law. Distinct runtime implementations with equal behaviours
still form a separate implementation preorder until quotienting them too. -/
theorem quotient_eq_of_mutual {a b : Outcome U} (h : a.Approx b) (k : b.Approx a) :
    Quotient.mk approximationSetoid a = Quotient.mk approximationSetoid b :=
  Quotient.sound ((mutual_iff_erase a b).mp ⟨h, k⟩)

theorem trapAsUB_more (u : U) (s : Outcome U) : s.Approx (s.trapAsUB u) := by
  cases s <;> first | exact .inl rfl | exact .inr ⟨u, rfl⟩

theorem noUB_of_trapAsUB (u : U) (s : Outcome U) : (s.trapAsUB u).NoUB → s.NoUB :=
  Silmaril.Proofs.Containers.Outcome.trap_policy u s

theorem trap_defined (code : Nat) : (Outcome.trapped (U := U) code).NoUB := trivial

theorem crash_refines_ub (signal : Nat) (u : U) :
    ((Outcome.undefined u).ubToCrash signal).Approx (.undefined u) := .inr ⟨u, rfl⟩

/-- Counterexample to transferring a noUB certificate through UB-to-crash masking. -/
theorem masked_noUB (u : U) (signal : Nat) :
    ((Outcome.undefined u).ubToCrash signal).NoUB ∧ ¬ (Outcome.undefined u).NoUB :=
  ⟨trivial, id⟩

end Silmaril.Containers.Outcome
