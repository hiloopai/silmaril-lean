module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.InstructionMap

/-! # Predicates on every instruction occurrence

These syntax predicates retain primitive attributes and traverse every nested
CFG block. They are independent of typing and effects. Renaming variables or
labels does not change them; instruction maps transport the predicate itself.
-/

@[expose] public section
universe u v
namespace Silmaril.Isotope.LambdaSSA
variable {Φ : Type u} {Ψ : Type v}

def Tm.ForallInstr (allowed : Φ → Prop) : Tm Φ → Prop
  | .var _ | .unit => True
  | .op instruction argument => allowed instruction ∧ argument.ForallInstr allowed
  | .let₁ value body | .let₂ value body => value.ForallInstr allowed ∧ body.ForallInstr allowed
  | .pair left right => left.ForallInstr allowed ∧ right.ForallInstr allowed
  | .inl value | .inr value | .abort value => value.ForallInstr allowed
  | .case discr left right => discr.ForallInstr allowed ∧ left.ForallInstr allowed ∧ right.ForallInstr allowed

def Region.ForallInstr (allowed : Φ → Prop) : Region Φ → Prop
  | .br _ argument => argument.ForallInstr allowed
  | .let₁ value body | .let₂ value body => value.ForallInstr allowed ∧ body.ForallInstr allowed
  | .case discr left right => discr.ForallInstr allowed ∧ left.ForallInstr allowed ∧ right.ForallInstr allowed
  | .cfg entry _ blocks => entry.ForallInstr allowed ∧ ∀ index, (blocks index).ForallInstr allowed

theorem Tm.forallInstr_true (term : Tm Φ) : term.ForallInstr (fun _ => True) := by
  induction term <;> simp_all [ForallInstr]

theorem Region.forallInstr_true (region : Region Φ) : region.ForallInstr (fun _ => True) := by
  induction region <;> simp_all [ForallInstr, Tm.forallInstr_true]

theorem Tm.ForallInstr.mono {allowed wider : Φ → Prop} {term : Tm Φ}
    (checked : term.ForallInstr allowed) (weaken : ∀ i, allowed i → wider i) : term.ForallInstr wider := by
  induction term <;> simp_all [ForallInstr]

theorem Region.ForallInstr.mono {allowed wider : Φ → Prop} {region : Region Φ}
    (checked : region.ForallInstr allowed) (weaken : ∀ i, allowed i → wider i) : region.ForallInstr wider := by
  induction region with
  | br => exact Tm.ForallInstr.mono checked weaken
  | let₁ _ _ ih | let₂ _ _ ih => exact ⟨Tm.ForallInstr.mono checked.1 weaken, ih checked.2⟩
  | case _ _ _ left right => exact ⟨Tm.ForallInstr.mono checked.1 weaken, left checked.2.1, right checked.2.2⟩
  | cfg _ _ _ entry blocks => exact ⟨entry checked.1, fun i => blocks i (checked.2 i)⟩

@[simp] theorem Tm.forallInstr_rename (allowed : Φ → Prop) (term : Tm Φ) (ρ : Nat → Nat) :
    (term.rename ρ).ForallInstr allowed ↔ term.ForallInstr allowed := by
  induction term generalizing ρ <;> simp_all [rename, ForallInstr]

@[simp] theorem Region.forallInstr_renameVars (allowed : Φ → Prop) (region : Region Φ) (ρ : Nat → Nat) :
    (region.renameVars ρ).ForallInstr allowed ↔ region.ForallInstr allowed := by
  induction region generalizing ρ <;> simp_all [renameVars, ForallInstr]

@[simp] theorem Region.forallInstr_renameLabels (allowed : Φ → Prop) (region : Region Φ) (ρ : Nat → Nat) :
    (region.renameLabels ρ).ForallInstr allowed ↔ region.ForallInstr allowed := by
  induction region generalizing ρ <;> simp_all [renameLabels, ForallInstr]

@[simp] theorem Tm.forallInstr_mapInstr (map : Φ → Ψ) (allowed : Ψ → Prop) (term : Tm Φ) :
    (term.mapInstr map).ForallInstr allowed ↔ term.ForallInstr (fun instruction => allowed (map instruction)) := by
  induction term <;> simp_all [mapInstr, ForallInstr]

@[simp] theorem Region.forallInstr_mapInstr (map : Φ → Ψ) (allowed : Ψ → Prop) (region : Region Φ) :
    (region.mapInstr map).ForallInstr allowed ↔ region.ForallInstr (fun instruction => allowed (map instruction)) := by
  induction region <;> simp_all [mapInstr, ForallInstr]

end Silmaril.Isotope.LambdaSSA
