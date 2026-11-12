module

public import Silmaril.Raw.SSA.Isotope.LetIter.LocallyNameless.Effects
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Operational

/-! The same typed loops under divergence-sensitive and complete effect signatures. -/

@[expose] public section

namespace Silmaril.Isotope.LetIter.EffectExamples

open LocallyNameless

inductive Instruction where
  | tick

abbrev valueTy : Ty Empty := .unit
abbrev stateTy : Ty Empty := .coprod valueTy valueTy
abbrev resultTy : Ty Empty := .product valueTy valueTy

instance : HasTy Instruction (Ty Empty) where
  src _ := valueTy
  trg _ := valueTy

instance : HasEff Instruction Bool where
  eff _ := false

/-- Exit with a product on the left; otherwise change to the left-tagged state. -/
def body : Tm Empty Instruction 1 :=
  .case (.bv 0) (.inl (.pair (.op .tick (.bv 0)) .unit))
    (.inr (.inl (.op .tick (.bv 0))))

def loop : Tm Empty Instruction 0 := .iter (.inr .unit) body

theorem body_typed : HasType Instruction (.nil : Ctx Empty (Ty Empty))
    (.snoc .nil stateTy) body (coprod resultTy stateTy) :=
  .case .bv (.inl (.pair (.op .bv) .unit)) (.inr (.inl (.op .bv)))

theorem loop_typed : HasType Instruction (.nil : Ctx Empty (Ty Empty)) .nil loop resultTy :=
  .iter (.inr .unit) body_typed

/-- A well-typed infinite loop with a pure body and no primitive transitions. -/
def spin : Tm Empty Instruction 0 := .iter .unit (.inr (.bv 0))

theorem spin_typed : HasType Instruction (.nil : Ctx Empty (Ty Empty)) .nil spin resultTy :=
  .iter .unit (.inr .bv)

theorem spin_diverges {α σ : Type} (instr : Instruction → Value α → σ → Value α → σ → Prop)
    (s : σ) :
    Semantics.Diverges instr Empty.elim (.term Fin.elim0 spin s) :=
  Semantics.Eval.iter_continue_diverges Fin.elim0 s (.unit (instr := instr))

theorem loop_not_loopFreePure : ¬ Pure false loop := Pure.not_iter _ _

theorem spin_not_loopFreePure : ¬ Pure false spin := Pure.not_iter _ _

section Partiality

local instance : EffectIteration Bool := EffectIteration.partiality Bool

theorem loop_effect_partiality : (loop.effect : Bool) = true := by
  rfl

theorem loop_hasTypeEffect_partiality :
    HasTypeEffect (.nil : Ctx Empty (Ty Empty)) .nil loop resultTy true :=
  ⟨loop_typed, le_rfl⟩

theorem spin_not_bottom_partiality : ¬ HasEffect spin false := by
  change ¬ (true ≤ false)
  decide

end Partiality

section Complete

local instance : EffectIteration Bool := EffectIteration.complete Bool

theorem loop_effect_complete : (loop.effect : Bool) = false := by
  rfl

theorem loop_hasTypeEffect_complete :
    HasTypeEffect (.nil : Ctx Empty (Ty Empty)) .nil loop resultTy false :=
  ⟨loop_typed, le_rfl⟩

/-- A bottom effect need not imply termination or loop-free syntactic purity. -/
theorem spin_hasTypeEffect_complete :
    HasTypeEffect (.nil : Ctx Empty (Ty Empty)) .nil spin resultTy false :=
  ⟨spin_typed, le_rfl⟩

end Complete

end Silmaril.Isotope.LetIter.EffectExamples
