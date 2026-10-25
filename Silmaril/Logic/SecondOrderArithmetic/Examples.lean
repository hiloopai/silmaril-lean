module

public import Silmaril.Logic.SecondOrderArithmetic.MetamathSystems
public import Silmaril.Logic.SecondOrderArithmetic.Henkin
public import Silmaril.Logic.SecondOrderArithmetic.Arithmetic
public import Silmaril.Logic.SecondOrderArithmetic.Thms

@[expose] public section

/-! Concrete independent proofs, native transports and capture checks. -/
namespace Silmaril.Logic.SecondOrderArithmetic

open Silmaril.Logic.Metamath Grammar

def zeroEq : Formula SecondOrder.V := .equal .zero .zero

def identityFrame : TAssertion SecondOrder.L SecondOrder.C SecondOrder.V where
  dv := []
  hyps := []
  concl := ⟨.turnstile, (Formula.imp zeroEq zeroEq).toTree⟩

private theorem zeroEq_sort : SecondOrder.grammar.HasSort identityFrame.ctx zeroEq.toTree .wff := by
  have hz : SecondOrder.grammar.HasSort identityFrame.ctx (.node .t0 []) .term :=
    .node rfl (by simp [SecondOrder.grammar, SecondOrder.rules, Examples.rule])
  apply HasSort.node rfl
  simp only [SecondOrder.grammar, SecondOrder.rules, Examples.rule,
    List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil, or_false]
  rintro p (rfl | rfl) <;> exact hz

def independentIdentity : Proof .RCA0 (.imp zeroEq zeroEq) :=
  (HilbertProof.identity zeroEq).toProof .RCA0

/-- The same concrete identity is kernel-derived in native RCA₀. -/
theorem identity_native : TDerivable SecondOrder.grammar SecondOrder.RCA0 identityFrame :=
  TDerivable.of_nonempty ((HilbertProof.identity zeroEq).toNativeRCA0
    (HilbertProof.identity_sorted zeroEq_sort))

/-- Here the fully proved reverse bridge recovers a typed independent proof. -/
theorem identity_recovered : ∃ p : HilbertProof (.imp zeroEq zeroEq), p.Sorted identityFrame.ctx := by
  apply (hilbert_derivation_iff (A := identityFrame) ?_ rfl _).mpr
  · exact (HilbertProof.identity zeroEq).toNative (HilbertProof.identity_sorted zeroEq_sort)
  · intro q c hc
    simp [TAssertion.ctx, identityFrame] at hc

def zeroAddZero : Formula SecondOrder.V := .equal (.add .zero .zero) .zero

def zeroAddZeroFrame : TAssertion SecondOrder.L SecondOrder.C SecondOrder.V where
  dv := []
  hyps := []
  concl := ⟨.turnstile, zeroAddZero.toTree⟩

def independentZeroAddZero : Proof .RCA0 zeroAddZero := .axiom (.base (.axPl0 .zero))

theorem zeroAddZero_native : TDerivable SecondOrder.grammar SecondOrder.RCA0 zeroAddZeroFrame := by
  let τ : SecondOrder.V → Tree SecondOrder.L SecondOrder.V := fun
    | .t => .node .t0 []
    | q => .var q
  have d := TDerivation.nonempty_step (A := zeroAddZeroFrame) (B := SecondOrder.axPl0)
    (G := SecondOrder.grammar) (Γ := SecondOrder.RCA0) (Or.inl (by simp [SecondOrder.base, SecondOrder.basicList])) τ
    (by decide) (by decide) (fun e he => by simp [TAssertion.essentials, SecondOrder.axPl0] at he)
  apply TDerivable.of_nonempty
  simpa [zeroAddZeroFrame, zeroAddZero, Formula.toTree, Term.toTree, SecondOrder.axPl0,
    TExpr.subst, τ] using d

/-- A full-comprehension instance with a fresh set name, and a closed result. -/
def universalSet : Formula ℕ := .comprehension 0 1 (.equal (.var 0) (.var 0))

def universalSetProof : Proof .Z2 universalSet :=
  .axiom (.fullComp 0 1 (.equal (.var 0) (.var 0)) (Or.inl rfl) (by decide))

theorem universalSet_closed : universalSet.Closed := by
  unfold Formula.Closed
  decide

/-- Replacing a free number by a bound number is rejected. -/
theorem number_capture_rejected :
    (Formula.all 1 (.equal (.var 0) .zero)).substNum 0 (.var 1) = none := by decide

/-- Set-name capture is checked independently of number-name capture. -/
theorem set_capture_rejected :
    (Formula.setAll 1 (.member .zero 0)).substSet 0 1 = none := by decide

/-- A concrete environment in the full standard number/set structure. -/
def fullStandardEnv : fullStandard.Env ℕ
  | .inl _ => (0 : ℕ)
  | .inr _ => ⟨∅, Set.mem_univ _⟩

/-- The common fragment's model theorem has a concrete standard-model instance. -/
theorem identity_fullStandard :
    (Formula.imp (.equal .zero .zero) (.equal .zero .zero) : Formula ℕ).henkinEval
      fullStandard fullStandardEnv :=
  Theorems.hilbert_sound fullStandard (HilbertProof.identity _) fullStandardEnv

end Silmaril.Logic.SecondOrderArithmetic
