module

public import Silmaril.Logic.HOL.Soundness.Equality

@[expose] public section

/-! Soundness by induction over the signature-parametric HOL proof rules. -/

namespace Silmaril.Proofs.Logic.HOL.Soundness

open Silmaril.Logic.HOL

universe u

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000 in
theorem proves_sound {Sig : Signature} [SigTyping Sig] [UniqueSigTyping Sig]
    [FamilyModel Sig] [TermModel Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} {H : List (Tm Sig depth)} {p : Tm Sig depth}
    (proof : Proves Γ H p) : Entails (Γ := Γ) H p := by
  intro freeEnv boundEnv hypotheses
  induction proof with
  | hyp typed member => exact hypotheses _ member
  | truth typed => exact .boolean true
  | falseElim typed hp falseProof ih =>
      have impossible := ih boundEnv hypotheses
      exact False.elim (Bool.noConfusion (impossible.unique (.boolean false)))
  | boolCases typed hp leftTyped rightTyped leftProof rightProof ihLeft ihRight =>
      obtain ⟨value, valueEval⟩ := hp.eval_exists freeEnv boundEnv
      cases value with
      | false =>
          apply ihRight boundEnv
          intro proposition member
          rcases List.mem_cons.mp member with rfl | member
          · exact .eqTrue .boolTy valueEval (.boolean false) rfl
          · exact hypotheses _ member
      | true =>
          apply ihLeft boundEnv
          intro proposition member
          rcases List.mem_cons.mp member with rfl | member
          · exact valueEval
          · exact hypotheses _ member
  | eqRefl typed hA hx =>
      obtain ⟨value, evaluation⟩ := hx.eval_exists freeEnv boundEnv
      exact .eqTrue hA evaluation evaluation rfl
  | @abs depth Γ H A B left right typed hA hB leftTyping rightTyping premise ih =>
      let leftFunction : DenoteTy (.arr A B) := fun argument =>
        Classical.choose (leftTyping.eval_exists freeEnv
          (extendBoundEnv argument boundEnv))
      let rightFunction : DenoteTy (.arr A B) := fun argument =>
        Classical.choose (rightTyping.eval_exists freeEnv
          (extendBoundEnv argument boundEnv))
      have leftEval : Eval Γ freeEnv boundEnv (.lam A left) (.arr A B) leftFunction :=
        .lam hA fun argument =>
          Classical.choose_spec (leftTyping.eval_exists freeEnv
            (extendBoundEnv argument boundEnv))
      have rightEval : Eval Γ freeEnv boundEnv (.lam A right) (.arr A B) rightFunction :=
        .lam hA fun argument =>
          Classical.choose_spec (rightTyping.eval_exists freeEnv
            (extendBoundEnv argument boundEnv))
      have equal : leftFunction = rightFunction := by
        funext argument
        have lifted : HypsTrue freeEnv (extendBoundEnv argument boundEnv) (H.map weaken) := by
          intro proposition member
          obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
          exact (hypotheses original originalMember).rename (ρ := Fin.succ)
            (target := extendBoundEnv argument boundEnv) (fun _ => rfl) (by
              intro i C lookup
              rfl)
        have pointwise := ih (extendBoundEnv argument boundEnv) lifted
        obtain ⟨leftValue, rightValue, leftPoint, rightPoint, same⟩ :=
          pointwise.eq_true_inv
        have leftChosen := Classical.choose_spec
          (leftTyping.eval_exists freeEnv (extendBoundEnv argument boundEnv))
        have rightChosen := Classical.choose_spec
          (rightTyping.eval_exists freeEnv (extendBoundEnv argument boundEnv))
        exact (leftChosen.unique leftPoint).trans (same.trans (rightPoint.unique rightChosen))
      exact .eqTrue (.arr hA hB) leftEval rightEval equal
  | eqMp typed hA hp hx hy equality application ihEquality ihApplication =>
      have equalityTrue := ihEquality boundEnv hypotheses
      have applicationTrue := ihApplication boundEnv hypotheses
      obtain ⟨left, right, leftEval, rightEval, equal⟩ := equalityTrue.eq_true_inv
      obtain ⟨domain, function, argument, functionEval, argumentEval, applied⟩ :=
        applicationTrue.app_inv
      cases hp.unique functionEval.typing
      cases hx.unique argumentEval.typing
      have argumentEqual := argumentEval.unique leftEval
      have output : applyValue function right = true := by
        rw [← equal, ← argumentEqual]
        exact applied.symm
      exact output ▸ Eval.app functionEval rightEval
  | choice typed hA hp hx application ih =>
      have applicationTrue := ih boundEnv hypotheses
      obtain ⟨domain, predicate, witness, predicateEval, witnessEval, holds⟩ :=
        applicationTrue.app_inv
      cases hp.unique predicateEval.typing
      cases hx.unique witnessEval.typing
      have selected := Eval.eps hA predicateEval
      have chosenTrue := chooseValue_spec predicate witness holds.symm
      exact chosenTrue ▸ Eval.app predicateEval selected
  | @generalize depth Γ H A body typed hA bodyTyping premise ih =>
      let left : DenoteTy (.arr A .boolTy) := fun argument =>
        Classical.choose (bodyTyping.eval_exists freeEnv (extendBoundEnv argument boundEnv))
      have leftEval : Eval Γ freeEnv boundEnv (.lam A body) (.arr A .boolTy) left :=
        .lam hA fun argument =>
          Classical.choose_spec
            (bodyTyping.eval_exists freeEnv (extendBoundEnv argument boundEnv))
      let right : DenoteTy (.arr A .boolTy) := fun _ => true
      have rightEval : Eval Γ freeEnv boundEnv (.lam A (.bool true))
          (.arr A .boolTy) right := .lam hA fun _ => .boolean true
      have equal : left = right := by
        funext argument
        have lifted : HypsTrue freeEnv (extendBoundEnv argument boundEnv) (H.map weaken) := by
          intro proposition member
          obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
          exact (hypotheses original originalMember).rename (ρ := Fin.succ)
            (target := extendBoundEnv argument boundEnv) (fun _ => rfl) (by
              intro i B lookup
              rfl)
        have bodyTrue := ih (extendBoundEnv argument boundEnv) lifted
        exact (Classical.choose_spec
          (bodyTyping.eval_exists freeEnv (extendBoundEnv argument boundEnv))).unique bodyTrue
      exact .eqTrue (.arr hA .boolTy) leftEval rightEval equal
  | @weakenBound depth Γ H p A K typed hA typedK embedding premise ih =>
      let sourceEnv : BoundEnv Γ := fun i B lookup => boundEnv i.succ B lookup
      have sourceHyps : HypsTrue freeEnv sourceEnv H := by
        intro proposition member
        obtain ⟨value, evaluation⟩ :=
          (typed proposition member).eval_exists freeEnv sourceEnv
        have weakened := evaluation.rename (ρ := Fin.succ) (target := boundEnv)
          (fun _ => rfl) (by
            intro i B lookup
            rfl)
        have targetTrue := hypotheses (weaken proposition) (embedding proposition member)
        have equal := weakened.unique targetTrue
        cases equal
        exact evaluation
      exact (ih sourceEnv sourceHyps).rename (ρ := Fin.succ) (target := boundEnv)
        (fun _ => rfl) (by
          intro i B lookup
          rfl)
  | convert typed equality premise ih =>
      have premiseTrue := ih boundEnv hypotheses
      obtain ⟨value, targetEval⟩ := equality.typing.2.eval_exists freeEnv boundEnv
      have values := equality.sound freeEnv boundEnv premiseTrue targetEval
      cases values
      exact targetEval
  | eqOfEqTm typed hA equality =>
      obtain ⟨left, leftEval⟩ := equality.typing.1.eval_exists freeEnv boundEnv
      obtain ⟨right, rightEval⟩ := equality.typing.2.eval_exists freeEnv boundEnv
      exact .eqTrue hA leftEval rightEval (equality.sound freeEnv boundEnv leftEval rightEval)
  | antisymm typed hp hq leftTyped rightTyped leftProof rightProof ihLeft ihRight =>
      obtain ⟨left, leftEval⟩ := hp.eval_exists freeEnv boundEnv
      obtain ⟨right, rightEval⟩ := hq.eval_exists freeEnv boundEnv
      have equal : left = right := by
        cases left <;> cases right <;> try rfl
        · have impossible := ihRight boundEnv (by
            intro r member
            rcases List.mem_cons.mp member with equal | member
            · subst r; exact rightEval
            · exact hypotheses _ member)
          exact False.elim (Bool.noConfusion (impossible.unique leftEval))
        · have impossible := ihLeft boundEnv (by
            intro r member
            rcases List.mem_cons.mp member with equal | member
            · subst r; exact leftEval
            · exact hypotheses _ member)
          exact False.elim (Bool.noConfusion (impossible.unique rightEval))
      exact .eqTrue .boolTy leftEval rightEval equal
  | absRep typed hA hp hx =>
      obtain ⟨value, valueEval⟩ := hx.eval_exists freeEnv boundEnv
      exact .eqTrue (.sub hA hp) (.abs hA hp (.rep hA hp valueEval)) valueEval rfl
  | repAbs typed hA hp hx predicateTyping predicateProof ih =>
      obtain ⟨value, valueEval⟩ := hx.eval_exists freeEnv boundEnv
      exact .eqTrue hA (.rep hA hp (.abs hA hp valueEval)) valueEval rfl

end Silmaril.Proofs.Logic.HOL.Soundness
