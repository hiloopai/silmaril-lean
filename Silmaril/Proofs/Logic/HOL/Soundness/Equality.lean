module

public import Silmaril.Logic.HOL.Soundness.Defs

@[expose] public section

/-! Equality-certificate typing and soundness proofs. -/

namespace Silmaril.Proofs.Logic.HOL.Soundness

open Silmaril.Logic.HOL

universe u

theorem equality_typing {Sig : Signature} [SigTyping Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} {t uterm : Tm Sig depth} {A : Ty Sig}
    (equality : EqTm Γ t uterm A) : HasType Γ t A ∧ HasType Γ uterm A := by
  induction equality with
  | refl typing => exact ⟨typing, typing⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | app _ _ ihf ihx => exact ⟨.app ihf.1 ihx.1, .app ihf.2 ihx.2⟩
  | lam hA _ ih => exact ⟨.lam _ hA ih.1, .lam _ hA ih.2⟩
  | beta body x hA bodyTyping argumentTyping resultTyping =>
      exact ⟨.app (.lam _ hA bodyTyping) argumentTyping, resultTyping⟩
  | eta name fresh functionTyping etaTyping => exact ⟨etaTyping, functionTyping⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000 in
theorem equality_sound {Sig : Signature} [SigTyping Sig] [UniqueSigTyping Sig]
    [FamilyModel Sig] [TermModel Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} {t uterm : Tm Sig depth} {A : Ty Sig}
    (equality : EqTm Γ t uterm A) (freeEnv : FreeEnv Sig) (boundEnv : BoundEnv Γ)
    {left right : DenoteTy A} (leftEval : Eval Γ freeEnv boundEnv t A left)
    (rightEval : Eval Γ freeEnv boundEnv uterm A right) : left = right := by
  induction equality with
  | refl typing => exact leftEval.unique rightEval
  | symm equality ih => exact (ih boundEnv rightEval leftEval).symm
  | trans first second ih₁ ih₂ =>
      obtain ⟨middle, middleEval⟩ := (equality_typing first).2.eval_exists freeEnv boundEnv
      exact (ih₁ boundEnv leftEval middleEval).trans (ih₂ boundEnv middleEval rightEval)
  | app functionEquality argumentEquality ihf ihx =>
      cases leftEval with
      | app leftFunction leftArgument =>
          cases rightEval with
          | app rightFunction rightArgument =>
              cases (equality_typing functionEquality).1.unique leftFunction.typing
              cases (equality_typing functionEquality).2.unique rightFunction.typing
              rw [ihf boundEnv leftFunction rightFunction,
                ihx boundEnv leftArgument rightArgument]
  | lam hA bodyEquality ih =>
      cases leftEval with
      | lam _ leftBody =>
          cases rightEval with
          | lam _ rightBody =>
              funext argument
              exact ih (extendBoundEnv argument boundEnv)
                (leftBody argument) (rightBody argument)
  | beta body x hA bodyTyping argumentTyping resultTyping =>
      cases leftEval with
      | app functionEval argumentEval =>
          cases functionEval with
          | lam _ bodyEval =>
              let argument := Classical.choose (argumentTyping.eval_exists freeEnv boundEnv)
              have chosenArgument := Classical.choose_spec
                (argumentTyping.eval_exists freeEnv boundEnv)
              have argumentValue := chosenArgument.unique argumentEval
              subst argumentValue
              let sourceEnv := extendBoundEnv argument boundEnv
              have substitutions : EnvSubstitution _ _ (Fin.cases x .bv)
                  freeEnv sourceEnv boundEnv := by
                intro i
                refine Fin.cases ?_ (fun j => ?_) i
                · intro hi
                  change Eval _ freeEnv boundEnv x _ argument
                  exact argumentEval
                · intro hi
                  exact .bv freeEnv boundEnv hi rfl
              have opened := bodyTyping.eval_instantiate (bodyEval argument) substitutions
              exact opened.unique rightEval
  | eta name fresh functionTyping etaTyping =>
      cases leftEval with
      | lam domainKinded etaBody =>
          funext argument
          have weakened := rightEval.rename (ρ := Fin.succ)
            (target := extendBoundEnv argument boundEnv) (fun _ => rfl) (by
              intro i B lookup
              rfl)
          have argumentEval := Eval.bv freeEnv (i := 0)
            (extendBoundEnv argument boundEnv) domainKinded rfl
          obtain ⟨domain, bodyFunctionValue, bodyArgumentValue,
              bodyFunction, bodyArgument, output⟩ := (etaBody argument).app_inv
          cases weakened.typing.unique bodyFunction.typing
          have hf := bodyFunction.unique weakened
          have ha := bodyArgument.unique argumentEval
          cases hf
          cases ha
          exact output

end Silmaril.Proofs.Logic.HOL.Soundness
