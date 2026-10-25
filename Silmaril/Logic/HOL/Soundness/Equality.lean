module

public import Silmaril.Logic.HOL.Soundness.Defs
import Silmaril.Proofs.Logic.HOL.Soundness.Equality

@[expose] public section

/-! # Typing and soundness of HOL equality certificates -/

namespace Silmaril.Logic.HOL

universe u

theorem EqTm.typing {Sig : Signature} [SigTyping Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} {t uterm : Tm Sig depth} {A : Ty Sig}
    (equality : EqTm Γ t uterm A) : HasType Γ t A ∧ HasType Γ uterm A :=
  Silmaril.Proofs.Logic.HOL.Soundness.equality_typing equality

theorem EqTm.sound {Sig : Signature} [SigTyping Sig] [UniqueSigTyping Sig]
    [FamilyModel Sig] [TermModel Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} {t uterm : Tm Sig depth} {A : Ty Sig}
    (equality : EqTm Γ t uterm A) (freeEnv : FreeEnv Sig) (boundEnv : BoundEnv Γ)
    {left right : DenoteTy A} (leftEval : Eval Γ freeEnv boundEnv t A left)
    (rightEval : Eval Γ freeEnv boundEnv uterm A right) : left = right :=
  Silmaril.Proofs.Logic.HOL.Soundness.equality_sound equality freeEnv boundEnv leftEval rightEval

end Silmaril.Logic.HOL
