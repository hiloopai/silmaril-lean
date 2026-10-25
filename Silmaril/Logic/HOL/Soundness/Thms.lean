module

public import Silmaril.Logic.HOL.Soundness.Defs
public import Silmaril.Logic.HOL.Soundness.Equality
import Silmaril.Proofs.Logic.HOL.Soundness.Kernel

@[expose] public section

/-! # Soundness of signature-parametric HOL

The theorem applies to the explicitly supplied family and term interpretations,
with unique primitive typing. Its model erases subtype predicates; it is separate
from the schematically polymorphic HOL Light development.
-/

namespace Silmaril.Logic.HOL

universe u

theorem Proves.sound {Sig : Signature} [SigTyping Sig] [UniqueSigTyping Sig]
    [FamilyModel Sig] [TermModel Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} {H : List (Tm Sig depth)} {p : Tm Sig depth}
    (proof : Proves Γ H p) : Entails (Γ := Γ) H p :=
  Silmaril.Proofs.Logic.HOL.Soundness.proves_sound proof

end Silmaril.Logic.HOL
