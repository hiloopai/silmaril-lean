module

public import Silmaril.Logic.ACL2.Books.Thms
public import Silmaril.Logic.ACL2.Recursive.Institution.Defs
public import Silmaril.Logic.ACL2.Recursive.Thms
import Silmaril.Proofs.Logic.ACL2.Recursive.Institution

@[expose] public section

namespace Silmaril.Logic.ACL2.Recursive.Block

variable {P : Presentation} {W : World} {B : Block W.signature} {fresh : B.TheoremNamesFresh W}

/-- The equation of each new block member is available to the existing syntactic π-institution. -/
theorem equation_mem (B : Block P.signature) {k : Nat} (f : B.members.Symbol k) :
    B.equation f ∈ (B.extendPresentation P).equations :=
  Proofs.Logic.ACL2.Recursive.Institution.equation_mem B f

/-- The equations are exactly the translated old equations and the equations of new members. -/
theorem extendPresentation_equations (B : Block P.signature) :
    (B.extendPresentation P).equations =
      Sentence.map B.inclusion '' P.equations ∪
        {p | ∃ (k : Nat) (f : B.members.Symbol k), p = B.equation f} :=
  Proofs.Logic.ACL2.Recursive.Institution.equations B

/-- The prior theorem table stays checked using the translated derivations. -/
theorem extendWorld_checked (hW : W.Checked) : (B.extendWorld W fresh).Checked :=
  Proofs.Logic.ACL2.Recursive.Institution.extendWorld_checked hW

/-- A well-founded interpretation expands the input model to a model of the extended world.
Its reduct along `(B.worldExtension W fresh).presentation.signature` is the original model
by `Block.modelBy_reduct`. -/
theorem modelBy_models {M : Model W.signature}
    {lt : Call B.members M.primitives.Value → Call B.members M.primitives.Value → Prop}
    (wf : WellFounded lt) (h : B.TerminatesBy M lt) (hM : W.Models M) :
    (B.extendWorld W fresh).Models (B.modelBy M wf h) :=
  Proofs.Logic.ACL2.Recursive.Institution.modelBy_models wf h hM

/-- Semantic conservativity over the old signature requires termination evidence on every
input-world model. A certificate for a particular model gives an expansion of that model. -/
theorem entails_iff
    (terminates : ∀ M : Model W.signature, W.Models M →
      ∃ lt : Call B.members M.primitives.Value → Call B.members M.primitives.Value → Prop,
        WellFounded lt ∧ B.TerminatesBy M lt)
    (p : Sentence W.signature) :
    (B.extendWorld W fresh).Entails (p.map B.inclusion) ↔ W.Entails p :=
  Proofs.Logic.ACL2.Recursive.Institution.entails_iff terminates p

end Silmaril.Logic.ACL2.Recursive.Block
