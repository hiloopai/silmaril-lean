module

public import Silmaril.Logic.ACL2.OrdinalAdmission.Defs
public import Silmaril.Logic.ACL2.Recursive.Thms

@[expose] public section

namespace Silmaril.Logic.ACL2.OrdinalAdmission

open Recursive

variable {S : Signature} {B : Block S} {M : Model S} {measure : Measure B M}

theorem Terminates.model_reduct (h : Terminates B M measure) : h.model.reduct B.inclusion = M :=
  B.modelBy_reduct h.wellFounded h.decreases

theorem Terminates.interpret_unfold (h : Terminates B M measure)
    (state : Call B.members M.primitives.Value) :
    h.interpret state =
      (B.body state.symbol).evalWith M state.args (fun next (_ : Decreases measure next state) =>
        h.interpret next) (h.decreases state) :=
  B.interpretBy_unfold h.wellFounded h.decreases state

theorem Terminates.equation_holds (h : Terminates B M measure) {k : Nat} (f : B.members.Symbol k) :
    (B.equation f).Holds h.model :=
  B.equation_holdsBy h.wellFounded h.decreases f

theorem Terminates.callInduction (h : Terminates B M measure)
    (p : Call B.members M.primitives.Value → Prop)
    (step : ∀ state, (B.body state.symbol).CallsSatisfy M state.args p → p state) :
    ∀ state, p state :=
  B.callInductionBy h.wellFounded h.decreases p step

end Silmaril.Logic.ACL2.OrdinalAdmission
