module

public import Silmaril.Machine.Translation.Defs
public import Silmaril.Machine.CBackend.Behaviour.Refinement.Defs

/-! # Soundness of a translation relation under chosen semantics -/

@[expose] public section

namespace Silmaril.Machine.Translation

inductive Direction where
  | targetRefinesSource
  | sourceRefinesTarget

variable {Src Tgt SrcState TgtState SrcRet TgtRet SrcTrap TgtTrap SrcFault TgtFault : Type*}

/-- The relation of all artifact pairs satisfying the chosen refinement
obligation. Entry and observation arguments are in source/target order.
The refined side supplies the safety premise to `Behaviour.Refines`, which
does not itself require either side to have a behaviour. -/
def largestSound (direction : Direction) (mode : Behaviour.Mode)
    (source : Src → Behaviour.Semantics SrcState SrcRet SrcTrap SrcFault)
    (target : Tgt → Behaviour.Semantics TgtState TgtRet TgtTrap TgtFault)
    (initial : Src → Tgt → SrcState → TgtState → Prop)
    (observation : Src → Tgt → SrcState → TgtState →
      Behaviour.Obs SrcRet TgtRet SrcTrap TgtTrap SrcFault TgtFault) : Relation Src Tgt :=
  fun src tgt => match direction with
  | .targetRefinesSource => Behaviour.Refines mode (target tgt) (source src)
      (fun tgtState srcState => initial src tgt srcState tgtState)
      (fun tgtState srcState => (observation src tgt srcState tgtState).flip)
  | .sourceRefinesTarget => Behaviour.Refines mode (source src) (target tgt)
      (initial src tgt) (observation src tgt)

/-- Every related artifact pair must satisfy the chosen semantic obligation. -/
def Sound (rel : Relation Src Tgt) (direction : Direction) (mode : Behaviour.Mode)
    (source : Src → Behaviour.Semantics SrcState SrcRet SrcTrap SrcFault)
    (target : Tgt → Behaviour.Semantics TgtState TgtRet TgtTrap TgtFault)
    (initial : Src → Tgt → SrcState → TgtState → Prop)
    (observation : Src → Tgt → SrcState → TgtState →
      Behaviour.Obs SrcRet TgtRet SrcTrap TgtTrap SrcFault TgtFault) : Prop :=
  ∀ src tgt, rel src tgt → largestSound direction mode source target initial observation src tgt

end Silmaril.Machine.Translation
