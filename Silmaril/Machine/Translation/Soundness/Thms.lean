module

public import Silmaril.Machine.Translation.Soundness.Defs

/-! # The largest sound translation relation -/

public section

namespace Silmaril.Machine.Translation

variable {Src Tgt SrcState TgtState SrcRet TgtRet SrcTrap TgtTrap SrcFault TgtFault : Type*}
variable {direction : Direction} {mode : Behaviour.Mode}
variable {source : Src → Behaviour.Semantics SrcState SrcRet SrcTrap SrcFault}
variable {target : Tgt → Behaviour.Semantics TgtState TgtRet TgtTrap TgtFault}
variable {initial : Src → Tgt → SrcState → TgtState → Prop}
variable {observation : Src → Tgt → SrcState → TgtState →
  Behaviour.Obs SrcRet TgtRet SrcTrap TgtTrap SrcFault TgtFault}

/-- Sound relations form the lower interval below the pairwise semantic bound. -/
theorem sound_iff_le_largestSound {rel : Relation Src Tgt} :
    Sound rel direction mode source target initial observation ↔
      rel ≤ largestSound direction mode source target initial observation := Iff.rfl

theorem largestSound_sound :
    Sound (largestSound direction mode source target initial observation)
      direction mode source target initial observation := sound_iff_le_largestSound.mpr le_rfl

theorem sound_sSup {rels : Set (Relation Src Tgt)}
    (sound : ∀ rel ∈ rels, Sound rel direction mode source target initial observation) :
    Sound (sSup rels) direction mode source target initial observation :=
  sound_iff_le_largestSound.mpr (sSup_le fun rel mem => sound_iff_le_largestSound.mp (sound rel mem))

end Silmaril.Machine.Translation
