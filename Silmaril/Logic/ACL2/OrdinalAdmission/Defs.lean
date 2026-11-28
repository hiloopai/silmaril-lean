module

public import Silmaril.Logic.ACL2.Ordinals.Thms
public import Silmaril.Logic.ACL2.Recursive.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.OrdinalAdmission

open Recursive Ordinals

variable {S : Signature} {B : Block S} {M : Model S}

/-- The measure of each state is the ACL2 encoding, including on inputs outside
any guard. -/
abbrev Measure (B : Block S) (M : Model S) := Call B.members M.primitives.Value → Encoding

def Decreases (measure : Measure B M) (next caller : Call B.members M.primitives.Value) : Prop :=
  (measure next).oLt (measure caller) = true

/-- The measure must be an O-P at every state. Each call on the selected path must
strictly decrease under ACL2 O<. -/
structure Terminates (B : Block S) (M : Model S) (measure : Measure B M) : Prop where
  valid : ∀ state, (measure state).oP = true
  decreases : B.TerminatesBy M (Decreases measure)

theorem Terminates.wellFounded {measure : Measure B M} (h : Terminates B M measure) :
    WellFounded (Decreases measure) :=
  let ordinal (state : Call B.members M.primitives.Value) : ValidOrdinal :=
    ⟨measure state, h.valid state⟩
  InvImage.wf ordinal ValidOrdinal.wellFounded

def Terminates.interpret {measure : Measure B M} (h : Terminates B M measure) :
    Call B.members M.primitives.Value → M.primitives.Value :=
  B.interpretBy M h.wellFounded h.decreases

def Terminates.model {measure : Measure B M} (h : Terminates B M measure) : Model B.signature :=
  B.modelBy M h.wellFounded h.decreases

end Silmaril.Logic.ACL2.OrdinalAdmission
