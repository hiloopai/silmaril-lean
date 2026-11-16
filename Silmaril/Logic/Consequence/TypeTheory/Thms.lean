module

public import Silmaril.Logic.Consequence.TypeTheory.Defs
public import Silmaril.Logic.Consequence.Institution.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Institution.Thms
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.OriginalInstitution.Thms
public import Silmaril.Logic.Consequence.Thms
import Silmaril.Proofs.Logic.Consequence.TypeTheory.Basic

/-!
# Martin-Löf type theories as consequence systems: laws and soundness

* `extensionalDerives_closed`, `intensionalDerives_closed`, `lambdaPiDerives_closed` and the
  semantic `…Entails_closed`: identity, weakening and cut on judgment hypotheses.
* The extensional systems are pullbacks along `ULift.up`, which keep these laws
  (`Proofs.Logic.Consequence.TypeTheory.closed_pullback_map`).
* `extensionalDerives_le_entails` (from `ExtensionalMLTT.Institution.logic_sound`) and
  `intensionalDerives_le_entails` (from `IntensionalMLTT.OriginalInstitution.logic_sound`):
  soundness. Completeness is not claimed.
-/

@[expose] public section

namespace Silmaril.Consequence.TypeTheory

open CategoryTheory Silmaril.Logic Silmaril.Logic.Institution Silmaril.Logic.TypeTheory

universe u

theorem extensionalDerives_closed :
    Structural.Closed Structural.tarskiRules extensionalDerives :=
  Proofs.Logic.Consequence.TypeTheory.closed_pullback_map ULift.up
    (listSys_closed (ExtensionalMLTT.Institution.logic.{0}.er ⟨⟨⟩⟩))

theorem extensionalEntails_closed :
    Structural.Closed Structural.tarskiRules extensionalEntails.{u} :=
  Proofs.Logic.Consequence.TypeTheory.closed_pullback_map ULift.up
    (roomSeq_closed ExtensionalMLTT.Institution.room.{u})

/-- **Soundness of extensional MLTT** for set hierarchies (in universe `0`). -/
theorem extensionalDerives_le_entails : extensionalDerives ≤ extensionalEntails.{0} :=
  System.pullback_mono _ _ (listSys_le_roomSeq ExtensionalMLTT.Institution.logic_sound ⟨⟨⟩⟩)

theorem intensionalDerives_closed (stage : IntensionalMLTT.OriginalInstitution.Stage) :
    Structural.Closed Structural.tarskiRules (intensionalDerives stage) :=
  listSys_closed ((IntensionalMLTT.OriginalInstitution.logic stage).er ⟨⟨⟩⟩)

theorem intensionalEntails_closed (stage : IntensionalMLTT.OriginalInstitution.Stage) :
    Structural.Closed Structural.tarskiRules (intensionalEntails stage) :=
  roomSeq_closed (IntensionalMLTT.OriginalInstitution.room stage)

/-- **Soundness of intensional MLTT** for realizability, at every stage. -/
theorem intensionalDerives_le_entails (stage : IntensionalMLTT.OriginalInstitution.Stage) :
    intensionalDerives stage ≤ intensionalEntails stage :=
  listSys_le_roomSeq (IntensionalMLTT.OriginalInstitution.logic_sound stage) ⟨⟨⟩⟩

theorem lambdaPiDerives_closed (C : LambdaPi.Calculus) :
    Structural.Closed Structural.tarskiRules (lambdaPiDerives C) :=
  listSys_closed (C.logic.er ⟨⟨⟩⟩)

end Silmaril.Consequence.TypeTheory
