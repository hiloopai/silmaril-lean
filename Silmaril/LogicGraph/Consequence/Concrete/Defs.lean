module

public import Silmaril.LogicGraph.Consequence.Defs
public import Silmaril.Logic.Consequence.Concrete.Thms

/-!
# The logic graph: HOL and extensional MLTT over their S-expression syntax

Registers the concrete institutions of `Silmaril.Logic.Consequence.Concrete` and their
consequence systems, next to the abstract ones (`Silmaril.LogicGraph.Consequence.Defs`). Lean
checks every record.

**Logic graph.**
* Institutions: `holInst` (a family over HOL signatures), `mlttInst`, and the abstract HOL
  institution `holAbstract` (`⟨HolSig, HOL.inst⟩`), which the HOL comorphism targets.
* Rooms: `holRoom` (a family), `mlttRoom`.
* Corridors `holCorridor`, `mlttCorridor` (to the abstract rooms) and comorphisms `holToAbstract`,
  `mlttToAbstract` (to the abstract institutions). Each sends a concrete sentence to what it
  denotes and keeps the models, with the proved fact `model_expansive`.

**Consequence systems** (HOL at its initial signature, MLTT at universe `0`): the kernel and the
sequent semantics on concrete propositions, the concrete HOL room's semantic consequence, and
derivability and semantic consequence on concrete MLTT judgments. A semantic reading is checked to
be the concrete room's consequence.

**Relations**, as standard consequence problems answered by the library's theorems:
* `sound_at`: soundness of each concrete derivability;
* `tarski_closed`: identity, weakening and cut;
* `translates_at` and `reflects_at`: each concrete system is translated into its abstract system by
  the relation to the abstract syntax (`toProp`, `toJdg`, `HOLSequent.toSeq`), and the translation
  is conservative. For derivability, the encoding translates the abstract system into the concrete
  one as well.
-/

@[expose] public section

namespace Silmaril.LogicGraph.Consequence.Concrete

open Silmaril.Consequence Silmaril.Consequence.Concrete Silmaril.Project.Shapes.Consequence

/-- The HOL kernel on concrete propositions over HOL's initial signature. -/
noncomputable def holKernel := Silmaril.Consequence.Concrete.holKernel LogicGraph.Consequence.holSig []
/-- HOL's sequent semantics on concrete propositions (universe `0`). -/
noncomputable def holSeq := Silmaril.Consequence.Concrete.holSeq.{0} LogicGraph.Consequence.holSig
/-- Semantic consequence between concrete HOL sequents. -/
noncomputable def holSequentEntails := roomSeq (holRoom.{0} LogicGraph.Consequence.holSig)
/-- Semantic consequence of the concrete MLTT room (universe `0`). -/
noncomputable def mlttEntails := Silmaril.Consequence.Concrete.mlttRoomEntails.{0}

end Silmaril.LogicGraph.Consequence.Concrete

open Silmaril.Consequence Silmaril.Consequence.Concrete Silmaril.Project.Shapes.Consequence
open Silmaril.LogicGraph.Consequence.Concrete

/-! ## Logic graph -/

silmaril institution logic.institution.metatheory.hol.institution :=
    Silmaril.Consequence.Concrete.holAbstract
  (title := "HOL (HOL Light), over its signatures")
silmaril institution logic.consequence.concrete.hol.institution :=
    Silmaril.Consequence.Concrete.holInst
  (title := "HOL over S-expressions, at a signature")
silmaril institution logic.consequence.concrete.mltt.institution :=
    Silmaril.Consequence.Concrete.mlttInst
  (title := "Extensional MLTT over S-expressions")
silmaril room logic.consequence.concrete.hol.room := Silmaril.Consequence.Concrete.holRoom
  (title := "Concrete HOL sequents, HOL models")
silmaril room logic.consequence.concrete.mltt.room := Silmaril.Consequence.Concrete.mlttRoom
  (title := "Concrete MLTT judgments, set hierarchies")
silmaril corridor logic.consequence.concrete.hol.corridor := Silmaril.Consequence.Concrete.holCorridor
  (facts := [Silmaril.Consequence.Concrete.holCorridor_modelExpansive])
  (title := "Each concrete HOL sequent to the sequent it denotes")
silmaril corridor logic.consequence.concrete.mltt.corridor := Silmaril.Consequence.Concrete.mlttCorridor
  (facts := [Silmaril.Consequence.Concrete.mlttCorridor_modelExpansive])
  (title := "Each concrete MLTT judgment to the judgment it denotes")
silmaril comorphism logic.consequence.concrete.hol.to_abstract :=
    Silmaril.Consequence.Concrete.holToAbstract
  (facts := [Silmaril.Consequence.Concrete.holToAbstract_modelExpansive])
  (title := "Concrete HOL to abstract HOL")
silmaril comorphism logic.consequence.concrete.mltt.to_abstract :=
    Silmaril.Consequence.Concrete.mlttToAbstract
  (facts := [Silmaril.Consequence.Concrete.mlttToAbstract_modelExpansive])
  (title := "Concrete extensional MLTT to abstract extensional MLTT")

/-! ## Consequence systems -/

silmaril consequence_system logic.consequence.concrete.hol.kernel :=
    Silmaril.LogicGraph.Consequence.Concrete.holKernel
  (reading := "derivability") (title := "HOL over S-expressions: the kernel on concrete propositions")
  (doc := "A kernel derivation of what the conclusion denotes from what the premises denote, over the initial signature. Concrete propositions are S-expressions such as (app (= bool) (fvar 3 bool)).")
silmaril consequence_system logic.consequence.concrete.hol.seq :=
    Silmaril.LogicGraph.Consequence.Concrete.holSeq
  (title := "HOL over S-expressions: sequent semantics on concrete propositions")
silmaril consequence_system logic.consequence.concrete.hol.sequent.entails :=
    Silmaril.LogicGraph.Consequence.Concrete.holSequentEntails
  (room := "logic.consequence.concrete.hol.room")
  (room_at := "Silmaril.LogicGraph.Consequence.holSig") (reading := "semantic")
  (title := "HOL over S-expressions: semantic consequence between concrete sequents")
silmaril consequence_system logic.consequence.concrete.mltt.derives :=
    Silmaril.Consequence.Concrete.mlttDerives
  (room := "logic.consequence.concrete.mltt.room") (reading := "derivability")
  (title := "Extensional MLTT over S-expressions: derivability")
  (doc := "Derivability of what the concrete judgments denote. Concrete judgments are S-expressions such as (jdg (ctx (x nat)) nat (fv x) (fv x)).")
silmaril consequence_system logic.consequence.concrete.mltt.entails :=
    Silmaril.LogicGraph.Consequence.Concrete.mlttEntails
  (room := "logic.consequence.concrete.mltt.room") (reading := "semantic")
  (title := "Extensional MLTT over S-expressions: validity in set hierarchies")

/-! ## Soundness and the structural laws -/

silmaril instance logic.consequence.concrete.hol.kernel.sound (expect := THM)
  (title := "The concrete HOL kernel is sound for the sequent semantics") :=
  silmaril.shapes.consequence.sound_at
  (S := Silmaril.LogicGraph.Consequence.Concrete.holKernel)
  (T := Silmaril.LogicGraph.Consequence.Concrete.holSeq)
@[answers "logic.consequence.concrete.hol.kernel.sound" thm]
theorem concrete_hol_kernel_sound :
    ∀ Γ φ, SoundAt Silmaril.LogicGraph.Consequence.Concrete.holKernel Silmaril.LogicGraph.Consequence.Concrete.holSeq Γ φ :=
  holKernel_le_holSeq

silmaril instance logic.consequence.concrete.mltt.sound (expect := THM)
  (title := "Concrete extensional MLTT is sound for its room") :=
  silmaril.shapes.consequence.sound_at
  (S := Silmaril.Consequence.Concrete.mlttDerives)
  (T := Silmaril.LogicGraph.Consequence.Concrete.mlttEntails)
@[answers "logic.consequence.concrete.mltt.sound" thm]
theorem concrete_mltt_sound :
    ∀ Γ φ, SoundAt mlttDerives Silmaril.LogicGraph.Consequence.Concrete.mlttEntails Γ φ :=
  mlttDerives_le_roomEntails

silmaril instance logic.consequence.concrete.hol.kernel.tarski (expect := THM)
  (title := "The concrete HOL kernel: identity, weakening and cut") :=
  silmaril.shapes.consequence.tarski_closed (S := Silmaril.LogicGraph.Consequence.Concrete.holKernel)
@[answers "logic.consequence.concrete.hol.kernel.tarski" thm]
theorem concrete_hol_kernel_tarski : TarskiClosed Silmaril.LogicGraph.Consequence.Concrete.holKernel :=
  holKernel_closed []

silmaril instance logic.consequence.concrete.mltt.derives.tarski (expect := THM)
  (title := "Concrete extensional MLTT derivability: identity, weakening and cut") :=
  silmaril.shapes.consequence.tarski_closed (S := Silmaril.Consequence.Concrete.mlttDerives)
@[answers "logic.consequence.concrete.mltt.derives.tarski" thm]
theorem concrete_mltt_tarski : TarskiClosed mlttDerives := mlttDerives_closed

/-! ## Concrete to abstract, and back -/

silmaril instance logic.consequence.concrete.hol.kernel.to_abstract (expect := THM)
  (title := "The concrete HOL kernel translates into the abstract kernel") :=
  silmaril.shapes.consequence.translates_at
  (S := Silmaril.LogicGraph.Consequence.Concrete.holKernel)
  (T := Silmaril.LogicGraph.Consequence.holKernel)
  (f := List.map Silmaril.Consequence.Concrete.HOLSen.toProp)
  (g := Silmaril.Consequence.Concrete.HOLSen.toProp)
@[answers "logic.consequence.concrete.hol.kernel.to_abstract" thm]
theorem concrete_hol_kernel_to_abstract :
    ∀ Γ φ, TranslatesAt Silmaril.LogicGraph.Consequence.Concrete.holKernel Silmaril.LogicGraph.Consequence.holKernel
      (List.map HOLSen.toProp) HOLSen.toProp Γ φ :=
  fun _ _ h => h

silmaril instance logic.consequence.concrete.hol.kernel.reflects (expect := THM)
  (title := "The translation of the concrete HOL kernel is conservative") :=
  silmaril.shapes.consequence.reflects_at
  (S := Silmaril.LogicGraph.Consequence.Concrete.holKernel)
  (T := Silmaril.LogicGraph.Consequence.holKernel)
  (f := List.map Silmaril.Consequence.Concrete.HOLSen.toProp)
  (g := Silmaril.Consequence.Concrete.HOLSen.toProp)
@[answers "logic.consequence.concrete.hol.kernel.reflects" thm]
theorem concrete_hol_kernel_reflects :
    ∀ Γ φ, ReflectsAt Silmaril.LogicGraph.Consequence.Concrete.holKernel Silmaril.LogicGraph.Consequence.holKernel
      (List.map HOLSen.toProp) HOLSen.toProp Γ φ :=
  fun _ _ h => h

silmaril instance logic.consequence.concrete.hol.kernel.of_abstract (expect := THM)
  (title := "The abstract HOL kernel translates into the concrete kernel by encoding") :=
  silmaril.shapes.consequence.translates_at
  (S := Silmaril.LogicGraph.Consequence.holKernel)
  (T := Silmaril.LogicGraph.Consequence.Concrete.holKernel)
  (f := List.map Silmaril.Consequence.Concrete.HOLSen.ofProp)
  (g := Silmaril.Consequence.Concrete.HOLSen.ofProp)
@[answers "logic.consequence.concrete.hol.kernel.of_abstract" thm]
theorem concrete_hol_kernel_of_abstract :
    ∀ Γ φ, TranslatesAt Silmaril.LogicGraph.Consequence.holKernel Silmaril.LogicGraph.Consequence.Concrete.holKernel
      (List.map HOLSen.ofProp) HOLSen.ofProp Γ φ :=
  fun Γ φ h => (holKernel_ofProp_iff [] Γ φ).2 h

silmaril instance logic.consequence.concrete.hol.sequent.to_abstract (expect := THM)
  (title := "Concrete HOL sequent consequence translates into abstract sequent consequence") :=
  silmaril.shapes.consequence.translates_at
  (S := Silmaril.LogicGraph.Consequence.Concrete.holSequentEntails)
  (T := Silmaril.LogicGraph.Consequence.holSequentEntails)
  (f := List.map Silmaril.Consequence.Concrete.HOLSequent.toSeq)
  (g := Silmaril.Consequence.Concrete.HOLSequent.toSeq)
@[answers "logic.consequence.concrete.hol.sequent.to_abstract" thm]
theorem concrete_hol_sequent_to_abstract :
    ∀ Γ φ, TranslatesAt Silmaril.LogicGraph.Consequence.Concrete.holSequentEntails
      Silmaril.LogicGraph.Consequence.holSequentEntails (List.map HOLSequent.toSeq) HOLSequent.toSeq Γ φ :=
  fun Γ φ h => (holRoom_seq_iff Γ φ).1 h

silmaril instance logic.consequence.concrete.hol.sequent.reflects (expect := THM)
  (title := "The translation of concrete HOL sequent consequence is conservative") :=
  silmaril.shapes.consequence.reflects_at
  (S := Silmaril.LogicGraph.Consequence.Concrete.holSequentEntails)
  (T := Silmaril.LogicGraph.Consequence.holSequentEntails)
  (f := List.map Silmaril.Consequence.Concrete.HOLSequent.toSeq)
  (g := Silmaril.Consequence.Concrete.HOLSequent.toSeq)
@[answers "logic.consequence.concrete.hol.sequent.reflects" thm]
theorem concrete_hol_sequent_reflects :
    ∀ Γ φ, ReflectsAt Silmaril.LogicGraph.Consequence.Concrete.holSequentEntails
      Silmaril.LogicGraph.Consequence.holSequentEntails (List.map HOLSequent.toSeq) HOLSequent.toSeq Γ φ :=
  fun Γ φ h => (holRoom_seq_iff Γ φ).2 h

silmaril instance logic.consequence.concrete.mltt.derives.to_abstract (expect := THM)
  (title := "Concrete MLTT derivability translates into abstract derivability") :=
  silmaril.shapes.consequence.translates_at
  (S := Silmaril.Consequence.Concrete.mlttDerives)
  (T := Silmaril.Consequence.TypeTheory.extensionalDerives)
  (f := List.map Silmaril.Consequence.Concrete.MLTTSen.toJdg)
  (g := Silmaril.Consequence.Concrete.MLTTSen.toJdg)
@[answers "logic.consequence.concrete.mltt.derives.to_abstract" thm]
theorem concrete_mltt_derives_to_abstract :
    ∀ Γ φ, TranslatesAt mlttDerives TypeTheory.extensionalDerives
      (List.map MLTTSen.toJdg) MLTTSen.toJdg Γ φ :=
  fun _ _ h => h

silmaril instance logic.consequence.concrete.mltt.derives.reflects (expect := THM)
  (title := "The translation of concrete MLTT derivability is conservative") :=
  silmaril.shapes.consequence.reflects_at
  (S := Silmaril.Consequence.Concrete.mlttDerives)
  (T := Silmaril.Consequence.TypeTheory.extensionalDerives)
  (f := List.map Silmaril.Consequence.Concrete.MLTTSen.toJdg)
  (g := Silmaril.Consequence.Concrete.MLTTSen.toJdg)
@[answers "logic.consequence.concrete.mltt.derives.reflects" thm]
theorem concrete_mltt_derives_reflects :
    ∀ Γ φ, ReflectsAt mlttDerives TypeTheory.extensionalDerives
      (List.map MLTTSen.toJdg) MLTTSen.toJdg Γ φ :=
  fun _ _ h => h

silmaril instance logic.consequence.concrete.mltt.derives.of_abstract (expect := THM)
  (title := "Abstract MLTT derivability translates into concrete derivability by encoding") :=
  silmaril.shapes.consequence.translates_at
  (S := Silmaril.Consequence.TypeTheory.extensionalDerives)
  (T := Silmaril.Consequence.Concrete.mlttDerives)
  (f := List.map Silmaril.Consequence.Concrete.MLTTSen.ofJdg)
  (g := Silmaril.Consequence.Concrete.MLTTSen.ofJdg)
@[answers "logic.consequence.concrete.mltt.derives.of_abstract" thm]
theorem concrete_mltt_derives_of_abstract :
    ∀ Γ φ, TranslatesAt TypeTheory.extensionalDerives mlttDerives
      (List.map MLTTSen.ofJdg) MLTTSen.ofJdg Γ φ :=
  fun Γ φ h => (mlttDerives_ofJdg_iff Γ φ).2 h

silmaril instance logic.consequence.concrete.mltt.entails.to_abstract (expect := THM)
  (title := "Concrete MLTT semantic consequence translates into validity in set hierarchies") :=
  silmaril.shapes.consequence.translates_at
  (S := Silmaril.LogicGraph.Consequence.Concrete.mlttEntails)
  (T := Silmaril.LogicGraph.Consequence.extensionalEntails)
  (f := List.map Silmaril.Consequence.Concrete.MLTTSen.toJdg)
  (g := Silmaril.Consequence.Concrete.MLTTSen.toJdg)
@[answers "logic.consequence.concrete.mltt.entails.to_abstract" thm]
theorem concrete_mltt_entails_to_abstract :
    ∀ Γ φ, TranslatesAt Silmaril.LogicGraph.Consequence.Concrete.mlttEntails
      Silmaril.LogicGraph.Consequence.extensionalEntails (List.map MLTTSen.toJdg) MLTTSen.toJdg Γ φ :=
  fun Γ φ h => (mlttRoomEntails_iff Γ φ).1 h

silmaril instance logic.consequence.concrete.mltt.entails.reflects (expect := THM)
  (title := "The translation of concrete MLTT semantic consequence is conservative") :=
  silmaril.shapes.consequence.reflects_at
  (S := Silmaril.LogicGraph.Consequence.Concrete.mlttEntails)
  (T := Silmaril.LogicGraph.Consequence.extensionalEntails)
  (f := List.map Silmaril.Consequence.Concrete.MLTTSen.toJdg)
  (g := Silmaril.Consequence.Concrete.MLTTSen.toJdg)
@[answers "logic.consequence.concrete.mltt.entails.reflects" thm]
theorem concrete_mltt_entails_reflects :
    ∀ Γ φ, ReflectsAt Silmaril.LogicGraph.Consequence.Concrete.mlttEntails
      Silmaril.LogicGraph.Consequence.extensionalEntails (List.map MLTTSen.toJdg) MLTTSen.toJdg Γ φ :=
  fun Γ φ h => (mlttRoomEntails_iff Γ φ).2 h
