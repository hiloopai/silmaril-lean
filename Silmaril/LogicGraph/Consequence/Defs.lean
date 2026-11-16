module

public import Silmaril.Project.Shapes.Consequence.Defs
public import Silmaril.LogicGraph.Nodes.Logic.Defs
public import Silmaril.Logic.Consequence.Metamath.Thms
public import Silmaril.Logic.Consequence.HOL.Thms
public import Silmaril.Logic.Consequence.TypeTheory.Thms

/-!
# The logic graph: consequence systems of its logics

Consequence systems of the registered logics (`docs/projects/logic-graph.md`, "Consequence
systems"). Each is a `consequence_system` record over the sentences of a registered room
(`room`, `room_at`, checked by Lean). A `semantic` reading is checked to be the room's semantic
consequence, and a `derivability` reading is a proof system on the same sentences. What relates
them is stated as standard consequence problems and answered by the library's theorems:

* `silmaril.shapes.consequence.sound_at`: derivability is sound for semantic consequence
  (`∀ Γ φ`, a THM), or one theory's consequences are another's;
* `silmaril.shapes.consequence.tarski_closed`: identity, weakening and cut.

No completeness is claimed. A system on HOL *propositions* (`HOL.kernel`, `HOL.seq`) is not over
the HOL room's sentences (sequents), so it names no room.

The definitions below are the library's systems at fixed universes and signatures (`0`, HOL's
initial signature, the full intensional stage), because records name universe-monomorphic
constants.
-/

@[expose] public section

namespace Silmaril.LogicGraph.Consequence

open Silmaril.Consequence Silmaril.Project.Shapes.Consequence

/-! ## Metamath: PA, ZF, ZFC and set.mm's ZFC -/

/-- Semantic consequence over the models of `peano.mm`'s PA (Carneiro's models, universe `0`). -/
def paEntails := Metamath.theoryEntails.{0, 0} Metamath.pa Metamath.PA
/-- Semantic consequence over the models of ZF. -/
def zfEntails := Metamath.theoryEntails.{0, 0} Metamath.zf Metamath.ZF0
/-- Semantic consequence over the models of ZFC. -/
def zfcEntails := Metamath.theoryEntails.{0, 0} Metamath.zf Metamath.ZFC
/-- Metamath derivability over set.mm's grammar, without axioms. -/
def setMMDerives := Metamath.derives Logic.Institution.Metatheory.Metamath.setMM
/-- Semantic consequence in the models of set.mm's grammar. -/
def setMMEntails := Metamath.entails.{0, 0} Logic.Institution.Metatheory.Metamath.setMM
/-- Semantic consequence over the models of set.mm's ZFC. -/
def setMMZFCEntails := Metamath.theoryEntails.{0, 0} Logic.Institution.Metatheory.Metamath.setMM
  Logic.Institution.Metatheory.Metamath.zfc

/-! ## HOL, over the initial signature -/

/-- HOL's initial signature (`bool`, `ind`, `=`, `@` and nothing else). -/
def holSig : Logic.Institution.Metatheory.HolSig := ⟨Logic.HOLLight.initialSignature⟩
/-- Pure HOL: the kernel on propositions. -/
def holKernel := HOL.kernel holSig
/-- HOL Light's sequent semantics on propositions (universe `0`). -/
def holSeq := HOL.seq.{0} holSig
/-- HOL derivability between sequents, the sentences of the HOL room. -/
def holSequentDerives := LogicalSystem.listSys Logic.Institution.Metatheory.HOL.logic.{0} holSig
/-- Semantic consequence between sequents. -/
def holSequentEntails := roomSeq (Logic.Institution.Metatheory.HOL.room.{0} holSig)

/-! ## Martin-Löf type theories -/

/-- Validity in set hierarchies (universe `0`). -/
def extensionalEntails := TypeTheory.extensionalEntails.{0}
/-- Intensional MLTT derivability with no universe bound. -/
noncomputable def intensionalDerives := TypeTheory.intensionalDerives ⊤
/-- Realizability with no universe bound. -/
noncomputable def intensionalEntails := TypeTheory.intensionalEntails ⊤

end Silmaril.LogicGraph.Consequence

open Silmaril.Consequence Silmaril.LogicGraph.Consequence Silmaril.Project.Shapes.Consequence

/-! ## Records -/

silmaril consequence_system logic.consequence.metamath.pa.derives :=
    Silmaril.Consequence.Metamath.paTheory
  (room := "logic.institution.metatheory.metamath.room")
  (room_at := "Silmaril.Consequence.Metamath.pa") (reading := "derivability")
  (title := "PA (peano.mm): derivability")
  (doc := "Tree derivability from the 30 axioms of peano.mm, with the premises as further axioms.")
silmaril consequence_system logic.consequence.metamath.pa.entails :=
    Silmaril.LogicGraph.Consequence.paEntails
  (room := "logic.institution.metatheory.metamath.room")
  (room_at := "Silmaril.Consequence.Metamath.pa") (reading := "semantic")
  (title := "PA (peano.mm): semantic consequence")
  (doc := "Every Carneiro model of peano.mm's grammar that satisfies PA and the premises satisfies the conclusion.")
silmaril consequence_system logic.consequence.metamath.zf.derives :=
    Silmaril.Consequence.Metamath.zfTheory
  (room := "logic.institution.metatheory.metamath.room")
  (room_at := "Silmaril.Consequence.Metamath.zf") (reading := "derivability")
  (title := "ZF (set.mm): derivability")
  (doc := "Tree derivability from set.mm's ZF axioms (ZFC without ax-ac) over its set-theory fragment.")
silmaril consequence_system logic.consequence.metamath.zf.entails :=
    Silmaril.LogicGraph.Consequence.zfEntails
  (room := "logic.institution.metatheory.metamath.room")
  (room_at := "Silmaril.Consequence.Metamath.zf") (reading := "semantic")
  (title := "ZF (set.mm): semantic consequence")
silmaril consequence_system logic.consequence.metamath.zfc.derives :=
    Silmaril.Consequence.Metamath.zfcTheory
  (room := "logic.institution.metatheory.metamath.room")
  (room_at := "Silmaril.Consequence.Metamath.zf") (reading := "derivability")
  (title := "ZFC (set.mm): derivability")
  (doc := "Tree derivability from set.mm's ZFC axioms over its set-theory fragment.")
silmaril consequence_system logic.consequence.metamath.zfc.entails :=
    Silmaril.LogicGraph.Consequence.zfcEntails
  (room := "logic.institution.metatheory.metamath.room")
  (room_at := "Silmaril.Consequence.Metamath.zf") (reading := "semantic")
  (title := "ZFC (set.mm): semantic consequence")
silmaril consequence_system logic.consequence.metamath.set_mm.derives :=
    Silmaril.LogicGraph.Consequence.setMMDerives
  (room := "logic.institution.metatheory.metamath.room")
  (room_at := "Silmaril.Logic.Institution.Metatheory.Metamath.setMM") (reading := "derivability")
  (title := "Metamath over set.mm's grammar: derivability")
  (doc := "Metamath's proof system: tree derivability with the premises as axioms, disjoint-variable conditions part of each assertion.")
silmaril consequence_system logic.consequence.metamath.set_mm.entails :=
    Silmaril.LogicGraph.Consequence.setMMEntails
  (room := "logic.institution.metatheory.metamath.room")
  (room_at := "Silmaril.Logic.Institution.Metatheory.Metamath.setMM") (reading := "semantic")
  (title := "Metamath over set.mm's grammar: semantic consequence")
silmaril consequence_system logic.consequence.metamath.set_mm.zfc.derives :=
    Silmaril.Consequence.Metamath.setMMZFCTheory
  (room := "logic.institution.metatheory.metamath.room")
  (room_at := "Silmaril.Logic.Institution.Metatheory.Metamath.setMM") (reading := "derivability")
  (title := "ZFC over all of set.mm's grammar: derivability")
silmaril consequence_system logic.consequence.metamath.set_mm.zfc.entails :=
    Silmaril.LogicGraph.Consequence.setMMZFCEntails
  (room := "logic.institution.metatheory.metamath.room")
  (room_at := "Silmaril.Logic.Institution.Metatheory.Metamath.setMM") (reading := "semantic")
  (title := "ZFC over all of set.mm's grammar: semantic consequence")

silmaril consequence_system logic.consequence.hol.kernel := Silmaril.LogicGraph.Consequence.holKernel
  (reading := "derivability") (title := "HOL: the kernel on propositions")
  (doc := "A HOL Light kernel derivation of the conclusion whose hypotheses are the premises, over the initial signature.")
silmaril consequence_system logic.consequence.hol.seq := Silmaril.LogicGraph.Consequence.holSeq
  (title := "HOL: sequent semantics on propositions")
  (doc := "Every point (model, type valuation, assignment) satisfying the premises satisfies the conclusion. Not over the HOL room's sentences, which are sequents.")
silmaril consequence_system logic.consequence.hol.sequent.derives :=
    Silmaril.LogicGraph.Consequence.holSequentDerives
  (room := "logic.institution.metatheory.hol.room")
  (room_at := "Silmaril.LogicGraph.Consequence.holSig") (reading := "derivability")
  (title := "HOL: derivability between sequents")
silmaril consequence_system logic.consequence.hol.sequent.entails :=
    Silmaril.LogicGraph.Consequence.holSequentEntails
  (room := "logic.institution.metatheory.hol.room")
  (room_at := "Silmaril.LogicGraph.Consequence.holSig") (reading := "semantic")
  (title := "HOL: semantic consequence between sequents")

silmaril consequence_system logic.consequence.mltt.extensional.derives :=
    Silmaril.Consequence.TypeTheory.extensionalDerives
  (room := "logic.type_theory.extensional_mltt.institution.room") (reading := "derivability")
  (title := "Extensional MLTT: derivability")
  (doc := "A derivation of the judgment with the premises as judgment hypotheses. Contexts are part of each judgment.")
silmaril consequence_system logic.consequence.mltt.extensional.entails :=
    Silmaril.LogicGraph.Consequence.extensionalEntails
  (room := "logic.type_theory.extensional_mltt.institution.room") (reading := "semantic")
  (title := "Extensional MLTT: validity in set hierarchies")
silmaril consequence_system logic.consequence.mltt.intensional.derives :=
    Silmaril.LogicGraph.Consequence.intensionalDerives
  (room := "logic.type_theory.intensional_mltt.original_institution.room") (room_at := "⊤")
  (reading := "derivability") (title := "Intensional MLTT (original rules): derivability")
silmaril consequence_system logic.consequence.mltt.intensional.entails :=
    Silmaril.LogicGraph.Consequence.intensionalEntails
  (room := "logic.type_theory.intensional_mltt.original_institution.room") (room_at := "⊤")
  (reading := "semantic") (title := "Intensional MLTT (original rules): realizability")

/-! ## Soundness and inclusions -/

silmaril instance logic.consequence.metamath.pa.sound (expect := THM)
  (title := "PA derivability is sound for its models") := silmaril.shapes.consequence.sound_at
  (S := Silmaril.Consequence.Metamath.paTheory) (T := Silmaril.LogicGraph.Consequence.paEntails)
@[answers "logic.consequence.metamath.pa.sound" thm]
theorem pa_sound : ∀ Γ φ, SoundAt Metamath.paTheory paEntails Γ φ :=
  Metamath.theory_le_theoryEntails _ _

silmaril instance logic.consequence.metamath.zf.sound (expect := THM)
  (title := "ZF derivability is sound for its models") := silmaril.shapes.consequence.sound_at
  (S := Silmaril.Consequence.Metamath.zfTheory) (T := Silmaril.LogicGraph.Consequence.zfEntails)
@[answers "logic.consequence.metamath.zf.sound" thm]
theorem zf_sound : ∀ Γ φ, SoundAt Metamath.zfTheory zfEntails Γ φ :=
  Metamath.theory_le_theoryEntails _ _

silmaril instance logic.consequence.metamath.zfc.sound (expect := THM)
  (title := "ZFC derivability is sound for its models") := silmaril.shapes.consequence.sound_at
  (S := Silmaril.Consequence.Metamath.zfcTheory) (T := Silmaril.LogicGraph.Consequence.zfcEntails)
@[answers "logic.consequence.metamath.zfc.sound" thm]
theorem zfc_sound : ∀ Γ φ, SoundAt Metamath.zfcTheory zfcEntails Γ φ :=
  Metamath.theory_le_theoryEntails _ _

silmaril instance logic.consequence.metamath.zf_zfc (expect := THM)
  (title := "Every consequence of ZF is a consequence of ZFC") :=
  silmaril.shapes.consequence.sound_at
  (S := Silmaril.Consequence.Metamath.zfTheory) (T := Silmaril.Consequence.Metamath.zfcTheory)
@[answers "logic.consequence.metamath.zf_zfc" thm]
theorem zf_zfc : ∀ Γ φ, SoundAt Metamath.zfTheory Metamath.zfcTheory Γ φ :=
  Metamath.zfTheory_le_zfcTheory

silmaril instance logic.consequence.metamath.set_mm.sound (expect := THM)
  (title := "Metamath derivability is sound for Carneiro's models") :=
  silmaril.shapes.consequence.sound_at
  (S := Silmaril.LogicGraph.Consequence.setMMDerives)
  (T := Silmaril.LogicGraph.Consequence.setMMEntails)
@[answers "logic.consequence.metamath.set_mm.sound" thm]
theorem setMM_sound : ∀ Γ φ, SoundAt setMMDerives setMMEntails Γ φ :=
  Metamath.derives_le_entails _

silmaril instance logic.consequence.metamath.set_mm.zfc.sound (expect := THM)
  (title := "set.mm's ZFC derivability is sound for its models") :=
  silmaril.shapes.consequence.sound_at
  (S := Silmaril.Consequence.Metamath.setMMZFCTheory)
  (T := Silmaril.LogicGraph.Consequence.setMMZFCEntails)
@[answers "logic.consequence.metamath.set_mm.zfc.sound" thm]
theorem setMMZFC_sound : ∀ Γ φ, SoundAt Metamath.setMMZFCTheory setMMZFCEntails Γ φ :=
  Metamath.theory_le_theoryEntails _ _

silmaril instance logic.consequence.hol.kernel.sound (expect := THM)
  (title := "The HOL kernel is sound for the sequent semantics") :=
  silmaril.shapes.consequence.sound_at
  (S := Silmaril.LogicGraph.Consequence.holKernel) (T := Silmaril.LogicGraph.Consequence.holSeq)
@[answers "logic.consequence.hol.kernel.sound" thm]
theorem hol_kernel_sound : ∀ Γ φ, SoundAt holKernel holSeq Γ φ :=
  HOL.kernel_le_seq

silmaril instance logic.consequence.hol.sequent.sound (expect := THM)
  (title := "HOL derivability between sequents is sound") := silmaril.shapes.consequence.sound_at
  (S := Silmaril.LogicGraph.Consequence.holSequentDerives)
  (T := Silmaril.LogicGraph.Consequence.holSequentEntails)
@[answers "logic.consequence.hol.sequent.sound" thm]
theorem hol_sequent_sound : ∀ Γ φ, SoundAt holSequentDerives holSequentEntails Γ φ :=
  HOL.logic_listSys_le_roomSeq holSig

silmaril instance logic.consequence.mltt.extensional.sound (expect := THM)
  (title := "Extensional MLTT is sound for set hierarchies") :=
  silmaril.shapes.consequence.sound_at
  (S := Silmaril.Consequence.TypeTheory.extensionalDerives)
  (T := Silmaril.LogicGraph.Consequence.extensionalEntails)
@[answers "logic.consequence.mltt.extensional.sound" thm]
theorem mltt_extensional_sound :
    ∀ Γ φ, SoundAt TypeTheory.extensionalDerives extensionalEntails Γ φ :=
  TypeTheory.extensionalDerives_le_entails

silmaril instance logic.consequence.mltt.intensional.sound (expect := THM)
  (title := "Intensional MLTT is sound for realizability") :=
  silmaril.shapes.consequence.sound_at
  (S := Silmaril.LogicGraph.Consequence.intensionalDerives)
  (T := Silmaril.LogicGraph.Consequence.intensionalEntails)
@[answers "logic.consequence.mltt.intensional.sound" thm]
theorem mltt_intensional_sound : ∀ Γ φ, SoundAt intensionalDerives intensionalEntails Γ φ :=
  TypeTheory.intensionalDerives_le_entails ⊤

/-! ## Identity, weakening and cut -/

silmaril instance logic.consequence.metamath.zfc.derives.tarski (expect := THM)
  (title := "ZFC derivability: identity, weakening and cut") :=
  silmaril.shapes.consequence.tarski_closed (S := Silmaril.Consequence.Metamath.zfcTheory)
@[answers "logic.consequence.metamath.zfc.derives.tarski" thm]
theorem zfc_tarski : TarskiClosed Metamath.zfcTheory := Metamath.theory_closed _ _

silmaril instance logic.consequence.metamath.pa.derives.tarski (expect := THM)
  (title := "PA derivability: identity, weakening and cut") :=
  silmaril.shapes.consequence.tarski_closed (S := Silmaril.Consequence.Metamath.paTheory)
@[answers "logic.consequence.metamath.pa.derives.tarski" thm]
theorem pa_tarski : TarskiClosed Metamath.paTheory := Metamath.theory_closed _ _

silmaril instance logic.consequence.hol.kernel.tarski (expect := THM)
  (title := "The HOL kernel: identity, weakening and cut") :=
  silmaril.shapes.consequence.tarski_closed (S := Silmaril.LogicGraph.Consequence.holKernel)
@[answers "logic.consequence.hol.kernel.tarski" thm]
theorem hol_kernel_tarski : TarskiClosed holKernel := HOL.kernelFrom_closed []

silmaril instance logic.consequence.mltt.extensional.derives.tarski (expect := THM)
  (title := "Extensional MLTT derivability: identity, weakening and cut") :=
  silmaril.shapes.consequence.tarski_closed
  (S := Silmaril.Consequence.TypeTheory.extensionalDerives)
@[answers "logic.consequence.mltt.extensional.derives.tarski" thm]
theorem mltt_extensional_tarski : TarskiClosed TypeTheory.extensionalDerives :=
  TypeTheory.extensionalDerives_closed

silmaril instance logic.consequence.mltt.intensional.derives.tarski (expect := THM)
  (title := "Intensional MLTT derivability: identity, weakening and cut") :=
  silmaril.shapes.consequence.tarski_closed
  (S := Silmaril.LogicGraph.Consequence.intensionalDerives)
@[answers "logic.consequence.mltt.intensional.derives.tarski" thm]
theorem mltt_intensional_tarski : TarskiClosed intensionalDerives :=
  TypeTheory.intensionalDerives_closed ⊤
