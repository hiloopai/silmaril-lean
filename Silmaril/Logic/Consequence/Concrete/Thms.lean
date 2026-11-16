module

public import Silmaril.Logic.Consequence.Concrete.Defs
public import Silmaril.Logic.Consequence.HOL.Thms
public import Silmaril.Logic.Consequence.TypeTheory.Thms
public import Silmaril.Logic.HOLLight.SExp.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp.Thms
public import Silmaril.Logic.Institution.Borrowing
import Silmaril.Proofs.Logic.Consequence.Concrete.Basic

/-!
# Institutions and consequence systems over concrete syntax: the relation to the abstract

**The relation.** `HOLSen.toProp` and `MLTTSen.toJdg` are bijections (`toProp_ofProp`,
`ofProp_toProp`, `toJdg_ofJdg`, `ofJdg_toJdg`), computed by the decoders (`decodeTm_toProp`,
`decodeJdg_toJdg`).

**Consequence is preserved and reflected.** `holKernel_ofProp_iff`, `holSeq_ofProp_iff`,
`mlttDerives_ofJdg_iff`, `mlttEntails_ofJdg_iff`: a consequence holds over concrete syntax iff it
holds over the abstract syntax it denotes. As translations: `holKernelToAbstract`,
`holKernelOfAbstract`, `mlttDerivesToAbstract`, `mlttDerivesOfAbstract`.

**Laws and soundness carry over.** `holKernel_closed`, `mlttDerives_closed` (identity, weakening,
cut); `holKernel_le_holSeq`, `mlttDerives_le_entails` (soundness). No completeness is claimed.

**Institutions.** The corridors and the comorphisms keep the models, so they are model-expansive
(`holCorridor_modelExpansive`, `holToAbstract_modelExpansive`, `mlttCorridor_modelExpansive`,
`mlttToAbstract_modelExpansive`). So semantic consequence over concrete sentences is semantic
consequence over what they denote (`holRoom_seq_iff`, `mlttRoom_seq_iff`, `mlttRoomEntails_iff`).
-/

@[expose] public section

namespace Silmaril.Consequence.Concrete

open CategoryTheory Silmaril.Logic Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Metatheory (HolSig)

universe u

/-! ## HOL -/

section HOL

open Silmaril.Logic.HOLLight Silmaril.Consequence.HOL

variable {S : HolSig}

theorem toProp_ofProp (p : HOLProp S) : (HOLSen.ofProp p).toProp = p :=
  Proofs.Logic.Consequence.Concrete.toProp_ofProp p

theorem ofProp_toProp (e : HOLSen S) : HOLSen.ofProp e.toProp = e :=
  Proofs.Logic.Consequence.Concrete.ofProp_toProp e

/-- The decoder computes the relation. -/
theorem decodeTm_toProp (e : HOLSen S) : SExp.decodeTm e.1 = some e.toProp.1 :=
  SExp.decodeTm_eq_some_iff.2 (Proofs.Logic.Consequence.Concrete.encode_toProp e)

theorem holKernel_ofProp_iff (Δ : Theory) (Γ : List (HOLProp S)) (p : HOLProp S) :
    holKernel S Δ (Γ.map HOLSen.ofProp) (HOLSen.ofProp p) ↔ kernelFrom S Δ Γ p :=
  Proofs.Logic.Consequence.Concrete.holKernel_ofProp_iff Δ Γ p

theorem holSeq_ofProp_iff (Γ : List (HOLProp S)) (p : HOLProp S) :
    holSeq.{u} S (Γ.map HOLSen.ofProp) (HOLSen.ofProp p) ↔ seq.{u} S Γ p :=
  Proofs.Logic.Consequence.Concrete.holSeq_ofProp_iff Γ p

/-- The concrete kernel translated to the abstract one (each sentence to what it denotes). -/
noncomputable def holKernelToAbstract (Δ : Theory) : Translation (holKernel S Δ) (kernelFrom S Δ) :=
  ⟨List.map HOLSen.toProp, HOLSen.toProp, fun _ _ h => h⟩

/-- The abstract kernel translated to the concrete one (each proposition to its concrete form). -/
def holKernelOfAbstract (Δ : Theory) : Translation (kernelFrom S Δ) (holKernel S Δ) :=
  ⟨List.map HOLSen.ofProp, HOLSen.ofProp, fun Γ p h => (holKernel_ofProp_iff Δ Γ p).2 h⟩

theorem holKernel_closed (Δ : Theory) : Structural.Closed Structural.tarskiRules (holKernel S Δ) :=
  Proofs.Logic.Consequence.Concrete.holKernel_closed Δ

/-- **Soundness of pure HOL over concrete syntax.** -/
theorem holKernel_le_holSeq : holKernel S [] ≤ holSeq.{u} S :=
  System.pullback_mono _ _ kernel_le_seq

theorem holCorridor_modelExpansive : (holCorridor.{u} S).ModelExpansive := fun M => ⟨M, rfl⟩

theorem holToAbstract_modelExpansive : (holToAbstract.{u} S).ModelExpansive :=
  fun _ M => ⟨M, rfl⟩

/-- Semantic consequence between concrete sequents is semantic consequence between the sequents
they denote. -/
theorem holRoom_seq_iff (Γ : List (HOLSequent S)) (e : HOLSequent S) :
    roomSeq (holRoom.{u} S) Γ e ↔
      roomSeq (Metatheory.HOL.room.{u} S) (Γ.map HOLSequent.toSeq) e.toSeq :=
  ⟨fun h => (corridorSeq (holCorridor.{u} S)).sound Γ e h,
    corridorSeq_reflect (holCorridor.{u} S) holCorridor_modelExpansive⟩

end HOL

/-! ## Extensional MLTT -/

section MLTT

open Silmaril.Logic.TypeTheory.ExtensionalMLTT

theorem toJdg_ofJdg (J : EJdg) : (MLTTSen.ofJdg J).toJdg = J :=
  Proofs.Logic.Consequence.Concrete.toJdg_ofJdg J

theorem ofJdg_toJdg (e : MLTTSen) : MLTTSen.ofJdg e.toJdg = e :=
  Proofs.Logic.Consequence.Concrete.ofJdg_toJdg e

/-- The decoder computes the relation. -/
theorem decodeJdg_toJdg (e : MLTTSen) : SExp.decodeJdg e.1 = some e.toJdg :=
  SExp.decodeJdg_eq_some_iff.2 (Proofs.Logic.Consequence.Concrete.encode_toJdg e)

theorem mlttDerives_ofJdg_iff (Γ : List EJdg) (J : EJdg) :
    mlttDerives (Γ.map MLTTSen.ofJdg) (MLTTSen.ofJdg J) ↔ TypeTheory.extensionalDerives Γ J :=
  Proofs.Logic.Consequence.Concrete.mlttDerives_ofJdg_iff Γ J

theorem mlttEntails_ofJdg_iff (Γ : List EJdg) (J : EJdg) :
    mlttEntails.{u} (Γ.map MLTTSen.ofJdg) (MLTTSen.ofJdg J) ↔
      TypeTheory.extensionalEntails.{u} Γ J :=
  Proofs.Logic.Consequence.Concrete.mlttEntails_ofJdg_iff Γ J

/-- Concrete derivability translated to the abstract (each sentence to what it denotes). -/
noncomputable def mlttDerivesToAbstract : Translation mlttDerives TypeTheory.extensionalDerives :=
  ⟨List.map MLTTSen.toJdg, MLTTSen.toJdg, fun _ _ h => h⟩

/-- Abstract derivability translated to the concrete (each judgment to its concrete form). -/
def mlttDerivesOfAbstract : Translation TypeTheory.extensionalDerives mlttDerives :=
  ⟨List.map MLTTSen.ofJdg, MLTTSen.ofJdg, fun Γ J h => (mlttDerives_ofJdg_iff Γ J).2 h⟩

theorem mlttDerives_closed : Structural.Closed Structural.tarskiRules mlttDerives :=
  Proofs.Logic.Consequence.Concrete.mlttDerives_closed

/-- **Soundness of extensional MLTT over concrete syntax.** -/
theorem mlttDerives_le_entails : mlttDerives ≤ mlttEntails.{0} :=
  System.pullback_mono _ _ TypeTheory.extensionalDerives_le_entails

theorem mlttCorridor_modelExpansive : mlttCorridor.{u}.ModelExpansive := fun M => ⟨M, rfl⟩

theorem mlttToAbstract_modelExpansive : mlttToAbstract.{u}.ModelExpansive := fun _ M => ⟨M, rfl⟩

/-- Semantic consequence between concrete judgments is semantic consequence between the
judgments they denote. -/
theorem mlttRoom_seq_iff (Γ : List mlttRoom.{u}.Sen) (e : mlttRoom.{u}.Sen) :
    roomSeq mlttRoom.{u} Γ e ↔
      roomSeq Institution.room.{u} (Γ.map mlttCorridor.{u}.sen) (mlttCorridor.{u}.sen e) :=
  ⟨fun h => (corridorSeq mlttCorridor.{u}).sound Γ e h,
    corridorSeq_reflect mlttCorridor.{u} mlttCorridor_modelExpansive⟩

/-- The concrete room's semantic consequence is validity in set hierarchies of what the concrete
judgments denote. -/
theorem mlttRoomEntails_iff (Γ : List MLTTSen) (e : MLTTSen) :
    mlttRoomEntails.{u} Γ e ↔ TypeTheory.extensionalEntails.{u} (Γ.map MLTTSen.toJdg) e.toJdg :=
  Proofs.Logic.Consequence.Concrete.mlttRoomEntails_iff Γ e

/-- **Soundness of extensional MLTT for the concrete room.** -/
theorem mlttDerives_le_roomEntails : mlttDerives ≤ mlttRoomEntails.{0} :=
  fun Γ e h => (mlttRoomEntails_iff Γ e).2 (mlttDerives_le_entails Γ e h)

end MLTT

end Silmaril.Consequence.Concrete
