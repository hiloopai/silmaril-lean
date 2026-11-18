module

public import Silmaril.Logic.Consequence.Derivation.Defs
public import Silmaril.Logic.Consequence.Soundness.Thms
public import Silmaril.Logic.Consequence.Structural.Defs
import Silmaril.Proofs.Logic.Consequence.Derivation.Basic

/-!
# Derivation systems: the checker, soundness, and the consequence system

* `check_iff`, `checkLines_iff`: the Boolean checkers decide validity of trees and lines exactly.
* `derives_closed`: `D.derives` is a Tarski consequence (identity, weakening along `⊆`, multi-cut
  by grafting proofs onto assumption leaves), for every derivation system.
* `linearDerives_eq`: indexed lines and proof trees derive the same judgments (`ProofTree.lines`
  flattens a tree; lines rebuild trees).
* `derives_soundFor`: a locally sound system is sound for `listSat M sat`;
  `consistentWrt_of_locallySound` gives consistency from a model in which the falsity fails.
* `derives_of_elaborate`: an elaborated, checked raw proof derives its conclusion; the
  elaboration function is untrusted.
* `Hom.valid`, `Hom.derives`, `Hom.translation`: a morphism of derivation systems translates proof
  trees, preserving validity, so it is a translation of the consequence systems.
-/

@[expose] public section

namespace Silmaril.Consequence.DerivationSystem

open Silmaril.Proofs.Logic.Consequence.Derivation

universe u v w

variable {J : Type u} {D : DerivationSystem.{u, v} J}

/-- **The tree checker decides validity.** -/
theorem check_iff [DecidableEq J] [∀ r ps c, Decidable (D.Instance r ps c)] {Γ : List J}
    {t : D.Proof} : D.check Γ t = true ↔ D.Valid Γ t :=
  Proofs.Logic.Consequence.Derivation.check_iff Γ t

/-- **The line checker decides validity.** -/
theorem checkLines_iff [DecidableEq J] [∀ r ps c, Decidable (D.Instance r ps c)] {Γ prev : List J}
    {ls : List (Line D.Rule J)} : D.checkLines Γ prev ls = true ↔ D.LinesValid Γ prev ls :=
  Proofs.Logic.Consequence.Derivation.checkLines_iff Γ prev ls

/-- A checked tree derives its conclusion. -/
theorem derives_of_check [DecidableEq J] [∀ r ps c, Decidable (D.Instance r ps c)] {Γ : List J}
    {t : D.Proof} (h : D.check Γ t = true) : D.derives Γ t.concl :=
  ⟨t, check_iff.1 h, rfl⟩

/-- Derivable premises have valid proof trees, one per premise. -/
theorem exists_trees {Γ : List J} {ps : List J} (h : ∀ p ∈ ps, D.derives Γ p) :
    ∃ ts : List D.Proof, (∀ t ∈ ts, D.Valid Γ t) ∧ ts.map ProofTree.concl = ps :=
  exists_proofs h

/-- **Derivability is a Tarski consequence**: identity, weakening along `⊆` and multi-cut. -/
theorem derives_closed : Structural.Closed Structural.tarskiRules D.derives :=
  Proofs.Logic.Consequence.Derivation.derives_closed

/-- **Indexed lines and proof trees derive the same judgments.** -/
theorem linearDerives_eq : D.linearDerives = D.derives :=
  le_antisymm linearDerives_le derives_le_linear

/-- A valid tree flattens to valid lines ending with its conclusion. -/
theorem lines_valid {Γ : List J} {t : D.Proof} (h : D.Valid Γ t) :
    D.LinesValid Γ [] (t.lines 0) ∧ ((t.lines 0).getLast?).map Line.concl = some t.concl :=
  lines_spec t [] h

/-- **Soundness from local soundness.** -/
theorem derives_soundFor {M : Type w} {sat : M → J → Prop} (hD : D.LocallySound sat) :
    D.derives.SoundFor (listSat M sat) :=
  fun _ _ ⟨_, ht, hc⟩ m hΓ => hc ▸ Valid.sound hD m hΓ ht

/-- **Consistency from a model**: a locally sound system does not derive `ff` from a context
satisfied by a model in which `ff` fails. -/
theorem consistentWrt_of_locallySound {M : Type w} {sat : M → J → Prop}
    (hD : D.LocallySound sat) {Γ : List J} {ff : J} (m : M) (hΓ : ∀ j ∈ Γ, sat m j)
    (hff : ¬ sat m ff) : D.derives.ConsistentWrt ff Γ :=
  consistentWrt_of_sound (I := listSat M sat) (derives_soundFor hD) m hΓ hff

/-- **Elaborated raw proofs**: if the untrusted elaboration succeeds and its output checks, the raw
proof's conclusion is derived. -/
theorem derives_of_elaborate [DecidableEq J] [∀ r ps c, Decidable (D.Instance r ps c)]
    {R : Type w} {f : R → List J → J → Option D.Rule} {Γ : List J} {t : ProofTree R J}
    {t' : D.Proof} (he : ProofTree.elaborate f t = some t') (hc : D.check Γ t' = true) :
    D.derives Γ t.concl :=
  elaborate_concl f he ▸ derives_of_check hc

/-- **Elaborated raw lines**: if the untrusted elaboration succeeds and its output checks, the
last raw line's conclusion is derived. -/
theorem derives_of_elaborateLines [DecidableEq J] [∀ r ps c, Decidable (D.Instance r ps c)]
    {R : Type w} {f : R → List J → J → Option D.Rule} {Γ : List J} {ls : List (Line R J)}
    {ls' : List (Line D.Rule J)} {c : J} (he : Line.elaborate f [] ls = some ls')
    (hc : D.checkLines Γ [] ls' = true) (hlast : (ls.getLast?).map Line.concl = some c) :
    D.derives Γ c := by
  rw [← linearDerives_eq]
  refine ⟨ls', checkLines_iff.1 hc, ?_⟩
  rw [← List.getLast?_map, elaborateLines_concl f he, List.getLast?_map, hlast]

/-! ## Morphisms -/

section Hom

variable {K : Type w} {E : DerivationSystem.{w, v} K}

/-- **A morphism preserves validity of proof trees.** -/
theorem Hom.valid (h : Hom D E) {Γ : List J} {t : D.Proof} (ht : D.Valid Γ t) :
    E.Valid (Γ.map h.f) (h.mapTree t) :=
  Proofs.Logic.Consequence.Derivation.Hom.valid h ht

/-- **A morphism transports derivability.** -/
theorem Hom.derives (h : Hom D E) {Γ : List J} {c : J} (hd : D.derives Γ c) :
    E.derives (Γ.map h.f) (h.f c) := by
  obtain ⟨t, ht, rfl⟩ := hd
  exact ⟨h.mapTree t, h.valid ht, Proofs.Logic.Consequence.Derivation.mapTree_concl h t⟩

/-- **A morphism of derivation systems is a translation of their consequence systems.** -/
def Hom.translation (h : Hom D E) : Translation D.derives E.derives :=
  ⟨List.map h.f, h.f, fun _ _ hd => h.derives hd⟩

end Hom

end Silmaril.Consequence.DerivationSystem
