module

public import Silmaril.Games.Inst.Defs
public import Silmaril.Games.DivComp.Thms
public import Silmaril.Games.DivLTS.Thms
import Silmaril.Proofs.Games.Inst.Basic

/-!
# Instantiation phases: theorems

* **Instantiation outcomes of `ofInst S`**, read off the instantiation run of
  `S` (before any import call): success (`ofInst_instReady_iff`), failure
  with outcome `r` (`ofInst_instFails_iff`), divergence
  (`ofInst_instDiverges_iff`).
* **Linking instantiates the provider first**: provider failure is reported
  by the linked component (`link_instFails`), provider divergence during
  instantiation makes the linked component diverge (`link_instDiverges`),
  and a ready provider followed by a successful consumer instantiation makes
  the linked component ready (`link_instReady`).
* Linking is composition, so it is monotone in the provider and in the
  consumer (`link_mono_left`, `link_mono_right`, `link_mono_of_divSimulation`)
  and linking above copycat is the consumer alone (`id_link`).

Proofs are in `Silmaril.Proofs.Games.Inst.Basic`.
-/

public section

namespace Silmaril.Games.DStrategy

open Silmaril.Proofs.Games.Inst

universe u

variable {X E F : Sig.{u}} {R : Type u}

/-- The finite plays of `ofInst S` are those of the transition system of `S`. -/
@[simp] theorem forget_ofInst (S : InstSystem E F R) :
    (ofInst S).forget = Strategy.ofLTS S.toLTS := rfl

/-- **Instantiation succeeds** iff the instantiation run can reach a ready
configuration silently. -/
theorem ofInst_instReady_iff {S : InstSystem E F R} :
    (ofInst S).InstReady ↔
      ∃ c st, Relation.ReflTransGen S.istep S.istart c ∧ S.iready c st := by
  rw [InstReady, OfInst.mem_inst_iff, OfInst.traces_inst_iff]
  constructor
  · rintro ⟨c, hc, ⟨-, st, h⟩ | ⟨r, h, -⟩⟩
    · exact ⟨c, st, hc, h⟩
    · cases h
  · rintro ⟨c, st, hc, h⟩
    exact ⟨c, hc, .inl ⟨rfl, st, h⟩⟩

/-- **Instantiation fails with `r`** iff the instantiation run can reach a
configuration failing with `r` silently. -/
theorem ofInst_instFails_iff {S : InstSystem E F R} {r : R} :
    (ofInst S).InstFails r ↔ ∃ c, Relation.ReflTransGen S.istep S.istart c ∧ S.ifail c r := by
  rw [InstFails, OfInst.mem_inst_iff, OfInst.traces_inst_iff]
  constructor
  · rintro ⟨c, hc, ⟨h, -⟩ | ⟨r', h, h'⟩⟩
    · cases h
    · cases h; exact ⟨c, hc, h'⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, .inr ⟨r, rfl, h⟩⟩

/-- **Instantiation diverges** iff the instantiation run has an infinite
sequence of internal steps. -/
theorem ofInst_instDiverges_iff {S : InstSystem E F R} :
    (ofInst S).InstDiverges ↔ Silmaril.InfiniteTrace S.istep S.istart :=
  OfInst.instDiverges_iff

/-- **Linking reports provider failure.** -/
theorem link_instFails {δ : DStrategy X (E.withInst R)} {S : InstSystem E F R} {r : R}
    (h : δ.InstFails r) : (δ.link S).InstFails r :=
  Link.link_instFails h

/-- **Linking diverges when the provider's instantiation does.** -/
theorem link_instDiverges {δ : DStrategy X (E.withInst R)} {S : InstSystem E F R}
    (h : δ.InstDiverges) : (δ.link S).InstDiverges :=
  Link.link_instDiverges h

/-- **Linking instantiates the provider, then the consumer.** -/
theorem link_instReady {δ : DStrategy X (E.withInst R)} {S : InstSystem E F R}
    (h : δ.InstReady) {c : S.IConf} {st : S.State}
    (hc : Relation.ReflTransGen S.istep S.istart c) (hr : S.iready c st) :
    (δ.link S).InstReady :=
  Link.link_instReady h hc hr

/-- Linking is monotone in the provider. -/
theorem link_mono_left {δ δ' : DStrategy X (E.withInst R)} (h : δ ≤ δ') (S : InstSystem E F R) :
    δ.link S ≤ δ'.link S :=
  comp_mono_left h _

/-- Linking is monotone in the consumer. -/
theorem link_mono_right (δ : DStrategy X (E.withInst R)) {S S' : InstSystem E F R}
    (h : ofLTS S.consumerLTS ≤ ofLTS S'.consumerLTS) : δ.link S ≤ δ.link S' :=
  comp_mono_right δ h

/-- A divergence-sensitive simulation of consumers refines linking. -/
theorem link_mono_of_divSimulation (δ : DStrategy X (E.withInst R)) {S S' : InstSystem E F R}
    (h : LTS.DivSimulation S.consumerLTS S'.consumerLTS) : δ.link S ≤ δ.link S' :=
  link_mono_right δ h.ofLTS_le

/-- Linking above copycat is the consumer alone. -/
theorem id_link (S : InstSystem E F R) :
    (DStrategy.id (E.withInst R)).link S = ofLTS S.consumerLTS :=
  id_comp _

end Silmaril.Games.DStrategy
