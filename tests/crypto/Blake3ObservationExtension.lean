module

import Silmaril.Crypto.Blake3.Range.Extension.Counterexample.Thms

open Silmaril.Crypto.Blake3
open Silmaril.Semantics.Naming
open Silmaril.Semantics.Naming.ByteRange (Fact Observations)

private def finiteBase : Relation Bool Bytes := fun name bytes => name = true ∧ bytes = [9]

private def finiteSeen : Observations Bool := fun name fact =>
  if name then fact = .whole [9] else fact = .range 1 [7] ∨ fact = .eof 3

example : ∃ names, finiteSeen.Model finiteBase names ∧
    (∀ bytes, names true bytes ↔ finiteBase true bytes) ∧ ∃ bytes, names false bytes ∧ bytes.length = 3 := by
  have oldFits : finiteSeen.Fits true [9] := by
    intro fact observed
    obtain rfl : fact = .whole [9] := by simpa [finiteSeen] using observed
    exact Fact.whole_iff.mpr rfl
  have newFits : finiteSeen.Fits false [0, 7, 0] := by
    intro fact observed
    rcases (show fact = .range 1 [7] ∨ fact = .eof 3 by simpa [finiteSeen] using observed) with rfl | rfl
    · exact Fact.range_iff.mpr ⟨[0], [0], rfl, rfl⟩
    · exact Fact.eof_iff.mpr rfl
  have model : ∃ names, finiteSeen.Model finiteBase names := by
    apply Observations.exists_model_iff.mpr
    refine ⟨fun {_ _ _} left right => left.2.trans right.2.symm, ?_, ?_⟩
    · rintro _ _ ⟨rfl, rfl⟩
      exact oldFits
    · intro name _
      cases name
      · exact Observations.exists_fits_iff.mp ⟨_, newFits⟩
      · exact Observations.exists_fits_iff.mp ⟨_, oldFits⟩
  obtain ⟨names, model⟩ := model
  have hit : finiteSeen false (.eof 3) := by simp [finiteSeen]
  obtain ⟨bytes, named, fits⟩ := model.2.2.2 false ⟨_, hit⟩
  exact ⟨names, model, model.preservesFiber (show finiteBase true [9] from ⟨rfl, rfl⟩),
    bytes, named, Fact.eof_iff.mp (fits _ hit)⟩

private def boundedInfinite : Observations Nat := fun name fact =>
  fact = .range name [7] ∨ fact = .eof (name + 2)

example : ∃ names, boundedInfinite.Model (fun _ _ => False) names := by
  apply Observations.exists_model_iff.mpr
  refine ⟨fun {_ _ _} hit _ => hit.elim, fun {_ _} hit => hit.elim, ?_⟩
  intro name _
  apply Observations.exists_fits_iff.mp
  refine ⟨List.replicate name 0 ++ [7] ++ [0], ?_⟩
  rintro _ (rfl | rfl)
  · exact Fact.range_iff.mpr ⟨List.replicate name 0, [0], rfl, by simp⟩
  · exact Fact.eof_iff.mpr (by simp)

private def unbounded : Observations Unit := fun _ fact => ∃ offset, fact = .range offset [0]

example : ¬ ∃ names, unbounded.Model (fun _ _ => False) names := by
  intro model
  have compatible := (Observations.exists_model_iff.mp model).2.2 () ⟨.range 0 [0], 0, rfl⟩
  obtain ⟨bound, all⟩ := compatible.2.1
  have impossible := all (.range bound [0]) ⟨bound, rfl⟩
  exact (Nat.not_succ_le_self bound) impossible

private def sameWhole : Observations Bool := fun _ fact => fact = .whole [7]

example : (∃ names, sameWhole.Model (fun _ _ => False) names) ∧
    ¬ (∃ names, sameWhole.Model (fun _ _ => False) names ∧ UniqueNames names) := by
  constructor
  · apply Observations.exists_model_iff.mpr
    refine ⟨fun {_ _ _} hit _ => hit.elim, fun {_ _} hit => hit.elim, ?_⟩
    intro name _
    apply Observations.exists_fits_iff.mp
    exact ⟨[7], fun _ eq => eq.symm ▸ Fact.whole_iff.mpr rfl⟩
  · rintro ⟨_, model, unique⟩
    obtain ⟨lhs, left, lfit⟩ := model.2.2.2 false ⟨.whole [7], rfl⟩
    obtain ⟨rhs, right, rfit⟩ := model.2.2.2 true ⟨.whole [7], rfl⟩
    have eq := Fact.whole_iff.mp (lfit (.whole [7]) rfl) |>.trans (Fact.whole_iff.mp (rfit (.whole [7]) rfl)).symm
    exact Bool.noConfusion (unique (eq ▸ left) right)

private def blockedSeen (digest : Bytes) : Observations Bytes := fun name fact =>
  name = digest ∧ (fact = .range 1024 [1] ∨ fact = .eof 1025)

example : ∃ base digest, (∃ names, (blockedSeen digest).Model (Named base) names) ∧
    (∀ extension, Compression.Extends base extension → ¬ extension.Collision → ∀ bytes, ¬ Named extension digest bytes) := by
  obtain ⟨run, digest, _, free, checked, eof, impossible⟩ := blocked_opaque_cv
  let base := Compression.graph run
  refine ⟨base, digest, CertifiedAt.model free ?_, impossible⟩
  rintro name ⟨_, rfl, _⟩
  refine ⟨1025, ?_, ?_⟩
  · rintro _ ⟨_, rfl | rfl⟩
    · exact checked
    · exact ⟨rfl, eof⟩
  · intro bytes named
    exact (impossible base (fun {_ _} hit => hit) free bytes named).elim

private def rootInput : Input := chunkInput true true true 0 iv [5]
private def oneRun (input : Input) : Option CV := if input = rootInput then some iv else none
private def oneSeen : Observations Bytes := fun digest fact =>
  digest = digestBytes iv ∧ (fact = .range 0 [5] ∨ fact = .eof 1)

example : ∃ rel : Compression, rel.Canonical ∧ ¬ rel.Collision ∧ rel.Realizes oneSeen := by
  let base : Compression := fun _ _ => False
  let support := fun _ : Bytes => Compression.graph oneRun
  have legal : Named (Compression.graph oneRun) (digestBytes iv) [5] :=
    root_graph.mp (by decide +kernel)
  have onlyInput {input : Input} {output : CV} (hit : Compression.graph oneRun input output) : input = rootInput := by
    change oneRun input = some output at hit
    by_contra ne
    simp [oneRun, ne] at hit
  have family : base.WitnessFamily oneSeen (fun _ => [5]) support := by
    refine ⟨?_, fun _ _ => ⟨fun {_ _ _} hit => hit.elim, fun {_ _ _} hit => hit.elim⟩,
      fun _ _ _ _ => ⟨Compression.graph_canonical oneRun, ?_⟩⟩
    · rintro digest ⟨_, rfl, _⟩
      refine ⟨?_, legal⟩
      rintro _ ⟨_, rfl | rfl⟩
      · exact Fact.range_iff.mpr ⟨[], [], rfl, rfl⟩
      · exact Fact.eof_iff.mpr rfl
    · exact fun {_ _ _} left right => (onlyInput left).trans (onlyInput right).symm
  obtain ⟨_, canonical, free, realized⟩ := family.union (fun {_ _ _} hit => hit.elim)
    (fun ⟨_, _, _, _, hit, _⟩ => hit.elim)
  exact ⟨_, canonical, free, realized⟩

#print axioms Observations.exists_model_iff
#print axioms Observations.exists_unique_model_iff
#print axioms Compression.WitnessFamily.union
#print axioms Compression.exists_extension_iff
#print axioms CertifiedAt.model
#print axioms blocked_opaque_cv
#print axioms conflicting_cross_extent
