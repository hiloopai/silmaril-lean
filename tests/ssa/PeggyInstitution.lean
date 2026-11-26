module

import Silmaril.SSA.Peggy.Institution.Family.Defs

namespace Silmaril.SSA.Peggy.Institution.Tests

open CategoryTheory
open Dialect
open PEG (EdgeKind Graph Index LoopForest Ref Ty Walk)
open RVSDG (Tuple)

private inductive SourceOp : List (Ty Unit) → Ty Unit → Type where
  | step : SourceOp [.count] .count

private inductive TargetOp : List (Ty Unit) → Ty Unit → Type where
  | stop : TargetOp [.count] .count
  | copy : TargetOp [.count] .count

private def source : FixedSortSignature Unit := ⟨SourceOp⟩
private def target : FixedSortSignature Unit := ⟨TargetOp⟩

private def rename : source ⟶ target := FixedSortSignature.ofOpcodeMap fun
  | .step => .stop

private def identify : target ⟶ source := FixedSortSignature.ofOpcodeMap fun
  | .stop | .copy => .step

private def model : Model.{0,0,0} target where
  carrier _ := Unit
  run
    | .stop, _ => none
    | .copy, input => some (input.get .head)

private def frame : LoopForest 1 := ⟨fun _ => none⟩
private def sorts : Fin 3 → Ty Unit := fun _ => .count
private def ref (i : Fin 3) : Ref sorts .count := Ref.ofId sorts i

private def orderedRoots (a b : Fin 3) : Tuple (Ref sorts) [.count, .count] :=
  .cons (ref a) (.cons (ref b) .nil)

/-- The seed initializes theta, whose value flows through `step` on its feedback path. -/
private def recurrence : Graph SourceOp [.count] [.count, .count] 3 1 where
  forest := frame
  sort := sorts
  node i := match i with
    | 0 => .ofLabel (.param .head) .nil
    | 1 => .ofLabel (.theta 0) (orderedRoots 0 2)
    | 2 => .ofLabel (.op .step) (.cons (ref 1) .nil)
  roots := orderedRoots 0 1

private theorem edgeFacts {a b : Fin 3} {k : EdgeKind (Fin 1)} (h : recurrence.Edge a k b) :
    (¬ k.IsFeedback → b.val < a.val) ∧ ∀ l, ¬ k.IsObserverAt l := by
  have localFacts : ∀ (a : Fin 3) (i : Fin (recurrence.node a).inputs.length),
      let k := (recurrence.node a).label.kind i
      let b := (recurrence.node a).arg i
      (¬ k.IsFeedback → b.id.val < a.val) ∧ ∀ l, ¬ k.IsObserverAt l := by
    unfold EdgeKind.IsObserverAt
    decide
  obtain ⟨i, rfl, rfl⟩ := h
  exact localFacts a i

private theorem noObserver {a b : Fin 3} {ks : List (EdgeKind (Fin 1))}
    (walk : Walk recurrence.Edge a ks b) : ∀ k ∈ ks, ∀ l, ¬ k.IsObserverAt l := by
  induction walk with
  | nil => simp
  | cons edge _ ih =>
    intro k hk l
    rcases List.mem_cons.mp hk with rfl | tail
    · exact (edgeFacts edge).2 l
    · exact ih k tail l

private theorem admitted : recurrence.WellFormed where
  forest := by
    intro i
    rintro ⟨ks, walk, nonempty⟩
    cases walk with
    | nil => exact nonempty rfl
    | cons edge _ => cases edge
  feedback := by
    intro a ks walk nonempty
    by_contra absent
    exact (Nat.lt_irrefl a.val) (walk.strictRank nonempty Fin.val
      (fun e hk => (edgeFacts e).1 (fun h => absent ⟨_, hk, h⟩)))
  loopScope := by
    intro a b ks start target walk ha hb
    have same : target = start := Subsingleton.elim _ _
    subst target
    exact .inl ⟨[], .nil start⟩
  outerFeedback := fun _ _ walk k hk l observer => (noObserver walk k hk l observer).elim

private abbrev sentence : Equation source where
  params := [.count]
  results := [.count, .count]
  loops := 1
  forest := frame
  leftNodes := 3
  rightNodes := 3
  lhs := ⟨recurrence, rfl, admitted⟩
  rhs := ⟨recurrence.withRoots (orderedRoots 1 0), rfl,
    (recurrence.wellFormed_withRoots (orderedRoots 1 0)).2 admitted⟩

private abbrev peggy := inst.{0,0,0} Unit
private def input : Tuple model.Value [.count] := .cons ⟨7⟩ .nil
private def clock (k : Nat) : Index 1 := fun _ => k

private def resultPair (a b : Option (model.Value .count)) :
    Tuple (fun ty => Option (model.Value ty)) [.count, .count] :=
  .cons a (.cons b .nil)

private noncomputable def values : recurrence.Valuation (reduct rename model) :=
  sentence.lhs.denote (reduct rename model) input

private theorem solves : recurrence.Solves (reduct rename model) input values :=
  recurrence.denote_solves (reduct rename model) input (recurrence.demandWellFounded admitted)

private theorem thetaAtZero : values (1, clock 0) = some ⟨7⟩ :=
  (solves (1, clock 0)).trans (solves (0, clock 0))

private theorem thetaAtOne : values (1, clock 1) = none := by
  have stop := solves (2, (clock 1).set 0 0)
  change values (2, (clock 1).set 0 0) =
    (PEG.collect (F := (reduct rename model).Value) [.count] _).elim none
      ((reduct rename model).run SourceOp.step) at stop
  have abort (args : Option (Tuple model.Value [.count])) :
      args.elim none ((reduct rename model).run SourceOp.step) = none := by
    cases args <;> rfl
  exact (solves (1, clock 1)).trans (stop.trans (abort _))

example : (sentence.map rename).lhs.denote model input (⟨1, by decide⟩, clock 1) = none := by
  change (sentence.lhs.map (FixedSortSignature.opcodeMap rename)).denote model input _ = none
  rw [OpenGraph.denote_map]
  exact thetaAtOne

-- Both sides coincide at the initial index.
example : (sentence.map rename).lhs.observe model input (clock 0) =
    (sentence.map rename).rhs.observe model input (clock 0) := by
  change (sentence.lhs.map (FixedSortSignature.opcodeMap rename)).observe model input (clock 0) =
    (sentence.rhs.map (FixedSortSignature.opcodeMap rename)).observe model input (clock 0)
  simp only [OpenGraph.observe_map]
  change resultPair (values (0, clock 0)) (values (1, clock 0)) =
    resultPair (values (1, clock 0)) (values (0, clock 0))
  rw [thetaAtZero, show values (0, clock 0) = some ⟨7⟩ from solves (0, clock 0)]
  rfl

-- At the next index the first root remains defined and the feedback root is bottom.
example : (sentence.map rename).lhs.observe model input (clock 1) =
    resultPair (some ⟨7⟩) none := by
  change (sentence.lhs.map (FixedSortSignature.opcodeMap rename)).observe model input (clock 1) = _
  rw [OpenGraph.observe_map]
  change resultPair (values (0, clock 1)) (values (1, clock 1)) = _
  rw [thetaAtOne, show values (0, clock 1) = some ⟨7⟩ from solves (0, clock 1)]
  rfl

example : peggy.Sat model (peggy.map rename sentence) ↔
    peggy.Sat (peggy.reduct rename model) sentence :=
  Silmaril.Logic.Institution.satisfaction_condition peggy.I rename model sentence

example : ¬ peggy.Sat model (peggy.map rename sentence) := by
  intro holds
  have sourceHolds := (Equation.holds_map rename model sentence).1 holds
  have equal := sourceHolds input (clock 1)
  change resultPair (values (0, clock 1)) (values (1, clock 1)) =
    resultPair (values (1, clock 1)) (values (0, clock 1)) at equal
  rw [thetaAtOne, show values (0, clock 1) = some ⟨7⟩ from solves (0, clock 1)] at equal
  have head := congrArg (fun roots : Tuple (fun ty => Option (model.Value ty)) [.count, .count] =>
    roots.get .head) equal
  cases head

example : ((modelFunctor.{0,0,0} Unit).map rename.op).toFunctor.obj model = reduct rename model :=
  modelFunctor_map_obj rename model

example : (peggy.I.map (𝟙 source)).mod = 𝟭 _ := reductFunctor_id source

example : (peggy.I.map (rename ≫ identify)).mod =
    (peggy.I.map identify).mod ⋙ (peggy.I.map rename).mod :=
  reductFunctor_comp rename identify

private abbrev Names := Silmaril.Inst.Disc Unit
private def sourceFamily : Names ⥤ FixedSortSignature Unit := (Functor.const Names).obj source
private def targetFamily : Names ⥤ FixedSortSignature Unit := (Functor.const Names).obj target

private def renameFamily : sourceFamily ⟶ targetFamily where
  app _ := rename
  naturality _ _ _ := by simp [sourceFamily, targetFamily]

private def changeFamily := familyChange.{0,0,0,0,0} renameFamily

example : (changeFamily.ρ.app ()).sen sentence = sentence.map rename := rfl
example : (changeFamily.ρ.app ()).mod.obj model = reduct rename model := rfl

end Silmaril.SSA.Peggy.Institution.Tests
