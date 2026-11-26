module

import Silmaril.SSA.PEG.Builder
import Silmaril.SSA.Peggy.Optimizer.Cyclic.Thms
import Silmaril.SSA.PEG.Rules.Thms
import Silmaril.SSA.PEG.Semantics.Thms
import Silmaril.SSA.Peggy.Bridge.Figure11.Thms
import Silmaril.SSA.Peggy.EPEG.Saturation.Thms
import Silmaril.SSA.Peggy.EPEG.Selection.Thms
meta import Silmaril.SSA.Peggy.Optimizer.Cyclic.Defs
meta import Silmaril.SSA.Peggy.Bridge.Egg.Defs
meta import Silmaril.SSA.Peggy.Bridge.Figure11.Defs
meta import Silmaril.SSA.Peggy.Acyclic.Defs
meta import Silmaril.SSA.Peggy.EPEG.Defs
meta import Silmaril.SSA.Peggy.EPEG.Saturation.Defs
meta import Silmaril.Logic.Egg.Core.Replay.Defs
meta import Silmaril.SSA.PEG.Builder

namespace Silmaril.SSA.Peggy.Tests

open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Egg
open Core.Replay (Receipt)
open PEG (Ty RawGraph Graph)
open Acyclic (Interpretation Ranked)
open Bridge.Egg

private inductive Op : List (Ty Unit) → Ty Unit → Type where
  | yes : Op [] .bool
  | no : Op [] .bool
  | bottom : Op [] .bool
  | fail : Op [] .count
  | add : Op [.count, .count] .count
  deriving DecidableEq

private abbrev params : List (Ty Unit) := [.bool, .count, .count]
private abbrev results : List (Ty Unit) := [.count, .count, .count, .bool]

/-- The add uses the selected value twice. The first and third outputs share
the add, and the two count parameters occupy distinct input slots. -/
private def sourceWith (control : Op [] .bool) : RawGraph Op params results 7 0 where
  forest := ⟨Fin.elim0⟩
  sort i := if i = 2 ∨ i = 6 then .bool else .count
  node i := match i with
    | 0 => ⟨_, .op .add, [1, 1]⟩
    | 1 => ⟨_, .phi, [2, 3, 4]⟩
    | 2 => ⟨_, .op control, []⟩
    | 3 => ⟨_, .param (.tail .head), []⟩
    | 4 => ⟨_, .op .fail, []⟩
    | 5 => ⟨_, .param (.tail (.tail .head)), []⟩
    | 6 => ⟨_, .param .head, []⟩
  roots := [0, 5, 0, 6]

private abbrev source := sourceWith .yes

private def target : RawGraph Op params results 4 0 where
  forest := ⟨Fin.elim0⟩
  sort i := if i = 3 then .bool else .count
  node i := match i with
    | 0 => ⟨_, .param (.tail .head), []⟩
    | 1 => ⟨_, .op .add, [0, 0]⟩
    | 2 => ⟨_, .param (.tail (.tail .head)), []⟩
    | 3 => ⟨_, .param .head, []⟩
  roots := [1, 2, 1, 3]

private def sourceRank (i : Fin 7) : Nat := match i with
  | 0 => 2 | 1 => 1 | _ => 0

private def targetRank (i : Fin 4) : Nat := if i = 1 then 1 else 0

private def src : Graph Op params results 7 0 := source.check.get (by decide)
private def dst : Graph Op params results 4 0 := target.check.get (by decide)
private def srcRanked : Ranked src := (Ranked.check src sourceRank).get (by decide)
private def dstRanked : Ranked dst := (Ranked.check dst targetRank).get (by decide)

-- A well-typed self-edge still fails fragment admission.
private def cyclic : Graph Op params results 7 0 :=
  ({ source with node := fun i => if i = 0 then { source.node i with args := [0, 1] }
    else source.node i }).check.get (by decide)

example : (Ranked.check cyclic sourceRank).isNone = true := by decide

private abbrev T := Term Op params

private def yes : T .bool := .app (.prim Op.yes) (fun j => j.elim0)
private def no : T .bool := .app (.prim Op.no) (fun j => j.elim0)
private def failed : T .count := .app (.prim Op.fail) (fun j => j.elim0)
private def condition : T .bool := .var 0
private def x : T .count := .var 1
private def y : T .count := .var 2

private def phi (c : T .bool) (a b : T .count) : T .count :=
  .app (.phi .count) (fun i => match i with | 0 => c | 1 => a | 2 => b)

private abbrev selectTrue : Core.Rule (signature Op) where
  scope := params.length
  context := context params
  guards := [⟨.bool, condition, yes⟩]
  conclusion := ⟨.count, phi condition x y, x⟩

private abbrev rules := [selectTrue]
private abbrev Rec := Receipt rules (context params)

private def substitute (i : Fin params.length) : T params[i] :=
  match i with | 0 => yes | 1 => x | 2 => failed

private def select (guardReceipt : Rec .bool) : Rec .count :=
  Receipt.rewrite (rs := rules) 0 substitute (fun j : Fin 1 => match j with | 0 => guardReceipt)

private def receipts (guardReceipt : Rec .bool) (i : Fin results.length) : Rec results[i] :=
  let rewrite := select guardReceipt
  let underAdd : Rec .count :=
    .congr (Symbol.prim Op.add) (fun i => match i with | 0 => rewrite | 1 => rewrite)
  match i with
  | 0 => underAdd
  | 1 => .refl y
  | 2 => .trans underAdd (.refl (.app (.prim Op.add) (fun j => match j with | 0 => x | 1 => x)))
  | 3 => .refl condition

private abbrev opEq : PrimitiveEq Op := fun _ _ => inferInstance

#guard (checkOutputs opEq srcRanked dstRanked (receipts (.refl yes))).isSome
#guard (checkOutputs opEq dstRanked srcRanked (fun i => .symm (receipts (.refl yes) i))).isSome
#guard (checkOutputs opEq srcRanked dstRanked (receipts (.refl no))).isNone
#guard ((Receipt.trans (.refl x) (.refl y) : Rec .count).replay (matchSymbol opEq)).isNone

private def swapped : Graph Op params results 4 0 :=
  ({ target with roots := [2, 1, 1, 3] }).check.get (by decide)

private def swappedRanked : Ranked swapped := (Ranked.check swapped targetRank).get (by decide)

#guard (checkOutputs opEq srcRanked swappedRanked (receipts (.refl yes))).isNone

private def nativeInterp : PEG.Interpretation.{0,0,0} Op where
  carrier _ := Unit
  run
    | .yes, .nil => some ⟨true⟩
    | .no, .nil => some ⟨false⟩
    | .bottom, .nil | .fail, .nil => none
    | .add, .cons a (.cons b .nil) => some ⟨Nat.add a.down b.down⟩

private def interp : Interpretation Op := Bridge.Figure11.toAcyclic nativeInterp

private def input (i : Fin params.length) : interp.Partial params[i] :=
  match i with | 0 => none | 1 => some (7 : Nat) | 2 => some (3 : Nat)

#guard (show Option Nat from srcRanked.evalOutputs interp input 0) == some 14
#guard (show Option Nat from srcRanked.evalOutputs interp input 1) == some 3
#guard (show Option Nat from srcRanked.evalOutputs interp input 2) == some 14
#guard (srcRanked.evalOutputs interp input 3).isNone
#guard (srcRanked.evalOutputs interp (fun _ => none) 0).isNone

private theorem selectTrue_holds : selectTrue.Holds (model interp) := by
  intro ρ guards
  have hc := guards ⟨.bool, condition, yes⟩ (List.mem_singleton_self _)
  change ρ 0 = some true at hc
  change (ρ 0).bind (fun b : Bool => if b then ρ 1 else ρ 2) = ρ 1
  rw [hc]
  rfl

example (accepted : (checkOutputs opEq srcRanked dstRanked (receipts (.refl yes))).isSome) :
    srcRanked.evalOutputs interp input = dstRanked.evalOutputs interp input := by
  apply checkOutputs_sound opEq accepted interp _ input
  intro r hr
  have : r = selectTrue := List.mem_singleton.mp hr
  exact this ▸ selectTrue_holds

private def nativeInputs : RVSDG.Tuple nativeInterp.Value params :=
  .cons ⟨false⟩ (.cons ⟨7⟩ (.cons ⟨3⟩ .nil))

example (accepted : (checkOutputs opEq srcRanked dstRanked (receipts (.refl yes))).isSome) :
    src.observe nativeInterp (src.denote nativeInterp nativeInputs
      (Bridge.Figure11.demandWellFounded srcRanked)) Fin.elim0 =
    dst.observe nativeInterp (dst.denote nativeInterp nativeInputs
      (Bridge.Figure11.demandWellFounded dstRanked)) Fin.elim0 := by
  apply Bridge.Figure11.checkOutputs_figure11_sound opEq accepted nativeInterp
  intro r hr
  have : r = selectTrue := List.mem_singleton.mp hr
  exact this ▸ selectTrue_holds

private def variant (control : Op [] .bool) : Graph Op params results 7 0 :=
  (sourceWith control).check.get (by rfl)

private def variantRanked (control : Op [] .bool) : Ranked (variant control) :=
  (Ranked.check (variant control) sourceRank).get (by rfl)

private noncomputable def variantValues (control : Op [] .bool) :
    (variant control).Valuation nativeInterp :=
  (variant control).denote nativeInterp nativeInputs
    (Bridge.Figure11.demandWellFounded (variantRanked control))

private theorem variantPhi (control : Op [] .bool) :
    variantValues control (1, Fin.elim0) = (nativeInterp.run control .nil).elim none
      (fun flag => if flag.down then some ⟨7⟩ else none) := by
  have step := (variant control).denote_solves nativeInterp nativeInputs
    (Bridge.Figure11.demandWellFounded (variantRanked control))
  have guard : variantValues control (2, Fin.elim0) = nativeInterp.run control .nil :=
    step (2, Fin.elim0)
  have yesArm : variantValues control (3, Fin.elim0) = some ⟨7⟩ := step (3, Fin.elim0)
  have noArm : variantValues control (4, Fin.elim0) = none := step (4, Fin.elim0)
  have eq := step (1, Fin.elim0)
  change variantValues control (1, Fin.elim0) =
    (variantValues control (2, Fin.elim0)).elim none (fun flag => if flag.down
      then variantValues control (3, Fin.elim0) else variantValues control (4, Fin.elim0)) at eq
  rw [guard, yesArm, noArm] at eq
  exact eq

-- The undefined arm is ignored exactly when it is unselected.
example : variantValues .yes (1, Fin.elim0) = some ⟨7⟩ := variantPhi .yes
example : variantValues .no (1, Fin.elim0) = none := variantPhi .no
example : variantValues .bottom (1, Fin.elim0) = none := variantPhi .bottom

-- Equal branch values do not justify dropping an undefined control operand.
private def unsafePhi : Core.Rule (signature Op) :=
  { selectTrue with guards := [], conclusion := ⟨.count, phi condition x x, x⟩ }

example : ¬unsafePhi.Holds (model interp) := by
  intro holds
  have eq := holds input (by intro e he; cases he)
  change (none : Option Nat) = some 7 at eq
  cases eq

end Silmaril.SSA.Peggy.Tests

namespace Silmaril.SSA.Peggy.EPEG.Tests

open PEG Saturation
open RVSDG (Tuple)

private inductive Op : List (Ty Unit) → Ty Unit → Type where
  | zero : Op [] .count
  | one : Op [] .count
  | succ : Op [.count] .count
  | atLeastTwo : Op [.count] .bool

private abbrev Result : List (Ty Unit) := [.count, .count]

/-- Vertices 0 and 1 form a feedback cycle. Vertices 3 and 9 duplicate θ
and pass respectively, and 7 and 8 eval at the two passes. -/
private def table : RawGraph Op [] Result 10 1 where
  forest := ⟨fun _ => none⟩
  sort i := if i = 5 then .bool else .count
  node i := match i with
    | 0 => ⟨_, .theta 0, [2, 1]⟩
    | 1 => ⟨_, .op .succ, [0]⟩
    | 2 => ⟨_, .op .zero, []⟩
    | 3 => ⟨_, .theta 0, [4, 1]⟩
    | 4 => ⟨_, .op .zero, []⟩
    | 5 => ⟨_, .op .atLeastTwo, [0]⟩
    | 6 => ⟨_, .pass 0, [5]⟩
    | 7 => ⟨_, .eval 0, [0, 6]⟩
    | 8 => ⟨_, .eval 0, [3, 9]⟩
    | 9 => ⟨_, .pass 0, [5]⟩
  roots := [0, 7]

private def cyclicSource : Graph Op [] Result 10 1 := table.check.get (by decide)

private def countRef (i : Fin 10) (h : cyclicSource.sort i = .count) :
    Ref cyclicSource.sort .count := ⟨i, h⟩

private def boolRef (i : Fin 10) (h : cyclicSource.sort i = .bool) :
    Ref cyclicSource.sort .bool := ⟨i, h⟩

private def counts (a b : Ref cyclicSource.sort .count) :
    Tuple (Ref cyclicSource.sort) [.count, .count] := .cons a (.cons b .nil)

private def rank : DemandRank 10 1 :=
  [.phase fun i => match i with
      | 0 | 1 | 2 | 3 | 4 => 0
      | 5 => 1
      | 6 | 9 => 2
      | _ => 3,
   .counter 0,
   .phase fun i => match i with | 0 | 3 => 1 | 1 => 2 | _ => 0]

private theorem sourceWF : WellFounded cyclicSource.Demand :=
  cyclicSource.demandWellFounded_of_check rank (by decide)

example : cyclicSource.Edge 0 (.feedback 0) 1 ∧ cyclicSource.Edge 1 .ordinary 0 :=
  ⟨⟨⟨1, by decide⟩, rfl, rfl⟩, ⟨⟨0, by decide⟩, rfl, rfl⟩⟩

private def arithmetic : PEG.Interpretation.{0,0,0} Op where
  carrier _ := Unit
  run
    | .zero, .nil => some ⟨0⟩
    | .one, .nil => some ⟨1⟩
    | .succ, .cons k .nil => some ⟨k.down + 1⟩
    | .atLeastTwo, .cons k .nil => some ⟨decide (2 ≤ k.down)⟩

private noncomputable def streams := cyclicSource.denote arithmetic .nil sourceWF

private theorem sourceSolves : cyclicSource.Solves arithmetic .nil streams :=
  cyclicSource.denote_solves arithmetic .nil sourceWF

private def zeros : MatchingNodes cyclicSource 2 4 :=
  ⟨[], .count, .op .zero, .nil, .nil, rfl, rfl, HEq.rfl, HEq.rfl⟩

private abbrev thetas : MatchingNodes cyclicSource 0 3 :=
  ⟨[.count, .count], .count, .theta 0,
    counts (countRef 2 rfl) (countRef 1 rfl), counts (countRef 4 rfl) (countRef 1 rfl),
    rfl, rfl, HEq.rfl, HEq.rfl⟩

private def passes : MatchingNodes cyclicSource 6 9 :=
  ⟨[.bool], .count, .pass 0,
    .cons (boolRef 5 rfl) .nil, .cons (boolRef 5 rfl) .nil, rfl, rfl, HEq.rfl, HEq.rfl⟩

private def evals : MatchingNodes cyclicSource 7 8 :=
  ⟨[.count, .count], .count, .eval 0,
    counts (countRef 0 rfl) (countRef 6 rfl), counts (countRef 3 rfl) (countRef 9 rfl),
    rfl, rfl, HEq.rfl, HEq.rfl⟩

private def seed : Equation cyclicSource := ⟨2, 4, rfl⟩

private def thetaRule : GuardedEquation cyclicSource := ⟨[seed], ⟨0, 3, rfl⟩⟩

private theorem thetaLaw : thetaRule.Holds streams := by
  intro guards
  apply thetas.streamEq sourceSolves
  intro k
  match k with
  | 0 => exact guards seed (List.mem_singleton_self _)
  | 1 => exact ⟨rfl, fun _ => HEq.rfl⟩

private def discrete : Classes 10 := Classes.discrete

-- Eval and θ are initially blocked. Passing over them must keep them eligible.
private def obligations : List (Obligation cyclicSource) :=
  [.congruent evals, .guarded thetaRule, .congruent passes, .congruent zeros]

private theorem contracts : ∀ o ∈ obligations, o.Holds streams := by
  intro o mem
  simp only [obligations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with eq | eq | eq | eq
  · subst o; trivial
  · subst o; exact thetaLaw
  · subst o; trivial
  · subst o; trivial

private def classes := saturate obligations discrete
private def limited := run 2 obligations discrete
private def reversed := saturate obligations.reverse discrete

example : thetaRule.check discrete = false := by decide
example : evals.checkOperands (discrete.merge 2 4) = false := by decide
example : limited 6 = limited 9 ∧ limited 7 ≠ limited 8 := by decide
example : isClosed obligations limited = false := by decide
example : isClosed obligations classes = true ∧ classes 7 = classes 8 := by decide

#guard (List.finRange 10).all (fun a => (List.finRange 10).all fun b =>
  (classes a == classes b) == (reversed a == reversed b))

example (a b : Fin 10) : classes a = classes b ↔ reversed a = reversed b :=
  saturate_perm (List.reverse_perm obligations).symm discrete a b

example : limited.Valid streams :=
  run_sound 2 obligations sourceSolves Classes.discrete_valid contracts

private theorem classesValid : classes.Valid streams :=
  run_sound obligations.length obligations (c := discrete) sourceSolves Classes.discrete_valid contracts

private def cyclicTarget : Graph Op [] Result 10 1 :=
  cyclicSource.withRoots (counts (countRef 3 rfl) (countRef 8 rfl))

private def selection : Selection cyclicSource cyclicTarget :=
  ⟨fun v => .ofId cyclicSource.sort v, rank⟩

example (idx : Index 1) :
    cyclicSource.observe arithmetic streams idx =
      cyclicTarget.observe arithmetic
        (cyclicTarget.denote arithmetic .nil
          (selection.demandWellFounded (classes := classes) (by decide))) idx :=
  run_selection_sound obligations.length obligations (c := discrete) (m := arithmetic) (env := .nil)
    selection sourceWF Classes.discrete_valid contracts (by decide) sourceSolves idx

/-- Now the increment reads vertex 3 instead of vertex 0. Together with
vertex 3's θ feedback, this gives the candidate a different cycle. -/
private def redirectedNode (v : Fin 10) :
    Node Op [] (Fin 1) cyclicSource.sort (cyclicSource.sort v) :=
  if h : v = 1 then
    h.symm ▸ Node.ofLabel (.op Op.succ) (.cons (countRef 3 rfl) .nil)
  else cyclicSource.node v

private def redirectedTarget : Graph Op [] Result 10 1 :=
  { cyclicTarget with node := redirectedNode }

private def redirectedSelection : Selection cyclicSource redirectedTarget :=
  ⟨fun v => .ofId cyclicSource.sort v, rank⟩

private def redirectedRows (v : Fin 10) : Selection.Row redirectedSelection v := by
  by_cases h : v = 1
  · subst v
    exact ⟨[.count], .op Op.succ, .cons (countRef 0 rfl) .nil, .cons (countRef 3 rfl) .nil,
      HEq.rfl, rfl⟩
  · let row := cyclicSource.node v
    exact ⟨row.inputs, row.label, row.args, row.args, HEq.rfl,
      by
        change redirectedNode v = Node.ofLabel row.label row.args
        rw [redirectedNode, dite_eq_right h]
        rfl⟩

example : redirectedTarget.Edge 3 (.feedback 0) 1 ∧ redirectedTarget.Edge 1 .ordinary 3 :=
  ⟨⟨⟨1, by decide⟩, rfl, rfl⟩, ⟨⟨0, by decide⟩, rfl, rfl⟩⟩

example : Selection.checkRows redirectedRows limited = false := by decide

example (idx : Index 1) :
    cyclicSource.observe arithmetic streams idx =
      redirectedTarget.observe arithmetic
        (redirectedTarget.denote arithmetic .nil
          (redirectedSelection.demandWellFounded (classes := classes) (by decide))) idx :=
  Selection.observe_sound_of_rows (m := arithmetic) (env := .nil) sourceWF classesValid
    (by decide) redirectedRows (by decide) idx

/-- Putting θ in its own initial slot preserves wiring types but violates
demand admission at index zero. -/
private def cyclicInitializer : Graph Op [] Result 10 1 :=
  ({ table with
    node := fun i => if i = 3 then { table.node i with args := [3, 1] } else table.node i
    roots := [3, 8] }).check.get (by decide)

private def badRank : Selection cyclicSource cyclicInitializer :=
  ⟨fun v => .ofId cyclicSource.sort v, rank⟩

example : badRank.check classes = false := by decide

/-- This candidate passes the rank and class-of-root checks, but the
representatives would assign zero to a vertex that now denotes one. -/
private def changedInitializer : Graph Op [] Result 10 1 :=
  ({ table with
    node := fun i => match i with
      | 2 => ⟨[], .op Op.one, []⟩
      | i => table.node i
    roots := [3, 8] }).check.get (by decide)

private def wrong : Selection cyclicSource changedInitializer :=
  ⟨fun v => .ofId cyclicSource.sort v, rank⟩

example : wrong.check classes = true := by decide

example : ¬changedInitializer.Solves arithmetic .nil (wrong.inherit streams) := by
  intro solves
  let idx : Index 1 := fun _ => 0
  have eq := solves (2, idx)
  change streams (2, idx) = some ⟨1⟩ at eq
  have zero : streams (2, idx) = some ⟨0⟩ := sourceSolves (2, idx)
  rw [zero] at eq
  cases eq

end Silmaril.SSA.Peggy.EPEG.Tests

namespace Silmaril.SSA.Peggy.Optimizer.Cyclic.Tests

open PEG
open RVSDG (Tuple)

private inductive Op : List (Ty Unit) → Ty Unit → Type where
  | zero : Op [] .count
  | bad : Op [] .count
  | succ : Op [.count] .count
  | add : Op [.count, .count] .count

private inductive Seed where
  | parameter
  | bottom
  | changing

private def Seed.address : Seed → Fin 7
  | .parameter => 3
  | .bottom => 6
  | .changing => 0

private abbrev params : List (Ty Unit) := [.count]
private abbrev results : List (Ty Unit) := [.count, .count, .count, .count]

/-- The live counter has θ/succ feedback. A second θ self-feeds its
initializer, is referenced by the add, and occurs twice at the boundary. -/
private abbrev countSort (_ : Fin 7) : Ty Unit := .count

private def countRef (i : Fin 7) : Ref countSort .count := ⟨i, rfl⟩

private def pair (a b : Fin 7) : Tuple (Ref countSort) [.count, .count] :=
  .cons (countRef a) (.cons (countRef b) .nil)

private def graph (seed : Seed) : Graph Op params results 7 1 where
  forest := ⟨fun _ => none⟩
  sort := countSort
  node i := match i with
    | 0 => .ofLabel (.theta 0) (pair 2 1)
    | 1 => .ofLabel (.op .succ) (.cons (countRef 0) .nil)
    | 2 => .ofLabel (.op .zero) .nil
    | 3 => .ofLabel (.param .head) .nil
    | 4 => .ofLabel (.theta 0) (pair seed.address 4)
    | 5 => .ofLabel (.op .add) (pair 4 0)
    | 6 => .ofLabel (.op .bad) .nil
  roots := .cons (countRef 4) (.cons (countRef 5) (pair 0 4))

private def nodeCount {n : Nat} (_ : Graph Op params results n 1) : Nat := n

private def optimizedRoots (seed : Seed) : Option (Nat × Nat × List Nat) :=
  (optimize (graph seed)).map fun result =>
    (result.site.val, nodeCount result.matched.extract, refNumbers result.matched.extract.roots)

#guard (optimize (graph .parameter)).isSome
#guard optimizedRoots .parameter == some (4, 6, [3, 4, 0, 3])
#guard optimizedRoots .bottom == some (4, 6, [5, 4, 0, 5])
#guard (admit (graph .changing)).isSome
#guard (matchAt (graph .changing) (show Fin 7 from 4)).isNone
#guard (optimize (graph .changing)).isNone

private def compactedEdges : Bool :=
  match optimize (graph .parameter) with
  | none => false
  | some result =>
    let target := result.matched.extract
    (target.node 0).label.thetaLoop == some 0 &&
      refNumbers (target.node 0).args == [2, 1] && refNumbers (target.node 1).args == [0] &&
      refNumbers (target.node 4).args == [3, 0]

#guard compactedEdges

private def arithmetic : Interpretation.{0,0,0} Op where
  carrier _ := Unit
  run
    | .zero, .nil => some ⟨0⟩
    | .bad, .nil => none
    | .succ, .cons a .nil => some ⟨a.down + 1⟩
    | .add, .cons a (.cons b .nil) => some ⟨a.down + b.down⟩

private def input : Tuple arithmetic.Value params := .cons ⟨7⟩ .nil
private def clock (k : Nat) : Index 1 := fun _ => k

private def admitted (seed : Seed) : Admission (graph seed) :=
  (admit (graph seed)).get (by cases seed <;> decide)

private noncomputable def streams (seed : Seed) : (graph seed).Valuation arithmetic :=
  (graph seed).denote arithmetic input (admitted seed).demandWellFounded

private theorem equations (seed : Seed) : (graph seed).Solves arithmetic input (streams seed) :=
  (graph seed).denote_solves arithmetic input (admitted seed).demandWellFounded

private theorem previous : (clock 1).set 0 0 = clock 0 := by
  funext loop
  have h : loop = 0 := Subsingleton.elim _ _
  subst loop
  rfl

private theorem counterZero (seed : Seed) : streams seed (0, clock 0) = some ⟨0⟩ := by
  have init : streams seed (2, clock 0) = some ⟨0⟩ := equations seed (2, clock 0)
  exact (equations seed (0, clock 0)).trans init

private def ref (seed : Seed) (i : Fin 7) : Ref (graph seed).sort .count := ⟨i, rfl⟩

private theorem counterOne (seed : Seed) : streams seed (0, clock 1) = some ⟨1⟩ := by
  have count := equations seed (0, clock 1)
  change streams seed (0, clock 1) = streams seed (1, (clock 1).set 0 0) at count
  have step := Rules.unary_at (equations seed) (r := ref seed 1) (arg := ref seed 0)
    (op := Op.succ) HEq.rfl (clock 0)
  change streams seed (1, clock 0) =
    (streams seed (0, clock 0)).bind (fun x => some ⟨x.down + 1⟩) at step
  rw [counterZero] at step
  exact count.trans (previous ▸ step)

private theorem selfStep (seed : Seed) :
    streams seed (4, clock 1) = streams seed (4, clock 0) := by
  have eq := equations seed (4, clock 1)
  change streams seed (4, clock 1) = streams seed (4, (clock 1).set 0 0) at eq
  rwa [previous] at eq

-- The near miss retains zero while its initializer has advanced to one.
example : streams .changing (4, clock 1) ≠ streams .changing (0, clock 1) := by
  have zero : streams .changing (4, clock 0) = streams .changing (0, clock 0) :=
    equations .changing (4, clock 0)
  rw [selfStep, zero, counterZero, counterOne]
  intro impossible
  exact Nat.noConfusion (congrArg ULift.down (Option.some.inj impossible))

example : streams .bottom (4, clock 1) = none := by
  have bad : streams .bottom (6, clock 0) = none := equations .bottom (6, clock 0)
  have init : streams .bottom (4, clock 0) = streams .bottom (6, clock 0) :=
    equations .bottom (4, clock 0)
  exact (selfStep .bottom).trans (init.trans bad)

end Silmaril.SSA.Peggy.Optimizer.Cyclic.Tests
