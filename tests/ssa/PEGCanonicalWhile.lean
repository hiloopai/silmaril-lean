module

import Silmaril.SSA.PEG.Simple.Revert.While.Thms
import Silmaril.SSA.PEG.Simple.Revert.While.Region.Placement.Thms
import Silmaril.SSA.PEG.Simple.Revert.While.Region.Placement.MustEval.Thms
import Silmaril.SSA.PEG.Simple.Revert.While.Pair.Thms
import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Projected.Thms
import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Region.Automatic.Thms
import Silmaril.SSA.PEG.Simple.Revert.Schedule.Thms
import Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Regions.Thms
import Silmaril.SSA.PEG.Semantics.Reindex.Defs
import Silmaril.SSA.PEG.Rules.Thms
import Mathlib.Data.Fin.Embedding
import Mathlib.Logic.Equiv.Basic
import Silmaril.SSA.PEG.Simple.Revert.While.Region.Automatic.Thms
import Silmaril.SSA.PEG.Simple.Thms
meta import Silmaril.SSA.PEG.Simple.Revert.Schedule.Defs
meta import Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Defs
meta import Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Cuts.Defs
meta import Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Regions.Defs
meta import Silmaril.SSA.PEG.Builder
meta import Silmaril.SSA.PEG.Simple.Revert.While.Defs
meta import Silmaril.SSA.PEG.Simple.Revert.While.Pair.Defs
meta import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Projected.Defs
meta import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Region.Automatic.Defs
meta import Silmaril.SSA.PEG.Semantics.Reindex.Defs
meta import Silmaril.SSA.PEG.Simple.Revert.While.Region.Automatic.Defs
meta import Silmaril.SSA.PEG.Simple.Revert.While.Region.Placement.Defs
meta import Silmaril.SSA.PEG.Simple.Revert.While.Region.Placement.MustEval.Defs

namespace Silmaril.SSA.PEG.Simple.Revert.While.Tests

open RVSDG (Tuple)

private inductive Op : InstructionSet Unit where
  | nonzero : Op [.count] .bool
  | pred : Op [.count] .count
  | not : Op [.bool] .bool
  deriving DecidableEq

private def model : Interpretation Op where
  carrier _ := Unit
  run
    | .nonzero, .cons n .nil => some ⟨n.down != 0⟩
    | .pred, .cons n .nil => some ⟨n.down - 1⟩
    | .not, .cons b .nil => some ⟨!b.down⟩

private def form : Form Op .count := ⟨.nonzero, .pred, .not⟩

private def store (n : Nat) : Tuple model.Value [.count] := .cons ⟨n⟩ .nil

private theorem countDown (n : Nat) :
    Exec model form.program.source.body (store n) (some (store 0)) := by
  induction n with
  | zero => exact .whileStop rfl
  | succ n ih =>
    let assigned := Tuple.cons (F := model.Value) (t := Ty.count) ⟨n⟩ (store (n + 1))
    exact .whileStep (next := store n) rfl (.seq (next := assigned) (.assign rfl) .project) ih

private theorem accepted : ∃ cert, extract form.compile = some cert ∧ cert.form = form :=
  form.compile_extract

-- The extracted SIMPLE loop returns at zero iterations and at arbitrary finite exits.
example (n : Nat) : ∃ cert, extract form.compile = some cert ∧
    cert.revert.Returns model (store n) ⟨0⟩ := by
  obtain ⟨cert, checked, recovered⟩ := accepted
  refine ⟨cert, checked, store 0, ?_, ?_⟩
  · change Exec model cert.form.program.source.body (store n) (some (store 0))
    rw [recovered]
    exact countDown n
  · change (store 0).get cert.form.program.retvar = _
    rw [recovered]
    rfl

example (n : Nat) : ∃ cert, extract form.compile = some cert ∧
    form.compile.observe model (form.compile.denote model (store n) cert.demandWellFounded)
      (fun _ => 19) = .cons (some ⟨0⟩) .nil := by
  obtain ⟨cert, checked, recovered⟩ := accepted
  refine ⟨cert, checked, cert.observe_of_returns model (store n) ?_ ?_ _⟩
  · rw [recovered]
    intro b
    rfl
  · change cert.form.program.source.Returns model (store n) ⟨0⟩
    rw [recovered]
    exact ⟨store 0, countDown n, rfl⟩

-- Pass reads the continuation test directly, bypassing negation. Wiring is
-- still well sorted, but this is a different loop exit.
private def wrongExitRaw : RawGraph Op [.count] [.count] 7 1 :=
  { form.compile.toRaw with node := fun i =>
    let row := form.compile.toRaw.node i
    if i = 1 then { row with args := [4] } else row }

private def wrongExit : Graph Op [.count] [.count] 7 1 := wrongExitRaw.check.get (by decide)

example : extract wrongExit = none := by
  cases h : extract wrongExit with
  | none => rfl
  | some cert =>
    have mismatch := congrArg (fun g : RawGraph Op [.count] [.count] 7 1 =>
      (g.node 1).args) cert.table
    change [4] = [2] at mismatch
    contradiction

set_option interpreter.prefer_native false

/-- info: true -/
#guard_msgs in
#eval (extract form.compile).isSome

/-- info: true -/
#guard_msgs in
#eval (extract wrongExit).isNone

end Silmaril.SSA.PEG.Simple.Revert.While.Tests

namespace Silmaril.SSA.PEG.Simple.Revert.While.Pair.Tests

open RVSDG (Tuple)

private abbrev acc : Ty Unit := .data ()

private inductive Op : InstructionSet Unit where
  | positive : Op [.count] .bool
  | pred : Op [.count] .count
  | addOld : Op [.count, acc] acc
  | bad : Op [.count, acc] acc
  | not : Op [.bool] .bool
  deriving DecidableEq

private def model : Interpretation Op where
  carrier _ := Nat
  run
    | .positive, .cons n .nil => some ⟨n.down != 0⟩
    | .pred, .cons n .nil => some ⟨n.down - 1⟩
    | .addOld, .cons n (.cons a .nil) => some ((show Nat from a) + n.down)
    | .bad, _ => none
    | .not, .cons flag .nil => some ⟨!flag.down⟩

private def input (n a : Nat) : Tuple model.Value [.count, acc] := .cons ⟨n⟩ (.cons a .nil)

private def sum : Form Op .count acc acc := ⟨.positive, .pred, .addOld, .not, .tail .head⟩

private theorem sumTotal : sum.Total model where
  guard x := ⟨x.down != 0, rfl⟩
  leftStep x := ⟨⟨x.down - 1⟩, rfl⟩
  rightStep store := by
    cases store with | cons n tail =>
    cases tail with | cons a tail =>
    cases tail
    exact ⟨(show Nat from a) + n.down, rfl⟩

private def runExtracted (fuel n a : Nat) : Option Nat := do
  let cert ← extract sum.compile
  cert.form.runFuel model fuel (input n a)

set_option interpreter.prefer_native false

-- The additions see 3, 2 and 1, even though the counter is assigned first.
/-- info: some 16 -/
#guard_msgs in
#eval runExtracted 3 3 10

/-- info: some 10 -/
#guard_msgs in
#eval runExtracted 0 0 10

/-- info: none -/
#guard_msgs in
#eval runExtracted 2 3 10

private theorem sumPeg :
    sum.compile.observe model
      (sum.compile.denote model (input 3 10) (sum.program.translate_demandWellFounded sum.negate))
      (fun _ => 17) = .cons (some (16 : Nat)) .nil :=
  sum.program.translate_returns sum.negate model (input 3 10) (fun _ => rfl)
    (sum.runFuel_returns model 3 (input 3 10) (value := (16 : Nat)) rfl) (fun _ => 17)

private def sumCertificate : Certificate sum.compile := ⟨sum, rfl⟩

example : sumCertificate.revert.Returns model (input 3 10) (16 : Nat) :=
  sumCertificate.returns_of_defined model (input 3 10) sumTotal (fun _ => rfl) _ sumPeg

example : ∃ k, sumCertificate.form.runFuel model k (input 3 10) = some (16 : Nat) := by
  obtain ⟨k, returned, _⟩ :=
    sumCertificate.runFuel_of_defined model (input 3 10) sumTotal (fun _ => rfl) _ sumPeg
  exact ⟨k, returned⟩

-- The right update reads the newly computed left value. This wire is well
-- typed but changes a simultaneous update into a sequential dependency.
private def sequentialRaw : RawGraph Op [.count, acc] [acc] 10 1 :=
  { sum.compile.toRaw with node := fun i =>
    let row := sum.compile.toRaw.node i
    if i = 3 then { row with args := [4, 7] } else row }

private def sequential : Graph Op [.count, acc] [acc] 10 1 :=
  sequentialRaw.check.get (by decide)

/-- info: true -/
#guard_msgs in
#eval (extract sequential).isNone

/-- Left is the only observed slot. The partial right update is still
executed by SIMPLE on a continuing iteration. -/
private def discarded : Form Op .count acc .count := ⟨.positive, .pred, .bad, .not, .head⟩

private theorem notTotal : ¬ discarded.Total model := by
  intro total
  obtain ⟨x, impossible⟩ := total.rightStep (input 1 10)
  cases impossible

private def runDiscarded : Option Nat := do
  let cert ← extract discarded.compile
  (cert.form.runFuel model 1 (input 1 10)).map ULift.down

/-- info: (true, none) -/
#guard_msgs in
#eval ((extract discarded.compile).isSome, runDiscarded)

private def tick (n : Nat) : Index 1 := fun _ => n

private theorem setTick (idx : Index 1) (n : Nat) : idx.set 0 n = tick n := by
  funext i
  have h : i = 0 := Subsingleton.elim _ _
  subst i
  simp [Index.set, tick]

private theorem collectOne {t : Ty Unit}
    (sample : (i : Fin [t].length) → Option (model.Value [t][i])) :
    collect [t] sample = (sample 0).map (fun x => Tuple.cons x .nil) := by
  unfold collect
  cases sample 0 <;> rfl

-- Only the left carried stream, unary guard and exit test are demanded.
-- The PEG can return despite the failed right update in the SIMPLE body.
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 850000 in
private theorem discardedPeg :
    discarded.compile.observe model
      (discarded.compile.denote model (input 1 10)
        (discarded.program.translate_demandWellFounded discarded.negate)) (tick 0) =
      .cons (some ⟨0⟩) .nil := by
  let wf := discarded.program.translate_demandWellFounded discarded.negate
  let values := discarded.compile.denote model (input 1 10) wf
  have eq (v : Fin 10) (idx : Index 1) :
      values (v, idx) = discarded.compile.equation model (input 1 10) values (v, idx) :=
    discarded.compile.denote_solves model (input 1 10) wf (v, idx)
  have initial : values (6, tick 0) = some ⟨1⟩ := by
    rw [eq 6 (tick 0)]
    change values (8, tick 0) = _
    exact eq 8 (tick 0)
  have update : values (4, tick 0) = some ⟨0⟩ := by
    rw [eq 4 (tick 0)]
    change (collect [.count] _).elim none (model.run Op.pred) = _
    rw [collectOne]
    change ((values (6, tick 0)).map (fun x => Tuple.cons x .nil)).elim none (model.run Op.pred) = _
    rw [initial]
    rfl
  have next : values (6, tick 1) = some ⟨0⟩ := by
    rw [eq 6 (tick 1)]
    change values (4, (tick 1).set 0 0) = _
    rw [setTick, update]
  have exit (idx : Index 1) (n : Nat) (value : values (6, idx) = some ⟨n⟩) :
      values (2, idx) = some ⟨!(n != 0)⟩ := by
    have guard : values (5, idx) = some ⟨n != 0⟩ := by
      rw [eq 5 idx]
      change (collect [.count] _).elim none (model.run Op.positive) = _
      rw [collectOne]
      change ((values (6, idx)).map (fun x => Tuple.cons x .nil)).elim none
        (model.run Op.positive) = _
      rw [value]
      rfl
    rw [eq 2 idx]
    change (collect [.bool] _).elim none (model.run Op.not) = _
    rw [collectOne]
    change ((values (5, idx)).map (fun x => Tuple.cons x .nil)).elim none (model.run Op.not) = _
    rw [guard]
    rfl
  let flags := fun k => (values (2, tick k)).map ULift.down
  have stop : flags 1 = some true := by
    unfold flags
    rw [exit (tick 1) 0 next]
    rfl
  have again : flags 0 = some false := by
    unfold flags
    rw [exit (tick 0) 1 initial]
    rfl
  have first : firstTrue flags = some 1 := by
    apply (firstTrue_eq_some_iff _ _).mpr
    refine ⟨(monotonize_eq_some_iff _ _ _).mpr ⟨stop, ?_⟩, ?_⟩
    · intro j h
      have zj : j = 0 := by omega
      rw [zj, again]
      rfl
    · intro j h hit
      have zj : j = 0 := by omega
      have trueSample := ((monotonize_eq_some_iff _ _ _).mp hit).1
      rw [zj, again] at trueSample
      cases trueSample
  have pass : values (1, tick 0) = some ⟨1⟩ := by
    rw [eq 1 (tick 0)]
    change (firstTrue (fun k => (values (2, (tick 0).set 0 k)).map ULift.down)).map ULift.up = _
    have aligned : (fun k => (values (2, (tick 0).set 0 k)).map ULift.down) = flags := by
      funext k
      exact congrArg (fun idx => (values (2, idx)).map ULift.down) (setTick (tick 0) k)
    rw [aligned, first]
    rfl
  change Tuple.cons (F := fun t => Option (model.Value t)) (values (0, tick 0)) .nil = _
  congr 1
  rw [eq 0 (tick 0)]
  change (values (1, tick 0)).elim none (fun count =>
    monotonize (fun j => values (6, (tick 0).set 0 j)) count.down) = _
  rw [pass]
  change monotonize (fun j => values (6, (tick 0).set 0 j)) 1 = _
  have aligned : (fun j => values (6, (tick 0).set 0 j)) = (fun j => values (6, tick j)) := by
    funext j
    exact congrArg (fun idx => (show Option (model.Value .count) from values (6, idx)))
      (setTick (tick 0) j)
  rw [aligned]
  apply (monotonize_eq_some_iff _ _ _).mpr
  refine ⟨next, fun j lt => ?_⟩
  have zj : j = 0 := by omega
  rw [zj, initial]
  rfl

private theorem discardedFails : discarded.program.source.Fails model (input 1 10) := by
  let updated : Tuple model.Value [.count, .count, acc] := .cons ⟨0⟩ (input 1 10)
  exact .whileBodyFailed rfl (.seq (next := updated) (.assign rfl) (.firstFailed (.assignFailed rfl)))

example : ¬ discarded.program.source.Returns model (input 1 10) ⟨0⟩ := by
  intro success
  obtain ⟨_, ran, _⟩ := success
  cases Exec.deterministic ran discardedFails

end Silmaril.SSA.PEG.Simple.Revert.While.Pair.Tests

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Tests

open RVSDG (Tuple)

private abbrev acc : Ty Unit := .data ()
private abbrev carried : List (Ty Unit) := [.count, acc, acc]

private inductive Op : InstructionSet Unit where
  | twice : Op [.count] .count
  | nonzero : Op [.count] .bool
  | pred : Op [.count] .count
  | sum : Op [acc, acc] acc
  | addCount : Op [.count, acc] acc
  | not : Op [.bool] .bool
  deriving DecidableEq

private def model : Interpretation Op where
  carrier _ := Nat
  run
    | .twice, .cons n .nil => some ⟨2 * n.down⟩
    | .nonzero, .cons n .nil => some ⟨n.down != 0⟩
    | .pred, .cons n .nil => some ⟨n.down - 1⟩
    | .sum, .cons a (.cons b .nil) => some ((show Nat from a) + (show Nat from b))
    | .addCount, .cons n (.cons a .nil) => some (n.down + (show Nat from a))
    | .not, .cons b .nil => some ⟨!b.down⟩

private def sorts (i : Fin 15) : Ty Unit :=
  match i.val with
  | 1 | 2 | 6 | 12 | 13 => .count
  | 4 | 11 => .bool
  | _ => acc

private inductive ExtraRow where
  | theta
  | parameter
  | cycle

-- Rows are interleaved, the root is row 5, and both accumulator updates use
-- row 0. The supplied-boundary regressions use an extra θ with self-feedback.
private def graph (crosses : Bool) (extra : ExtraRow := .theta) (ambiguous : Bool := false) :
    Graph Op carried [acc] 15 1 where
  forest := ⟨fun _ => none⟩
  sort := sorts
  node := fun i =>
    match i with
    | 0 => .ofLabel (.op .sum)
        (.cons ⟨8, rfl⟩ (.cons (if crosses then ⟨10, rfl⟩ else ⟨3, rfl⟩) .nil))
    | 1 => .ofLabel (.theta 0) (.cons ⟨13, rfl⟩ (.cons ⟨6, rfl⟩ .nil))
    | 2 => .ofLabel (.pass 0) (.cons ⟨11, rfl⟩ .nil)
    | 3 => .ofLabel (.theta 0)
        (.cons (if ambiguous then ⟨9, rfl⟩ else ⟨14, rfl⟩) (.cons ⟨0, rfl⟩ .nil))
    | 4 => .ofLabel (.op .nonzero) (.cons ⟨12, rfl⟩ .nil)
    | 5 => .ofLabel (.eval 0) (.cons ⟨8, rfl⟩ (.cons ⟨2, rfl⟩ .nil))
    | 6 => .ofLabel (.op .pred) (.cons ⟨1, rfl⟩ .nil)
    | 7 => .ofLabel (.op .addCount) (.cons ⟨1, rfl⟩ (.cons ⟨0, rfl⟩ .nil))
    | 8 => .ofLabel (.theta 0) (.cons ⟨9, rfl⟩ (.cons ⟨7, rfl⟩ .nil))
    | 9 => .ofLabel (.param (.tail .head)) .nil
    | 10 =>
      match extra with
      | .theta => .ofLabel (.theta 0) (.cons ⟨14, rfl⟩ (.cons ⟨10, rfl⟩ .nil))
      | .parameter => .ofLabel (.param (.tail .head)) .nil
      | .cycle => .ofLabel (.op .sum) (.cons ⟨10, rfl⟩ (.cons ⟨8, rfl⟩ .nil))
    | 11 => .ofLabel (.op .not) (.cons ⟨4, rfl⟩ .nil)
    | 12 => .ofLabel (.op .twice) (.cons ⟨1, rfl⟩ .nil)
    | 13 => .ofLabel (.param .head) .nil
    | 14 => .ofLabel (.param (.tail (.tail .head))) .nil
  roots := .cons ⟨5, rfl⟩ .nil

private def phase (i : Fin 15) : Nat := if i = 5 then 2 else if i = 2 then 1 else 0

private def localRank (i : Fin 15) : Nat :=
  match i.val with
  | 7 | 11 => 5
  | 0 | 4 => 4
  | 6 | 12 => 3
  | 1 | 3 | 8 | 10 => 2
  | _ => 1

private def descriptor (crosses : Bool) : Descriptor (graph crosses) where
  theta := .cons ⟨1, rfl⟩ (.cons ⟨8, rfl⟩ (.cons ⟨3, rfl⟩ .nil))
  initial := .cons ⟨13, rfl⟩ (.cons ⟨9, rfl⟩ (.cons ⟨14, rfl⟩ .nil))
  next := .cons ⟨6, rfl⟩ (.cons ⟨7, rfl⟩ (.cons ⟨0, rfl⟩ .nil))
  guard := ⟨4, rfl⟩
  negated := ⟨11, rfl⟩
  negate := .not
  pass := ⟨2, rfl⟩
  returnSlot := .tail .head

private def rank : DemandRank 15 1 := [.phase phase, .counter 0, .phase localRank]

private def input (n a b : Nat) : Tuple model.Value carried := .cons ⟨n⟩ (.cons a (.cons b .nil))

private def checked := checkScheduled (graph false) (descriptor false) rank

private def run (fuel n a b : Nat) : Option Nat := do
  let cert ← checked
  cert.runFuel model fuel (input n a b)

set_option interpreter.prefer_native false

-- The updates read the old counter and both old accumulators. At the first
-- step the new pair is (13, 11), and at the second it is (25, 24).
/-- info: (some 25, some 10, none) -/
#guard_msgs in
#eval (run 2 2 10 1, run 0 0 10 1, run 1 2 10 1)

-- Demand ranking alone admits the fourth θ. The checker refuses to read
-- it as a same-iteration update operand because it is outside the region.
/-- info: (true, true, true) -/
#guard_msgs in
#eval (rank.check (graph true), (checkScheduled (graph true) (descriptor true) rank).isNone,
  (check (graph true) (descriptor true) ⟨[12, 4], [6, 0, 7], rank⟩).isNone)

-- An operand must be in scope before its consumer is emitted.
/-- info: true -/
#guard_msgs in
#eval (check (graph false) (descriptor false) ⟨[12, 4], [6, 7, 0], rank⟩).isNone

-- The inferred update order includes the shared sum just once.
/-- info: some [6, 0, 7] -/
#guard_msgs in
#eval sliceOrder (graph false) (descriptor false) (descriptor false).next

-- The graph and its designated output determine the complete certificate.
private def runInferred (fuel n a b : Nat) : Option Nat := do
  let cert ← Automatic.extract (graph false .parameter)
  cert.runFuel model fuel (input n a b)

/-- info: (some 25, some 10, none) -/
#guard_msgs in
#eval (runInferred 2 2 10 1, runInferred 0 0 10 1, runInferred 1 2 10 1)

-- Both accumulator θs initialize from the first accumulator's port.
-- Matching the total θ count alone would miss the ambiguity.
/-- info: (3, 2, true) -/
#guard_msgs in
#eval let bad := graph false .parameter true
  (Automatic.thetaCount bad, (Automatic.candidates bad (.tail .head)).length,
    (Automatic.extract bad).isNone)

-- The same boundary can be read with an unused ordinary self-cycle.
-- The assembled demand rank is checked across the entire graph.
/-- info: (true, false, true) -/
#guard_msgs in
#eval let cyclic := graph false .cycle
  ((Automatic.inferBoundary cyclic).isSome, (Automatic.inferDemandRank cyclic).check cyclic,
    (Automatic.extract cyclic).isNone)

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Tests

namespace Silmaril.SSA.PEG.Simple.Revert.While.Nested.Tests

open RVSDG (Tuple)

private abbrev Outer : List (Ty Unit) := [.count, .count]
private abbrev Inner : List (Ty Unit) := [.count, .count, .count]

private inductive Op : InstructionSet Unit where
  | positive : Op [.count] .bool
  | pred : Op [.count] .count
  | add : Op [.count, .count] .count
  | not : Op [.bool] .bool
  deriving DecidableEq

private def model : Interpretation Op where
  carrier _ := Unit
  run
    | .positive, .cons x .nil => some ⟨x.down != 0⟩
    | .pred, .cons x .nil => some ⟨x.down - 1⟩
    | .add, .cons x (.cons y .nil) => some ⟨x.down + y.down⟩
    | .not, .cons b .nil => some ⟨!b.down⟩

-- Outer store is (counter, accumulator). The child captures these two
-- values and a second copy of the old outer counter for the final commit.
private def form : Form Op Outer Inner .count where
  outerGuard := .op .positive (.cons (.var .head) .nil)
  captures := .cons .head (.cons (.tail .head) (.cons .head .nil))
  innerGuard := .op .positive (.cons (.var .head) .nil)
  innerStep :=
    .seq (.assign (.op .pred (.cons (.var .head) .nil))) <|
    .seq (.assign (.op .add (.cons (.var (.tail .head)) (.cons (.var (.tail (.tail .head))) .nil)))) <|
    .project (.cons (.tail .head) (.cons .head (.cons (.tail (.tail (.tail (.tail .head)))) .nil)))
  commit :=
    .seq (.assign (.op .pred (.cons (.var (.tail (.tail .head))) .nil))) <|
    .project (.cons .head (.cons (.tail (.tail .head)) .nil))
  returnSlot := .tail .head
  negate := .not

private def outerStore (n acc : Nat) : Tuple model.Value Outer := .cons ⟨n⟩ (.cons ⟨acc⟩ .nil)
private def innerStore (n acc saved : Nat) : Tuple model.Value Inner :=
  .cons ⟨n⟩ (.cons ⟨acc⟩ (.cons ⟨saved⟩ .nil))

private def run (outerFuel innerFuel n acc : Nat) : Option Nat := do
  let _ ← check form form.compile
  (form.runFuel model outerFuel innerFuel (outerStore n acc)).map ULift.down

-- The first inner invocation takes three steps, then two, then one.
-- The sum of their contributions is 6 + 3 + 1.
set_option interpreter.prefer_native false in
/-- info: (some 10, some 7, none, none) -/
#guard_msgs in
#eval (run 3 3 3 0, run 0 0 0 7, run 2 3 3 0, run 3 2 3 0)

-- The modified graph remains sorted and has the same number of rows.
-- Its child counter reads the old accumulator instead of the old counter.
private def wrongCapture : Form Op Outer Inner .count :=
  { form with captures := .cons (.tail .head) (.cons (.tail .head) (.cons .head .nil)) }

private def wrongParent : Graph Op Outer [.count] form.size form.size :=
  { form.compile with forest := ⟨fun _ => none⟩ }

set_option interpreter.prefer_native false in
/-- info: (true, true) -/
#guard_msgs in
#eval ((check form wrongCapture.compile).isNone, (check form wrongParent).isNone)

private def childResult (acc : Nat) : Nat → Nat
  | 0 => acc
  | n + 1 => childResult (n + 1 + acc) n

private theorem childExec (n acc saved : Nat) :
    Exec model form.child (innerStore n acc saved) (some (innerStore 0 (childResult acc n) saved)) := by
  induction n generalizing acc with
  | zero => exact .whileStop rfl
  | succ n ih =>
    exact .whileStep (next := innerStore n (n + 1 + acc) saved) rfl
      (form.innerStep.runLoopFree_enableWhile (innerStore (n + 1) acc saved)) (ih _)

private def outerResult (acc : Nat) : Nat → Nat
  | 0 => acc
  | n + 1 => outerResult (childResult acc (n + 1)) n

private theorem outerExec (n acc : Nat) :
    Exec model form.source.body (outerStore n acc) (some (outerStore 0 (outerResult acc n))) := by
  induction n generalizing acc with
  | zero => exact .whileStop rfl
  | succ n ih =>
    refine .whileStep (next := outerStore n (childResult acc (n + 1))) rfl ?_ (ih _)
    exact .seq (next := innerStore (n + 1) acc (n + 1)) .project
      (.seq (childExec (n + 1) acc (n + 1))
        (form.commit.runLoopFree_enableWhile (innerStore 0 (childResult acc (n + 1)) (n + 1))))

private theorem total : form.Total model where
  guard old := ⟨(old.get .head).down != 0, rfl⟩
  child old _ := by
    cases old with | cons n tail =>
    cases tail with | cons acc tail =>
    cases tail
    exact ⟨_, childExec n.down acc.down n.down⟩
  commit {old final} _ := by
    cases final with | cons _ tail =>
    cases tail with | cons _ tail =>
    cases tail with | cons _ tail =>
    cases tail
    exact ⟨_, rfl⟩

private def cert : Certificate form form.compile := ⟨rfl⟩

private theorem returnsTen : form.source.Returns model (outerStore 3 0) ⟨10⟩ :=
  ⟨outerStore 0 (outerResult 0 3), outerExec 3 0, rfl⟩

private theorem observedTen (i : Index form.size) :
    form.compile.observe model
      (form.compile.denote model (outerStore 3 0) cert.demandWellFounded) i =
      .cons (some ⟨10⟩) .nil :=
  (cert.returns_iff_observe model (outerStore 3 0) total (fun _ => rfl) i ⟨10⟩).mp returnsTen

example (i : Index form.size) : ∃ k final,
    WhileTrace model form.outerGuard form.body k (outerStore 3 0) final ∧
      final.get form.returnSlot = ⟨10⟩ :=
  cert.trace_of_defined model (outerStore 3 0) total (fun _ => rfl) i (observedTen i)

private def runDiscovered {n : Nat} (g : Graph Op Outer [.count] n n)
    (outerFuel innerFuel n0 acc : Nat) : Option Nat := do
  let accepted ← Automatic.extract g
  (accepted.form.runFuel model outerFuel innerFuel (outerStore n0 acc)).map ULift.down

-- Same graph as the supplied check, with the form now recovered by the graph-only API.
-- Capturing a different in-scope old value defines a second valid input graph.
/-- info: (some 10, some 5) -/
#guard_msgs in
#eval (runDiscovered form.compile 3 3 3 0, runDiscovered wrongCapture.compile 2 2 2 1)

-- The child initializer bypasses the old outer θ and reads its parameter
-- directly. The modified edge is well sorted, but escapes the capture scope.
private def bypassCapture {n : Nat} (g : Graph Op Outer [.count] n n) :
    Graph Op Outer [.count] n n :=
  { g with node := fun i =>
      let row := g.node i
      match row with
      | ⟨_, .theta loop, args⟩ =>
        if (g.forest.parent loop).isSome then
          match Region.nodeAt g (args.get .head) with
          | ⟨_, .theta _, outerArgs⟩ =>
            .ofLabel (.theta loop) (.cons (outerArgs.get .head) (.cons (args.get (.tail .head)) .nil))
          | _ => row
        else row
      | _ => row }

/-- info: (true, true) -/
#guard_msgs in
#eval ((Automatic.extract (bypassCapture form.compile)).isNone,
  (Automatic.extract wrongParent).isNone)

private def reverseId {width : Nat} (i : Fin width) : Fin width :=
  ⟨width - 1 - i.val, by have := i.isLt; omega⟩

private theorem reverseTwice {width : Nat} (i : Fin width) : reverseId (reverseId i) = i := by
  apply Fin.ext
  have := i.isLt
  simp only [reverseId]
  omega

private def reversed (width : Nat) : Fin width ≃ Fin width :=
  ⟨reverseId, reverseId, reverseTwice, reverseTwice⟩

private def moved : Graph Op Outer [.count] form.size form.size :=
  form.compile.reindex (reversed form.size) (reversed form.size)

private def runMoved : Option Nat := do
  let ids ← checkFinEquiv (reverseId (width := form.size)) reverseId
  let accepted ← Reindexed.extract moved ids ids
  (accepted.form.runFuel model 3 3 (outerStore 3 0)).map ULift.down

-- Both the row addresses and loop keys have changed.
/-- info: some 10 -/
#guard_msgs in
#eval runMoved

-- The supplied maps cannot certify a table whose child counter captures
-- a different old slot than the reference graph.
private def wrongWire : Graph Op Outer [.count] form.size form.size :=
  wrongCapture.compile.reindex (reversed form.size) (reversed form.size)

/-- info: true -/
#guard_msgs in
#eval let ids := reversed form.size
  (form.compile.checkReindex wrongWire ids ids).isNone

private def movedCertificate :
    form.compile.ReindexCertificate moved (reversed form.size) (reversed form.size) :=
  ⟨rfl⟩

private theorem movedWF : WellFounded moved.Demand :=
  movedCertificate.demandWellFounded_iff.mpr cert.demandWellFounded

example (i : Index form.size) :
    moved.observe model (moved.denote model (outerStore 3 0) movedWF) i = .cons (some ⟨10⟩) .nil :=
  (movedCertificate.observe_denote model (outerStore 3 0) cert.demandWellFounded movedWF i).trans
    (observedTen _)

-- The outer pass key is permuted independently of its vertex address.
-- The returned accumulator is the only designated root, so the other
-- outer eval must be covered by the discovered bundle anchor.
private def movedIndependently : Graph Op Outer [.count] form.size form.size :=
  form.compile.reindex (reversed form.size)
    (Equiv.swap ⟨0, by decide⟩ ⟨2, by decide⟩)

private def runInferredNumbering : Option Nat := do
  let accepted ← Reindexed.Automatic.extract movedIndependently
  (accepted.form.runFuel model 3 3 (outerStore 3 0)).map ULift.down

/-- info: some 10 -/
#guard_msgs in
#eval runInferredNumbering

/-- info: true -/
#guard_msgs in
#eval (Reindexed.Automatic.extract (bypassCapture movedIndependently)).isNone

-- The second parameter is isolated when the primitive's two operands
-- share the first parameter. An explicit anchor covers the isolated row.
private def sharedOperands (split : Bool) : Graph Op Outer [.count] 3 0 where
  forest := ⟨Fin.elim0⟩
  sort _ := .count
  node i := match i with
    | 0 => .ofLabel (.op .add) (.cons ⟨1, rfl⟩ (.cons ⟨if split then 2 else 1, rfl⟩ .nil))
    | 1 => .ofLabel (.param .head) .nil
    | 2 => .ofLabel (.param (.tail .head)) .nil
  roots := .cons ⟨0, rfl⟩ .nil

-- Splitting a repeated wire forces one source row to pair with two
-- target rows, even though every operand sort still agrees.
/-- info: (true, true, true) -/
#guard_msgs in
#eval
  let same := sharedOperands false
  let changed := sharedOperands true
  let infer new anchors := Silmaril.SSA.PEG.Reindex.Automatic.infer same new anchors
  ((infer same []).isNone, (infer same [(2, 2)]).isSome, (infer changed [(2, 2)]).isNone)

private def paddedSort {n : Nat} (sort : Fin n → Ty Unit) (i : Fin (n + 1)) : Ty Unit :=
  if h : i.val < n then sort (i.castLT h) else .count

private def padRef {n : Nat} {sort : Fin n → Ty Unit} {t : Ty Unit} (r : Ref sort t) :
    Ref (paddedSort sort) t :=
  ⟨r.id.castSucc, by simpa [paddedSort, r.id.isLt] using r.typed⟩

-- Add a dead primitive that consumes the designated result. Observing
-- the result never demands its consumer. Keep the original loop table.
private def pad {n l : Nat} (g : Graph Op Outer [.count] n l) : Graph Op Outer [.count] (n + 1) l where
  forest := g.forest
  sort := paddedSort g.sort
  node i :=
    if h : i.val < n then
      let row := g.node (i.castLT h)
      (show paddedSort g.sort i = g.sort (i.castLT h) by simp [paddedSort, h]).symm ▸
        Node.ofLabel row.label (row.args.map fun _ r => padRef r)
    else
      (show paddedSort g.sort i = .count by simp [paddedSort, h]).symm ▸
        Node.ofLabel (.op .pred) (.cons (padRef (g.roots.get .head)) .nil)
  roots := g.roots.map fun _ r => padRef r

private def padded := pad movedIndependently

-- Structured compiler images have equally many row and loop keys.
-- The padded graph cannot have both bijections to any such image.
example {k : Nat} :
    ¬ (Nonempty (Fin (form.size + 1) ≃ Fin k) ∧ Nonempty (Fin form.size ≃ Fin k)) :=
  fun ⟨rows, loops⟩ =>
    Nat.succ_ne_self _ ((Fin.equiv_iff_eq.mp rows).trans (Fin.equiv_iff_eq.mp loops).symm)

private def runProjected : Option (Bool × Nat) := do
  let a ← Projected.extract padded
  let value ← a.core.form.runFuel model 3 3 (outerStore 3 0)
  return (a.projection.rows.length == form.size, value.down)

/-- info: some (true, 10) -/
#guard_msgs in
#eval runProjected

-- Retain the child θ but delete its initializer from the proposed
-- projection. The initializer is an outer θ, not the designated eval.
private def rejectsMissingCapture : Option Bool := do
  let cached := Automatic.cacheRows padded
  let header ← Automatic.locate cached
  let exit ← (Automatic.bundleIds cached header.childKey).head?
  let slot ← Automatic.readSlotAt cached header.childKey header.childPass (Ref.ofId cached.sort exit)
  let rows := (List.finRange (form.size + 1)).filter
    (fun i => i != slot.initial.id && i != Fin.last form.size)
  return decide (slot.theta.id ∈ rows) && (padded.checkProjection rows).isNone

/-- info: some true -/
#guard_msgs in
#eval rejectsMissingCapture

end Silmaril.SSA.PEG.Simple.Revert.While.Nested.Tests

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Placement.Tests

open RVSDG (Tuple)

private inductive Op : InstructionSet Unit where
  | guard : Op [.count] .bool
  | not : Op [.bool] .bool
  | twoOrMore : Op [.count] .bool
  | pred : Op [.count] .count
  | positivePred : Op [.count] .count
  | copy : Op [.count] .count
  deriving DecidableEq

private def model : Interpretation Op where
  carrier _ := Unit
  run
    | .guard, .cons n .nil => some ⟨n.down != 0⟩
    | .not, .cons b .nil => some ⟨!b.down⟩
    | .twoOrMore, .cons n .nil => some ⟨2 ≤ n.down⟩
    | .pred, .cons n .nil => some ⟨n.down - 1⟩
    | .positivePred, .cons n .nil => if n.down = 0 then none else some ⟨n.down - 1⟩
    | .copy, .cons n .nil => some n

private def sort : Fin 11 → Ty Unit
  | 0 | 1 | 2 | 3 | 5 | 6 | 7 => .count
  | 4 | 8 | 9 => .bool
  | _ => .count

-- The live feedback is φ (old ≥ 2) (positivePred shared) (copy shared).
-- The two differently wired arms share one computation, pred old.
private def raw : RawGraph Op [.count] [.count] 11 1 where
  forest := ⟨fun _ => none⟩
  sort := sort
  node
    | 0 => ⟨_, .eval 0, [3, 10]⟩
    | 1 => ⟨_, .op .pred, [3]⟩
    | 2 => ⟨_, .param .head, []⟩
    | 3 => ⟨_, .theta 0, [2, 7]⟩
    | 4 => ⟨_, .op .twoOrMore, [3]⟩
    | 5 => ⟨_, .op .positivePred, [1]⟩
    | 6 => ⟨_, .op .copy, [1]⟩
    | 7 => ⟨_, .phi, [4, 5, 6]⟩
    | 8 => ⟨_, .op .guard, [3]⟩
    | 9 => ⟨_, .op .not, [8]⟩
    | 10 => ⟨_, .pass 0, [9]⟩
  roots := [0]

private def graph : Graph Op [.count] [.count] 11 1 := raw.check.get (by decide)

private def input (n : Nat) : Tuple model.Value [.count] := .cons ⟨n⟩ .nil

private def checked := extract graph 7 1

private def run (fuel n : Nat) : Option Nat := do
  let cert ← checked
  (cert.region.runFuel model fuel (input n)).map ULift.down

-- Inspect the emitted update: the shared primitive is before the branch,
-- with one arm-local operation on each side and a final projection.
private def hasSharedBranch {vars outs : List (Ty Unit)} : Stmt Op false vars outs → Bool
  | .seq (.assign (.op .twoOrMore _))
      (.seq (.assign (.op .pred _))
        (.seq (.branch (.var _)
          (.seq (.assign (.op .positivePred _)) (.project _))
          (.seq (.assign (.op .copy _)) (.project _))) (.project _))) => true
  | _ => false

set_option interpreter.prefer_native false

/-- info: (true, true, true) -/
#guard_msgs in
#eval ((Figure19.check graph .inward 12).isSome, (Automatic.extract graph).isNone,
  (checked.map fun cert => hasSharedBranch cert.region.update.lower).getD false)

/-- info: (some 0, none, some 0) -/
#guard_msgs in
#eval (run 3 5, run 2 5, run 0 0)

-- At old = 1 that instruction would fail before the branch, although the
-- original selected arm returns zero. Keep Figure 19 and rank unchanged.
example : model.run Op.positivePred (.cons ⟨0⟩ .nil) = none := rfl

/-- info: (true, some 0) -/
#guard_msgs in
#eval ((extract graph 7 5).isNone, run 1 1)

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Placement.Tests

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Placement.MustEval.Tests

open RVSDG (Tuple)

private inductive Op : InstructionSet Unit where
  | guard : Op [.count] .bool
  | not : Op [.bool] .bool
  | large : Op [.count] .bool
  | larger : Op [.count] .bool
  | positivePred : Op [.count] .count
  | copy : Op [.count] .count
  | zeroLike : Op [.count] .count
  deriving DecidableEq

private def model : Interpretation Op where
  carrier _ := Unit
  run
    | .guard, .cons n .nil => some ⟨n.down != 0⟩
    | .not, .cons b .nil => some ⟨!b.down⟩
    | .large, .cons n .nil => some ⟨3 ≤ n.down⟩
    | .larger, .cons n .nil => some ⟨4 ≤ n.down⟩
    | .positivePred, .cons n .nil => if n.down = 0 then none else some ⟨n.down - 1⟩
    | .copy, .cons n .nil => some n
    | .zeroLike, .cons _ .nil => some ⟨0⟩

private def sort : Fin 15 → Ty Unit
  | 4 | 5 | 12 | 13 => .bool
  | _ => .count

-- The outer arms are separate lazy branches. Both strictly need row 1
-- regardless of their choice, while both may skip row 6.
private def raw : RawGraph Op [.count] [.count] 15 1 where
  forest := ⟨fun _ => none⟩
  sort := sort
  node
    | 0 => ⟨_, .eval 0, [3, 14]⟩
    | 1 => ⟨_, .op .positivePred, [3]⟩
    | 2 => ⟨_, .param .head, []⟩
    | 3 => ⟨_, .theta 0, [2, 11]⟩
    | 4 => ⟨_, .op .large, [3]⟩
    | 5 => ⟨_, .op .larger, [3]⟩
    | 6 => ⟨_, .op .positivePred, [1]⟩
    | 7 => ⟨_, .op .copy, [1]⟩
    | 8 => ⟨_, .phi, [5, 6, 7]⟩
    | 9 => ⟨_, .op .zeroLike, [1]⟩
    | 10 => ⟨_, .phi, [5, 6, 9]⟩
    | 11 => ⟨_, .phi, [4, 8, 10]⟩
    | 12 => ⟨_, .op .guard, [3]⟩
    | 13 => ⟨_, .op .not, [12]⟩
    | 14 => ⟨_, .pass 0, [13]⟩
  roots := [0]

private def graph : Graph Op [.count] [.count] 15 1 := raw.check.get (by decide)

private def checked := extract graph

private def run (fuel n : Nat) : Option Nat := do
  let a ← checked
  (a.region.runFuel model fuel (.cons ⟨n⟩ .nil)).map ULift.down

-- Require a single placed binding in the update prefix with both
-- nested branches still in their respective outer arms.
private def nestedBranch {vars outs : List (Ty Unit)} : Stmt Op false vars outs → Bool
  | .seq (.assign (.op .larger _)) (.seq (.branch (.var _) _ _) (.project _)) => true
  | _ => false

private def shares {vars outs : List (Ty Unit)} : Stmt Op false vars outs → Bool
  | .seq (.assign (.op .large _))
      (.seq (.assign (.op .positivePred _))
        (.seq (.branch (.var _) yes no) (.project _))) => nestedBranch yes && nestedBranch no
  | _ => false

private def rejectsUnsafe : Bool :=
  match Automatic.inferBoundary graph with
  | none => false
  | some d =>
    let depth := Figure19.inferDepth graph.forest 1
    let table := Figure19.MustEval.analyze graph
    (Candidate.check d depth table 11 6).isNone

set_option interpreter.prefer_native false

/-- info: (true, some (11, 1, true)) -/
#guard_msgs in
#eval ((Placement.extract graph 11 1).isNone,
  checked.map fun a => (a.candidate.branch.val, a.candidate.shared.val, shares a.region.update.lower))

-- The continuing iterations visit both inner outcomes in the outer
-- true arm, then run the outer false arm. The zero-trip case never runs row 1.
/-- info: (some 0, none, some 0) -/
#guard_msgs in
#eval (run 3 5, run 2 5, run 0 0)

-- At old = 1, shared row 1 returns zero and row 6 would fail if placed
-- eagerly. Both outer arms can reach row 6 but neither requires it.
example : model.run Op.positivePred (.cons ⟨0⟩ .nil) = none := rfl

/-- info: (true, some 0) -/
#guard_msgs in
#eval (rejectsUnsafe, run 1 1)

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Placement.MustEval.Tests

namespace Silmaril.SSA.PEG.Simple.Revert.While.Nested.Region.Tests

open RVSDG (Tuple)

private inductive Op : InstructionSet Unit where
  | done : Op [.count] .bool
  | pred : Op [.count] .count
  | add : Op [.count, .count] .count
  | not : Op [.bool] .bool
  | zero : Op [] .count
  | tick : Op [.count] .count
  | atLeast : Op [.count, .count] .bool
  deriving DecidableEq

private def model : Interpretation Op where
  carrier _ := Unit
  run
    | .done, .cons count .nil => some ⟨count.down == 0⟩
    | .pred, .cons count .nil => some ⟨count.down - 1⟩
    | .add, .cons a (.cons b .nil) => some ⟨a.down + b.down⟩
    | .not, .cons b .nil => some ⟨!b.down⟩
    | .zero, .nil => some ⟨0⟩
    | .tick, .cons x .nil => some ⟨x.down + 1⟩
    | .atLeast, .cons x (.cons y .nil) => some ⟨decide (y.down ≤ x.down)⟩

private abbrev state := ([.count, .count] : List (Ty Unit))

private def sort (i : Fin 16) : Ty Unit := if i = 10 ∨ i = 11 then .bool else .count
private def r (i : Fin 16) (h : sort i = .count) : Ref sort .count := ⟨i, h⟩
private def firstFlag : Ref sort .bool := ⟨10, rfl⟩
private def childFlag : Ref sort .bool := ⟨11, rfl⟩

private def pair {F : Ty Unit → Type} (a b : F .count) : Tuple F state := .cons a (.cons b .nil)

-- The pass keys are 0 and 1, independent of the pass row addresses.
-- The child copies the current accumulator and remaining outer count.
-- Each child step adds the old child count and decrements that count.
private def graph (staleCapture : Bool) : Graph Op state [.count] 16 2 where
  forest := ⟨fun key => if key = 1 then some 0 else none⟩
  sort := sort
  node i := match i with
    | 0 => .ofLabel (.eval 0) (pair (r 2 rfl) (r 4 rfl))
    | 1 => .ofLabel (.eval 1) (pair (r 5 rfl) (r 7 rfl))
    | 2 => .ofLabel (.theta 0) (pair (r 13 rfl) (r 1 rfl))
    | 3 => .ofLabel (.theta 0) (pair (r 14 rfl) (r 12 rfl))
    | 4 => .ofLabel (.pass 0) (.cons firstFlag .nil)
    | 5 => .ofLabel (.theta 1) (pair (r 2 rfl) (r 8 rfl))
    | 6 => .ofLabel (.theta 1) (pair (if staleCapture then r 14 rfl else r 3 rfl) (r 9 rfl))
    | 7 => .ofLabel (.pass 1) (.cons childFlag .nil)
    | 8 => .ofLabel (.op .add) (pair (r 5 rfl) (r 6 rfl))
    | 9 => .ofLabel (.op .pred) (.cons (r 6 rfl) .nil)
    | 10 => .ofLabel (.op .done) (.cons (r 3 rfl) .nil)
    | 11 => .ofLabel (.op .done) (.cons (r 6 rfl) .nil)
    | 12 => .ofLabel (.op .pred) (.cons (r 3 rfl) .nil)
    | 13 => .ofLabel (.param .head) .nil
    | 14 => .ofLabel (.param (.tail .head)) .nil
    | 15 => .ofLabel (.eval 1) (pair (r 6 rfl) (r 7 rfl))
    | ⟨k + 16, bound⟩ => False.elim (by omega)
  roots := .cons (r 0 rfl) .nil

private def rank : DemandRank 16 2 :=
  [.phase (fun i => if i = 0 then 2 else if i = 4 then 1 else 0), .counter 0,
   .phase (fun i => if i = 1 ∨ i = 15 then 2 else if i = 7 then 1 else 0), .counter 1,
   .phase (fun i => match i.val with
    | 8 | 9 | 11 => 3
    | 5 | 6 | 10 | 12 => 2
    | 2 | 3 => 1
    | _ => 0)]

private def checked := Automatic.extract (graph false) rank Op.not

private def wrongPass : Graph Op state [.count] 16 2 :=
  { graph false with
    node := fun i =>
      if bad : i = 15 then bad.symm ▸ Node.ofLabel (.eval 1) (pair (r 6 rfl) (r 9 rfl))
      else (graph false).node i }

private def input (count : Nat) : Tuple model.Value state := pair ⟨0⟩ ⟨count⟩

#guard rank.check (graph false)
#guard rank.check (graph true)
#guard (Automatic.describe (graph true) Op.not).isSome
#guard (Automatic.extract (graph true) rank Op.not).isNone
#guard rank.check wrongPass
#guard (Automatic.describe wrongPass Op.not).isNone
#guard (Automatic.extract wrongPass rank Op.not).isNone
#guard (Automatic.extract (graph false) [] Op.not).isNone

-- The first invocation needs two steps and returns accumulator 3.
-- The next needs one step and returns accumulator 4. Read the actual
-- stores handed between the two emitted outer body steps.
private def twoActivations : Option (Nat × Nat × Nat × Nat) := do
  let accepted ← checked
  let a := accepted.certificate
  let start ← a.outerGuard.lower.runLoopFree model (input 2)
  let first ← a.stepFuel model 2 start
  let second ← a.stepFuel model 1 first
  if (a.stepFuel model 1 start).isNone && (a.stepFuel model 0 first).isNone then
    return ((first.get (.tail .head)).down, (first.get (.tail (.tail .head))).down,
      (second.get (.tail .head)).down, (second.get (.tail (.tail .head))).down)
  else none

#guard twoActivations == some (3, 1, 4, 0)

private def certifiedRun :
    Option {a : Automatic.Recovered (graph false) Op.not //
      a.certificate.revert.Returns model (input 2) ⟨4⟩ ∧
      ∀ i, (graph false).observe model
        ((graph false).denote model (input 2) a.certificate.demandWellFounded) i =
          .cons (some ⟨4⟩) .nil} := do
  let discovered ← checked
  let a := discovered.certificate
  match ran : (a.runFuel model 2 2 (input 2) : Option (ULift Nat)) with
  | some ⟨4⟩ =>
    have returned := a.returns_of_runFuel 2 2 ran
    return ⟨discovered, returned,
      fun i => discovered.observe_of_returns (fun _ => rfl) (input 2) i returned⟩
  | _ => none

#guard certifiedRun.isSome

private def relocation : Equiv.Perm (Fin 16) :=
  (Equiv.swap 0 8).trans ((Equiv.swap 1 15).trans ((Equiv.swap 4 13).trans (Equiv.swap 7 14)))

private def loopRelocation : Equiv.Perm (Fin 2) := Equiv.swap 0 1

private def moved := (graph false).reindex relocation loopRelocation

private def movedCheck := Automatic.extract moved (rank.reindex relocation loopRelocation) Op.not

-- Both pass addresses and keys change. Relocating the two child evals
-- reverses the child's typed store order, including its capture slots.
#guard (movedCheck.map fun a =>
  let d := a.certificate.descriptor
  (d.outerKey.val, d.childKey.val, d.outerPass.id.val, d.childPass.id.val, refNumbers d.childExit,
    refNumbers d.childInit)) == some (1, 0, 13, 14, [1, 15], [3, 2])

#guard (movedCheck.bind fun a => (a.certificate.runFuel model 2 2 (input 2)).map ULift.down) == some 4
#guard (movedCheck.bind fun a => a.certificate.runFuel model 2 1 (input 2)).isNone

private theorem total : ∀ {ins out} (op : Op ins out) args, ∃ val, model.run op args = some val
  | _, _, .done, .cons _ .nil => ⟨_, rfl⟩
  | _, _, .pred, .cons _ .nil => ⟨_, rfl⟩
  | _, _, .add, .cons _ (.cons _ .nil) => ⟨_, rfl⟩
  | _, _, .not, .cons _ .nil => ⟨_, rfl⟩
  | _, _, .zero, .nil => ⟨_, rfl⟩
  | _, _, .tick, .cons _ .nil => ⟨_, rfl⟩
  | _, _, .atLeast, .cons _ (.cons _ .nil) => ⟨_, rfl⟩

private theorem setTwice (idx : Index 2) (key : Fin 2) (j k : Nat) :
    (idx.set key j).set key k = idx.set key k := by
  funext i
  by_cases h : i = key <;> simp [Index.set, h]

private theorem setCurrent (idx : Index 2) (key : Fin 2) : idx.set key (idx key) = idx := by
  funext i
  by_cases h : i = key <;> simp [Index.set, h]

private theorem countdown {count : Nat} {values : (graph false).Valuation model}
    (solved : (graph false).Solves model (input count) values)
    {theta init tick : Ref sort .count} {key : Fin 2}
    (thetaRow : Rules.HasNode (g := graph false) theta (.theta key) (pair init tick))
    (tickRow : Rules.HasNode (g := graph false) tick (.op Op.pred) (.cons theta .nil))
    (base : Index 2) {seed : Nat}
    (started : Rules.readRef values init (base.set key 0) = some ⟨seed⟩) (j : Nat) :
    Rules.readRef values theta (base.set key j) = some ⟨seed - j⟩ := by
  induction j with
  | zero =>
    rw [Rules.theta_zero solved thetaRow (by simp [Index.set])]
    exact started
  | succ j ih =>
    rw [Rules.theta_succ solved thetaRow (k := j) (by simp [Index.set]), setTwice,
      Rules.unary_at solved tickRow, ih]
    change some (⟨seed - j - 1⟩ : ULift Nat) = some ⟨seed - (j + 1)⟩
    rw [Nat.sub_sub]

private theorem countedPass {count : Nat} {values : (graph false).Valuation model}
    (solved : (graph false).Solves model (input count) values)
    {clock pass : Ref sort .count} {flag : Ref sort .bool} {key : Fin 2}
    (guardRow : Rules.HasNode (g := graph false) flag (.op Op.done) (.cons clock .nil))
    (passRow : Rules.HasNode (g := graph false) pass (.pass key) (.cons flag .nil))
    (base : Index 2) {seed : Nat}
    (counts : ∀ j, Rules.readRef values clock (base.set key j) = some ⟨seed - j⟩) :
    Rules.readRef values pass base = some ⟨seed⟩ := by
  have flags (j : Nat) :
      (Rules.readRef values flag (base.set key j)).map ULift.down = some (decide (seed ≤ j)) := by
    rw [Rules.unary_at solved guardRow, counts]
    change some ((seed - j) == 0) = some (decide (seed ≤ j))
    by_cases h : seed ≤ j
    · simp [h, Nat.sub_eq_zero_of_le h]
    · have ne : seed - j ≠ 0 := by omega
      simp [h, ne]
  rw [Rules.pass_at solved passRow]
  have first : firstTrue (fun j => (Rules.readRef values flag (base.set key j)).map ULift.down) =
      some seed := (firstTrue_eq_some_iff_samples _ _).mpr
    ⟨by simp [flags], fun j lt => by simp [flags, Nat.not_le_of_lt lt]⟩
  rw [first]
  rfl

private theorem outerCountdown {count : Nat} {values : (graph false).Valuation model}
    (solved : (graph false).Solves model (input count) values) (base : Index 2) (j : Nat) :
    Rules.readRef values (r 3 rfl) (base.set 0 j) = some ⟨count - j⟩ :=
  countdown solved (theta := r 3 rfl) (init := r 14 rfl) (tick := r 12 rfl)
    (key := 0) HEq.rfl HEq.rfl base (solved (14, base.set 0 0)) j

private theorem outerPassAt {count : Nat} {values : (graph false).Valuation model}
    (solved : (graph false).Solves model (input count) values) (base : Index 2) :
    Rules.readRef values (r 4 rfl) base = some ⟨count⟩ :=
  countedPass solved (clock := r 3 rfl) (pass := r 4 rfl) (flag := firstFlag)
    (key := 0) HEq.rfl HEq.rfl base (outerCountdown solved base)

private theorem childPassAt {count : Nat} {values : (graph false).Valuation model}
    (solved : (graph false).Solves model (input count) values) (base : Index 2) (outer : Nat) :
    Rules.readRef values (r 7 rfl) (base.set 0 outer) = some ⟨count - outer⟩ := by
  let idx := (base.set 0 outer).set 1 0
  have seed := outerCountdown solved idx (idx 0)
  rw [setCurrent] at seed
  have outerIdx : idx 0 = outer := by simp [idx, Index.set]
  rw [outerIdx] at seed
  exact countedPass solved (clock := r 6 rfl) (pass := r 7 rfl) (flag := childFlag)
    (key := 1) HEq.rfl HEq.rfl (base.set 0 outer)
    (countdown solved (theta := r 6 rfl) (init := r 3 rfl) (tick := r 9 rfl)
      (key := 1) HEq.rfl HEq.rfl (base.set 0 outer) seed)

private def FixtureTrace {inner : List (Ty Unit)} (a : Accepted (graph false) inner) (count : Nat) : Prop :=
  (∀ j < count, Rules.readRef ((graph false).denote model (input count) a.demandWellFounded)
    a.descriptor.childPass (Index.set (fun _ => 0) a.descriptor.outerKey j) = some ⟨count - j⟩) ∧
  ∃ start final, Exec model a.outerGuard.lower.enableWhile (input count) (some start) ∧
    WhileTrace model (continueTest a.descriptor.negate) a.body count start final

/-- Construct the nested SIMPLE derivation from the PEG equations.
The exact child counts are established before any target execution. -/
private theorem deriveFixtureTrace (discovered : Automatic.Recovered (graph false) Op.not)
    (outerKey : discovered.certificate.descriptor.outerKey = 0)
    (outerPass : discovered.certificate.descriptor.outerPass = r 4 rfl)
    (childPass : discovered.certificate.descriptor.childPass = r 7 rfl)
    (count : Nat) : FixtureTrace discovered.certificate count := by
  let a := discovered.certificate
  let base : Index 2 := fun _ => 0
  let values := (graph false).denote model (input count) a.demandWellFounded
  have solved := (graph false).denote_solves model (input count) a.demandWellFounded
  have outer : Rules.readRef values a.descriptor.outerPass base = some ⟨count⟩ := by
    rw [outerPass]
    exact outerPassAt solved base
  have child (j : Nat) :
      Rules.readRef values a.descriptor.childPass (base.set a.descriptor.outerKey j) =
        some ⟨count - j⟩ := by
    rw [childPass, outerKey]
    exact childPassAt solved base j
  have exits : a.FirstExits model values base count := ⟨outer, fun j hj => by
    by_cases zero : count = 0
    · omega
    · exact ⟨_, child j⟩⟩
  exact ⟨fun j _ => child j, a.trace_of_exits (discovered.negates (fun _ => rfl)) (input count)
    (a.definedSlices_of_total values total) base exits⟩

-- Assert the recovered anchors for the fixture's independent Figure 11
-- calculation. Discovery itself receives only the graph, rank and opcode.
private def fromPEG (count : Nat) :
    Option {a : Automatic.Recovered (graph false) Op.not // FixtureTrace a.certificate count} := do
  let a ← checked
  let d := a.certificate.descriptor
  letI := Simple.Revert.While.Region.refEq d.outerPass (r 4 rfl)
  letI := Simple.Revert.While.Region.refEq d.childPass (r 7 rfl)
  if h : d.outerKey = 0 ∧ d.outerPass = r 4 rfl ∧ d.childPass = r 7 rfl then
    return ⟨a, deriveFixtureTrace a h.1 h.2.1 h.2.2 count⟩
  else none

#guard (fromPEG 2).isSome
#guard (fromPEG 0).isSome

open Simple.Revert.Schedule (Plan)

private structure Scheduled (stale : Bool) where
  accepted : Simple.Revert.Schedule.Accepted (graph stale)
  laws : accepted.plan.Laws model

-- The same local certificate is proposed against both original tables.
-- A stale initializer reads the function input instead of the old outer slot.
private def schedule (stale : Bool) : Option (Scheduled stale) := do
  let found ← checked
  let stage : Simple.Revert.Schedule.Stage (graph stale) state [.count] :=
    ⟨16, 2, graph false, .nested found.certificate, fun i => ⟨i, rfl⟩, id⟩
  let plan : Plan (graph stale) state [.count] :=
    .step (ports state) stage (.done (.cons .head .nil))
  let accepted ← Simple.Revert.Schedule.check (graph stale) plan (pair (r 13 rfl) (r 14 rfl)) rank
  return ⟨accepted.val, accepted.property.symm ▸
    (show plan.Laws model from ⟨found.negates (fun _ => rfl), trivial⟩)⟩

private def scheduledRun :
    Option {a : Scheduled false //
      Exec model a.accepted.plan.revert (input 2) (some (.cons ⟨4⟩ .nil)) ∧
      ∀ i, (graph false).observe model ((graph false).denote model (input 2) a.accepted.demandWellFounded) i =
        .cons (some ⟨4⟩) .nil} := do
  let a ← schedule false
  match ran : a.accepted.plan.runFuel model 2 (input 2) with
  | some (.cons ⟨4⟩ .nil) =>
    have exec := a.accepted.plan.exec_of_runFuel 2 ran
    return ⟨a, exec, fun i => (a.accepted.observations_of_exec a.laws (input 2) i exec).2⟩
  | _ => none

#guard scheduledRun.isSome
#guard (schedule true).isNone

open Simple.Revert.Schedule.Automatic (Leaf Found discover)

-- Use the unrelocated leaf. Discovery must pair both loop scopes and
-- their rows with the original graph's permuted keys and addresses.
private def inferredRegion :
    Option {a : Found moved (.nestedOnly Op.not) (rank.reindex relocation loopRelocation) //
      Exec model a.gate.val.plan.revert (input 2) (some (.cons ⟨4⟩ .nil)) ∧
      ∀ i, moved.observe model (moved.denote model (input 2) a.gate.val.demandWellFounded) i =
        .cons (some ⟨4⟩) .nil} := do
  let leaf ← Leaf.nested (.nestedOnly Op.not) (graph false) rank
  let .ok a := discover moved (.nestedOnly Op.not) (rank.reindex relocation loopRelocation) [leaf] 1000 | none
  match ran : a.gate.val.plan.runFuel model 2 (input 2) with
  | some (.cons ⟨4⟩ .nil) =>
    let exec := a.gate.val.plan.exec_of_runFuel 2 ran
    return ⟨a, exec, fun i => (a.observations_of_exec (fun _ => rfl) (input 2) i exec).2⟩
  | _ => none

#guard inferredRegion.isSome

open Simple.Revert.Schedule.Automatic

-- Child evals are recovered from the labelled rows. The second child
-- exit slot is needed for the certificate and is absent from the root slice.
private def nestedCut : Cuts.Boundary moved :=
  ⟨state, [.count], pair ((r 13 rfl).reindex relocation) ((r 14 rfl).reindex relocation), moved.roots⟩

private def runFromNestedCut :
    Option {a : Found moved (.nestedOnly Op.not) (rank.reindex relocation loopRelocation) //
      Exec model a.gate.val.plan.revert (input 2) (some (.cons ⟨4⟩ .nil)) ∧
      ∀ i, moved.observe model (moved.denote model (input 2) a.gate.val.demandWellFounded) i =
        .cons (some ⟨4⟩) .nil} := do
  let .ok a := Cuts.discover moved (.nestedOnly Op.not) (rank.reindex relocation loopRelocation) [nestedCut] 4 | none
  match ran : a.gate.val.plan.runFuel model 2 (input 2) with
  | some (.cons ⟨4⟩ .nil) =>
    let exec := a.gate.val.plan.exec_of_runFuel 2 ran
    return ⟨a, exec, fun i => (a.observations_of_exec (fun _ => rfl) (input 2) i exec).2⟩
  | _ => none

#guard runFromNestedCut.isSome

private def discoverNested (original : Graph Op state [.count] 16 2) (ranking : DemandRank 16 2) :=
  Regions.discover original (.nestedOnly Op.not) ranking 1

private def runGraphOnly (original : Graph Op state [.count] 16 2) (ranking : DemandRank 16 2) :
    Option {a : Found original (.nestedOnly Op.not) ranking //
      Exec model a.gate.val.plan.revert (input 2) (some (.cons ⟨4⟩ .nil)) ∧
      ∀ i, original.observe model (original.denote model (input 2) a.gate.val.demandWellFounded) i =
        .cons (some ⟨4⟩) .nil} := do
  let .ok a := discoverNested original ranking | none
  match ran : a.gate.val.plan.runFuel model 2 (input 2) with
  | some (.cons ⟨4⟩ .nil) =>
    let exec := a.gate.val.plan.exec_of_runFuel 2 ran
    return ⟨a, exec, fun i => (a.observations_of_exec (fun _ => rfl) (input 2) i exec).2⟩
  | _ => none

#guard (runGraphOnly (graph false) rank).isSome
#guard (runGraphOnly moved (rank.reindex relocation loopRelocation)).isSome
#guard match discoverNested (graph true) rank with
  | .error (.checkedCuts (.unsupported 0 .leafCheck)) => true
  | _ => false

private def mixedSort (i : Fin 23) : Ty Unit :=
  if h : i.val < 16 then sort ⟨i.val, h⟩ else if i = 19 then .bool else .count

-- The final unit-counter sibling uses row 0, the completed outer
-- return, as its limit. Selecting child eval 1 instead is a frame leak.
private def mixedRaw (leak : Bool) : RawGraph Op state [.count, .count, .count] 23 3 where
  forest := ⟨fun key => if key = 1 then some 0 else none⟩
  sort := mixedSort
  node i :=
    if h : i.val < 16 then
      let row := (graph false).node ⟨i.val, h⟩
      have typed : (graph false).sort ⟨i.val, h⟩ = mixedSort i := by
        simp only [mixedSort, dite_eq_left h]
        rfl
      typed ▸ ⟨row.inputs, row.label.map (fun op => op) (fun key => key.castLE (by decide)),
        refNumbers row.args⟩
    else if flag : i = 19 then
      have typed : mixedSort i = .bool := by simp only [mixedSort, dite_eq_right h, ite_eq_left flag]
      typed.symm ▸ (⟨_, .op .atLeast, [16, if leak then 1 else 0]⟩ : RawNode Op state 3 .bool)
    else
      have typed : mixedSort i = .count := by simp only [mixedSort, dite_eq_right h, ite_eq_right flag]
      let row : RawNode Op state 3 .count := match i.val with
        | 16 => ⟨_, .theta 2, [17, 18]⟩
        | 17 => ⟨_, .op .zero, []⟩
        | 18 => ⟨_, .op .tick, [16]⟩
        | 20 => ⟨_, .pass 2, [19]⟩
        | 21 => ⟨_, .eval 2, [16, 20]⟩
        | _ => ⟨_, .op .tick, [21]⟩
      typed.symm ▸ row
  roots := [22, 0, 22]

private def mixed (leak : Bool) : Graph Op state [.count, .count, .count] 23 3 :=
  (mixedRaw leak).check.get (by cases leak <;> decide)

private def mixedRank : DemandRank 23 3 :=
  [.phase (fun i => if 16 ≤ i.val then 1 else 0),
   .phase (fun i => if i = 22 then 3 else if i = 21 then 2 else if i = 20 then 1 else 0),
   .counter 2, .phase (fun i => if i = 18 ∨ i = 19 then 2 else if i = 16 then 1 else 0)] ++
  rank.map (fun component => match component with
    | .phase heights => .phase (fun i => if h : i.val < 16 then heights ⟨i.val, h⟩ else 0)
    | .counter key => .counter (key.castLE (by decide)))

private def countedRoles : CountedRoles Op := ⟨.zero, .tick, .not⟩
private theorem countedLaws : countedRoles.Laws model := ⟨rfl, fun _ => rfl, fun _ => rfl⟩

private def mixedRun :
    Option {a : Found (mixed false) (.counted countedRoles) mixedRank //
      Exec model a.gate.val.plan.revert (input 2) (some (.cons ⟨5⟩ (.cons ⟨4⟩ (.cons ⟨5⟩ .nil)))) ∧
      ∀ i, (mixed false).observe model ((mixed false).denote model (input 2) a.gate.val.demandWellFounded) i =
        .cons (some ⟨5⟩) (.cons (some ⟨4⟩) (.cons (some ⟨5⟩) .nil))} := do
  let .ok a := Regions.discover (mixed false) (.counted countedRoles) mixedRank 2 | none
  match ran : a.gate.val.plan.runFuel model 4 (input 2) with
  | some (.cons ⟨5⟩ (.cons ⟨4⟩ (.cons ⟨5⟩ .nil))) =>
    let exec := a.gate.val.plan.exec_of_runFuel 4 ran
    return ⟨a, exec, fun i => (a.observations_of_exec countedLaws (input 2) i exec).2⟩
  | _ => none

#guard match Regions.inferBoundaries (mixed false) with
  | .ok [outer, next] => refNumbers outer.outputs == [0] && refNumbers next.inputs == [0]
  | _ => false
#guard mixedRun.isSome
#guard mixedRank.check (mixed true)
#guard match Regions.discover (mixed true) (.counted countedRoles) mixedRank 2 with
  | .error (.iterationValue 1) => true
  | _ => false

end Silmaril.SSA.PEG.Simple.Revert.While.Nested.Region.Tests
