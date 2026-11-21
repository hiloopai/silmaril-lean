module

public import Silmaril.Formats.Dasl.EGraph.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.EGraph

open Silmaril.Formats Silmaril.Formats.Dasl.EGraph Silmaril.Formats.PER.EGraph
open Silmaril.Semantics.Naming (Relation)

variable {Operator Name : Type} [DecidableEq Operator] {dag : Dag Operator} {seeds : Seeds dag.val.size}

theorem replayFrom_sound {steps : List (Step dag.val.size)} {initial result : Partition dag.val.size}
    (sound : dag.Sound seeds initial) (hit : replayFrom? dag seeds initial steps = some result) :
    dag.Sound seeds result := by
  induction steps generalizing initial with
  | nil => cases hit; exact sound
  | cons step rest ih =>
    obtain ⟨next, _, later⟩ := Option.bind_eq_some_iff.mp hit
    exact ih (Dag.merge_sound next.property.1 next.property.2 sound) later

omit [DecidableEq Operator] in
private theorem checkTable_rows {names : Relation Name Nat} [DecidableRel names]
    {classes : Nat} {rows : Dasl.IndexSequence.Checked (.classId classes) Name} {table : NamedTable dag classes names}
    (hit : checkTable? dag names rows = some table) : table.val.rows = rows := by
  unfold checkTable? at hit
  split at hit
  · dsimp only at hit
    split at hit
    · cases hit; rfl
    · contradiction
  · contradiction

theorem certify_replayed {names : Relation Name Nat} [DecidableRel names] {steps : List (Step dag.val.size)}
    {classes : Nat} {rows : Dasl.IndexSequence.Checked (.classId classes) Name} {table : NamedTable dag classes names}
    (hit : certify? dag seeds names steps rows = some table) :
    table.val.rows = rows ∧ ∃ audited, replay? dag seeds steps = some audited ∧ Agrees table.val.partition audited := by
  obtain ⟨bound, aligned, replayHit⟩ := Option.bind_eq_some_iff.mp hit
  obtain ⟨audited, replayed, accepted⟩ := Option.bind_eq_some_iff.mp replayHit
  split at accepted
  · cases accepted
    exact ⟨checkTable_rows aligned, audited, replayed, ‹_›⟩
  · contradiction

end Silmaril.Proofs.Formats.Dasl.EGraph
