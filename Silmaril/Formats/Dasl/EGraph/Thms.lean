module

public import Silmaril.Formats.Dasl.EGraph.Defs
import Silmaril.Proofs.Formats.Dasl.EGraph

public section

namespace Silmaril.Formats.Dasl.EGraph

open Silmaril.Formats.PER.EGraph
open Silmaril.Semantics.Naming (Relation)

variable {Operator Name Cas : Type} {size classes : Nat} {dag : Dag Operator} {seeds : Seeds dag.val.size}

theorem Agrees.per_eq {table audited : Partition size} (same : Agrees table audited) : table.per = audited.per :=
  PER.ext same

theorem Agrees.rawPER_eq {table audited : Partition size} (same : Agrees table audited) :
    table.rawPER = audited.rawPER := by
  rw [table.rawPER_eq, audited.rawPER_eq, same.per_eq]

variable [DecidableEq Operator] {names : Relation Name Nat} [DecidableRel names]
  {steps : List (Step dag.val.size)} {table : NamedTable dag classes names}

theorem replay_sound {result : Partition dag.val.size} (hit : replay? dag seeds steps = some result) :
    dag.Sound seeds result :=
  Proofs.Formats.Dasl.EGraph.replayFrom_sound (dag.sound_of_injective seeds _ fun _ _ equal => equal) hit

theorem certify_replayed {rows : IndexSequence.Checked (.classId classes) Name}
    (hit : certify? dag seeds names steps rows = some table) :
    table.val.rows = rows ∧ ∃ audited, replay? dag seeds steps = some audited ∧ Agrees table.val.partition audited :=
  Proofs.Formats.Dasl.EGraph.certify_replayed hit

theorem certify_sound {rows : IndexSequence.Checked (.classId classes) Name}
    (hit : certify? dag seeds names steps rows = some table) : dag.Sound seeds table.val.partition := by
  obtain ⟨_, _, replayed, same⟩ := certify_replayed hit
  unfold Dag.Sound; rw [same.per_eq]; exact replay_sound replayed

theorem decodeCertified_sound {codec : IndexSequence.SequenceCodec (Name × Nat) Cas} {raw : Shallow Cas}
    (hit : decodeCertified? dag seeds names steps classes codec raw = some table) :
    dag.Sound seeds table.val.partition := by
  obtain ⟨_, _, checked⟩ := Option.bind_eq_some_iff.mp hit
  exact certify_sound checked

theorem decodeCertified_raw_sound {codec : IndexSequence.SequenceCodec (Name × Nat) Cas} {raw : Shallow Cas}
    (hit : decodeCertified? dag seeds names steps classes codec raw = some table) :
    table.val.partition.rawPER ≤ (dag.generated seeds).decodePull (termId? dag.val.size) := by
  rw [table.val.partition.rawPER_eq]
  rintro _ _ ⟨left, right, hl, hr, related⟩
  exact ⟨left, right, hl, hr, decodeCertified_sound hit related⟩

/-- A source spelling need not be the encoder's spelling. A successful checked
row decode suffices to transport its certificate computation. -/
theorem certified_reencode {source target : IndexSequence.SequenceCodec (Name × Nat) Cas} {raw : Shallow Cas}
    {rows : IndexSequence.Checked (.classId classes) Name}
    (decoded : (IndexSequence.checked (.classId classes) source).decode? raw = some rows) :
    decodeCertified? dag seeds names steps classes source raw =
      decodeCertified? dag seeds names steps classes target ((IndexSequence.checked (.classId classes) target).encode rows) := by
  simp [decodeCertified?, decoded, Encode.TotalCodec.recovers]

/-- Transport between any two recoverable row-sequence codecs, including
parallel columns and independently paged columns. This compares results,
including the interpreted partition and witnessed names, not DASL objects or bytes. -/
theorem certified_transport (dag : Dag Operator) (seeds : Seeds dag.val.size) (names : Relation Name Nat)
    [DecidableRel names] (steps : List (Step dag.val.size)) (rows : IndexSequence.Checked (.classId classes) Name)
    (source target : IndexSequence.SequenceCodec (Name × Nat) Cas) :
    decodeCertified? dag seeds names steps classes source ((IndexSequence.checked (.classId classes) source).encode rows) =
    decodeCertified? dag seeds names steps classes target ((IndexSequence.checked (.classId classes) target).encode rows) :=
  certified_reencode ((IndexSequence.checked (.classId classes) source).recovers rows)

end Silmaril.Formats.Dasl.EGraph
