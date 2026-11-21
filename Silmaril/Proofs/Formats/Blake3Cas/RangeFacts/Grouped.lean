module

public import Silmaril.Formats.Blake3Cas.RangeFacts.Grouped.Defs

public section

namespace Silmaril.Proofs.Formats.Blake3Cas.RangeFacts

open Silmaril.Crypto.Blake3
open Silmaril.Formats.Blake3Cas
open Silmaril.Formats.Blake3Cas.RangeFacts.Grouped

theorem check_expand {shape : Shape} (grouped : Evidence shape) (root : Bool) :
    grouped.check? root = eval? (some ∘ compress32) root shape grouped.expand := by
  induction grouped generalizing root with
  | raw => rfl
  | «opaque» => simp [Evidence.check?, Evidence.expand, eval?]
  | fork _ _ lhs rhs => simp [Evidence.check?, Evidence.expand, eval?, ← lhs, ← rhs, parentCV]

theorem raw_width {shape : Shape} {bytes : Bytes} {root : Bool} {cv : CV}
    (hit : subtreeCV? root shape bytes = some cv) : bytes.length = shape.size := by
  induction shape generalizing bytes root cv with
  | leaf chunk size =>
    change eval? (some ∘ compress32) root (.leaf chunk size) (.leaf bytes) = some cv at hit
    rw [eval?] at hit
    split at hit
    · rename_i valid; exact valid.1
    · contradiction
  | fork left right leftIH rightIH =>
    change ((subtreeCV? false left (bytes.take left.size)).bind fun lcv =>
      (subtreeCV? false right (bytes.drop left.size)).bind fun rcv => some (parentCV root lcv rcv)) = some cv at hit
    cases lhit : subtreeCV? false left (bytes.take left.size) with
    | none => simp [lhit] at hit
    | some lcv =>
      cases rhit : subtreeCV? false right (bytes.drop left.size) with
      | none => simp [lhit, rhit] at hit
      | some rcv =>
        have lengths := congrArg List.length (List.take_append_drop left.size bytes)
        simpa only [List.length_append, leftIH lhit, rightIH rhit, Shape.size] using lengths.symm

theorem forLayers_reveals (layers : Nat) (selected : Nat → Bool) {shape : Shape} {root : Bool}
    {index : Nat} (inside : index ∈ chunkIndices shape) (wanted : selected index = true) :
    index ∈ (Cut.forLayers layers selected root shape).revealed := by
  induction shape generalizing root with
  | leaf chunk size =>
    have nonempty := List.any_eq_true.mpr ⟨index, inside, wanted⟩
    rw [Cut.forLayers.eq_def]
    simp [nonempty, Cut.revealed, inside]
  | fork left right leftIH rightIH =>
    have nonempty := List.any_eq_true.mpr ⟨index, inside, wanted⟩
    rw [Cut.forLayers.eq_def]
    simp only [nonempty, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false]
    split
    · exact inside
    · simp only [Cut.revealed, List.mem_append]
      exact (List.mem_append.mp inside).imp (leftIH (root := false)) (rightIH (root := false))

theorem emit_checked {root : Bool} {shape : Shape} (cut : Cut root shape) {bytes : Bytes} {cv : CV}
    (full : subtreeCV? root shape bytes = some cv) :
    ∃ grouped, cut.emit? bytes = some grouped ∧ grouped.check? root = some cv ∧
      grouped.expand.exposesEOF = cut.opensEdge ∧
      Refines concrete shape grouped.expand (disclose shape bytes) := by
  induction cut generalizing bytes cv with
  | raw =>
    exact ⟨.raw bytes, rfl, full, disclose_exposesEOF .., .keep ..⟩
  | «opaque» =>
    exact ⟨.opaque cv, by simp [Cut.emit?, full], rfl, rfl, .expose (eval_graph.mp full)⟩
  | @fork root left right lhs rhs leftIH rightIH =>
    change (do
      let lcv ← subtreeCV? false left (bytes.take left.size)
      let rcv ← subtreeCV? false right (bytes.drop left.size)
      some (parentCV root lcv rcv)) = some cv at full
    cases lhit : subtreeCV? false left (bytes.take left.size) with
    | none => simp [lhit] at full
    | some lcv =>
      cases rhit : subtreeCV? false right (bytes.drop left.size) with
      | none => simp [lhit, rhit] at full
      | some rcv =>
        obtain ⟨l, lemit, lcheck, _, lref⟩ := leftIH lhit
        obtain ⟨r, remit, rcheck, redge, rref⟩ := rightIH rhit
        exact ⟨.fork l r, by simp [Cut.emit?, lemit, remit],
          by simpa [Evidence.check?, lcheck, rcheck, lhit, rhit] using full, redge, .fork lref rref⟩

end Silmaril.Proofs.Formats.Blake3Cas.RangeFacts
