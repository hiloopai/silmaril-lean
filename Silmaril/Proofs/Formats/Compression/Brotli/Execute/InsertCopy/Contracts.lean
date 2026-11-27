module

public import Silmaril.Formats.Compression.Brotli.Execute.InsertCopy.Defs
import Silmaril.Formats.Compression.Brotli.BlockTypes.Switch.Thms
import Silmaril.Formats.Compression.Brotli.Execute.Thms
import Silmaril.Formats.Compression.Brotli.CompressedHeader.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Execute.InsertCopy

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Execute
open Silmaril.Formats.Compression.Brotli.Execute.InsertCopy
open Silmaril.Formats.Compression.Brotli.BlockTypes

private theorem bind_mapped_ok {ε δ α β : Type} {action : Except ε α} {next : α → Except δ β}
    {error : ε → δ} {out : β} (read : (action.mapError error >>= next) = .ok out) :
    ∃ value, action = .ok value ∧ next value = .ok out := by
  cases action with
  | error _ => cases read
  | ok value => exact ⟨value, rfl, read⟩

theorem selected_tree_exists {header : CompressedHeader.Header} {work : Nat} {bits : List Bool} {run : Switch.Run}
    (wire : CompressedHeader.Wire work bits header) (valid : run.Valid header.initial.controls.insertCopy) :
    ∃ table, header.insertCopyTrees[run.current]? = some table ∧ table.alphabetSize = 704 := by
  obtain ⟨groupSize, groupAlphabet⟩ := wire.groups .insertCopy
  change header.insertCopyTrees.length = header.initial.controls.insertCopy.typeCount at groupSize
  have inRange : run.current < header.insertCopyTrees.length := groupSize.symm ▸ valid.1
  have selected := List.getElem?_eq_getElem inRange
  exact ⟨_, selected, groupAlphabet _ (List.getElem_mem inRange)⟩

theorem read_sound {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {initial : InsertCopy.State} {before after : LSBReader} {input : List Bool} {result : InsertCopy.Result}
    (rep : before.Rep input) (count : before.count < 8)
    (read : InsertCopy.read header block limits initial before = .ok (result, after)) :
    result.runs.insertCopy.Valid header.initial.controls.insertCopy ∧
    result.runs.literal = initial.runs.literal ∧ result.runs.distance = initial.runs.distance ∧
    initial.execution.output.size < result.execution.state.output.size ∧
    result.execution.state.output.size ≤ block.endOutput ∧ result.execution.state.output.size ≤ limits.output ∧
    ∃ used suffix, InsertCopy.Wire header block initial used result ∧ input = used ++ suffix ∧ after.Rep suffix ∧
      after.count < 8 ∧ after.totalRead = before.totalRead + used.length ∧ used.length ≤ limits.bits := by
  unfold InsertCopy.read at read
  split at read
  · contradiction
  · rename_i literal
    split at read
    · contradiction
    · rename_i distance
      obtain ⟨⟨runs, atCommand⟩, runRead, rest⟩ := bind_mapped_ok read
      dsimp only at rest
      split at rest
      · rename_i tree selected
        obtain ⟨⟨executed, stop⟩, commandRead, done⟩ := bind_mapped_ok rest
        cases done
        obtain ⟨valid, others, switchBits, tail, switchWire, split, tailRep, tailCount, position, bitCap⟩ :=
          Switch.select_sound rep count runRead
        obtain ⟨_, _, _, _, grows, outCap, callerCap, commandBits, suffix, commandWire, commandSplit,
          afterRep, afterCount, afterPosition, commandCap⟩ := Execute.read_sound tailRep tailCount commandRead
        change commandBits.length ≤ limits.bits - (atCommand.totalRead - before.totalRead) at commandCap
        have lit := others .literal (by decide)
        have dist := others .distance (by decide)
        refine ⟨valid, lit, dist, grows, outCap, callerCap, switchBits ++ commandBits, suffix,
          ⟨literal, distance, switchBits, commandBits, tree, rfl, switchWire, selected, commandWire⟩,
          ?_, afterRep, afterCount, ?_, ?_⟩
        · rw [split, commandSplit, List.append_assoc]
        · rw [afterPosition, position, List.length_append, Nat.add_assoc]
        · simp only [List.length_append]
          omega
      · contradiction

theorem read_error {header : CompressedHeader.Header} {block : Block} {limits : Execute.Limits}
    {initial : InsertCopy.State} {before : LSBReader} {input : List Bool} {error : InsertCopy.Error}
    (rep : before.Rep input) (count : before.count < 8)
    (read : InsertCopy.read header block limits initial before = .error error) :
    Failure header block limits initial before input error := by
  unfold InsertCopy.read at read
  split at read
  · rename_i _ _ _ _ literal
    cases read
    exact .literalBlockTypes (by simp [literal])
  · split at read
    · rename_i _ _ _ _ distance
      cases read
      exact .distanceBlockTypes (by simp [distance])
    · cases selected : Switch.select header.initial.controls .insertCopy limits.bits initial.runs before with
      | error reason =>
        simp only [selected, Except.mapError, bind, Except.bind] at read
        cases read
        exact .switch (Switch.select_error rep count selected)
      | ok pair =>
        obtain ⟨runs, atCommand⟩ := pair
        simp only [selected, Except.mapError, bind, Except.bind] at read
        obtain ⟨_, _, used, suffix, wire, split, tailRep, _, position, bitCap⟩ :=
          Switch.select_sound rep count selected
        have site : CommandSite header limits initial before atCommand input runs.insertCopy :=
          ⟨used, suffix, wire, split, tailRep, position, bitCap⟩
        cases tree : header.insertCopyTrees[runs.insertCopy.current]? with
        | none =>
          simp only [tree] at read
          cases read
          exact .commandTree site tree
        | some table =>
          simp only [tree] at read
          cases executed : Execute.read (commandHeader header table) block
              { limits with bits := limits.bits - (atCommand.totalRead - before.totalRead) }
              initial.execution atCommand with
          | error reason =>
            simp only [executed] at read
            cases read
            exact .execute site tree executed
          | ok pair =>
            obtain ⟨_, _⟩ := pair
            simp only [executed] at read
            cases read

end Silmaril.Proofs.Formats.Compression.Brotli.Execute.InsertCopy
