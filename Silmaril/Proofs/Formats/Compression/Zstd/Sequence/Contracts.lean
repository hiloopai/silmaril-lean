module

public import Silmaril.Formats.Compression.Zstd.Sequence.Defs
import Silmaril.Formats.Compression.HistoryCopy.Thms

public section

namespace Silmaril.Proofs.Formats.Compression.Zstd.Sequence

open Silmaril.Formats.Compression.Zstd.Sequence
open Silmaril.Formats.Compression.Zstd.Sequence.Internal

theorem resolve_sound {offsets next : RepeatOffsets} {literalLength value distance : Nat}
    (success : resolve offsets literalLength value = some (distance, next)) :
    OffsetWire offsets literalLength value distance next := by
  match value with
  | 0 => cases success
  | 1 =>
    by_cases zero : literalLength = 0
    · subst literalLength
      cases success
      exact .zeroFirst
    · simp [resolve, zero] at success
      obtain ⟨rfl, rfl⟩ := success
      exact .first (by omega)
  | 2 =>
    by_cases zero : literalLength = 0
    · subst literalLength
      cases success
      exact .zeroSecond
    · simp [resolve, zero] at success
      obtain ⟨rfl, rfl⟩ := success
      exact .second (by omega)
  | 3 =>
    by_cases zero : literalLength = 0
    · subst literalLength
      cases success
      exact .zeroThird
    · simp [resolve, zero] at success
      obtain ⟨rfl, rfl⟩ := success
      exact .third (by omega)
  | n + 4 =>
    cases success
    exact .explicit literalLength n

private theorem repeats_valid {offsets next : RepeatOffsets} {literalLength value distance : Nat}
    (wire : OffsetWire offsets literalLength value distance next) (valid : offsets.Valid)
    (positive : 0 < distance) : next.Valid := by
  cases wire <;> simp_all [RepeatOffsets.Valid]

private theorem match_of_copy {distance : Nat} {history bytes : List UInt8}
    (wire : Silmaril.Formats.Compression.HistoryCopy.Wire distance history bytes) :
    MatchWire distance history bytes := by
  induction wire with
  | nil history => exact .nil history
  | cons positive available lookup _ ih => exact .cons positive available lookup ih

theorem copy_sound {distance : Nat} (positive : 0 < distance) (count : Nat)
    (data : Array UInt8) (available : distance ≤ data.size) :
    ∃ bytes, (copy distance positive count data available).toList = data.toList ++ bytes ∧
      bytes.length = count ∧ MatchWire distance data.toList bytes := by
  obtain ⟨bytes, shape, length, wire⟩ :=
    Silmaril.Formats.Compression.HistoryCopy.copy_sound positive count data available
  exact ⟨bytes, shape, length, match_of_copy wire⟩

private theorem step_sound {window remaining : Nat} {history written : Array UInt8}
    {literals suffix : List UInt8} {offsets next : RepeatOffsets} {command : Command}
    (success : step window remaining history literals offsets command = .ok (written, suffix, next)) :
    ∃ emitted, written.toList = history.toList ++ emitted ∧
      StepWire window command history.toList literals offsets emitted suffix next ∧
      command.outputLength ≤ remaining := by
  simp only [step] at success
  split at success
  · simp [throw, bind, Except.bind] at success
  · rename_i minMatch
    split at success
    · simp [throw, bind, Except.bind] at success
    · rename_i budget
      simp only [List.splitAt_eq] at success
      split at success
      · simp [throw, bind, Except.bind] at success
      · rename_i litExtent
        have takenLength : (literals.take command.literalLength).length = command.literalLength :=
          Decidable.not_not.mp litExtent
        cases resolved : resolve offsets command.literalLength command.offsetValue with
        | none => simp [resolved, throw] at success
        | some fields =>
          obtain ⟨distance, advanced⟩ := fields
          simp only [resolved] at success
          split at success
          · rename_i positive
            split at success
            · simp [throw] at success
            · rename_i inWindow
              split at success
              · rename_i available
                cases success
                obtain ⟨matched, shape, length, copyWire⟩ := copy_sound positive command.matchLength
                  (history ++ (literals.take command.literalLength).toArray) (by simpa using available)
                refine ⟨literals.take command.literalLength ++ matched, ?_, ?_, Nat.le_of_not_gt budget⟩
                · simpa [List.append_assoc] using shape
                · exact ⟨literals.take command.literalLength, matched, distance,
                    (List.take_append_drop _ _).symm, takenLength, resolve_sound resolved,
                    positive, Nat.lt_of_not_ge inWindow, by simpa using available,
                    Nat.le_of_not_gt minMatch, length, by simpa using copyWire, rfl⟩
              · simp [throw] at success
          · simp [throw] at success

theorem run_sound {window remaining : Nat} {commands : List Command}
    {history written : Array UInt8} {literals suffix : List UInt8} {offsets next : RepeatOffsets}
    (success : run window commands remaining history literals offsets = .ok (written, suffix, next)) :
    ∃ emitted, written.toList = history.toList ++ emitted ∧
      Runs window commands history.toList literals offsets emitted suffix next ∧
      (commands.map Command.outputLength).sum ≤ remaining := by
  induction commands generalizing remaining history literals offsets with
  | nil =>
    cases success
    exact ⟨[], by simp, .nil _ _ _, by simp⟩
  | cons command commands ih =>
    cases stepped : step window remaining history literals offsets command with
    | error err => simp [run, stepped, bind, Except.bind] at success
    | ok fields =>
      obtain ⟨middle, tail, updated⟩ := fields
      have restSuccess := success
      simp only [run, stepped, bind, Except.bind] at restSuccess
      obtain ⟨head, headShape, one, headFits⟩ := step_sound stepped
      obtain ⟨bytes, bytesShape, rest, restFits⟩ := ih restSuccess
      rw [headShape] at bytesShape rest
      refine ⟨head ++ bytes, by simpa [List.append_assoc] using bytesShape, .cons one rest, ?_⟩
      simp only [List.map_cons, List.sum_cons]
      omega

theorem runs_account {window : Nat} {commands : List Command}
    {history literals emitted suffix : List UInt8} {offsets next : RepeatOffsets}
    (wire : Runs window commands history literals offsets emitted suffix next) (valid : offsets.Valid) :
    suffix = literals.drop (commands.map Command.literalLength).sum ∧
      literals.length = (commands.map Command.literalLength).sum + suffix.length ∧
      emitted.length = (commands.map Command.outputLength).sum ∧ next.Valid := by
  induction wire with
  | nil => exact ⟨rfl, by simp, rfl, valid⟩
  | cons one rest ih =>
    obtain ⟨taken, matched, _, litShape, litLength, offsetWire, positive, _, _, _, matchLength,
      _, emittedShape⟩ := one
    obtain ⟨suffixShape, tailSize, size, nextValid⟩ := ih (repeats_valid offsetWire valid positive)
    refine ⟨?_, ?_, ?_, nextValid⟩
    · rw [suffixShape, litShape, List.map_cons, List.sum_cons, ← litLength,
        ← List.drop_drop, List.drop_left]
    · simp [litShape, litLength, tailSize, Nat.add_assoc]
    · simp [emittedShape, litLength, matchLength, size, Command.outputLength, Nat.add_assoc]

theorem execute_sound {limits : Limits} {history : Array UInt8} {literals : List UInt8}
    {offsets : RepeatOffsets} {commands : List Command} {result : Result}
    (success : execute limits history literals offsets commands = .ok result) :
    ∃ emitted suffix, Runs limits.window commands history.toList literals offsets emitted suffix result.offsets ∧
      suffix = literals.drop (commands.map Command.literalLength).sum ∧
      literals.length = (commands.map Command.literalLength).sum + suffix.length ∧
      result.bytes = emitted ++ suffix ∧
      result.bytes.length = (commands.map Command.outputLength).sum + suffix.length ∧
      result.bytes.length ≤ limits.capacity ∧ history.size ≤ limits.window ∧ result.offsets.Valid := by
  simp only [execute] at success
  split at success
  · simp [throw, bind, Except.bind] at success
  · rename_i historyFits
    split at success
    · simp [throw, bind, Except.bind] at success
    · rename_i offsetsValid
      have valid : offsets.Valid := Decidable.not_not.mp offsetsValid
      cases ran : run limits.window commands limits.capacity history literals offsets with
      | error err => simp [ran, bind, Except.bind] at success
      | ok fields =>
        obtain ⟨written, suffix, next⟩ := fields
        obtain ⟨emitted, shape, wire, commandsFit⟩ := run_sound ran
        obtain ⟨suffixShape, literalLength, emittedLength, nextValid⟩ := runs_account wire valid
        have writtenSize : written.size = history.size + emitted.length := by
          simpa only [Array.length_toList, List.length_append] using congrArg List.length shape
        have newBytes : written.toList.drop history.size = emitted := by
          rw [shape, ← Array.length_toList, List.drop_left]
        simp only [ran, bind, Except.bind] at success
        split at success
        · simp [throw] at success
        · rename_i suffixFits
          cases success
          rw [writtenSize] at suffixFits
          simp only [Nat.add_sub_cancel_left] at suffixFits
          refine ⟨emitted, suffix, wire, suffixShape, literalLength, by rw [newBytes], ?_, ?_,
            Nat.le_of_not_gt historyFits, nextValid⟩
          · rw [newBytes, List.length_append, emittedLength]
          · rw [newBytes, List.length_append]
            omega

end Silmaril.Proofs.Formats.Compression.Zstd.Sequence
