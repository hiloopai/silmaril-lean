module

public import Silmaril.Formats.Hive.Date32.Utf8.Defs

public section

namespace Silmaril.Proofs.Formats.Hive.Date32.Utf8

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Hive Silmaril.Formats.Hive.Date32.Utf8
open Silmaril.Formats.Parquet
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Value)

private theorem sequence_two {Result : Fin 2 → Type}
    (check : (i : Fin 2) → Except (TypedPartitions.Error Hive.Date32.Error) (Result i)) :
    TypedPartitions.decode.sequenceFin 2 check = (do
      let first ← check 0
      let second ← check (0 : Fin 1).succ
      pure (Fin.cases first (Fin.cases second (fun i => nomatch i)))) := by
  simp only [TypedPartitions.decode.sequenceFin, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  cases check 0 <;> cases check (0 : Fin 1).succ <;> rfl

theorem decode_eq_fields (keys : Keys) (entries : PartitionPath.Partition)
    (valid : PartitionPath.validateKeys (entries.map Prod.fst) = .ok ())
    (known : ∀ entry ∈ entries, entry.1 = keys.date ∨ entry.1 = keys.text) :
    TypedPartitions.decode keys.schema convert entries =
      (match keys.order with
      | .dateFirst => do
        let day ← TypedPartitions.decodeField convert entries keys.dateField
        let text ← TypedPartitions.decodeField convert entries keys.textField
        pure (keys.cells day text)
      | .textFirst => do
        let text ← TypedPartitions.decodeField convert entries keys.textField
        let day ← TypedPartitions.decodeField convert entries keys.dateField
        pure (keys.cells day text)) := by
  have noUnknown :
      entries.find? (fun entry => !keys.schema.keys.contains entry.1) = none := by
    apply List.find?_eq_none.mpr
    intro entry member
    have hit := known entry member
    rcases keys with ⟨dateName, textName, order⟩
    cases order <;> rcases hit with hit | hit <;>
      simp_all [Keys.schema, Keys.dateField, Keys.textField, TypedPartitions.PartitionSchema.keys]
  simp only [TypedPartitions.decode, valid, noUnknown]
  rcases keys with ⟨dateName, textName, order⟩
  cases order <;> exact sequence_two _

theorem preparePaths_first_binding_error (int32 byteArray : Field) (keys : Keys)
    (options : PartitionPath.Options) (before : List String) (bad : String) (after : List String)
    (cause : TypedPartitions.Error Hive.Date32.Error)
    {files : List (Manifest.File keys.schema Value)}
    (prefixOk : preparePaths int32 byteArray keys options before = .ok files)
    (failed : Manifest.prepareFile keys.schema options convert bad = .error (.binding bad cause)) :
    preparePaths int32 byteArray keys options (before ++ bad :: after) = .error (.binding bad cause) := by
  unfold preparePaths Manifest.prepare at prefixOk ⊢
  cases schemaOk : TypedPartitions.checkSchema (Failure := Hive.Date32.Error)
      (Int32ByteArrayGroup.File.schema int32 byteArray) keys.schema with
  | error reason => simp [schemaOk] at prefixOk
  | ok checked =>
    simp only [schemaOk] at prefixOk ⊢
    simp [List.mapM_append, prefixOk, List.mapM_cons, failed, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Hive.Date32.Utf8
