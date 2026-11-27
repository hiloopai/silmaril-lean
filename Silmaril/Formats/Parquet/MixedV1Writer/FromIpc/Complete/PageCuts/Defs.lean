module

public import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Complete.Defs
public import Silmaril.Formats.Parquet.MixedV1Writer.MultiPage.Defs

/-! Opt-in explicit page cuts for each ordered native IPC record batch. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Complete.PageCuts

open Silmaril.Formats.Relational.NamedTable
open Int32ByteArrayGroup (Selection)

/-- Slot counts in each logical column. Their interpretation is independent
of the physical field order. There is one policy entry per RecordBatch. -/
structure BatchCuts where
  integers : List Nat
  octets : List Nat
  deriving DecidableEq, Repr

abbrev Policy := List BatchCuts

inductive CutError where
  | batchCount (expected actual : Nat)
  | chunkPages (batch : Nat) (column : Selection) (maximum actual : Nat)
  | totalPages (maximum actual : Nat)
  | shape (batch : Nat) (column : Selection)
  | extent (batch : Nat) (column : Selection) (expected actual : Nat)
  deriving DecidableEq, Repr

inductive Error where
  | source (cause : MixedIpc.Error)
  | cuts (cause : CutError)
  | plan (cause : PlanError)
  | schemaOnly (cause : Multi.Error)
  | sink (cause : MultiPage.Error)
  deriving DecidableEq, Repr

def BatchCuts.pageCount (cuts : BatchCuts) : Nat := cuts.integers.length + cuts.octets.length

def validateColumn (maximum batch : Nat) (column : Selection) (rows : Nat) (cuts : List Nat) :
    Except CutError Unit :=
  if maximum < cuts.length then .error (.chunkPages batch column maximum cuts.length)
  else if ¬ MultiPage.ValidCuts cuts then .error (.shape batch column)
  else if cuts.sum ≠ rows then .error (.extent batch column rows cuts.sum)
  else .ok ()

/-- Split in slot order. The caller has checked that the cuts cover the
entire column. Each list becomes one page under the original field layout. -/
def splitSlots {α : Type} : List Nat → List α → List (List α)
  | [], _ => []
  | cut :: rest, slots => slots.take cut :: splitSlots rest (slots.drop cut)

def cutInts (cuts : List Nat) : PlainV1Writer.Input → List PlainV1Writer.Input
  | .required slots => (splitSlots cuts slots).map .required
  | .optional slots => (splitSlots cuts slots).map .optional

def cutBytes (cuts : List Nat) : PlainByteArrayV1Writer.Input → List PlainByteArrayV1Writer.Input
  | .required slots => (splitSlots cuts slots).map .required
  | .optional slots => (splitSlots cuts slots).map .optional

def cutGroup (maximum ordinal : Nat) (cuts : BatchCuts) (group : Multi.Group) :
    Except CutError MultiPage.Group := do
  validateColumn maximum ordinal .int32 group.integers.numValues cuts.integers
  validateColumn maximum ordinal .byteArray group.octets.numValues cuts.octets
  return ⟨cutInts cuts.integers group.integers, cutBytes cuts.octets group.octets⟩

def cutGroups (maximum : Nat) : Nat → Policy → List Multi.Group →
    Except CutError (List MultiPage.Group)
  | _, [], [] => .ok []
  | ordinal, cut :: cuts, group :: groups => do
    let first ← cutGroup maximum ordinal cut group
    let rest ← cutGroups maximum (ordinal + 1) cuts groups
    return first :: rest
  | ordinal, cuts, groups => .error (.batchCount (ordinal + groups.length) (ordinal + cuts.length))

def groupCuts (group : MultiPage.Group) : BatchCuts := ⟨group.intCuts, group.byteCuts⟩

/-- Enforce policy extent and the total page cap before splitting columns.
Retain the same checked field and slot preparation as the original writer. -/
def prepare (limits : MultiPage.Limits) (policy : Policy) (observed : MixedIpc.Prepared) :
    Except Error MultiPage.Input := do
  if policy.length ≠ observed.batches.length then
    throw (.cuts (.batchCount observed.batches.length policy.length))
  let count := (policy.map BatchCuts.pageCount).sum
  if limits.maxPages < count then throw (.cuts (.totalPages limits.maxPages count))
  let plan ← (prepareOrdered observed).mapError .plan
  let groups ← (cutGroups limits.maxPagesPerChunk 0 policy plan.groups).mapError .cuts
  return ⟨plan.intField, plan.byteField, groups⟩

/-- Read exactly once through EOS. The zero-batch case uses the existing
schema-only writer and an empty policy. Every real batch uses the checked
multi-page writer, including an empty batch with singleton zero cuts. -/
def convert (source : MixedIpc.Limits) (limits : MultiPage.Limits) (policy : Policy) (input : KBytes) :
    Except Error Bytes := do
  let observed ← (MixedIpc.read source input).mapError .source
  match observed.batches with
  | [] =>
    if policy ≠ [] then throw (.cuts (.batchCount 0 policy.length))
    (SchemaOnly.emit limits.file observed.descriptor).mapError .schemaOnly |>.map (·.bytes)
  | _ :: _ =>
    let plan ← prepare limits policy observed
    (MultiPage.emit (physicalOrder observed.descriptor) limits plan).mapError .sink |>.map (·.bytes)

end Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Complete.PageCuts
