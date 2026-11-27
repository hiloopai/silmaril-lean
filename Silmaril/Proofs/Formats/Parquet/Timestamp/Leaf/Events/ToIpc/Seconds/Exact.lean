module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Defs
public import Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds.Defs
import Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds.Thms
import Silmaril.Numeric.Timestamp.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Thms
import Silmaril.Formats.Arrow.TimestampStream.Writer.Thms
import Silmaril.Formats.ColumnarTimestamp.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds

open Silmaril.Formats Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Internal
open Silmaril.Numeric.Timestamp (Kind TickUnit Ticks)

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (h : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, h⟩

private theorem mapError_eq_ok {α ε η : Type} {input : Except ε α} {wrap : ε → η} {out : α} :
    input.mapError wrap = .ok out ↔ input = .ok out := by
  cases input <;> simp [Except.mapError]

theorem binding_exact (bound : Bound) :
    (binding bound).name = bound.binding.leaf.name ∧
      (binding bound).nullable = (bound.binding.leaf.repetition == some .optional) ∧
      (binding bound).metadata.unit = .second ∧
      (binding bound).metadata.timezone = (if bound.binding.descriptor.isAdjustedToUTC then some "UTC" else none) ∧
      (binding bound).metadata.kind = bound.binding.descriptor.kind :=
  ⟨rfl, rfl, rfl, rfl, ColumnarTimestamp.Parquet.Metadata.arrow_kind _ _⟩

theorem millis_nonintegral_iff {kind : Kind} (value : Ticks kind .millisecond) :
    value.rescale .second = none ↔ value.ticks % 1000 ≠ 0 := by
  unfold Ticks.rescale
  change (if value.ticks * 1000000 % 1000000000 = 0 then some _ else none) = none ↔ _
  have scale : value.ticks * 1000000 % 1000000000 = 1000000 * (value.ticks % 1000) := by
    rw [Int.mul_comm value.ticks]
    exact Int.mul_emod_mul_of_pos value.ticks 1000 (by decide)
  by_cases divisible : value.ticks % 1000 = 0
  · simp [scale, divisible]
  · have nonzero : 1000000 * (value.ticks % 1000) ≠ 0 := by omega
    simp [scale, divisible, nonzero]

theorem millis_exact {kind : Kind} {value : Ticks kind .millisecond} {seconds : Ticks kind .second}
    (read : value.rescale .second = some seconds) :
    value.denote = seconds.denote ∧ value.ticks = seconds.ticks * 1000 := by
  have meaning := Ticks.rescale_eq_some_iff.mp read
  have scaled := congrArg Ticks.ticks meaning
  change value.ticks * 1000000 = seconds.ticks * 1000000000 at scaled
  exact ⟨meaning, by omega⟩

private theorem interpretMillis {kind : Kind} {unit : TickUnit}
    (admitted : unit = .millisecond) (value : Ticks kind unit) :
    value.rescale .second = (⟨value.ticks⟩ : Ticks kind .millisecond).rescale .second := by
  subst unit
  rfl

private theorem rescaleSlot_uses_millis {bound : Bound} (unit : bound.binding.descriptor.unit = .millis)
    (value : Silmaril.Formats.Parquet.Timestamp.Page.Value bound.binding) :
    value.rescale .second =
      (⟨value.ticks⟩ : Ticks bound.binding.descriptor.kind .millisecond).rescale .second :=
  interpretMillis (congrArg ColumnarTimestamp.Parquet.TimeUnit.tickUnit unit) value

theorem rescaleSlot_nonintegral {bound : Bound} {group slot : Nat}
    (unit : bound.binding.descriptor.unit = .millis) (value : Silmaril.Formats.Parquet.Timestamp.Page.Value bound.binding)
    (offGrid : Ticks.ticks value % 1000 ≠ 0) :
    rescaleSlot bound group slot (some value) = .error (.nonintegral group slot (Ticks.ticks value)) := by
  have refused : value.rescale .second = none :=
    (rescaleSlot_uses_millis unit value).trans ((millis_nonintegral_iff _).mpr offGrid)
  simp [rescaleSlot, Option.mapM, refused]

private theorem rescaleSlot_counts {bound : Bound} {group slot : Nat}
    (unit : bound.binding.descriptor.unit = .millis)
    {original : Option (Silmaril.Formats.Parquet.Timestamp.Page.Value bound.binding)}
    {output : Option (Arrow.TimestampBatch.Value (binding bound))}
    (read : rescaleSlot bound group slot original = .ok output) :
    (original.map Ticks.ticks).mapM (fun count =>
      ((⟨count⟩ : Ticks bound.binding.descriptor.kind .millisecond).rescale .second).map Ticks.ticks) =
      some (output.map Ticks.ticks) := by
  cases original with
  | none =>
    simp [rescaleSlot, Option.mapM, Pure.pure, Except.pure] at read
    subst output
    rfl
  | some value =>
    cases exact : value.rescale .second with
    | none => simp [rescaleSlot, Option.mapM, exact] at read
    | some seconds =>
      simp [rescaleSlot, Option.mapM, exact] at read
      subst output
      have inverse := (rescaleSlot_uses_millis unit value).symm.trans exact
      simp [Option.mapM, inverse]

private theorem mapIndexed_recover {α β γ δ ε : Type} {f : α → Nat → Except ε β}
    {input : α → γ} {output : β → δ} {inverse : γ → Option δ}
    {xs : List α} {ys : List β} {start : Nat}
    (step : ∀ x y index, f x index = .ok y → inverse (input x) = some (output y))
    (done : (xs.zipIdx start).mapM (fun (x, index) => f x index) = .ok ys) :
    (xs.map input).mapM inverse = some (ys.map output) := by
  have pairs : List.Forall₂ (fun x y => inverse (input x) = some (output y)) xs ys := by
    rw [← List.zipIdx_map_fst start xs, List.forall₂_map_left_iff]
    exact (List.mapM_eq_ok_iff_forall₂.mp done).imp fun pair y h => step pair.1 y pair.2 h
  clear done
  induction pairs with
  | nil => rfl
  | cons head _ tail => simp [List.mapM_cons, head, tail, Bind.bind, Option.bind]

theorem rescaleGroups_exact {bound : Bound} {groups : List (Slots bound)}
    {batches : List (Arrow.TimestampBatch.Column (binding bound))}
    (rescaled : rescaleGroups bound groups = .ok batches) :
    bound.snapshot.metadata.schema.length = 2 ∧ bound.binding.descriptor.unit = .millis ∧
      FromIpc.Seconds.recover bound.binding.descriptor.kind (groups.map FromIpc.Internal.counts) =
        some (batches.map Arrow.TimestampBatch.Writer.tickCounts) := by
  by_cases fields : bound.snapshot.metadata.schema.length = 2
  · by_cases unit : bound.binding.descriptor.unit = .millis
    · refine ⟨fields, unit, ?_⟩
      simp only [rescaleGroups, fields, unit, ne_eq, not_true_eq_false, ↓reduceIte] at rescaled
      unfold FromIpc.Seconds.recover
      refine mapIndexed_recover (f := fun slots index => rescaleGroup bound index slots) (start := 0) ?_ rescaled
      intro slots output index done
      unfold rescaleGroup at done
      exact mapIndexed_recover (f := fun value slot => rescaleSlot bound index slot value) (start := 0)
        (fun _ _ _ => rescaleSlot_counts unit) done
    · simp [rescaleGroups, fields, unit] at rescaled
  · simp [rescaleGroups, fields] at rescaled

theorem readGroups_agree {limits : Leaf.Limits} {bound : Bound} {groups : List (Slots bound)} :
    readGroups limits bound = .ok groups ↔ FromIpc.Internal.readGroups limits bound = .ok groups := by
  simp only [readGroups, FromIpc.Internal.readGroups, List.mapM_eq_ok_iff_forall₂, mapError_eq_ok]

theorem convert_first_source_error {inputLimits : Leaf.Events.ToIpc.Limits}
    {outputLimits : Arrow.ObservationLimits} {input : Bytes} {bound : Bound}
    {before after : List Nat} {index : Nat} {prefixGroups : List (Slots bound)} {cause : Leaf.Error}
    (opened : Leaf.Events.ToIpc.openBound inputLimits input 1 = .ok bound)
    (split : List.range bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (Leaf.readGroup inputLimits.leaf bound) = .ok prefixGroups)
    (failed : Leaf.readGroup inputLimits.leaf bound index = .error cause) :
    convert inputLimits outputLimits input = .error (.source (.source (.groupFailure index cause))) := by
  have readPrefix : before.mapM (fun i =>
      (Leaf.readGroup inputLimits.leaf bound i).mapError
        (fun e => Leaf.Events.ToIpc.Seconds.Error.source (.source (.groupFailure i e)))) = .ok prefixGroups := by
    simpa only [List.mapM_eq_ok_iff_forall₂, mapError_eq_ok] using earlier
  have broken : readGroups inputLimits.leaf bound = .error (.source (.source (.groupFailure index cause))) := by
    unfold readGroups
    rw [split, List.mapM_append, readPrefix]
    simp [failed, Bind.bind, Except.bind, Except.mapError]
  simp [convert, opened, broken, Bind.bind, Except.bind, Except.mapError]

theorem rescaleGroup_first_error {bound : Bound} {group slot : Nat}
    {value : Option (Silmaril.Formats.Parquet.Timestamp.Page.Value bound.binding)} {slots : Slots bound}
    {before after : List (Option (Silmaril.Formats.Parquet.Timestamp.Page.Value bound.binding) × Nat)}
    {output : Arrow.TimestampBatch.Column (binding bound)} {cause : Leaf.Events.ToIpc.Seconds.Error}
    (split : slots.zipIdx = before ++ (value, slot) :: after)
    (earlier : before.mapM (fun (item, index) => rescaleSlot bound group index item) = .ok output)
    (failed : rescaleSlot bound group slot value = .error cause) :
    rescaleGroup bound group slots = .error cause := by
  simp [rescaleGroup, split, earlier, failed, Bind.bind, Except.bind]

theorem convert_first_rescale_error {inputLimits : Leaf.Events.ToIpc.Limits}
    {outputLimits : Arrow.ObservationLimits} {input : Bytes} {bound : Bound}
    {groups : List (Slots bound)} {group : Nat} {slots : Slots bound}
    {before after : List (Slots bound × Nat)}
    {output : List (Arrow.TimestampBatch.Column (binding bound))} {cause : Leaf.Events.ToIpc.Seconds.Error}
    (opened : Leaf.Events.ToIpc.openBound inputLimits input 1 = .ok bound)
    (read : readGroups inputLimits.leaf bound = .ok groups)
    (fields : bound.snapshot.metadata.schema.length = 2)
    (unit : bound.binding.descriptor.unit = .millis)
    (split : groups.zipIdx = before ++ (slots, group) :: after)
    (earlier : before.mapM (fun (items, i) => rescaleGroup bound i items) = .ok output)
    (failed : rescaleGroup bound group slots = .error cause) :
    convert inputLimits outputLimits input = .error cause := by
  simp [convert, opened, read, rescaleGroups, fields, unit, split, earlier, failed,
    Bind.bind, Except.bind, Except.mapError]

theorem convert_readback {inputLimits : Leaf.Events.ToIpc.Limits} {outputLimits : Arrow.ObservationLimits}
    {input : Bytes} {wire : KBytes} (written : convert inputLimits outputLimits input = .ok wire) :
    ∃ bound groups result,
      Leaf.Events.ToIpc.openBound inputLimits input 1 = .ok bound ∧
      readGroups inputLimits.leaf bound = .ok groups ∧
      bound.snapshot.metadata.schema.length = 2 ∧ bound.binding.descriptor.unit = .millis ∧
      Arrow.TimestampStream.read outputLimits.ipc wire = .ok result ∧ result.binding = binding bound ∧
      FromIpc.Seconds.recover bound.binding.descriptor.kind (groups.map FromIpc.Internal.counts) =
        some (result.batches.map Arrow.TimestampBatch.Writer.tickCounts) := by
  unfold convert at written
  obtain ⟨bound, opened, written⟩ := bind_ok written
  obtain ⟨groups, read, written⟩ := bind_ok written
  obtain ⟨batches, rescaled, written⟩ := bind_ok written
  obtain ⟨fields, millis, exactCounts⟩ := rescaleGroups_exact rescaled
  obtain ⟨result, decoded, same, counts⟩ :=
    Arrow.TimestampStream.Writer.emit_readback (mapError_eq_ok.mp written)
  exact ⟨bound, groups, result, mapError_eq_ok.mp opened, read, fields, millis, decoded, same,
    exactCounts.trans (congrArg some counts.symm)⟩

theorem ipc_roundtrip {ipc : Arrow.Limits} {outputLimits : Arrow.ObservationLimits}
    {writeLimits : FromIpc.Limits} {readLimits : Leaf.Events.ToIpc.Limits}
    {input output : KBytes} {middle : Bytes}
    (sameSnapshot : readLimits.snapshot = writeLimits.snapshot)
    (sameLeaf : readLimits.leaf = writeLimits.leaf)
    (toParquet : FromIpc.Seconds.convert ipc writeLimits input = .ok middle)
    (toIpc : convert readLimits outputLimits middle = .ok output) :
    ∃ original prepared bound groups result,
      Arrow.TimestampStream.read ipc input = .ok original ∧
      FromIpc.Seconds.prepare original = .ok prepared ∧
      Leaf.openLeaf writeLimits.snapshot middle 1 = .ok bound ∧
      FromIpc.Internal.readGroups writeLimits.leaf bound = .ok groups ∧
      FromIpc.Internal.ReadbackMatches prepared bound groups ∧
      Arrow.TimestampStream.read outputLimits.ipc output = .ok result ∧
      Arrow.TimestampStream.Writer.descriptor result.binding =
        Arrow.TimestampStream.Writer.descriptor original.binding ∧
      result.batches.map Arrow.TimestampBatch.Writer.tickCounts =
        original.batches.map Arrow.TimestampBatch.Writer.tickCounts := by
  obtain ⟨original, prepared, bound, groups, inputRead, adapted, opened, checked, agrees, _⟩ :=
    FromIpc.Seconds.convert_readback toParquet
  obtain ⟨other, otherGroups, result, otherOpen, otherRead, _, _, outputRead, resultBinding, recovered⟩ :=
    convert_readback toIpc
  have openedOther := (Leaf.Events.ToIpc.openBound_sound otherOpen).1
  rw [sameSnapshot, opened] at openedOther
  have sameBound := Except.ok.inj openedOther
  subst other
  have canonical := readGroups_agree.mp otherRead
  rw [sameLeaf, checked] at canonical
  have sameGroups := Except.ok.inj canonical
  subst otherGroups
  obtain ⟨prior, inverseBound, inverseGroups, sameInput, inverseOpen, inverseRead, inverse⟩ :=
    FromIpc.Seconds.convert_inverse toParquet
  rw [inputRead] at sameInput
  have sameOriginal := Except.ok.inj sameInput
  subst prior
  rw [opened] at inverseOpen
  have sameInverseBound := Except.ok.inj inverseOpen
  subst inverseBound
  rw [checked] at inverseRead
  have sameInverseGroups := Except.ok.inj inverseRead
  subst inverseGroups
  obtain ⟨originalUnit, _, originalZone, preparedBinding, _⟩ := FromIpc.Seconds.prepare_exact adapted
  have readback := agrees
  obtain ⟨name, nullable, _, adjusted, _, _, _⟩ := agrees
  obtain ⟨outName, outNullable, outUnit, outZone, outKind⟩ := binding_exact bound
  have sameName : (binding bound).name = original.binding.name :=
    outName.trans (name.trans (congrArg (·.name) preparedBinding))
  have sameNullable : (binding bound).nullable = original.binding.nullable := by
    rw [outNullable, nullable, preparedBinding]
    change (some (if original.binding.nullable then Formats.Parquet.Footer.Repetition.optional else .required) == some .optional) = _
    cases original.binding.nullable <;> rfl
  have sameZone : (binding bound).metadata.timezone = original.binding.metadata.timezone :=
    outZone.trans (adjusted ▸ originalZone.symm)
  have sameEpoch : bound.binding.descriptor.kind = original.binding.metadata.kind :=
    outKind.symm.trans (by simp [ColumnarTimestamp.Arrow.Metadata.kind,
      ColumnarTimestamp.Arrow.Metadata.timezoneAnnotation, sameZone])
  have sameRecovery := congrArg
    (fun kind => FromIpc.Seconds.recover kind (groups.map FromIpc.Internal.counts)) sameEpoch
  have sameCounts := Option.some.inj (recovered.symm.trans (sameRecovery.trans inverse))
  have descriptor : Arrow.TimestampStream.Writer.descriptor result.binding =
      Arrow.TimestampStream.Writer.descriptor original.binding := by
    rw [resultBinding]
    simp only [Arrow.TimestampStream.Writer.descriptor, Prod.mk.injEq]
    exact ⟨sameName, sameNullable, outUnit.trans originalUnit.symm, sameZone⟩
  exact ⟨original, prepared, bound, groups, result, inputRead, adapted, opened, checked, readback,
    outputRead, descriptor, sameCounts⟩

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds
