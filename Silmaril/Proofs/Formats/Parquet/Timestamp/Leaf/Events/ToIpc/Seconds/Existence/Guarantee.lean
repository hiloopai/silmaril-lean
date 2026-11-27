module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Existence.Defs
import Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Thms
import Silmaril.Formats.Arrow.TimestampStream.Writer.Thms
import Mathlib.Data.List.Basic
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Existence

open Silmaril.Formats Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Internal
open Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Existence
open Silmaril.Numeric.Timestamp (Kind TickUnit Ticks)

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (h : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, h⟩

private theorem mapError_ok {α ε η : Type} {input : Except ε α} {wrap : ε → η} {out : α}
    (h : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases h
  rfl

theorem emit_iff_sink {limits : Arrow.ObservationLimits} {original : Arrow.TimestampStream.Stream}
    {wire : KBytes} :
    Arrow.TimestampStream.Writer.emit limits original.binding original.batches = .ok wire ↔
      SinkAdmits limits original wire := by
  constructor
  · intro emitted
    unfold Arrow.TimestampStream.Writer.emit at emitted
    obtain ⟨encoded, serialized, emitted⟩ := bind_ok emitted
    obtain ⟨result, verified, emitted⟩ := bind_ok emitted
    split at emitted
    · cases emitted
      exact ⟨serialized, result, mapError_ok verified, by assumption⟩
    · contradiction
  · rintro ⟨serialized, result, decoded, metadata, slots⟩
    simp [Arrow.TimestampStream.Writer.emit, serialized, decoded, metadata, slots,
      Bind.bind, Except.bind, Except.mapError, Pure.pure, Except.pure]

private theorem mapIndexed_observe {α β γ δ ε : Type} {f : α → Nat → Except ε β}
    {input : α → γ} {output : β → δ} {inverse : γ → Option δ}
    (step : ∀ x index, (f x index).toOption.map output = inverse (input x))
    (xs : List α) (start : Nat) :
    ((xs.zipIdx start).mapM (fun (x, index) => f x index)).toOption.map (List.map output) =
      (xs.map input).mapM inverse := by
  induction xs generalizing start with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.zipIdx_cons, List.mapM_cons, List.map_cons]
    rw [← step head start, ← ih (start + 1)]
    cases f head start <;> cases (tail.zipIdx (start + 1)).mapM (fun (x, i) => f x i) <;> rfl

private theorem slot_observe {bound : Bound} (unit : bound.binding.descriptor.unit = .millis)
    (group slot : Nat) (original : Option (Page.Value bound.binding)) :
    (rescaleSlot bound group slot original).toOption.map (Option.map Ticks.ticks) =
      (original.map Ticks.ticks).mapM (fun count =>
        ((⟨count⟩ : Ticks bound.binding.descriptor.kind .millisecond).rescale .second).map Ticks.ticks) := by
  cases original with
  | none => rfl
  | some value =>
    have interpret {kind : Kind} {source : TickUnit} (tick : Ticks kind source) (h : source = .millisecond) :
        tick.rescale .second = (⟨tick.ticks⟩ : Ticks kind .millisecond).rescale .second := by
      subst source
      rfl
    have same := interpret value (congrArg ColumnarTimestamp.Parquet.TimeUnit.tickUnit unit)
    cases scaled : value.rescale .second <;>
      simp [rescaleSlot, Option.mapM, ← same, scaled, Except.toOption]

theorem rescale_of_recovery {bound : Bound} {groups : List (Slots bound)}
    {counts : List (List (Option Int))}
    (fields : bound.snapshot.metadata.schema.length = 2)
    (unit : bound.binding.descriptor.unit = .millis)
    (recover : FromIpc.Seconds.recover bound.binding.descriptor.kind (groups.map FromIpc.Internal.counts) =
      some counts) :
    ∃ batches, rescaleGroups bound groups = .ok batches ∧
      batches.map Arrow.TimestampBatch.Writer.tickCounts = counts := by
  have observed : (rescaleGroups bound groups).toOption.map (List.map Arrow.TimestampBatch.Writer.tickCounts) =
      FromIpc.Seconds.recover bound.binding.descriptor.kind (groups.map FromIpc.Internal.counts) := by
    simp only [rescaleGroups, fields, unit, ne_eq, not_true_eq_false, ↓reduceIte]
    unfold FromIpc.Seconds.recover
    apply mapIndexed_observe (f := fun slots i => rescaleGroup bound i slots)
    intro slots index
    unfold rescaleGroup
    exact mapIndexed_observe (f := fun value i => rescaleSlot bound index i value)
      (fun slotValue slotIndex => slot_observe unit index slotIndex slotValue) slots 0
  rw [recover] at observed
  cases rescaled : rescaleGroups bound groups with
  | error _ => simp [rescaled, Except.toOption] at observed
  | ok batches => exact ⟨batches, rfl, by simpa [rescaled, Except.toOption] using observed⟩

private theorem stream_eq {left right : Arrow.TimestampStream.Stream}
    (sameBinding : left.binding = right.binding)
    (slots : left.batches.map Arrow.TimestampBatch.Writer.tickCounts =
      right.batches.map Arrow.TimestampBatch.Writer.tickCounts) : left = right := by
  obtain ⟨leftBinding, leftBatches⟩ := left
  obtain ⟨rightBinding, rightBatches⟩ := right
  change leftBinding = rightBinding at sameBinding
  subst rightBinding
  have injective : Function.Injective (@Arrow.TimestampBatch.Writer.tickCounts leftBinding) := by
    unfold Arrow.TimestampBatch.Writer.tickCounts
    apply List.map_injective_iff.mpr
    apply Option.map_injective
    intro a b same
    cases a
    cases b
    cases same
    rfl
  have same : leftBatches = rightBatches := List.map_injective_iff.mpr injective slots
  cases same
  rfl

private theorem binding_from_image {original : Arrow.TimestampStream.Stream} {prepared : FromIpc.Source}
    {bound : Bound} {groups : List (Slots bound)}
    (adapted : FromIpc.Seconds.prepare original = .ok prepared)
    (agrees : FromIpc.Internal.ReadbackMatches prepared bound groups) :
    binding bound = original.binding := by
  obtain ⟨originalUnit, _, originalZone, preparedBinding, _⟩ := FromIpc.Seconds.prepare_exact adapted
  obtain ⟨name, nullable, _, adjusted, _, _, _⟩ := agrees
  obtain ⟨outName, outNullable, outUnit, outZone, _⟩ := binding_exact bound
  have sameName : (binding bound).name = original.binding.name :=
    outName.trans (name.trans (congrArg (·.name) preparedBinding))
  have sameNullable : (binding bound).nullable = original.binding.nullable := by
    rw [outNullable, nullable, preparedBinding]
    change (some (if original.binding.nullable then Silmaril.Formats.Parquet.Footer.Repetition.optional
      else .required) == some .optional) = _
    cases original.binding.nullable <;> rfl
  have sameUnit := outUnit.trans originalUnit.symm
  have sameZone := outZone.trans (adjusted ▸ originalZone.symm)
  generalize binding bound = left at sameName sameNullable sameUnit sameZone ⊢
  generalize original.binding = right at sameName sameNullable sameUnit sameZone ⊢
  obtain ⟨_, _, ⟨_, _⟩⟩ := left
  obtain ⟨_, _, ⟨_, _⟩⟩ := right
  cases sameName
  cases sameNullable
  cases sameUnit
  cases sameZone
  rfl

theorem rescale_writer_image {ipc : Arrow.Limits} {writeLimits : FromIpc.Limits}
    {readLimits : Leaf.Events.ToIpc.Limits} {input : KBytes} {middle : Bytes}
    (sameSnapshot : readLimits.snapshot = writeLimits.snapshot)
    (sameLeaf : readLimits.leaf = writeLimits.leaf)
    (written : FromIpc.Seconds.convert ipc writeLimits input = .ok middle) :
    ∃ original bound groups batches,
      Arrow.TimestampStream.read ipc input = .ok original ∧
      Leaf.openLeaf readLimits.snapshot middle 1 = .ok bound ∧
      readGroups readLimits.leaf bound = .ok groups ∧
      rescaleGroups bound groups = .ok batches ∧
      (⟨binding bound, batches⟩ : Arrow.TimestampStream.Stream) = original ∧
      bound.snapshot.groupCount = original.batches.length ∧
      bound.snapshot.metadata.numRows.toNat = FromIpc.totalRows original := by
  obtain ⟨original, prepared, bound, groups, source, adapted, opened, decoded, fields, agrees, _⟩ :=
    FromIpc.Seconds.convert_image written
  obtain ⟨_, millis, _, _, scaled⟩ := FromIpc.Seconds.prepare_exact adapted
  have unit := agrees.2.2.1.trans millis
  have sameBinding := binding_from_image adapted agrees
  obtain ⟨prior, inverseBound, inverseGroups, sameInput, inverseOpen, inverseRead, inverse⟩ :=
    FromIpc.Seconds.convert_inverse written
  rw [source] at sameInput
  have priorEq := Except.ok.inj sameInput
  subst prior
  rw [opened] at inverseOpen
  have boundsEq := Except.ok.inj inverseOpen
  subst inverseBound
  rw [decoded] at inverseRead
  have groupsEq := Except.ok.inj inverseRead
  subst inverseGroups
  have kindEq := (binding_exact bound).2.2.2.2.symm.trans
    (congrArg (fun field : Arrow.TimestampBatch.Binding => field.metadata.kind) sameBinding)
  have recovery := (congrArg (fun kind => FromIpc.Seconds.recover kind (groups.map FromIpc.Internal.counts))
    kindEq).trans inverse
  obtain ⟨batches, rescaled, counts⟩ := rescale_of_recovery fields unit recovery
  have sameLengths : prepared.stream.batches.map List.length = original.batches.map List.length := by
    have lengths := congrArg (List.map List.length) scaled
    simpa [List.map_map, Function.comp_def, FromIpc.Internal.counts] using lengths
  have groupCount : prepared.stream.batches.length = original.batches.length := by
    simpa using congrArg List.length sameLengths
  have rowCount : FromIpc.totalRows prepared.stream = FromIpc.totalRows original :=
    congrArg List.sum sameLengths
  have total := congrArg Int.toNat agrees.2.2.2.2.2.1
  refine ⟨original, bound, groups, batches, source, sameSnapshot ▸ opened,
    readGroups_agree.mpr (sameLeaf ▸ decoded), rescaled, stream_eq sameBinding counts,
    agrees.2.2.2.2.1.trans groupCount, ?_⟩
  simpa [rowCount] using total

theorem roundtrip_of_sink {ipc : Arrow.Limits} {writeLimits : FromIpc.Limits}
    {readLimits : Leaf.Events.ToIpc.Limits} {outputLimits : Arrow.ObservationLimits}
    {input : KBytes} {middle : Bytes}
    (sameSnapshot : readLimits.snapshot = writeLimits.snapshot)
    (sameLeaf : readLimits.leaf = writeLimits.leaf)
    (written : FromIpc.Seconds.convert ipc writeLimits input = .ok middle) :
    ∃ original, Arrow.TimestampStream.read ipc input = .ok original ∧
      ∀ wire, MiddleBounds readLimits middle original → SinkAdmits outputLimits original wire →
        convert readLimits outputLimits middle = .ok wire ∧
        Arrow.TimestampStream.read outputLimits.ipc wire = .ok original := by
  obtain ⟨original, bound, groups, batches, source, checked, decoded, rescaled, same, count, rows⟩ :=
    rescale_writer_image sameSnapshot sameLeaf written
  refine ⟨original, source, fun wire middleBounds sink => ?_⟩
  have checkedModern : Leaf.openLeafWith .modernOnly readLimits.snapshot middle 1 = .ok bound := checked
  have opened : Leaf.Events.ToIpc.openBound readLimits middle 1 = .ok bound := by
    simp only [Leaf.Events.ToIpc.openBound, Leaf.Events.ToIpc.openBoundWith, Leaf.Events.ToIpc.openBoundUsing,
      checkedModern, count, rows, Nat.not_lt.mpr middleBounds.fileBytes, Nat.not_lt.mpr middleBounds.groups,
      Nat.not_lt.mpr middleBounds.rows, ↓reduceIte, Bind.bind, Except.bind, Except.mapError]
  have admitted := emit_iff_sink.mpr sink
  have emitted : Arrow.TimestampStream.Writer.emit outputLimits (binding bound) batches = .ok wire :=
    (congrArg (fun stream : Arrow.TimestampStream.Stream =>
      Arrow.TimestampStream.Writer.emit outputLimits stream.binding stream.batches) same).trans admitted
  obtain ⟨result, read, binding, counts⟩ := Arrow.TimestampStream.Writer.emit_readback admitted
  refine ⟨?_, (stream_eq binding counts) ▸ read⟩
  simp [convert, opened, decoded, rescaled, emitted, Bind.bind, Except.bind, Except.mapError]

theorem roundtrip_exists {ipc : Arrow.Limits} {writeLimits : FromIpc.Limits}
    {readLimits : Leaf.Events.ToIpc.Limits} {outputLimits : Arrow.ObservationLimits}
    {input : KBytes} {middle : Bytes}
    (sameSnapshot : readLimits.snapshot = writeLimits.snapshot)
    (sameLeaf : readLimits.leaf = writeLimits.leaf)
    (written : FromIpc.Seconds.convert ipc writeLimits input = .ok middle)
    (fits : ∀ original, Arrow.TimestampStream.read ipc input = .ok original →
      MiddleBounds readLimits middle original)
    (admitted : ∀ original, Arrow.TimestampStream.read ipc input = .ok original →
      ∃ output, SinkAdmits outputLimits original output) :
    ∃ original output, Arrow.TimestampStream.read ipc input = .ok original ∧
      convert readLimits outputLimits middle = .ok output ∧
      Arrow.TimestampStream.read outputLimits.ipc output = .ok original := by
  obtain ⟨original, decoded, guarantee⟩ := roundtrip_of_sink sameSnapshot sameLeaf written
  obtain ⟨output, sink⟩ := admitted original decoded
  exact ⟨original, output, decoded, guarantee output (fits original decoded) sink⟩

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds.Existence
