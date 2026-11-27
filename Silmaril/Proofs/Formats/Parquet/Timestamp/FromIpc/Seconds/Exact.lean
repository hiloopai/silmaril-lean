module

public import Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds.Defs
import Silmaril.Formats.Parquet.Timestamp.FromIpc.Thms
import Silmaril.Formats.ColumnarTimestamp.Thms
import Silmaril.Numeric.Timestamp.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.FromIpc.Seconds

open Silmaril.Formats Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds
open Silmaril.Formats.Parquet.Timestamp.FromIpc.Seconds.Internal
open Silmaril.Numeric.Timestamp (Ticks Kind TickUnit)

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (h : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, h⟩

private theorem mapError_ok {α ε η : Type} {input : Except ε α} {wrap : ε → η} {out : α}
    (h : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases h
  rfl

theorem admit_exact {binding : Arrow.TimestampBatch.Binding} {descriptor : Descriptor}
    (accepted : admit binding = .ok descriptor) :
    binding.metadata.unit = .second ∧ descriptor.unit = .millis ∧
      binding.metadata.timezone = (if descriptor.isAdjustedToUTC then some "UTC" else none) ∧
      descriptor.kind = binding.metadata.kind := by
  by_cases unit : binding.metadata.unit = .second
  · have selected : FromIpc.descriptor (millisecondBinding binding) = .ok descriptor :=
      mapError_ok (by simpa [admit, unit] using accepted)
    obtain ⟨admittedUnit, zone, meaning⟩ := FromIpc.descriptor_exact selected
    have millis : descriptor.unit = .millis := by
      cases tag : descriptor.unit <;>
        simp [tag, millisecondBinding, ColumnarTimestamp.Parquet.TimeUnit.tickUnit] at admittedUnit ⊢
    exact ⟨unit, millis, zone, meaning⟩
  · simp [admit, unit] at accepted

theorem rescale_seconds {kind : Kind} (value : Ticks kind .second) :
    value.rescale .millisecond = some ⟨value.ticks * 1000⟩ := by
  apply Ticks.rescale_eq_some_iff.mpr
  apply congrArg Ticks.mk
  change value.ticks * 1000000000 = value.ticks * 1000 * 1000000
  omega

theorem seconds_inverse {kind : Kind} (value : Ticks kind .second) :
    (⟨value.ticks * 1000⟩ : Ticks kind .millisecond).rescale .second = some value :=
  Ticks.rescale_roundtrip (rescale_seconds value)

theorem overflow_iff {kind : Kind} (value : Ticks kind .second) :
    value.toInt64 .millisecond = .error .outOfRange ↔
      value.ticks < -9223372036854775 ∨ 9223372036854775 < value.ticks := by
  simp only [Ticks.toInt64, rescale_seconds]
  split
  · rename_i range
    change -9223372036854775808 ≤ value.ticks * 1000 ∧ value.ticks * 1000 ≤ 9223372036854775807 at range
    constructor
    · intro impossible
      cases impossible
    · intro overflow
      omega
  · rename_i range
    change ¬ (-9223372036854775808 ≤ value.ticks * 1000 ∧ value.ticks * 1000 ≤ 9223372036854775807) at range
    exact ⟨fun _ => by omega, fun _ => rfl⟩

theorem rescaleSlot_overflow {binding : Arrow.TimestampBatch.Binding}
    {batch slot : Nat} (unit : binding.metadata.unit = .second)
    (value : Arrow.TimestampBatch.Value binding)
    (outside : Ticks.ticks value < -9223372036854775 ∨ 9223372036854775 < Ticks.ticks value) :
    rescaleSlot batch slot (some value) = .error (.rescale batch slot .outOfRange) := by
  obtain ⟨name, nullable, source, zone⟩ := binding
  change source = .second at unit
  subst source
  have rejected := (overflow_iff value).mpr outside
  simp [rescaleSlot, Option.mapM, rejected, Except.map, Except.mapError]

private theorem slot_exact {binding : Arrow.TimestampBatch.Binding} (unit : binding.metadata.unit = .second)
    {batch slot : Nat} {value : Option (Arrow.TimestampBatch.Value binding)}
    {converted : Option (Arrow.TimestampBatch.Value (millisecondBinding binding))}
    (read : rescaleSlot batch slot value = .ok converted) :
    converted.map Ticks.ticks = value.map (fun ticks => ticks.ticks * 1000) := by
  cases value with
  | none =>
    simp [rescaleSlot, Option.mapM, pure, Except.pure, Except.mapError] at read
    subst converted
    rfl
  | some ticks =>
    cases encoded : Ticks.toInt64 ticks .millisecond with
    | error cause =>
      simp [rescaleSlot, Option.mapM, Except.map, encoded, Except.mapError] at read
    | ok payload =>
      simp [rescaleSlot, Option.mapM, Except.map, encoded, Except.mapError] at read
      subst converted
      have denotation := ColumnarTimestamp.toInt64_eq_ok_iff.mp encoded
      have scale : binding.metadata.unit.nanosecondsPerTick = 1000000000 := by rw [unit]; rfl
      change ticks.ticks * binding.metadata.unit.nanosecondsPerTick = payload.toInt * 1000000 at denotation
      rw [scale] at denotation
      change some payload.toInt = some (ticks.ticks * 1000)
      congr 1
      omega

private theorem mapIndexed_exact {α β ε γ : Type} {f : α → Nat → Except ε β}
    {left : α → γ} {right : β → γ} {xs : List α} {ys : List β} {start : Nat}
    (step : ∀ x y index, f x index = .ok y → right y = left x)
    (done : (xs.zipIdx start).mapM (fun (x, index) => f x index) = .ok ys) :
    ys.map right = xs.map left := by
  have pairs : List.Forall₂ (fun x y => right y = left x) xs ys := by
    rw [← List.zipIdx_map_fst start xs, List.forall₂_map_left_iff]
    exact (List.mapM_eq_ok_iff_forall₂.mp done).imp fun pair y h => step pair.1 y pair.2 h
  clear done
  induction pairs with
  | nil => rfl
  | cons slot _ tail => exact congrArg₂ List.cons slot tail

theorem prepare_exact {original : Arrow.TimestampStream.Stream} {prepared : FromIpc.Source}
    (accepted : prepare original = .ok prepared) :
    original.binding.metadata.unit = .second ∧ prepared.descriptor.unit = .millis ∧
      original.binding.metadata.timezone =
        (if prepared.descriptor.isAdjustedToUTC then some "UTC" else none) ∧
      prepared.stream.binding = millisecondBinding original.binding ∧
      prepared.stream.batches.map FromIpc.Internal.counts =
        (original.batches.map FromIpc.Internal.counts).map (List.map (Option.map (· * 1000))) := by
  unfold prepare at accepted
  obtain ⟨descriptor, admitted, accepted⟩ := bind_ok accepted
  obtain ⟨batches, converted, accepted⟩ := bind_ok accepted
  cases accepted
  obtain ⟨unit, millis, zone, _⟩ := admit_exact admitted
  refine ⟨unit, millis, zone, rfl, ?_⟩
  rw [List.map_map]
  refine mapIndexed_exact (f := fun slots batch => rescaleBatch batch slots)
    (start := 0) ?_ converted
  intro original output index done
  unfold rescaleBatch at done
  simp only [FromIpc.Internal.counts, List.map_map, Function.comp_def, Option.map_map]
  exact mapIndexed_exact (f := fun slot i => rescaleSlot index i slot) (start := 0)
    (fun _ _ _ => slot_exact unit) done

theorem convert_source_error {ipc : Arrow.Limits} {limits : FromIpc.Limits} {input : KBytes}
    {cause : Arrow.TimestampStream.Error} (bytes : input.len ≤ limits.maxInputBytes)
    (failed : Arrow.TimestampStream.read ipc input = .error cause) :
    convert ipc limits input = .error (.source cause) := by
  simp [convert, Nat.not_lt.mpr bytes, failed, Except.mapError, Bind.bind, Except.bind]

theorem rescaleBatch_first_error {binding : Arrow.TimestampBatch.Binding}
    {batch slot : Nat} {value : Option (Arrow.TimestampBatch.Value binding)}
    {slots : Arrow.TimestampBatch.Column binding}
    {before after : List (Option (Arrow.TimestampBatch.Value binding) × Nat)}
    {output : Arrow.TimestampBatch.Column (millisecondBinding binding)} {cause : FromIpc.Seconds.Error}
    (split : slots.zipIdx = before ++ (value, slot) :: after)
    (earlier : before.mapM (fun (value, index) => rescaleSlot batch index value) = .ok output)
    (failed : rescaleSlot batch slot value = .error cause) :
    rescaleBatch batch slots = .error cause := by
  simp [rescaleBatch, split, earlier, failed, Bind.bind, Except.bind]

theorem convert_first_rescale_error {ipc : Arrow.Limits} {limits : FromIpc.Limits} {input : KBytes}
    {original : Arrow.TimestampStream.Stream} {annotation : Descriptor}
    {batch : Nat} {slots : Arrow.TimestampBatch.Column original.binding}
    {before after : List (Arrow.TimestampBatch.Column original.binding × Nat)}
    {output : List (Arrow.TimestampBatch.Column (millisecondBinding original.binding))}
    {cause : FromIpc.Seconds.Error} (bytes : input.len ≤ limits.maxInputBytes)
    (read : Arrow.TimestampStream.read ipc input = .ok original)
    (admitted : admit original.binding = .ok annotation)
    (split : original.batches.zipIdx = before ++ (slots, batch) :: after)
    (earlier : before.mapM (fun (items, index) => rescaleBatch index items) = .ok output)
    (failed : rescaleBatch batch slots = .error cause) :
    convert ipc limits input = .error cause := by
  simp [convert, Nat.not_lt.mpr bytes, read, prepare, admitted, split, earlier, failed,
    Except.mapError, Bind.bind, Except.bind]

theorem convert_readback {ipc : Arrow.Limits} {limits : FromIpc.Limits} {input : KBytes} {wire : Bytes}
    (written : convert ipc limits input = .ok wire) :
    ∃ original prepared bound groups,
      Arrow.TimestampStream.read ipc input = .ok original ∧ prepare original = .ok prepared ∧
      Leaf.openLeaf limits.snapshot wire 1 = .ok bound ∧
      FromIpc.Internal.readGroups limits.leaf bound = .ok groups ∧
      FromIpc.Internal.ReadbackMatches prepared bound groups ∧
      groups.map FromIpc.Internal.counts =
        (original.batches.map FromIpc.Internal.counts).map (List.map (Option.map (· * 1000))) := by
  unfold convert at written
  split at written
  · contradiction
  · obtain ⟨original, inputRead, written⟩ := bind_ok written
    obtain ⟨prepared, adapted, written⟩ := bind_ok written
    obtain ⟨output, _, written⟩ := bind_ok written
    obtain ⟨_, certified, written⟩ := bind_ok written
    cases written
    obtain ⟨bound, groups, checked, decoded, exactRead⟩ := FromIpc.certify_readback (mapError_ok certified)
    have scaled := (prepare_exact adapted).2.2.2.2
    exact ⟨original, prepared, bound, groups, mapError_ok inputRead, adapted, checked, decoded, exactRead,
      exactRead.2.2.2.2.2.2.trans scaled⟩

private theorem recover_scaled (kind : Kind) (groups : List (List (Option Int))) :
    recover kind (groups.map (List.map (Option.map (· * 1000)))) = some groups := by
  have recoverGroup (rows : List (Option Int)) :
      (rows.map (Option.map (· * 1000))).mapM (Option.mapM fun count =>
        ((⟨count⟩ : Ticks kind .millisecond).rescale .second).map Ticks.ticks) = some rows := by
    induction rows with
    | nil => rfl
    | cons row tail ih =>
      cases row with
      | none => simp [List.mapM_cons, Option.mapM, ih, pure, Bind.bind, Option.bind]
      | some count =>
        have exactInverse := seconds_inverse (⟨count⟩ : Ticks kind .second)
        simp [List.mapM_cons, Option.mapM, exactInverse, ih, Bind.bind, Option.bind]
  unfold recover
  induction groups with
  | nil => rfl
  | cons group tail ih => simp [List.mapM_cons, recoverGroup, ih, Bind.bind, Option.bind]

theorem convert_inverse {ipc : Arrow.Limits} {limits : FromIpc.Limits} {input : KBytes} {wire : Bytes}
    (written : convert ipc limits input = .ok wire) :
    ∃ original bound groups,
      Arrow.TimestampStream.read ipc input = .ok original ∧
      Leaf.openLeaf limits.snapshot wire 1 = .ok bound ∧
      FromIpc.Internal.readGroups limits.leaf bound = .ok groups ∧
      recover original.binding.metadata.kind (groups.map FromIpc.Internal.counts) =
        some (original.batches.map FromIpc.Internal.counts) := by
  obtain ⟨original, _, bound, groups, decoded, _, opened, checked, _, scaled⟩ := convert_readback written
  exact ⟨original, bound, groups, decoded, opened, checked,
    by rw [scaled]; exact recover_scaled _ _⟩

end Silmaril.Proofs.Formats.Parquet.Timestamp.FromIpc.Seconds
