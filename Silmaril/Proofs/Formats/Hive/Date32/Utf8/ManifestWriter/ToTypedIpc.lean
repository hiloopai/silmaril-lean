module

public import Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.ToTypedIpc.Defs
import Silmaril.Formats.Arrow.DateUtf8Stream.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Date32.Utf8.ManifestWriter.ToTypedIpc

open Silmaril.Formats Silmaril.Formats.Hive Silmaril.Formats.Parquet Silmaril.Relational
open Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter
open Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.ToTypedIpc
open Int32ByteArrayGroup.File (Value)
open Silmaril.Formats.Arrow (ObservationLimits)

private theorem decodeText_exact {value : Bytes} {text : String}
    (decoded : decodeText value = .ok text) : text.toUTF8 = value.data := by
  unfold decodeText at decoded
  split at decoded <;> cases decoded
  rfl

private theorem decodeSlot_exact {slot : Option Bytes} {text : Option String}
    (decoded : Option.mapM decodeText slot = .ok text) :
    text.map String.toUTF8 = slot.map Bytes.data := by
  cases slot with
  | none => cases decoded; rfl
  | some value =>
    cases decodedText : decodeText value with
    | error cause => simp [Option.mapM, decodedText, Functor.map, Except.map] at decoded
    | ok result =>
      have same : some result = text := by
        simpa [Option.mapM, decodedText, Functor.map, Except.map] using decoded
      subst text
      exact congrArg some (decodeText_exact decodedText)

private theorem mapM_observe {α β γ Failure : Type*} (f : α → Except Failure β) (src : α → γ)
    (dst : β → γ) (exactSlot : ∀ a b, f a = .ok b → dst b = src a)
    (xs : List α) {ys : List β} (checked : xs.mapM f = .ok ys) :
    ys.map dst = xs.map src := by
  induction xs generalizing ys with
  | nil => cases checked; rfl
  | cons x xs ih =>
    cases head : f x with
    | error cause => simp [List.mapM_cons, head, Bind.bind, Except.bind] at checked
    | ok y =>
      cases tail : xs.mapM f with
      | error cause => simp [List.mapM_cons, head, tail, Bind.bind, Except.bind] at checked
      | ok rest =>
        have same : y :: rest = ys := by
          simpa [List.mapM_cons, head, tail, Bind.bind, Except.bind, Pure.pure, Except.pure] using checked
        subst ys
        exact congrArg₂ List.cons (exactSlot x y head) (ih tail)

private theorem prepareBatch_exact {layout : Schema} {input : ToTypedIpc.Batch layout} {index : Nat}
    {batch : Arrow.DateUtf8Stream.Batch} (checked : prepareBatch layout input index = .ok batch) :
    observe batch = observeSource layout input := by
  rcases slotValues : slots layout input with ⟨dates, texts⟩
  cases decoded : texts.mapM (Option.mapM decodeText) with
  | error cause => simp [prepareBatch, slotValues, decoded, Except.mapError, Bind.bind, Except.bind] at checked
  | ok strings =>
    have same : (⟨dates, strings⟩ : Arrow.DateUtf8Stream.Batch) = batch := by
      simpa [prepareBatch, slotValues, decoded, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        using checked
    subst batch
    simp only [observe, observeSource, slotValues, Prod.mk.injEq, true_and]
    exact mapM_observe _ _ _ (fun _ _ => decodeSlot_exact) texts decoded

theorem prepare_exact {layout : Schema} {trace : Trace layout} {batches : List Arrow.DateUtf8Stream.Batch}
    (checked : prepare layout trace = .ok batches) :
    batches.map observe = trace.batches.map (observeSource layout) := by
  have result := mapM_observe (fun (entry : ToTypedIpc.Batch layout × Nat) =>
    prepareBatch layout entry.1 entry.2) (fun entry => observeSource layout entry.1) observe
    (fun _ _ => prepareBatch_exact) trace.batches.zipIdx checked
  rw [result]
  simpa only [List.map_map, Function.comp_def] using
    congrArg (List.map (observeSource layout)) (List.zipIdx_map_fst 0 trace.batches)

theorem convert_outcome (layout : Schema) (options : PartitionPath.Options) (limits : Limits)
    (ipc : ObservationLimits) (keep : Scan.Predicate layout.keys.schema.toScan Value) (files : List File) :
    convert layout options limits ipc keep files =
      match readSelected layout options limits (projection layout) keep files with
      | .error cause => .error (.admission cause)
      | .ok trace =>
        if trace.termination = .eos then
          (prepare layout trace).bind fun batches => (Arrow.DateUtf8Stream.emit ipc (schema layout) batches).mapError .writer
        else .error (.source trace.termination) := by
  cases admitted : readSelected layout options limits (projection layout) keep files with
  | error cause => simp [convert, admitted, Except.mapError, Bind.bind, Except.bind]
  | ok trace =>
    by_cases eos : trace.termination = .eos <;>
      simp [convert, admitted, encodeTrace, eos, Except.mapError, Bind.bind, Except.bind]

theorem convert_readback {layout : Schema} {options : PartitionPath.Options} {limits : Limits}
    {ipc : ObservationLimits} {keep : Scan.Predicate layout.keys.schema.toScan Value} {files : List File}
    {wire : KBytes} (written : convert layout options limits ipc keep files = .ok wire) :
    ∃ (trace : Trace layout) (batches : List Arrow.DateUtf8Stream.Batch),
      readSelected layout options limits (projection layout) keep files = .ok trace ∧
      trace.termination = .eos ∧
      Arrow.DateUtf8Stream.read ipc wire = .ok ⟨schema layout, batches⟩ ∧
      batches.map observe = trace.batches.map (observeSource layout) := by
  rw [convert_outcome] at written
  cases admitted : readSelected layout options limits (projection layout) keep files with
  | error cause => simp [admitted] at written
  | ok trace =>
    by_cases eos : trace.termination = .eos
    · cases ready : prepare layout trace with
      | error cause => simp [admitted, eos, ready, Except.bind] at written
      | ok batches =>
        cases emitted : Arrow.DateUtf8Stream.emit ipc (schema layout) batches with
        | error cause => simp [admitted, eos, ready, emitted, Except.bind, Except.mapError] at written
        | ok bytes =>
          have equal : bytes = wire := by
            simpa [admitted, eos, ready, emitted, Except.bind, Except.mapError] using written
          subst wire
          exact ⟨trace, batches, rfl, eos, Arrow.DateUtf8Stream.emit_readback emitted, prepare_exact ready⟩
    · simp [admitted, eos] at written

end Silmaril.Proofs.Formats.Hive.Date32.Utf8.ManifestWriter.ToTypedIpc
