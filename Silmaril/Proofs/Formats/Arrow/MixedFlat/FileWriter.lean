module

public import Silmaril.Formats.Arrow.MixedFlat.FileWriter.Defs
public import Silmaril.Formats.Arrow.MixedFlat.File.Events.Pull.Defs
public import Mathlib.Data.List.Forall2
import Silmaril.Formats.Arrow.MixedFlat.File.Thms
import Silmaril.Formats.Arrow.MixedFlat.File.Events.Thms
import Silmaril.Formats.Arrow.MixedFlat.File.Events.Pull.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.FileWriter

open Silmaril.Formats.Arrow
open MixedFlat.FileWriter
open MixedFlat.OrderedWriter (BatchInput)

private theorem assemble_checked {limits : MixedFlat.Limits} {fields : List MixedFlat.Field}
    {batches : List BatchInput} {plan : Assembly}
    (written : assemble limits fields batches = .ok plan) :
    plan.footer.fields = fields ∧
      Body.checkBudget limits.observation fields.length (batches.map (·.rowCount)).sum = .ok () ∧
      plan.footerStart + plan.footerLength + 10 = plan.bytes.len := by
  unfold assemble at written
  dsimp only at written
  split at written
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at written
  cases budget : Body.checkBudget limits.observation fields.length (batches.map (·.rowCount)).sum with
  | error fault => simp [budget, bind, Except.bind, Except.mapError] at written
  | ok accepted =>
    cases accepted
    simp only [budget, bind, Except.bind, Except.mapError] at written
    split at written
    · contradiction
    · split at written
      · contradiction
      · split at written
        · contradiction
        · simp only [pure, Except.pure, Except.ok.injEq] at written
          subst plan
          refine ⟨rfl, rfl, ?_⟩
          change 8 + _ + _ + _ + 10 = 8 + (_ + (_ + (_ + (4 + 6))))
          dsimp only
          omega

private theorem orderedReads {limits : MixedFlat.Limits} {wire : KBytes} {fields : List MixedFlat.Field}
    {blocks : List FileBlock} {observed : List MixedFlat.Observed} {index : Nat}
    (read : (blocks.zipIdx index).mapM (fun item =>
      (MixedFlat.File.readRecord limits wire fields item.1).mapError
        (fun cause => MixedFlat.File.Error.batch item.2 cause)) = .ok observed) :
    blocks.mapM (MixedFlat.File.readRecord limits wire fields) = .ok observed ∧
      blocks.length = observed.length := by
  induction blocks generalizing index observed with
  | nil =>
    have empty : [] = observed := by simpa [pure, Except.pure] using read
    subst observed
    exact ⟨rfl, rfl⟩
  | cons block rest ih =>
    cases decoded : MixedFlat.File.readRecord limits wire fields block with
    | error fault =>
      simp [List.zipIdx_cons, decoded, Except.mapError, bind, Except.bind] at read
    | ok batch =>
      have head : (MixedFlat.File.readRecord limits wire fields block).mapError
          (MixedFlat.File.Error.batch index) = .ok batch := by
        rw [decoded]
        rfl
      simp only [List.zipIdx_cons, List.mapM_cons, head, bind, Except.bind] at read
      cases tail : (rest.zipIdx (index + 1)).mapM (fun item =>
          (MixedFlat.File.readRecord limits wire fields item.1).mapError
            (fun cause => MixedFlat.File.Error.batch item.2 cause)) with
      | error fault => rw [tail] at read; contradiction
      | ok remaining =>
        obtain ⟨exactTail, length⟩ := ih tail
        rw [tail] at read
        simp only [pure, Except.pure, Except.ok.injEq] at read
        subst observed
        simp [decoded, exactTail, length, bind, Except.bind, pure, Except.pure]

theorem emit_index_exact {limits : MixedFlat.Limits} {fields : List MixedFlat.Field}
    {batches : List BatchInput} {wire : KBytes} (written : emit limits fields batches = .ok wire) :
    ∃ (plan : Assembly) (index : MixedFlat.File.Index wire) (observed : List MixedFlat.Observed),
      assemble limits fields batches = .ok plan ∧ plan.bytes = wire ∧
      MixedFlat.File.readIndex limits.observation.ipc wire = .ok index ∧
      index.footer = plan.footer ∧ index.footer.fields = fields ∧
      16 + index.schemaSize = plan.schemaEnd ∧
      index.span.start = plan.footerStart ∧ index.span.length = plan.footerLength ∧
      plan.footerStart + plan.footerLength + 10 = wire.len ∧
      index.footer.blocks.length = batches.length ∧
      index.footer.blocks.mapM (MixedFlat.File.readRecord limits wire index.footer.fields) = .ok observed ∧
      observed.map observe = batches.map BatchInput.observe := by
  unfold emit at written
  cases planned : assemble limits fields batches with
  | error fault => simp [planned, bind, Except.bind] at written
  | ok plan =>
    cases decoded : MixedFlat.File.readIndex limits.observation.ipc plan.bytes with
    | error fault => simp [planned, decoded, bind, Except.bind, Except.mapError] at written
    | ok index =>
      simp only [planned, decoded, bind, Except.bind, Except.mapError] at written
      split at written
      · simp [throw, throwThe, MonadExceptOf.throw] at written
      rename_i mismatch
      simp only [not_or, not_not] at mismatch
      obtain ⟨footer, schemaEnd, footerStart, footerLength⟩ := mismatch
      cases read : readback limits plan.bytes index.footer with
      | error fault => simp [read] at written
      | ok observed =>
        simp only [read] at written
        split at written
        · simp [throw, throwThe, MonadExceptOf.throw] at written
        rename_i wrong
        have values : observed.map observe = batches.map BatchInput.observe := by simpa using wrong
        have output : plan.bytes = wire := by simpa [pure, Except.pure] using written
        subst wire
        obtain ⟨fieldsExact, _, extent⟩ := assemble_checked planned
        obtain ⟨records, length⟩ := orderedReads read
        have count := congrArg List.length values
        simp only [List.length_map] at count
        exact ⟨plan, index, observed, rfl, rfl, decoded, footer, (congrArg MixedFlat.FileFooter.fields footer).trans fieldsExact,
          schemaEnd, footerStart, footerLength, extent, length.trans count, records, values⟩

private theorem block_offset {footerStart start : Nat} {blocks : List FileBlock} {n : Nat}
    {block : FileBlock} (fits : FileReader.BlocksFit footerStart start blocks)
    (found : blocks[n]? = some block) :
    block.offset = start + ((blocks.take n).map (fun item => item.metadataLength + item.bodyLength)).sum := by
  induction blocks generalizing start n with
  | nil => simp at found
  | cons first rest ih =>
    cases n with
    | zero =>
      simp at found
      subst block
      exact fits.1
    | succ n =>
      have later := ih fits.2.2.2.2.2.2 (by simpa using found)
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      rw [later, FileBlock.endOffset, fits.1]
      omega

theorem emit_block_offset {limits : MixedFlat.Limits} {fields : List MixedFlat.Field}
    {batches : List BatchInput} {wire : KBytes} (written : emit limits fields batches = .ok wire)
    {index : MixedFlat.File.Index wire}
    (checked : MixedFlat.File.readIndex limits.observation.ipc wire = .ok index)
    {n : Nat} {block : FileBlock} (found : index.footer.blocks[n]? = some block) :
    ∃ plan, assemble limits fields batches = .ok plan ∧
      block.offset = plan.schemaEnd +
        ((index.footer.blocks.take n).map (fun item => item.metadataLength + item.bodyLength)).sum := by
  obtain ⟨plan, decoded, _, planned, _, admitted, _, _, schemaEnd, _, _, _, _, _, _⟩ := emit_index_exact written
  have same := Except.ok.inj (admitted.symm.trans checked)
  subst decoded
  exact ⟨plan, planned, schemaEnd ▸ block_offset index.fits found⟩

theorem emit_readAt {limits : MixedFlat.Limits} {fields : List MixedFlat.Field}
    {batches : List BatchInput} {wire : KBytes} (written : emit limits fields batches = .ok wire) :
    ∃ (index : MixedFlat.File.Index wire) (observed : List MixedFlat.Observed),
      MixedFlat.File.readIndex limits.observation.ipc wire = .ok index ∧
      index.footer.fields = fields ∧ observed.map observe = batches.map BatchInput.observe ∧
      ∀ n, index.readAt limits n = .ok observed[n]? := by
  obtain ⟨_, index, observed, _, _, checked, _, fieldsExact, _, _, _, _, _, records, values⟩ :=
    emit_index_exact written
  exact ⟨index, observed, checked, fieldsExact, values, MixedFlat.File.Index.readAt_sequential index records⟩

private theorem budget_prefix {limits : ObservationLimits} {width used total : Nat}
    (bound : used ≤ total) (checked : Body.checkBudget limits width total = .ok ()) :
    Body.checkBudget limits width used = .ok () := by
  have rows : ¬ total > limits.totalRows := by
    intro exceeded
    simp [Body.checkBudget, exceeded] at checked
  have cells : ¬ width * total > limits.totalCells := by
    intro exceeded
    simp [Body.checkBudget, rows, exceeded] at checked
  have prefixRows : ¬ used > limits.totalRows := by omega
  have prefixCells : ¬ width * used > limits.totalCells := by
    have le := Nat.mul_le_mul_left width bound
    omega
  simp [Body.checkBudget, prefixRows, prefixCells]

private theorem eventDrain {limits : MixedFlat.Limits} {wire : KBytes} {fields : List MixedFlat.Field}
    {blocks : List FileBlock} {observed : List MixedFlat.Observed} {n rows : Nat}
    (read : blocks.mapM (MixedFlat.File.readRecord limits wire fields) = .ok observed)
    (budget : Body.checkBudget limits.observation fields.length
      (rows + (observed.map (·.rowCount)).sum) = .ok ()) :
    ∃ events, MixedFlat.File.Events.read.drain limits wire fields n rows blocks = .ok events ∧
      List.Forall₂ (MixedFlat.Events.Agrees (MixedFlat.Events.schema fields)) observed events := by
  induction blocks generalizing observed n rows with
  | nil =>
    have empty : [] = observed := by simpa [pure, Except.pure] using read
    subst observed
    exact ⟨[], rfl, .nil⟩
  | cons block rest ih =>
    cases decoded : MixedFlat.File.readRecord limits wire fields block with
    | error fault => simp [decoded, bind, Except.bind] at read
    | ok batch =>
      cases tail : rest.mapM (MixedFlat.File.readRecord limits wire fields) with
      | error fault => simp [decoded, tail, bind, Except.bind] at read
      | ok remaining =>
        simp [decoded, tail, bind, Except.bind, pure, Except.pure] at read
        subst observed
        let total := rows + batch.rowCount
        have accepted : Body.checkBudget limits.observation fields.length
            (total + (remaining.map (·.rowCount)).sum) = .ok () := by
          simpa [total, Nat.add_assoc] using budget
        have current := budget_prefix (Nat.le_add_right total _) accepted
        have step : ∃ event, MixedFlat.File.Events.readStep limits wire fields n rows block = .ok (total, event) := by
          unfold MixedFlat.File.Events.readStep
          split
          · rename_i fault rejected
            rw [decoded] at rejected
            contradiction
          · rename_i found passed
            have same := Except.ok.inj (passed.symm.trans decoded)
            subst found
            simp [total, current, bind, Except.bind, Except.mapError, pure, Except.pure]
        obtain ⟨event, stepped⟩ := step
        obtain ⟨readBatch, exactBatch, _, aligned⟩ := MixedFlat.File.Events.readStep_exact stepped
        have same := Except.ok.inj (exactBatch.symm.trans decoded)
        subst readBatch
        obtain ⟨events, drained, alignedTail⟩ := ih (n := n + 1) tail accepted
        refine ⟨event :: events, ?_, .cons aligned alignedTail⟩
        simp [MixedFlat.File.Events.read.drain, stepped, drained, bind, Except.bind, pure, Except.pure]

theorem emit_events {limits : MixedFlat.Limits} {fields : List MixedFlat.Field}
    {batches : List BatchInput} {wire : KBytes} (written : emit limits fields batches = .ok wire) :
    ∃ (index : MixedFlat.File.Index wire) (observed : List MixedFlat.Observed)
      (events : List (MixedFlat.Events.Batch (MixedFlat.Events.schema fields))),
      MixedFlat.File.readIndex limits.observation.ipc wire = .ok index ∧ index.footer.fields = fields ∧
      index.footer.blocks.mapM (MixedFlat.File.readRecord limits wire index.footer.fields) = .ok observed ∧
      observed.map observe = batches.map BatchInput.observe ∧
      List.Forall₂ (MixedFlat.Events.Agrees (MixedFlat.Events.schema fields)) observed events ∧
      MixedFlat.File.Events.Pull.readAll limits wire = .ok ⟨MixedFlat.Events.schema fields, ⟨events, .eos⟩⟩ := by
  obtain ⟨_, index, observed, assembly, _, checked, _, fieldsExact, _, _, _, _, _, records, values⟩ :=
    emit_index_exact written
  have count := congrArg (List.map Prod.fst) values
  simp only [List.map_map, Function.comp_def, observe, MixedFlat.OrderedWriter.BatchInput.observe] at count
  have budget : Body.checkBudget limits.observation fields.length
      (0 + (observed.map (·.rowCount)).sum) = .ok () := by
    rw [count, Nat.zero_add]
    exact (assemble_checked assembly).2.1
  subst fields
  obtain ⟨events, drained, aligned⟩ := eventDrain records budget (n := 0)
  refine ⟨index, observed, events, checked, rfl, records, values, aligned, ?_⟩
  apply (MixedFlat.File.Events.Pull.readAll_eager.mpr ?_).1
  simp [MixedFlat.File.Events.read, checked, drained, bind, Except.bind, Except.mapError, pure, Except.pure]

theorem emit_schema_exact {limits : MixedFlat.Limits} {fields : List MixedFlat.Field}
    {batches : List BatchInput} {wire : KBytes} (written : emit limits fields batches = .ok wire) :
    ∃ index : MixedFlat.File.Index wire,
      MixedFlat.File.readIndex limits.observation.ipc wire = .ok index ∧ index.footer.fields = fields ∧
      MixedFlat.readSchema limits.observation.ipc index.schemaMetadata = .ok fields ∧
      readEnvelope limits.observation.ipc wire (index.span.start - 8) = .ok .eos := by
  obtain ⟨_, index, _, _, _, indexed, _, fieldsExact, _, _, _, _, _, _, _⟩ := emit_index_exact written
  obtain ⟨_, _, embedded, ended⟩ := MixedFlat.File.readIndex_exact indexed
  exact ⟨index, indexed, fieldsExact, embedded.trans (congrArg Except.ok fieldsExact), ended⟩

end Silmaril.Proofs.Formats.Arrow.MixedFlat.FileWriter
