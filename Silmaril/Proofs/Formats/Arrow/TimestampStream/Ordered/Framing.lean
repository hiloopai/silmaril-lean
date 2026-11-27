module

public import Silmaril.Formats.Arrow.TimestampStream.Ordered.Defs
import Silmaril.Formats.Arrow.TimestampBatch.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.TimestampStream.Ordered

open Silmaril
open Silmaril.Formats.Arrow hiding Column Field decodeBatch
open Silmaril.Formats.Arrow.TimestampStream.Ordered hiding Error

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

theorem readSchema_wire {limits : Limits} {input : KBytes} {fields : List TimestampStream.Ordered.Field} {start : Nat}
    (read : readSchema limits input = .ok (fields, start)) :
    ∃ size schema,
      readEnvelope limits input 0 = .ok (.metadata size) ∧
      SchemaReader.readMessage limits (input.slice 8 size) = .ok schema ∧ schema.endianness = .little ∧
      (schema.fields.zipIdx.mapM fun (field, i) => bindField field i) = .ok fields ∧ start = 8 + size := by
  cases envelope : readEnvelope limits input 0 with
  | error => simp [readSchema, envelope, Except.mapError, Bind.bind, Except.bind] at read
  | ok tag =>
    cases tag with
    | eos => simp [readSchema, envelope, Except.mapError, Bind.bind, Except.bind] at read
    | metadata size =>
      cases observed : SchemaReader.readMessage limits (input.slice 8 size) with
      | error => simp [readSchema, envelope, observed, Except.mapError, Bind.bind, Except.bind] at read
      | ok schema =>
        by_cases little : schema.endianness = .little
        · cases columns : schema.fields.zipIdx.mapM (fun (field, i) => bindField field i) with
          | error => simp [readSchema, envelope, observed, little, columns, Except.mapError, Bind.bind, Except.bind] at read
          | ok bound =>
            have same : bound = fields ∧ 8 + size = start := by
              simpa [readSchema, envelope, observed, little, columns, Except.mapError,
                Bind.bind, Except.bind, pure, Except.pure] using read
            exact ⟨size, schema, rfl, observed, little, same.1 ▸ columns, same.2.symm⟩
        · simp [readSchema, envelope, observed, little, Except.mapError, Bind.bind, Except.bind] at read

theorem readColumns_wire (limits : Limits) (rows : Nat) (body : KBytes)
    {fields : List TimestampStream.Ordered.Field} {nodes : List FieldNode} {buffers : List Buffer} {columns : List Column}
    (read : readColumns limits rows body fields nodes buffers = .ok columns) :
    ColumnsWire limits rows body fields nodes buffers columns := by
  induction fields generalizing nodes buffers columns with
  | nil =>
    cases nodes <;> cases buffers <;> simp [readColumns] at read
    subst columns
    exact .nil
  | cons field fields ih =>
    cases nodes with
    | nil => simp [readColumns] at read
    | cons node nodes =>
      cases buffers with
      | nil => simp [readColumns] at read
      | cons bitmap buffers =>
        cases buffers with
        | nil => simp [readColumns] at read
        | cons values buffers =>
          simp only [readColumns] at read
          obtain ⟨slots, decoded, read⟩ := bind_ok read
          obtain ⟨tail, rest, read⟩ := bind_ok read
          cases Except.ok.inj read
          exact .next decoded (ih rest)

theorem columnsWire_aligned {limits : Limits} {rows : Nat} {body : KBytes} {fields : List TimestampStream.Ordered.Field}
    {nodes : List FieldNode} {buffers : List Buffer} {columns : List Column}
    (wire : ColumnsWire limits rows body fields nodes buffers columns) :
    (⟨rows, columns⟩ : Batch).Aligned fields := by
  induction wire with
  | nil => simp [Batch.Aligned]
  | @next field fields node nodes bitmap values buffers slots tail read _ ih =>
    obtain ⟨view, _, checked, _, _, slotsSize, _⟩ := TimestampBatch.decodeBatch_sound read
    obtain ⟨_, _, batch', node', bitmap', data', header, nodes', buffers', rowSize, _, _, _, _, _, viewEq⟩ :=
      TimestampBatch.batchView_layout checked
    have record : batch' = ⟨rows, [node], [bitmap, values]⟩ := by
      simpa only [columnMessage, MessageHeader.recordBatch.injEq, eq_comm] using header
    subst batch'
    change [node] = [node'] at nodes'
    have same : node = node' := List.cons.inj nodes' |>.1
    subst node'
    have size : slots.length = rows := by
      rw [slotsSize, viewEq]
      exact rowSize
    exact ⟨by simp [Batch.Aligned] at ih; simp [ih.1], by
      intro col member
      rcases List.mem_cons.mp member with rfl | later
      · simpa [TimestampBatch.Writer.tickCounts] using size
      · exact ih.2 col later⟩

private theorem checkBody_wire {limits : Limits} {batch : RecordBatch} {length : Nat} {body : KBytes}
    (checked : StreamWriter.checkBody limits ⟨.recordBatch batch, length⟩ body = .ok ()) :
    length = body.len ∧ body.wf = true ∧ body.len % 8 = 0 ∧ body.len ≤ limits.bodyBytes := by
  by_cases lengthOk : length = body.len
  · by_cases aligned : body.len % 8 = 0
    · by_cases valid : body.wf = true
      · by_cases cap : body.len ≤ limits.bodyBytes
        · exact ⟨lengthOk, valid, aligned, cap⟩
        · simp [StreamWriter.checkBody, lengthOk, aligned, valid, Nat.lt_of_not_ge cap] at checked
      · simp [StreamWriter.checkBody, lengthOk, aligned, valid] at checked
    · simp [StreamWriter.checkBody, lengthOk, aligned] at checked
  · simp [StreamWriter.checkBody, lengthOk] at checked

theorem decodeBatch_wire {limits : Limits} {fields : List TimestampStream.Ordered.Field} {batch : RecordBatch}
    {length : Nat} {body : KBytes} {decoded : Batch}
    (read : decodeBatch limits fields batch length body = .ok decoded) :
    BatchWire limits fields batch length body decoded := by
  unfold decodeBatch at read
  obtain ⟨_, checked, read⟩ := bind_ok read
  obtain ⟨exactLength, valid, aligned, bodyCap⟩ := checkBody_wire checked
  by_cases widthCap : fields.length ≤ limits.fields
  · by_cases rowCap : batch.rowCount ≤ limits.rows
    · by_cases fits : BuffersFit body.len 0 batch.buffers
      · simp only [Nat.not_lt_of_ge widthCap, Nat.not_lt_of_ge rowCap, fits, not_true_eq_false,
          ↓reduceIte] at read
        obtain ⟨columns, observed, read⟩ := bind_ok read
        cases Except.ok.inj read
        exact ⟨exactLength, valid, aligned, bodyCap, widthCap, rfl, rowCap, fits,
          readColumns_wire limits batch.rowCount body observed⟩
      · simp [Nat.not_lt_of_ge widthCap, Nat.not_lt_of_ge rowCap, fits, Bind.bind, Except.bind] at read
    · simp [Nat.not_lt_of_ge widthCap, Nat.lt_of_not_ge rowCap, Bind.bind, Except.bind] at read
  · simp [Nat.lt_of_not_ge widthCap, Bind.bind, Except.bind] at read

theorem batchWire_aligned {limits : Limits} {fields : List TimestampStream.Ordered.Field} {batch : RecordBatch}
    {length : Nat} {body : KBytes} {decoded : Batch}
    (wire : BatchWire limits fields batch length body decoded) : decoded.Aligned fields := by
  obtain ⟨_, _, _, _, _, count, _, _, columns⟩ := wire
  cases decoded
  dsimp at count
  subst count
  exact columnsWire_aligned columns

theorem readBatch_wire {limits : Limits} {input : KBytes} {fields : List TimestampStream.Ordered.Field}
    {offset size : Nat} {decoded : Batch} {next : Nat}
    (read : readBatch limits input fields offset size = .ok (decoded, next)) :
    ∃ batch length body,
      readMessage limits (input.slice (offset + 8) size) = .ok ⟨.recordBatch batch, length⟩ ∧
      readBody limits input (offset + 8 + size) length = .ok body ∧
      BatchWire limits fields batch length body decoded ∧ next = offset + 8 + size + length := by
  unfold readBatch at read
  obtain ⟨message, metadata, read⟩ := bind_ok read
  cases message with
  | mk header length =>
    cases header with
    | schema => contradiction
    | recordBatch batch =>
      obtain ⟨body, extracted, read⟩ := bind_ok read
      obtain ⟨values, complete, read⟩ := bind_ok read
      cases Except.ok.inj read
      exact ⟨batch, length, body, mapError_ok metadata, mapError_ok extracted,
        decodeBatch_wire (mapError_ok complete), rfl⟩

theorem readBatches_iff (limits : Limits) (input : KBytes) (fields : List TimestampStream.Ordered.Field)
    (remaining index offset : Nat) (batches : List Batch) :
    readBatches limits input fields remaining index offset = .ok batches ↔
      BatchesWire limits input fields remaining offset batches := by
  constructor
  · intro decoded
    induction remaining generalizing index offset batches with
    | zero =>
      cases envelope : readEnvelope limits input offset with
      | error => simp [readBatches, envelope, bind, Except.bind, Except.mapError] at decoded
      | ok value =>
        cases value with
        | metadata => simp [readBatches, envelope, bind, Except.bind, Except.mapError] at decoded
        | eos =>
          by_cases exactEnd : offset + 8 = input.len
          · have ordered : [] = batches := by
              simpa [readBatches, envelope, exactEnd, bind, Except.bind, Except.mapError] using decoded
            exact ordered ▸ .eos envelope exactEnd
          · simp [readBatches, envelope, exactEnd, bind, Except.bind, Except.mapError] at decoded
    | succ fuel ih =>
      cases envelope : readEnvelope limits input offset with
      | error => simp [readBatches, envelope, bind, Except.bind, Except.mapError] at decoded
      | ok value =>
        cases value with
        | eos =>
          by_cases exactEnd : offset + 8 = input.len
          · have ordered : [] = batches := by
              simpa [readBatches, envelope, exactEnd, bind, Except.bind, Except.mapError] using decoded
            exact ordered ▸ .eos envelope exactEnd
          · simp [readBatches, envelope, exactEnd, bind, Except.bind, Except.mapError] at decoded
        | metadata size =>
          cases batchRead : readBatch limits input fields offset size with
          | error =>
            simp [readBatches, envelope, batchRead, bind, Except.bind, Except.mapError] at decoded
          | ok result =>
            obtain ⟨slots, next⟩ := result
            cases tailRead : readBatches limits input fields fuel (index + 1) next with
            | error =>
              simp [readBatches, envelope, batchRead, tailRead, bind, Except.bind, Except.mapError]
                at decoded
            | ok tail =>
              have ordered : slots :: tail = batches := by
                simpa [readBatches, envelope, batchRead, tailRead, bind, Except.bind,
                  Except.mapError, pure, Except.pure] using decoded
              exact ordered ▸ .next envelope batchRead (ih _ _ _ tailRead)
  · intro wire
    induction wire generalizing index with
    | @eos remaining _ envelope exactEnd =>
      cases remaining <;> simp [readBatches, envelope, exactEnd, bind, Except.bind, Except.mapError]
    | next envelope batchRead _ ih =>
      simp [readBatches, envelope, batchRead, ih (index + 1), bind, Except.bind, Except.mapError,
        pure, Except.pure]

theorem read_iff (limits : Limits) (input : KBytes) (result : TimestampStream.Ordered.Stream) :
    TimestampStream.Ordered.read limits input = .ok result ↔
      input.wf = true ∧
        ∃ start, readSchema limits input = .ok (result.fields, start) ∧
          BatchesWire limits input result.fields limits.batches start result.batches := by
  constructor
  · intro accepted
    cases wellFormed : input.wf with
    | false => simp [TimestampStream.Ordered.read, wellFormed] at accepted
    | true =>
      cases schemaRead : readSchema limits input with
      | error => simp [TimestampStream.Ordered.read, wellFormed, schemaRead, bind, Except.bind] at accepted
      | ok schema =>
        obtain ⟨fields, start⟩ := schema
        cases batchRead : readBatches limits input fields limits.batches 0 start with
        | error =>
          simp [TimestampStream.Ordered.read, wellFormed, schemaRead, batchRead, bind, Except.bind] at accepted
        | ok batches =>
          have same : (⟨fields, batches⟩ : TimestampStream.Ordered.Stream) = result := by
            simpa [TimestampStream.Ordered.read, wellFormed, schemaRead, batchRead, bind, Except.bind,
              pure, Except.pure] using accepted
          subst result
          exact ⟨rfl, start, rfl, (readBatches_iff _ _ _ _ _ _ _).mp batchRead⟩
  · rintro ⟨wellFormed, start, schemaRead, wire⟩
    have batchRead := (readBatches_iff limits input result.fields limits.batches 0 start result.batches).mpr wire
    cases result
    simp [TimestampStream.Ordered.read, wellFormed, schemaRead, batchRead, bind, Except.bind, pure, Except.pure]

theorem batchesWire_aligned {limits : Limits} {input : KBytes} {fields : List TimestampStream.Ordered.Field}
    {remaining offset : Nat} {batches : List Batch}
    (wire : BatchesWire limits input fields remaining offset batches) : ∀ batch ∈ batches, batch.Aligned fields := by
  induction wire with
  | eos => simp
  | next _ record _ ih =>
    intro batch member
    rcases List.mem_cons.mp member with rfl | later
    · obtain ⟨_, _, _, _, _, layout, _⟩ := readBatch_wire record
      exact batchWire_aligned layout
    · exact ih batch later

end Silmaril.Proofs.Formats.Arrow.TimestampStream.Ordered
