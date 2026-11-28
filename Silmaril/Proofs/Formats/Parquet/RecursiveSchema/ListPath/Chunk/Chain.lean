module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Defs
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.Parquet.Footer.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Page

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk

open Silmaril.Formats
open Parquet
open Parquet.RecursiveSchema.ListPath
open Parquet.RecursiveSchema.ListPath.Chunk

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {out : β}
    (read : (first >>= next) = .ok out) : ∃ found, first = .ok found ∧ next found = .ok out := by
  cases first with
  | error => contradiction
  | ok result => exact ⟨result, rfl, read⟩

private theorem from_mapError {α ε δ : Type} {first : Except ε α} {wrap : ε → δ} {out : α}
    (read : first.mapError wrap = .ok out) : first = .ok out := by
  cases first with
  | error => simp [Except.mapError] at read
  | ok => simpa only [Except.mapError, Except.ok.injEq] using read

public theorem binding_span {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} (binding : Binding schema group) :
    let offset := binding.column.metadata.dictionaryPageOffset.getD binding.column.metadata.dataPageOffset
    (binding.span.start : Int) = offset ∧
      (binding.span.stop : Int) = offset + binding.column.metadata.totalCompressedSize ∧
      binding.span.start < binding.span.stop ∧ binding.span.stop ≤ snapshot.footer.start := by
  have fromFooter := Footer.checkDataSpan_some_iff.mp binding.originalSpan
  exact ⟨fromFooter.1, fromFooter.2.1, fromFooter.2.2.2.1, fromFooter.2.2.2.2⟩

private theorem readPrefix_wire {limits : Limits} {carrier : Carrier} {encoding : ColumnEncoding carrier.metadata}
    {frames data : List Page.Frame} {dictionary : Option RecursiveSchema.Repeated.Chunk.Dictionary}
    (read : readPrefix limits carrier encoding frames = .ok (dictionary, data)) :
    PrefixWire limits carrier dictionary frames data := by
  cases encoding with
  | plain _ offset =>
    cases Except.ok.inj read
    exact .plain offset
  | dictionary _ codec =>
    obtain ⟨⟨table, rest⟩, checked, done⟩ := bind_ok read
    cases Except.ok.inj done
    obtain ⟨rfl, tableCodec, offset, next, hasData, contents⟩ :=
      RecursiveSchema.Repeated.Chunk.readFramedDictionary_wire checked
    exact .dictionary codec tableCodec offset next hasData contents

private theorem prefix_frames {limits : Limits} {carrier : Carrier} {frames data : List Page.Frame}
    {dictionary : Option RecursiveSchema.Repeated.Chunk.Dictionary}
    (wire : PrefixWire limits carrier dictionary frames data) :
    frames = dictionary.toList.map (·.frame) ++ data := by
  cases wire <;> rfl

private theorem decodeFrames_wire {limits : Limits} {carrier : Carrier} {frames : List Page.Frame}
    {dictionary : Option RecursiveSchema.Repeated.Chunk.Dictionary}
    {ordinal : Nat} {start : State} {reversed : List ObservedPage} {out : Observation}
    (accepted : decodeFrames limits carrier (wrappers carrier.plan) dictionary frames ordinal start reversed = .ok out) :
    ∃ suffix, out.pages = reversed.reverse ++ suffix ∧ suffix.map ObservedPage.frame = frames ∧
      out.dictionary = dictionary ∧ ChainWire limits carrier dictionary start out.stop suffix := by
  induction frames generalizing ordinal start reversed out with
  | nil =>
    cases Except.ok.inj accepted
    exact ⟨[], by simp, rfl, rfl, .nil _⟩
  | cons frame frames ih =>
    simp only [decodeFrames] at accepted
    obtain ⟨decoded, page, rest⟩ := bind_ok accepted
    obtain ⟨suffix, final, original, table, chain⟩ := ih rest
    exact ⟨⟨frame, start, decoded⟩ :: suffix, by simpa [List.reverse_cons, List.append_assoc] using final,
      by simp [original], table, .cons (decodeDataPage_wire (from_mapError page)) chain⟩

private theorem check_totals {carrier : Carrier} {observed out : Observation} {frames : List Page.Frame}
    (accepted : checkTotals carrier frames observed = .ok out) :
    out = observed ∧ observed.stop.slots = carrier.slots ∧ observed.stop.rows = carrier.rows ∧
      carrier.storedSize = Int.ofNat (RecursiveSchema.Repeated.Chunk.storedChunkBytes frames) ∧
      carrier.rawSize = Int.ofNat (RecursiveSchema.Repeated.Chunk.rawChunkBytes frames) := by
  unfold checkTotals at accepted
  dsimp only at accepted
  split at accepted
  · contradiction
  · rename_i slots
    split at accepted
    · contradiction
    · rename_i rows
      split at accepted
      · contradiction
      · rename_i stored
        split at accepted
        · contradiction
        · rename_i raw
          exact ⟨(Except.ok.inj accepted).symm, Decidable.not_not.mp slots,
            Decidable.not_not.mp rows, Decidable.not_not.mp stored, Decidable.not_not.mp raw⟩

public theorem read_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {binding : Binding schema group}
    {limits : Limits} {out : Observation} (accepted : Parquet.RecursiveSchema.ListPath.Chunk.read limits binding = .ok out) :
    Wire limits (carrierOf binding) out := by
  unfold Parquet.RecursiveSchema.ListPath.Chunk.read at accepted
  dsimp only at accepted
  split at accepted
  · contradiction
  rename_i overBytes
  split at accepted
  · contradiction
  rename_i overSlots
  split at accepted
  · contradiction
  rename_i overRows
  let carrier := carrierOf binding
  obtain ⟨frames, parsed, accepted⟩ := bind_ok accepted
  obtain ⟨⟨dictionary, data⟩, prefixRead, accepted⟩ := bind_ok accepted
  obtain ⟨observed, decoded, accepted⟩ := bind_ok accepted
  obtain ⟨exactOutput, slots, rows, stored, raw⟩ := check_totals accepted
  subst out
  obtain ⟨pages, ordered, eqFrames, table, chain⟩ := decodeFrames_wire decoded
  have same : observed.pages = pages := by simpa using ordered
  have sameData : observed.pages.map ObservedPage.frame = data := same ▸ eqFrames
  have leading := readPrefix_wire (from_mapError prefixRead)
  have framesExact : observed.frames = frames := by
    rw [Observation.frames, table, sameData, ← prefix_frames leading]
  have parsedExact : Page.readChunk limits.framing carrier.source carrier.span = .ok observed.frames :=
    framesExact ▸ from_mapError parsed
  exact ⟨parsedExact, (Page.readChunk_chain parsedExact).2.2,
    framesExact ▸ sameData ▸ table ▸ leading, table ▸ same ▸ chain, slots, rows,
    framesExact ▸ stored, framesExact ▸ raw, Nat.le_of_not_gt overBytes, Nat.le_of_not_gt overSlots,
    Nat.le_of_not_gt overRows⟩

private theorem first_data_anchor {span : Footer.Span} {start stop : Nat} {frame : Page.Frame}
    {rest : List Page.Frame} (chain : Page.Chain span start stop (frame :: rest))
    (hasData : frame.payload.stop < stop) :
    ∃ first, rest.head? = some first ∧ frame.header.start = start ∧
      first.header.start = frame.payload.stop := by
  cases chain with
  | cons within remainder =>
    cases remainder with
    | nil => exact (Nat.lt_irrefl _ hasData).elim
    | cons firstWithin _ => exact ⟨_, rfl, within.headerStart, firstWithin.headerStart⟩

public theorem dictionary_anchors {limits : Limits} {carrier : Carrier} {observed : Observation}
    {table : RecursiveSchema.Repeated.Chunk.Dictionary}
    (wire : Wire limits carrier observed) (found : observed.dictionary = some table) :
    ∃ first,
      (observed.pages.map ObservedPage.frame).head? = some first ∧
      Page.readPage limits.framing carrier.source carrier.span carrier.span.start = .ok table.frame ∧
      table.frame.header.start = carrier.span.start ∧
      first.header.start = table.frame.payload.stop ∧
      carrier.metadata.dictionaryPageOffset = some (Int.ofNat table.frame.header.start) ∧
      carrier.metadata.dataPageOffset = Int.ofNat first.header.start := by
  have originalFrames : observed.frames = table.frame :: observed.pages.map ObservedPage.frame := by
    simp [Observation.frames, found]
  have framed := originalFrames ▸ wire.pages
  have leading := originalFrames ▸ found ▸ wire.leading
  cases leading with
  | dictionary _ _ offset dataOffset hasData _ =>
    obtain ⟨first, atHead, start, next⟩ := first_data_anchor framed hasData
    have header := Page.readChunk_readPage wire.framed table.frame (by simp [originalFrames])
    exact ⟨first, atHead, start ▸ header, start, next, start.symm ▸ offset, next.symm ▸ dataOffset⟩

private theorem decodeFrames_failure {limits : Limits} {carrier : Carrier} {frames : List Page.Frame}
    {dictionary : Option RecursiveSchema.Repeated.Chunk.Dictionary}
    {initial ordinal byte : Nat} {start atFailure : State} {reversed : List ObservedPage}
    {address : RecursiveSchema.Chunk.Address} {cause : PageCause}
    (refused : decodeFrames limits carrier (wrappers carrier.plan) dictionary frames initial start reversed =
      .error (.page address ordinal byte atFailure cause)) :
    address = carrier.address ∧ ∃ completed frame rest,
      frames = completed.map ObservedPage.frame ++ frame :: rest ∧
      ChainWire limits carrier dictionary start atFailure completed ∧
      ordinal = initial + completed.length ∧ byte = frame.header.start ∧
      decodeDataPage limits carrier.plan (wrappers carrier.plan) carrier.source frame atFailure
        (carrier.slots - atFailure.slots) carrier.rows carrier.codec dictionary = .error cause := by
  induction frames generalizing initial start reversed with
  | nil => contradiction
  | cons frame frames ih =>
    simp only [decodeFrames] at refused
    cases page : decodeDataPage limits carrier.plan (wrappers carrier.plan) carrier.source frame start
        (carrier.slots - start.slots) carrier.rows carrier.codec dictionary with
    | error actual =>
      simp only [page, Except.mapError, Bind.bind, Except.bind, Except.error.injEq, Error.page.injEq] at refused
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := refused
      exact ⟨rfl, [], frame, frames, rfl, .nil _, rfl, rfl, page⟩
    | ok decoded =>
      simp only [page, Except.mapError, Bind.bind, Except.bind] at refused
      obtain ⟨column, completed, failed, rest, original, chain, index, offset, error⟩ := ih refused
      refine ⟨column, ⟨frame, start, decoded⟩ :: completed, failed, rest, ?_,
        .cons (decodeDataPage_wire page) chain, ?_, offset, error⟩
      · simp [original]
      · simp only [List.length_cons]
        omega

public theorem read_page_failure {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {binding : Binding schema group}
    {limits : Limits} {address : RecursiveSchema.Chunk.Address} {ordinal byte : Nat} {start : State} {cause : PageCause}
    (refused : Parquet.RecursiveSchema.ListPath.Chunk.read limits binding = .error (.page address ordinal byte start cause)) :
    PageFailureWire limits (carrierOf binding) address ordinal byte start cause := by
  unfold Parquet.RecursiveSchema.ListPath.Chunk.read at refused
  dsimp only at refused
  split at refused
  · simp at refused
  split at refused
  · simp at refused
  split at refused
  · simp at refused
  let carrier := carrierOf binding
  change ((Page.readChunk limits.framing carrier.source carrier.span).mapError
    (Error.chunk carrier.address carrier.span ∘ ChunkCause.framing) >>= _) = _ at refused
  cases parsed : Page.readChunk limits.framing carrier.source carrier.span with
  | error => simp [parsed, Except.mapError, Bind.bind, Except.bind] at refused
  | ok frames =>
    simp only [parsed, Except.mapError, Bind.bind, Except.bind] at refused
    let wrap := fun cause : RecursiveSchema.Repeated.Chunk.DictionaryPrefixError => Error.dictionary carrier.address cause.ordinal cause.byte cause.cause
    change ((readPrefix limits carrier binding.encodings frames).mapError wrap >>= _) = _ at refused
    cases prefixRead : readPrefix limits carrier binding.encodings frames with
    | error error => simp [prefixRead, wrap, Except.mapError, Bind.bind, Except.bind] at refused
    | ok leadingResult =>
      obtain ⟨dictionary, data⟩ := leadingResult
      simp only [prefixRead, Except.mapError, Bind.bind, Except.bind] at refused
      change (decodeFrames limits carrier (wrappers carrier.plan) dictionary data dictionary.isSome.toNat {} [] >>=
        fun observed => checkTotals carrier frames observed) = _ at refused
      cases decoded : decodeFrames limits carrier (wrappers carrier.plan) dictionary data
          dictionary.isSome.toNat {} [] with
      | error actual =>
        simp only [decoded, Bind.bind, Except.bind, Except.error.injEq] at refused
        subst actual
        obtain ⟨column, completed, frame, rest, original, chain, index, offset, error⟩ :=
          decodeFrames_failure decoded
        have leading := original ▸ readPrefix_wire prefixRead
        have member : frame ∈ frames := by rw [prefix_frames leading]; simp
        exact ⟨column, dictionary, frames, completed, frame, rest, parsed, leading,
          offset.symm ▸ Page.readChunk_readPage parsed frame member, chain, index, offset, error⟩
      | ok observed =>
        simp only [decoded, Bind.bind, Except.bind] at refused
        unfold checkTotals at refused
        dsimp only at refused
        repeat' split at refused
        all_goals simp at refused

private theorem decodeFrames_dictionary {limits : Limits} {carrier : Carrier} {axes : List Nat}
    {dictionary : Option RecursiveSchema.Repeated.Chunk.Dictionary} {frames : List Page.Frame}
    {initial : Nat} {state : State} {done : List ObservedPage}
    {address : RecursiveSchema.Chunk.Address} {ordinal byte : Nat}
    {cause : RecursiveSchema.Repeated.Chunk.PageCause} :
    decodeFrames limits carrier axes dictionary frames initial state done ≠
      .error (.dictionary address ordinal byte cause) := by
  induction frames generalizing initial state done with
  | nil => simp [decodeFrames]
  | cons frame rest ih =>
    intro refused
    simp only [decodeFrames] at refused
    cases read : decodeDataPage limits carrier.plan axes carrier.source frame state
        (carrier.slots - state.slots) carrier.rows carrier.codec dictionary with
    | error => simp [read, Except.mapError, Bind.bind, Except.bind] at refused
    | ok =>
      simp only [read, Except.mapError, Bind.bind, Except.bind] at refused
      exact ih refused

public theorem read_dictionary_failure {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {binding : Binding schema group}
    {limits : Limits} {address : RecursiveSchema.Chunk.Address} {ordinal byte : Nat}
    {cause : RecursiveSchema.Repeated.Chunk.PageCause}
    (refused : Parquet.RecursiveSchema.ListPath.Chunk.read limits binding = .error (.dictionary address ordinal byte cause)) :
    DictionaryFailureWire limits (carrierOf binding) binding.encodings address ordinal byte cause := by
  unfold Parquet.RecursiveSchema.ListPath.Chunk.read at refused
  dsimp only at refused
  split at refused
  · simp at refused
  split at refused
  · simp at refused
  split at refused
  · simp at refused
  let carrier := carrierOf binding
  change ((Page.readChunk limits.framing carrier.source carrier.span).mapError
    (Error.chunk carrier.address carrier.span ∘ ChunkCause.framing) >>= _) = _ at refused
  cases parsed : Page.readChunk limits.framing carrier.source carrier.span with
  | error => simp [parsed, Except.mapError, Bind.bind, Except.bind] at refused
  | ok frames =>
    simp only [parsed, Except.mapError, Bind.bind, Except.bind] at refused
    let wrap := fun cause : RecursiveSchema.Repeated.Chunk.DictionaryPrefixError =>
      Error.dictionary carrier.address cause.ordinal cause.byte cause.cause
    change ((readPrefix limits carrier binding.encodings frames).mapError wrap >>= _) = _ at refused
    cases checked : readPrefix limits carrier binding.encodings frames with
    | error error =>
      rcases error with ⟨page, offset, reason⟩
      simp [checked, wrap, Except.mapError, Bind.bind, Except.bind] at refused
      obtain ⟨rfl, rfl, rfl, rfl⟩ := refused
      exact ⟨rfl, frames, parsed, checked⟩
    | ok admitted =>
      obtain ⟨dictionary, data⟩ := admitted
      simp only [checked, Except.mapError, Bind.bind, Except.bind] at refused
      change (decodeFrames limits carrier (wrappers carrier.plan) dictionary data dictionary.isSome.toNat {} [] >>=
        fun observed => checkTotals carrier frames observed) = _ at refused
      cases decoded : decodeFrames limits carrier (wrappers carrier.plan) dictionary data dictionary.isSome.toNat {} [] with
      | error error =>
        simp only [decoded, Bind.bind, Except.bind, Except.error.injEq] at refused
        subst error
        exact (decodeFrames_dictionary decoded).elim
      | ok observed =>
        simp only [decoded, Bind.bind, Except.bind] at refused
        unfold checkTotals at refused
        dsimp only at refused
        repeat' split at refused
        all_goals simp at refused

public theorem chain_counts {limits : Limits} {carrier : Carrier} {start stop : State} {pages : List ObservedPage}
    {dictionary : Option RecursiveSchema.Repeated.Chunk.Dictionary}
    (wire : ChainWire limits carrier dictionary start stop pages) :
    start.slots + (pages.flatMap (·.decoded.atoms)).length = stop.slots ∧
    start.rows + (pages.flatMap (·.decoded.atoms)).countP (·.repetition == 0) = stop.rows := by
  induction wire with
  | nil => simp
  | cons page _ ih =>
    obtain ⟨slots, rows⟩ := data_page_counts page
    simpa [List.flatMap_cons, List.length_append, List.countP_append, ← Nat.add_assoc, slots, rows] using ih

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk
