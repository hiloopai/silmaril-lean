module

public import Silmaril.Formats.Compression.Inflate.Defs
public import Silmaril.Formats.Compression.Zlib.Thms
public import Silmaril.Formats.Compression.Gzip.Thms
import Silmaril.Proofs.Formats.Compression.Inflate
import Silmaril.Proofs.Formats.Compression.InflateComplete
import Silmaril.Proofs.Formats.Compression.InflateOutput
import Silmaril.Raw.Formats.Compression.Inflate.Stream.MemberSpec
import Silmaril.Raw.Formats.Compression.Inflate.Stream.MemberExamples
import Silmaril.Raw.Formats.Compression.Inflate.Packed.PackedTables
import Silmaril.Raw.Formats.Compression.Inflate.Packed.PackedLookupSound
import Silmaril.Raw.Formats.Compression.Inflate.Packed.PackedFixedToken

/-!
# Streaming inflate: correctness of every call schedule

Proved (standard axioms):

* `member_sound`, `member_rejectSound`: for both versions and both container
  kinds, a schedule that finishes has emitted exactly the member decoder's
  output on the input offered so far, whatever the chunking, scheduler budgets
  or output capacities, and passes later input through; a schedule that fails
  means the decoder rejects every extension. `zlib_sound` and `gzip_sound` state
  this against `Zlib.decoder` and `Gzip.decoder`;
* `raw_sound`: the same for the raw DEFLATE machine against `Deflate.decoder`;
* `member_complete`, `zlib_complete`, `gzip_complete`, `raw_complete`: for both
  versions, every member the decoder accepts is finished by a schedule offering
  no further input (each call with a large enough scheduler budget and output
  capacity); hence `task_member_complete` and `task_raw_complete`;
* `raw_call_output`, `raw_run_output`, `member_call_output`, `member_run_output`:
  every call only appends to the output, and appends at most the call's output
  capacity (a schedule, at most the sum of its capacities), whatever the input;
* `member_calls_invariant`: after **any** schedule, finished or not, the saved
  machine denotes the member specification of all input offered so far and any
  future input;
* `member_runs_agree`: finished schedules on the same input agree, across
  versions and chunkings;
* `zlib_local_of_task`, `deflate_local_of_task`: completeness of the machine
  gives the append law of its decoder (both tasks are now proved);
* non-vacuity: `hello_chunked_done` runs the zlib 1.3.1 member machine on
  `Zlib.sampleHello` split over four calls with one- or two-byte output
  capacity and a trailing caller byte, and `hello_member_complete` is the
  completeness witness at `sampleHello`; `hello_bad_adler_rejected` checks that
  a corrupted Adler-32 is rejected;
* packed tables: `Packed.fixed_sizes`; `Packed.fixed_literalLength_root`,
  `Packed.fixed_distance_root`: for every root index the packed fixed tables and
  the canonical RFC 1951 decoder agree on meaning and reader position
  (kernel-checked finite certificates); `Packed.lookup_readBits`: a packed lookup
  is one logical read of its code bits; `Packed.fixed_token_decode` and
  `Packed.fixed_token_no_refill`: with 31 bits buffered the packed fixed-table
  token decoder agrees with the canonical token parser and pulls no input.

`zlib_local_of_task` and `deflate_local_of_task` take the (now proved) tasks as
hypotheses; their conclusions are also proved directly as `Zlib.local` and
`Deflate.local`.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate

open Silmaril.Formats.Compression.Inflate.Stream

theorem shared_zlib : shared .zlib = Zlib.decoder := Proofs.Formats.Compression.Inflate.shared_zlib

theorem shared_gzip : shared .gzip = Gzip.decoder := Proofs.Formats.Compression.Inflate.shared_gzip

theorem member_sound (version : Stream.Version) (kind : MemberSemantics.Kind) :
    (member version kind).Sound (shared kind) :=
  Proofs.Formats.Compression.Inflate.member_sound version kind

theorem member_rejectSound (version : Stream.Version) (kind : MemberSemantics.Kind) :
    (member version kind).RejectSound (shared kind) :=
  Proofs.Formats.Compression.Inflate.member_rejectSound version kind

theorem zlib_sound (version : Stream.Version) : (member version .zlib).Sound Zlib.decoder :=
  shared_zlib ▸ member_sound version .zlib

theorem gzip_sound (version : Stream.Version) : (member version .gzip).Sound Gzip.decoder :=
  shared_gzip ▸ member_sound version .gzip

theorem raw_sound (version : Stream.Version) : (raw version).Sound Deflate.decoder :=
  Proofs.Formats.Compression.Inflate.raw_sound version

/-- **Invariant of every schedule.** No completion assumption: the saved machine
denotes the member specification on the delivered input and every extension. -/
theorem member_calls_invariant (version : Stream.Version) (kind : MemberSemantics.Kind)
    (initial : List UInt8) (calls : List RawMachine.Call) :
    ∃ rest : LSBReader,
      Reservoir.Normalizes
        (MemberMachine.runCalls version (MemberMachine.start kind initial) calls).reservoir rest ∧
      ∀ future, shared kind (initial ++ RawRuns.deliveredInput calls ++ future) =
        MemberSemantics.inputView
          ((MemberMachine.runCalls version (MemberMachine.start kind initial) calls).denote
            (Reservoir.readerFeed rest future)) := by
  obtain ⟨rest, hr, _, h⟩ := MemberMachine.start_runCalls_correct_feed version kind initial calls
  exact ⟨rest, hr, h⟩

/-- Finished schedules on the same input agree, across versions and chunkings. -/
theorem member_runs_agree (v₁ v₂ : Stream.Version) (kind : MemberSemantics.Kind)
    (i₁ i₂ : List UInt8) (c₁ c₂ : List RawMachine.Call) (σ₁ σ₂ : RawState)
    (h₁ : MemberMachine.runCalls v₁ (MemberMachine.start kind i₁) c₁ = .done σ₁)
    (h₂ : MemberMachine.runCalls v₂ (MemberMachine.start kind i₂) c₂ = .done σ₂)
    (same : i₁ ++ RawRuns.deliveredInput c₁ = i₂ ++ RawRuns.deliveredInput c₂) :
    σ₁.output = σ₂.output := by
  obtain ⟨_, _, _, _, h, _⟩ :=
    MemberMachine.completed_schedules_agree v₁ v₂ kind i₁ i₂ c₁ c₂ σ₁ σ₂ h₁ h₂ same
  exact h

/-- One raw call appends at most its output capacity. -/
theorem raw_call_output (version : Stream.Version) (m : RawMachine) (call : RawMachine.Call) :
    ∃ emitted, (RawMachine.applyCall version m call).output = m.output ++ emitted ∧
      emitted.length ≤ call.capacity :=
  ⟨_, RawEmission.call_output version m call, RawEmission.call_emitted_capacity version m call⟩

theorem raw_run_output (version : Stream.Version) (m : RawMachine) (calls : List RawMachine.Call) :
    ∃ emitted, (RawMachine.runCalls version m calls).output = m.output ++ emitted ∧
      emitted.length ≤ (calls.map RawMachine.Call.capacity).sum :=
  RawEmission.run_extension version m calls

/-- One member call appends at most its output capacity. -/
theorem member_call_output (version : Stream.Version) (m : MemberMachine) (call : RawMachine.Call) :
    ∃ emitted, (MemberMachine.applyCall version m call).output = m.output ++ emitted ∧
      emitted.length ≤ call.capacity :=
  Proofs.Formats.Compression.InflateOutput.member_call_extension version m call

theorem member_run_output (version : Stream.Version) (m : MemberMachine)
    (calls : List RawMachine.Call) :
    ∃ emitted, (MemberMachine.runCalls version m calls).output = m.output ++ emitted ∧
      emitted.length ≤ (calls.map RawMachine.Call.capacity).sum :=
  Proofs.Formats.Compression.InflateOutput.member_run_extension version m calls

/-- **Completeness**: every member the shared specification accepts is finished
by the member machine, with calls that offer no further input. -/
theorem member_complete (version : Stream.Version) (kind : MemberSemantics.Kind) :
    (member version kind).Complete (shared kind) :=
  Proofs.Formats.Compression.InflateComplete.member_complete version kind

theorem zlib_complete (version : Stream.Version) : (member version .zlib).Complete Zlib.decoder :=
  Proofs.Formats.Compression.InflateComplete.zlib_complete version

theorem gzip_complete (version : Stream.Version) : (member version .gzip).Complete Gzip.decoder :=
  Proofs.Formats.Compression.InflateComplete.gzip_complete version

theorem raw_complete (version : Stream.Version) : (raw version).Complete Deflate.decoder :=
  Proofs.Formats.Compression.InflateComplete.raw_complete version

theorem task_member_complete : Task.member_complete := zlib_complete .v131

theorem task_raw_complete : Task.raw_complete := raw_complete .v131

theorem zlib_local_of_task (h : Task.member_complete) : Zlib.decoder.Local :=
  Incremental.local_of_sound_complete (zlib_sound .v131) h

theorem deflate_local_of_task (h : Task.raw_complete) : Deflate.Task.local :=
  Incremental.local_of_sound_complete (raw_sound .v131) h

/-! ## Non-vacuity -/

set_option maxRecDepth 100000 in
theorem hello_chunked_done :
    MemberMachine.runCalls .v131 (MemberMachine.start .zlib [0x78]) helloChunked =
      .done ⟨⟨0, 0, [0x07], 104⟩, ⟨Zlib.helloBytes⟩, Zlib.helloBytes⟩ := by
  rfl

set_option maxRecDepth 100000 in
theorem hello_chunked_take :
    ∃ rest : List UInt8, ∀ future,
      Zlib.decoder (Zlib.sampleHello ++ [0x07] ++ future) = some (Zlib.helloBytes, rest ++ future) :=
  have input : [0x78] ++ (member .v131 .zlib).delivered helloChunked = Zlib.sampleHello ++ [0x07] :=
    rfl
  input ▸ zlib_sound .v131 [0x78] helloChunked _ (congrArg memberStatus hello_chunked_done)

set_option maxRecDepth 100000 in
/-- `Task.member_complete` at `sampleHello`: empty calls alone finish the member. -/
theorem hello_member_complete :
    ∃ calls : List RawMachine.Call, (member .v131 .zlib).delivered calls = [] ∧
      (member .v131 .zlib).status ((member .v131 .zlib).run
        ((member .v131 .zlib).start Zlib.sampleHello) calls) = .done Zlib.helloBytes :=
  ⟨List.replicate 30 ⟨[], 64, 64⟩, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `sampleHello` with the last Adler-32 byte `15` changed to `16` is rejected. -/
theorem hello_bad_adler_rejected :
    (member .v131 .zlib).status ((member .v131 .zlib).run
      ((member .v131 .zlib).start
        [0x78, 0x9c, 0xcb, 0x48, 0xcd, 0xc9, 0xc9, 0x07, 0x00, 0x06, 0x2c, 0x02, 0x16])
      (List.replicate 30 ⟨[], 64, 64⟩)) = .failed :=
  rfl

/-! ## Packed tables -/

namespace Packed

open Silmaril.Formats.Compression.Inflate.Manual.PackedTables

theorem fixed_sizes : lenfix.size = 512 ∧ distfix.size = 32 :=
  Manual.PackedTables.fixed_sizes

set_option maxRecDepth 100000 in
theorem fixed_literalLength_root (index : Fin 512) :
    packedCodeObservation .literalLength lenfix 9 index.val =
      canonicalCodeObservation Deflate.fixedLitLenTable literalLengthMeaning 9 index.val :=
  fixed_literalLength_root_correspondence index

set_option maxRecDepth 100000 in
theorem fixed_distance_root (index : Fin 32) :
    packedCodeObservation .distance distfix 5 index.val =
      canonicalCodeObservation Deflate.fixedDistTable distanceMeaning 5 index.val :=
  fixed_distance_root_correspondence index

theorem lookup_readBits (kind : Manual.PackedTables.Kind) (table : Array Entry) (rootBits : Nat)
    (state rest : Reservoir) (entry : Entry) (codeBits : Nat) (reader : LSBReader)
    (normalizes : Reservoir.Normalizes state reader)
    (h : lookup kind table rootBits state = .found entry rest codeBits) :
    ∃ after, reader.readBits codeBits = some (state.lowBits codeBits, after) ∧
      Reservoir.Normalizes rest after :=
  Manual.PackedTables.lookup_readBits kind table rootBits state rest entry codeBits reader
    normalizes h

set_option maxRecDepth 65536 in
theorem fixed_token_decode (state : Reservoir) (reader : LSBReader)
    (normalizes : Reservoir.Normalizes state reader) (buffered : 31 ≤ state.bits) :
    TokenCorrespondence state reader (decodeFixedToken state) :=
  Manual.PackedTables.fixed_token_decode state reader normalizes buffered

set_option maxRecDepth 65536 in
theorem fixed_token_no_refill (state : Reservoir) (reader : LSBReader)
    (normalizes : Reservoir.Normalizes state reader) (buffered : 31 ≤ state.bits) :
    match decodeFixedToken state with
    | .value _ after trace | .error _ after trace =>
      after.input = state.input ∧ after.bits = state.bits - trace.total ∧
        after.consumed = state.consumed + trace.total ∧
        after.hold = state.hold / 2 ^ trace.total ∧ trace.total ≤ 31
    | .incomplete => False :=
  Manual.PackedTables.fixed_token_no_refill state reader normalizes buffered

end Packed

end Silmaril.Formats.Compression.Inflate
