module

public import Silmaril.Formats.Compression.Inflate.Stream.Parser
public import Silmaril.Raw.Formats.Compression.Inflate.Stream.Bits
public import Silmaril.Raw.Formats.Compression.Bits.Bit
public import Silmaril.Formats.Compression.Bits.Bitstream
public import Silmaril.Raw.Formats.Compression.Deflate.Huffman
public import Silmaril.Formats.Compression.Deflate.Decompress
public import Silmaril.Raw.Formats.Compression.Deflate.Stored
public import Silmaril.Raw.Formats.Compression.Deflate.WithHistory
public import Silmaril.Formats.Compression.Deflate.Compress
public import Silmaril.Raw.Formats.Compression.Deflate.LZ77
public import Silmaril.Raw.Formats.Compression.Bits.ByteFields
public import Silmaril.Raw.Formats.Compression.Checksum.Adler32
public import Silmaril.Raw.Formats.Compression.Checksum.CRC32
public import Silmaril.Raw.Formats.Compression.Zlib.Basic
public import Silmaril.Raw.Formats.Compression.Zlib.Take
public import Silmaril.Raw.Formats.Compression.Zlib.Dictionary
public import Silmaril.Raw.Formats.Compression.Gzip.Basic

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Stream.Parser`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream

open Silmaril.Formats.Compression

namespace Parser

theorem eval_bind {α β : Type} (parser : Parser α) (next : α → Parser β) (reader : LSBReader) :
    (parser.bind next).eval reader =
      match parser.eval reader with
      | .error error => .error error
      | .ok (value, rest) => (next value).eval rest := by
  induction parser generalizing reader with
  | pure value => rfl
  | fail error => rfl
  | bits count error continuation ih =>
    simp only [bind, eval]
    cases read : reader.readBits count with
    | none => rfl
    | some pair =>
      rcases pair with ⟨value, rest⟩
      exact ih value rest
  | align continuation ih => exact ih reader.alignToByte

theorem eval_readBits (count : Nat) (error : Deflate.DecompressError) (reader : LSBReader) :
    (readBits count error).eval reader =
      match reader.readBits count with
      | none => .error error
      | some (value, rest) => .ok (value, rest) := by
  unfold readBits eval
  cases reader.readBits count <;> rfl

theorem eval_alignToByte (reader : LSBReader) :
    alignToByte.eval reader = .ok ((), reader.alignToByte) := rfl

end Parser

namespace Parser

/-- Every completed prefix remains valid under every future input extension.
In particular, `needInput` retains the continuation before its uncompleted
read, together with all physically prefetched bytes. -/
theorem run_correct_feed {α : Type} (fuel : Nat) (parser : Parser α)
    {state : Reservoir} {reader : LSBReader} (h : Reservoir.Normalizes state reader) :
    ∃ rest, Reservoir.Normalizes (run fuel parser state).state rest ∧
      ∀ added, parser.eval (Reservoir.readerFeed reader added) =
        (run fuel parser state).observe (Reservoir.readerFeed rest added) := by
  induction fuel generalizing parser state reader with
  | zero => exact ⟨reader, h, fun _ => rfl⟩
  | succ fuel ih =>
    cases parser with
    | pure value => exact ⟨reader, h, fun _ => rfl⟩
    | fail error => exact ⟨reader, h, fun _ => rfl⟩
    | bits count error next =>
      cases read : Reservoir.readBits count state with
      | needInput filled =>
        simp only [run, read, RunResult.state, RunResult.observe]
        exact ⟨reader, h.readBits_needInput read, fun _ => rfl⟩
      | value value middle =>
        obtain ⟨reader1, read1, hmiddle⟩ := h.readBits read
        obtain ⟨rest, hrest, observations⟩ := ih (next value) hmiddle
        simp only [run, read]
        refine ⟨rest, hrest, ?_⟩
        intro added
        simp only [eval, Reservoir.readerFeed_readBits count read1 added]
        exact observations added
    | align next =>
      obtain ⟨rest, hrest, observations⟩ := ih next h.byteBits
      refine ⟨rest, hrest, ?_⟩
      intro added
      change next.eval (Reservoir.readerFeed reader.alignToByte added) = _
      exact observations added

/-- Successful, erroneous and suspended observations all agree with canonical
evaluation, with a canonical reader related to the retained reservoir. -/
theorem run_correct {α : Type} (fuel : Nat) (parser : Parser α)
    {state : Reservoir} {reader : LSBReader} (h : Reservoir.Normalizes state reader) :
    ∃ rest, Reservoir.Normalizes (run fuel parser state).state rest ∧
      parser.eval reader = (run fuel parser state).observe rest := by
  obtain ⟨rest, hrest, observations⟩ := run_correct_feed fuel parser h
  exact ⟨rest, hrest, by simpa only [Reservoir.readerFeed_nil] using observations []⟩

/-! These kernel-reduced witnesses check that the interface suspends after a
partial refill and then completes the same little-endian read on resumption. -/

theorem run_partial_read :
    run 1 (readBits 16 .decodeOverrun) (Reservoir.ofBytes [0x41]) =
      .needInput (readBits 16 .decodeOverrun) ⟨0x41, 8, [], 0⟩ := rfl

theorem run_resumed_read :
    run 2 (readBits 16 .decodeOverrun)
        ((⟨0x41, 8, [], 0⟩ : Reservoir).feed [0x42]) =
      .done 0x4241 ⟨0, 0, [], 16⟩ := rfl

end Parser
end Silmaril.Formats.Compression.Inflate.Stream
