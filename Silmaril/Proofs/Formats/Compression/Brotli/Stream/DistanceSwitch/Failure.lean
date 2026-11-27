module

public import Silmaril.Formats.Compression.Brotli.Stream.DistanceSwitch.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Stream.DistanceSwitch.Contracts
import Silmaril.Formats.Compression.Brotli.Stream.Thms
import Silmaril.Formats.Compression.Brotli.Thms
import Silmaril.Formats.Compression.Brotli.CompressedHeader.Thms
import Silmaril.Formats.Compression.Brotli.Literal.Switch.Thms
import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Block.Thms

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Stream.DistanceSwitch

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Internal (Cursor start readWindow_sound)
open Silmaril.Formats.Compression.Brotli.Stream (Header)
open Silmaril.Formats.Compression.Brotli.Stream.Internal
open Silmaril.Formats.Compression.Brotli.Stream.DistanceSwitch
open Silmaril.Formats.Compression.Brotli.Literal.Switch (Source)

private theorem readBody_error {limits : Stream.Limits} {window index : Nat}
    {header : Header} {initial : Execute.State} {before : LSBReader} {input : List Bool}
    {error : Stream.DistanceSwitch.Error} (cursor : Cursor before input)
    (outFits : initial.output.size ≤ limits.output)
    (read : Stream.DistanceSwitch.Internal.readBody limits window index header initial before = .error error) :
    BodyFailure limits window index header initial before input error := by
  cases header with
  | terminal => cases read
  | metadata last length =>
    unfold Stream.DistanceSwitch.Internal.readBody readBodyWith readBodyWithResult at read
    cases bytes : alignedBody limits length.size before with
    | error reason =>
      simp only [bytes, Except.mapError, bind, Except.bind] at read
      cases read
      exact .envelope (.byteBody bytes)
    | ok pair =>
      obtain ⟨_, _⟩ := pair
      simp [bytes, Except.mapError, bind, Except.bind, pure, Except.pure] at read
  | raw length =>
    unfold Stream.DistanceSwitch.Internal.readBody readBodyWith readBodyWithResult at read
    dsimp only at read
    split at read
    · rename_i cap
      cases read
      exact .envelope (.outputLimit before cap)
    cases bytes : alignedBody limits length.size before with
    | error reason =>
      simp only [bytes, Except.mapError, bind, Except.bind] at read
      cases read
      exact .envelope (.byteBody bytes)
    | ok pair =>
      obtain ⟨_, _⟩ := pair
      simp [bytes, Except.mapError, bind, Except.bind, pure, Except.pure] at read
  | compressed last length =>
    unfold Stream.DistanceSwitch.Internal.readBody readBodyWith readBodyWithResult at read
    dsimp only at read
    split at read
    · rename_i cap
      cases read
      exact .envelope (.outputLimit before cap)
    cases parsed : CompressedHeader.read
        ⟨limits.mapEntries, limits.trees, limits.bits - before.totalRead⟩ before with
    | error reason =>
      simp only [parsed, Except.mapError, bind, Except.bind] at read
      cases read
      exact .envelope (.header parsed)
    | ok pair =>
      obtain ⟨header, payload⟩ := pair
      simp only [parsed, Except.mapError, bind, Except.bind] at read
      obtain ⟨_, _, _, used, tail, _, _, split, rep, count, position, _⟩ :=
        CompressedHeader.read_sound cursor.1 cursor.2.1 parsed
      unfold Stream.DistanceSwitch.Internal.readPayload at read
      cases commands : Execute.DistanceSwitch.readBlock header window length.size
          (payloadLimits limits payload) initial payload with
      | ok pair =>
        obtain ⟨_, _⟩ := pair
        simp [commands, Except.mapError, bind, Except.bind, pure, Except.pure] at read
      | error failed =>
        simp only [commands, Except.mapError, bind, Except.bind] at read
        cases read
        have found := (Execute.DistanceSwitch.readBlock_error rep count commands).2
        cases failed with
        | initialOutput _ => exact False.elim (Nat.not_lt_of_ge outFits found)
        | fuel _ _ => exact False.elim found
        | command _ _ => exact .command rfl parsed ⟨split, rep, count, position⟩ found

private theorem readBlocks_error {limits : Stream.Limits} {window fuel index : Nat}
    {initial : Execute.State} {before : LSBReader} {input : List Bool} {error : Stream.DistanceSwitch.Error}
    (cursor : Cursor before input) (outFits : initial.output.size ≤ limits.output)
    (read : readBlocksWith Error.envelope Stream.DistanceSwitch.Internal.readBody limits window fuel index initial before =
      .error error) :
    FailedBlocks limits window fuel index initial before input error := by
  induction fuel generalizing index initial before input with
  | zero => cases read; exact .fuel
  | succ fuel ih =>
    unfold readBlocksWith readBlocksWithState at read
    cases head : readHeader before with
    | error reason =>
      simp only [head, Except.mapError, bind, Except.bind, Function.comp_apply] at read
      cases read
      exact .framing head
    | ok pair =>
      obtain ⟨header, payload⟩ := pair
      simp only [head, Except.mapError, bind, Except.bind] at read
      cases cap : withinBits limits payload with
      | error reason =>
        simp only [cap] at read
        cases read
        exact .framingBits head cap
      | ok admitted =>
        cases admitted
        simp only [cap] at read
        obtain ⟨tail, _, split, next, position⟩ := readHeader_sound cursor head
        have framing : Source before payload input header.bits tail := ⟨split, next.1, next.2.1, position⟩
        cases body : Stream.DistanceSwitch.Internal.readBody limits window index header initial payload with
        | error reason =>
          simp only [body] at read
          cases read
          exact .body head cap framing body (readBody_error next outFits body)
        | ok pair =>
          obtain ⟨state, after⟩ := pair
          simp only [body] at read
          obtain ⟨fits, _, used, rest, _, _, restBits, afterCursor, afterPos⟩ :=
            readBody_sound next outFits (withinBits_ok cap) body
          have source : Source payload after tail used rest :=
            ⟨restBits, afterCursor.1, afterCursor.2.1, afterPos⟩
          have passed : PassedBlock limits window index header initial state before after input rest :=
            ⟨payload, header.bits ++ used, head, cap, body, framing.trans source⟩
          split at read
          · rename_i last
            cases endRead : finish limits after with
            | ok _ => simp only [endRead] at read; cases read
            | error reason =>
              simp only [endRead] at read
              cases read
              exact .finish passed last endRead
          · rename_i more
            exact .next passed (by simpa using more) (ih afterCursor fits read)

theorem decode_failure {limits : Stream.Limits} {input : List UInt8} {error : Stream.DistanceSwitch.Error}
    (read : Stream.DistanceSwitch.decode limits input = .error error) : FailureWire limits input error := by
  unfold Stream.DistanceSwitch.decode decodeWith decodeWithState at read
  dsimp only at read
  split at read
  · rename_i cap
    cases read
    exact .inputLimit cap
  · rename_i inputFits
    have inputFit := Nat.le_of_not_gt inputFits
    cases windowRead : Brotli.Internal.readWindow (start input) with
    | error reason =>
      simp only [windowRead, Except.mapError, bind, Except.bind, Function.comp_apply] at read
      cases read
      exact .window inputFit windowRead
    | ok pair =>
      obtain ⟨window, reader⟩ := pair
      simp only [windowRead, Except.mapError, bind, Except.bind] at read
      cases cap : withinBits limits reader with
      | error reason =>
        simp only [cap] at read
        cases read
        exact .windowBits inputFit windowRead cap
      | ok admitted =>
        cases admitted
        simp only [cap] at read
        split at read
        · rename_i windowCap
          cases read
          exact .windowLimit inputFit windowRead cap windowCap
        · rename_i windowFits
          have cursor : Cursor (start input) (bytesBits input) := by simp [Cursor, start, LSBReader.Rep, natBits]
          obtain ⟨code, tail, wire, split, next, position⟩ := readWindow_sound cursor windowRead
          exact .blocks inputFit windowRead cap (Nat.le_of_not_gt windowFits) wire
            ⟨split, next.1, next.2.1, position⟩ (readBlocks_error next (Nat.zero_le _) read)

private def Offset (origin : Nat) (input : List Bool) (bit : Nat) : Prop :=
  ∃ used suffix, input = used ++ suffix ∧ bit = origin + used.length

private theorem Offset.here (origin : Nat) (input : List Bool) : Offset origin input origin :=
  ⟨[], input, rfl, by simp⟩

private theorem Offset.prepend {before after : LSBReader} {input used tail : List Bool} {bit : Nat}
    (source : Source before after input used tail) (offset : Offset after.totalRead tail bit) :
    Offset before.totalRead input bit := by
  obtain ⟨consumed, suffix, rest, reached⟩ := offset
  exact ⟨used ++ consumed, suffix, by rw [source.split, rest, List.append_assoc],
    by rw [reached, source.position, List.length_append, Nat.add_assoc]⟩

private theorem BodyFailure.offset {limits : Stream.Limits} {window index : Nat} {framing : Header}
    {initial : Execute.State} {before : LSBReader} {input : List Bool} {error : Stream.DistanceSwitch.Error}
    (failed : BodyFailure limits window index framing initial before input error) :
    Offset before.totalRead input error.bit := by
  cases failed with
  | envelope _ => exact Offset.here _ _
  | command _ _ source failure =>
    exact Offset.prepend source (Execute.DistanceSwitch.BlockFailure.offset source.rep source.count failure).2

private theorem FailedBlocks.offset {limits : Stream.Limits} {window fuel index : Nat}
    {initial : Execute.State} {before : LSBReader} {input : List Bool} {error : Stream.DistanceSwitch.Error}
    (failed : FailedBlocks limits window fuel index initial before input error) :
    Offset before.totalRead input error.bit := by
  induction failed with
  | fuel | framing _ | framingBits _ _ => exact Offset.here _ _
  | body _ _ source _ failed => exact Offset.prepend source (BodyFailure.offset failed)
  | finish passed _ _ =>
    obtain ⟨_, _, _, _, _, source⟩ := passed.parts
    exact Offset.prepend source (Offset.here _ _)
  | next passed _ _ ih =>
    obtain ⟨_, _, _, _, _, source⟩ := passed.parts
    exact Offset.prepend source ih

theorem FailureWire.offset {limits : Stream.Limits} {input : List UInt8} {error : Stream.DistanceSwitch.Error}
    (failed : FailureWire limits input error) :
    ∃ used suffix, bytesBits input = used ++ suffix ∧ error.bit = used.length := by
  cases failed with
  | inputLimit _ | window _ _ | windowBits _ _ _ | windowLimit _ _ _ _ =>
    exact ⟨[], bytesBits input, rfl, rfl⟩
  | blocks _ _ _ _ _ source failed =>
    simpa only [Offset, start, Nat.zero_add] using Offset.prepend source (FailedBlocks.offset failed)

end Silmaril.Proofs.Formats.Compression.Brotli.Stream.DistanceSwitch
