module

public import Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch.Defs
import Silmaril.Proofs.Formats.Compression.Brotli.Stream.LiteralSwitch.Contracts
import Silmaril.Formats.Compression.Brotli.Stream.Thms
import Silmaril.Formats.Compression.Brotli.Thms
import Silmaril.Formats.Compression.Brotli.CompressedHeader.Thms
import Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch.Thms

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Stream.LiteralSwitch

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Internal (Cursor start readWindow_sound)
open Silmaril.Formats.Compression.Brotli.Stream (Header)
open Silmaril.Formats.Compression.Brotli.Stream.Internal
open Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch

private def Offset (origin : Nat) (input : List Bool) (bit : Nat) : Prop :=
  ∃ used suffix, input = used ++ suffix ∧ bit = origin + used.length

private theorem Offset.here (origin : Nat) (input : List Bool) : Offset origin input origin :=
  ⟨[], input, rfl, by simp⟩

private theorem Offset.prepend {before after bit : Nat} {input used tail : List Bool}
    (split : input = used ++ tail) (position : after = before + used.length)
    (offset : Offset after tail bit) : Offset before input bit := by
  obtain ⟨consumed, suffix, rest, reached⟩ := offset
  exact ⟨used ++ consumed, suffix, by rw [split, rest, List.append_assoc],
    by rw [reached, position, List.length_append, Nat.add_assoc]⟩

private theorem run_not_initialOutput {header : CompressedHeader.Header} {block : Execute.Block}
    {limits : Execute.Limits} {origin before : LSBReader} {fuel index bit : Nat}
    {state : Execute.InsertCopy.State}
    (read : Execute.LiteralSwitch.Internal.run header block limits origin fuel index state before =
      .error (.initialOutput bit)) : False := by
  induction fuel generalizing index state before with
  | zero => unfold Execute.LiteralSwitch.Internal.run Execute.LiteralSwitch.Internal.runWith Execute.LiteralSwitch.Internal.runWithResult at read; split at read <;> cases read
  | succ fuel ih =>
    unfold Execute.LiteralSwitch.Internal.run Execute.LiteralSwitch.Internal.runWith Execute.LiteralSwitch.Internal.runWithResult at read
    split at read
    · cases read
    cases step : Execute.LiteralSwitch.read header block
        {limits with bits := Execute.LiteralSwitch.remainingBits limits.bits origin before} state before with
    | error _ => simp [step, Except.mapError, bind, Except.bind] at read
    | ok pair =>
      obtain ⟨_, _⟩ := pair
      simp only [step, Except.mapError, bind, Except.bind] at read
      exact ih read

private theorem run_fuel_offset {header : CompressedHeader.Header} {block : Execute.Block} {limits : Execute.Limits}
    {origin before : LSBReader} {fuel index command bit : Nat} {state : Execute.InsertCopy.State}
    {input : List Bool} (cursor : Cursor before input)
    (read : Execute.LiteralSwitch.Internal.run header block limits origin fuel index state before =
      .error (.fuel command bit)) :
    Offset before.totalRead input bit := by
  induction fuel generalizing index state before input with
  | zero =>
    unfold Execute.LiteralSwitch.Internal.run Execute.LiteralSwitch.Internal.runWith Execute.LiteralSwitch.Internal.runWithResult at read
    split at read
    · cases read
    · cases read; exact Offset.here _ _
  | succ fuel ih =>
    unfold Execute.LiteralSwitch.Internal.run Execute.LiteralSwitch.Internal.runWith Execute.LiteralSwitch.Internal.runWithResult at read
    split at read
    · cases read
    cases step : Execute.LiteralSwitch.read header block
        {limits with bits := Execute.LiteralSwitch.remainingBits limits.bits origin before} state before with
    | error _ => simp [step, Except.mapError, bind, Except.bind] at read
    | ok pair =>
      obtain ⟨result, after⟩ := pair
      simp only [step, Except.mapError, bind, Except.bind] at read
      obtain ⟨_, _, _, used, suffix, _, source, _⟩ :=
        Execute.LiteralSwitch.read_sound cursor.1 cursor.2.1 step
      have next := cursor_advance cursor source.split source.rep source.count source.position
      exact Offset.prepend source.split source.position (ih next read)

private theorem readBody_error {limits : Stream.Limits} {window index : Nat}
    {header : Header} {initial : Execute.State} {before : LSBReader} {input : List Bool}
    {error : Stream.LiteralSwitch.Error} (cursor : Cursor before input)
    (read : Stream.LiteralSwitch.Internal.readBody limits window index header initial before = .error error) :
    Offset before.totalRead input error.bit ∧
      ∀ {block command reason}, error = .block block (.command command reason) →
        block = index ∧ BodyCommandFailure limits window header initial before input command reason := by
  have envelope (cause : Stream.Cause)
      (equal : error = .envelope ⟨before.totalRead, some index, none, cause⟩) :
      Offset before.totalRead input error.bit ∧
        ∀ {block command reason}, error = .block block (.command command reason) →
          block = index ∧ BodyCommandFailure limits window header initial before input command reason := by
    subst error
    exact ⟨Offset.here _ _, by intro _ _ _ impossible; cases impossible⟩
  cases header with
  | terminal => cases read
  | metadata last length =>
    unfold Stream.LiteralSwitch.Internal.readBody readBodyWith readBodyWithResult at read
    cases bytes : alignedBody limits length.size before with
    | error reason =>
      simp only [bytes, Except.mapError, bind, Except.bind, Except.error.injEq] at read
      exact envelope reason read.symm
    | ok pair =>
      obtain ⟨_, _⟩ := pair
      simp [bytes, Except.mapError, bind, Except.bind, pure, Except.pure] at read
  | raw length =>
    unfold Stream.LiteralSwitch.Internal.readBody readBodyWith readBodyWithResult at read
    dsimp only at read
    split at read
    · cases read; exact envelope _ rfl
    cases bytes : alignedBody limits length.size before with
    | error reason =>
      simp only [bytes, Except.mapError, bind, Except.bind, Except.error.injEq] at read
      exact envelope reason read.symm
    | ok pair =>
      obtain ⟨_, _⟩ := pair
      simp [bytes, Except.mapError, bind, Except.bind, pure, Except.pure] at read
  | compressed last length =>
    unfold Stream.LiteralSwitch.Internal.readBody readBodyWith readBodyWithResult at read
    dsimp only at read
    split at read
    · cases read; exact envelope _ rfl
    cases parsed : CompressedHeader.read
        ⟨limits.mapEntries, limits.trees, limits.bits - before.totalRead⟩ before with
    | error reason =>
      simp only [parsed, Except.mapError, bind, Except.bind, Except.error.injEq] at read
      exact envelope (.header reason) read.symm
    | ok pair =>
      obtain ⟨header, payload⟩ := pair
      simp only [parsed, Except.mapError, bind, Except.bind] at read
      obtain ⟨_, _, _, used, tail, _, _, split, rep, count, position, _⟩ :=
        CompressedHeader.read_sound cursor.1 cursor.2.1 parsed
      have next := cursor_advance cursor split rep count position
      unfold Stream.LiteralSwitch.Internal.readPayload at read
      cases commands : Execute.LiteralSwitch.readBlock header window length.size
          (payloadLimits limits payload) initial payload with
      | ok pair =>
        obtain ⟨_, _⟩ := pair
        simp [commands, Except.mapError, bind, Except.bind, pure, Except.pure] at read
      | error failed =>
        simp only [commands, Except.mapError, bind, Except.bind] at read
        cases read
        cases failed with
        | initialOutput bit =>
          unfold Execute.LiteralSwitch.readBlock at commands
          split at commands
          · cases commands
            exact ⟨Offset.prepend split position (Offset.here _ _), by intro _ _ _ impossible; cases impossible⟩
          · exact False.elim (run_not_initialOutput commands)
        | fuel command bit =>
          unfold Execute.LiteralSwitch.readBlock at commands
          split at commands
          · cases commands
          · exact ⟨Offset.prepend split position (run_fuel_offset next commands),
              by intro _ _ _ impossible; cases impossible⟩
        | command command reason =>
          have failure := Execute.LiteralSwitch.readBlock_command_error rep count commands
          obtain ⟨_, offset⟩ := Execute.LiteralSwitch.BlockFailure.offset rep count failure
          refine ⟨Offset.prepend split position offset, ?_⟩
          intro failedBlock failedCommand cause equal
          cases equal
          exact ⟨rfl, last, length, header, payload, tail, rfl, parsed, ⟨used, split, position, next⟩, failure⟩

private theorem readBlocks_error {limits : Stream.Limits} {window fuel index : Nat}
    {initial : Execute.State} {before : LSBReader} {input : List Bool} {error : Stream.LiteralSwitch.Error}
    (cursor : Cursor before input) (outFits : initial.output.size ≤ limits.output)
    (read : readBlocksWith Error.envelope Stream.LiteralSwitch.Internal.readBody limits window fuel index initial before =
      .error error) :
    Offset before.totalRead input error.bit ∧
      ∀ {block command reason}, error = .block block (.command command reason) →
        CommandFailure limits window block command reason index initial before input := by
  induction fuel generalizing index initial before input with
  | zero =>
    cases read
    exact ⟨Offset.here _ _, by intro _ _ _ impossible; cases impossible⟩
  | succ fuel ih =>
    unfold readBlocksWith readBlocksWithState at read
    cases head : readHeader before with
    | error reason =>
      simp only [head, Except.mapError, bind, Except.bind, Function.comp_apply] at read
      cases read
      exact ⟨Offset.here _ _, by intro _ _ _ impossible; cases impossible⟩
    | ok pair =>
      obtain ⟨header, payload⟩ := pair
      simp only [head, Except.mapError, bind, Except.bind] at read
      cases cap : withinBits limits payload with
      | error reason =>
        simp only [cap] at read
        cases read
        exact ⟨Offset.here _ _, by intro _ _ _ impossible; cases impossible⟩
      | ok admitted =>
        cases admitted
        simp only [cap] at read
        obtain ⟨tail, _, split, next, position⟩ := readHeader_sound cursor head
        cases body : Stream.LiteralSwitch.Internal.readBody limits window index header initial payload with
        | error reason =>
          simp only [body] at read
          cases read
          obtain ⟨offset, commandPath⟩ := readBody_error next body
          refine ⟨Offset.prepend split position offset, ?_⟩
          intro block command cause equal
          obtain ⟨rfl, witness⟩ := commandPath equal
          exact .here head cap ⟨header.bits, split, position, next⟩ witness
        | ok pair =>
          obtain ⟨state, after⟩ := pair
          simp only [body] at read
          obtain ⟨fits, _, used, rest, _, _, restBits, afterCursor, afterPos⟩ :=
            readBody_sound next outFits (withinBits_ok cap) body
          split at read
          · cases endRead : finish limits after with
            | ok _ => simp only [endRead] at read; cases read
            | error reason =>
              simp only [endRead] at read
              cases read
              exact ⟨Offset.prepend split position (Offset.prepend restBits afterPos (Offset.here _ _)),
                by intro _ _ _ impossible; cases impossible⟩
          · rename_i more
            obtain ⟨offset, commandPath⟩ := ih afterCursor fits read
            refine ⟨Offset.prepend split position (Offset.prepend restBits afterPos offset), ?_⟩
            intro block command reason equal
            have source : Source before after input rest :=
              ⟨header.bits ++ used, by rw [split, restBits, List.append_assoc],
                by rw [afterPos, position, List.length_append, Nat.add_assoc], afterCursor⟩
            exact .more head cap body (by simpa using more) source (commandPath equal)

theorem decode_error {limits : Stream.Limits} {input : List UInt8} {error : Stream.LiteralSwitch.Error}
    (read : Stream.LiteralSwitch.decode limits input = .error error) :
    (∃ used suffix, bytesBits input = used ++ suffix ∧ error.bit = used.length) ∧
      ∀ {block command reason}, error = .block block (.command command reason) →
        CommandFailureWire limits input block command reason := by
  have envelope (cause : Stream.Cause) (equal : error = .envelope ⟨0, none, none, cause⟩) :
      (∃ used suffix, bytesBits input = used ++ suffix ∧ error.bit = used.length) ∧
        ∀ {block command reason}, error = .block block (.command command reason) →
          CommandFailureWire limits input block command reason := by
    subst error
    exact ⟨⟨[], bytesBits input, rfl, rfl⟩, by intro _ _ _ impossible; cases impossible⟩
  unfold Stream.LiteralSwitch.decode decodeWith decodeWithState at read
  dsimp only at read
  split at read
  · cases read; exact envelope _ rfl
  cases windowRead : Brotli.Internal.readWindow (start input) with
  | error reason =>
    simp only [windowRead, Except.mapError, bind, Except.bind, Function.comp_apply] at read
    cases read
    exact envelope _ rfl
  | ok pair =>
    obtain ⟨window, reader⟩ := pair
    simp only [windowRead, Except.mapError, bind, Except.bind] at read
    cases cap : withinBits limits reader with
    | error reason =>
      simp only [cap] at read
      cases read
      exact envelope _ rfl
    | ok admitted =>
      cases admitted
      simp only [cap] at read
      split at read
      · cases read; exact envelope _ rfl
      have cursor : Cursor (start input) (bytesBits input) := by simp [Cursor, start, LSBReader.Rep, natBits]
      obtain ⟨code, tail, wire, split, next, position⟩ := readWindow_sound cursor windowRead
      obtain ⟨offset, commandPath⟩ := readBlocks_error next (Nat.zero_le _) read
      refine ⟨?_, ?_⟩
      · simpa only [Offset, start, Nat.zero_add] using Offset.prepend split position offset
      · intro block command reason equal
        exact ⟨window, reader, code, tail, windowRead, wire, split, by simpa [start] using position,
          commandPath equal⟩

end Silmaril.Proofs.Formats.Compression.Brotli.Stream.LiteralSwitch
