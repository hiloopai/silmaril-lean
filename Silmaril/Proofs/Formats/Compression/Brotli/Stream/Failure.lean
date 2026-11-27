module

public import Silmaril.Formats.Compression.Brotli.Stream.Defs
import Silmaril.Formats.Compression.Brotli.Thms
import Silmaril.Formats.Compression.Brotli.CompressedHeader.Thms
import Silmaril.Formats.Compression.Brotli.Execute.Thms
import Silmaril.Proofs.Formats.Compression.Brotli.Stream.Framing
import Silmaril.Proofs.Formats.Compression.Brotli.Stream.Contracts
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Compression.Brotli.Stream

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Internal (Cursor start readWindow_sound)
open Silmaril.Formats.Compression.Brotli.Stream
open Silmaril.Formats.Compression.Brotli.Stream.Internal

private theorem here {limits : Stream.Limits} {before : LSBReader} {bits : List Bool}
    {block command : Option Nat} {cause : Cause} (cursor : Cursor before bits)
    (fault : FailedOperation limits before cause) :
    FailureWire limits before.totalRead bits ⟨before.totalRead, block, command, cause⟩ :=
  ⟨[], bits, before, rfl, cursor, by simp, rfl, fault⟩

private theorem preceded {limits : Stream.Limits} {error : Stream.Error}
    {before after : LSBReader} {input used tail : List Bool}
    (consumed : input = used ++ tail) (position : after.totalRead = before.totalRead + used.length)
    (failure : FailureWire limits after.totalRead tail error) :
    FailureWire limits before.totalRead input error := by
  obtain ⟨consumedBits, suffix, site, split, rep, cursor, bit, fault⟩ := failure
  refine ⟨used ++ consumedBits, suffix, site, ?_, rep, ?_, bit, fault⟩
  · rw [consumed, split, List.append_assoc]
  · rw [cursor, position, List.length_append, Nat.add_assoc]

private theorem runCommands_error {limits : Stream.Limits} {header : CompressedHeader.Header} {block : Execute.Block}
    {index fuel command : Nat} {initial : Execute.State} {before : LSBReader} {input : List Bool} {error : Stream.Error}
    (cursor : Cursor before input) (size : initial.output.size ≤ block.endOutput)
    (enough : block.endOutput ≤ initial.output.size + fuel)
    (read : runCommands limits header block index fuel command initial before = .error error) :
    FailureWire limits before.totalRead input error ∧ error.block = some index ∧
      ∃ passed state reader reason, passed < fuel ∧ error.command = some (command + passed) ∧
        PassedCommands limits header block initial before passed state reader ∧
        Execute.read header block ⟨limits.output, limits.bits - reader.totalRead⟩ state reader = .error reason ∧
        error.bit = reader.totalRead ∧ error.cause = .command reason := by
  induction fuel generalizing command initial before input with
  | zero =>
    have done : initial.output.size = block.endOutput := by omega
    simp [runCommands, done] at read
  | succ fuel ih =>
    unfold runCommands at read
    split at read
    · contradiction
    cases step : Execute.read header block ⟨limits.output, limits.bits - before.totalRead⟩ initial before with
    | error reason =>
      simp only [step, Except.mapError, bind, Except.bind] at read
      cases read
      exact ⟨here cursor (.command step), rfl, 0, initial, before, reason, by omega, by simp,
        .none initial before, step, rfl, rfl⟩
    | ok pair =>
      obtain ⟨result, after⟩ := pair
      simp only [step, Except.mapError, bind, Except.bind] at read
      obtain ⟨_, _, _, _, grows, bound, _, used, tail, _, split, rep, count, position, _⟩ :=
        Execute.read_sound cursor.1 cursor.2.1 step
      have next := cursor_advance cursor split rep count position
      obtain ⟨fault, atBlock, passed, state, reader, reason, countFit, atCommand, path, fails, bit, cause⟩ :=
        ih next bound (by omega) read
      exact ⟨preceded split position fault, atBlock, passed + 1, state, reader, reason,
        by omega, by rw [atCommand]; congr 1; omega, .next step path, fails, bit, cause⟩

private theorem readBody_error {limits : Stream.Limits} {window index : Nat} {header : Header}
    {initial : Execute.State} {before : LSBReader} {input : List Bool} {error : Stream.Error}
    (cursor : Cursor before input)
    (read : readBody limits window index header initial before = .error error) :
    FailureWire limits before.totalRead input error ∧ error.block = some index ∧
      ∀ command, error.command = some command → CommandSite limits window initial header before error command := by
  cases header with
  | terminal => contradiction
  | metadata last length =>
    unfold readBody at read
    cases body : alignedBody limits length.size before with
    | ok pair => obtain ⟨_, _⟩ := pair; simp only [body, Except.mapError, bind, Except.bind] at read; cases read
    | error reason =>
      simp only [body, Except.mapError, bind, Except.bind] at read
      cases read
      exact ⟨here cursor (.byteBody body), rfl, by simp⟩
  | raw length =>
    unfold readBody at read
    dsimp only at read
    split at read
    · rename_i excess
      cases read
      exact ⟨here cursor (.outputLimit before excess), rfl, by simp⟩
    · cases body : alignedBody limits length.size before with
      | ok pair => obtain ⟨_, _⟩ := pair; simp only [body, Except.mapError, bind, Except.bind] at read; cases read
      | error reason =>
        simp only [body, Except.mapError, bind, Except.bind] at read
        cases read
        exact ⟨here cursor (.byteBody body), rfl, by simp⟩
  | compressed last length =>
    unfold readBody at read
    dsimp only at read
    split at read
    · rename_i excess
      cases read
      exact ⟨here cursor (.outputLimit before excess), rfl, by simp⟩
    · cases head : CompressedHeader.read
        ⟨limits.mapEntries, limits.trees, limits.bits - before.totalRead⟩ before with
      | error reason =>
        simp only [head, Except.mapError, bind, Except.bind] at read
        cases read
        exact ⟨here cursor (.header head), rfl, by simp⟩
      | ok pair =>
        obtain ⟨header, after⟩ := pair
        simp only [head, Except.mapError, bind, Except.bind] at read
        split at read
        · rename_i omitted
          cases read
          exact ⟨here cursor (.blockTypes head (by simpa using omitted)), rfl, by simp⟩
        · obtain ⟨_, _, _, used, tail, _, _, split, rep, count, position, _⟩ :=
            CompressedHeader.read_sound cursor.1 cursor.2.1 head
          have next := cursor_advance cursor split rep count position
          obtain ⟨fault, atBlock, passed, state, reader, reason, fits, atCommand, path, fails, bit, cause⟩ :=
            runCommands_error next (Nat.le_add_right _ _) (Nat.le_refl _) read
          refine ⟨preceded split position fault, atBlock, ?_⟩
          intro command same
          have equal : command = passed := by simpa [atCommand] using same.symm
          subst command
          exact ⟨last, length, header, after, state, reader, reason, rfl, head, path, fits, fails, bit, cause⟩

private theorem readBlocks_error {limits : Stream.Limits} {window fuel index : Nat}
    {initial : Execute.State} {before : LSBReader} {input : List Bool} {error : Stream.Error}
    (cursor : Cursor before input) (outFits : initial.output.size ≤ limits.output)
    (read : readBlocks limits window fuel index initial before = .error error) :
    FailureWire limits before.totalRead input error ∧
      (∃ passed, passed ≤ fuel ∧ error.block = some (index + passed)) ∧
      IndexedFailure limits window index initial before error := by
  induction fuel generalizing index initial before input with
  | zero =>
    cases read
    exact ⟨here cursor (.stepLimit before), ⟨0, Nat.le_refl _, by simp⟩,
      index, initial, before, .none _ _ _, rfl, by simp⟩
  | succ fuel ih =>
    unfold readBlocks at read
    cases head : readHeader before with
    | error reason =>
      simp only [head, Except.mapError, bind, Except.bind, Function.comp_apply] at read
      cases read
      exact ⟨here cursor (.framing head), ⟨0, by omega, by simp⟩,
        index, initial, before, .none _ _ _, rfl, by simp⟩
    | ok pair =>
      obtain ⟨header, payload⟩ := pair
      simp only [head, Except.mapError, bind, Except.bind] at read
      cases bits : withinBits limits payload with
      | error reason =>
        have cause : reason = .bitLimit := by
          unfold withinBits at bits
          split at bits
          · contradiction
          · cases bits; rfl
        subst reason
        simp only [bits] at read
        cases read
        exact ⟨here cursor (.framingBits head bits), ⟨0, by omega, by simp⟩,
          index, initial, before, .none _ _ _, rfl, by simp⟩
      | ok result =>
        cases result
        simp only [bits] at read
        obtain ⟨tail, _, split, next, position⟩ := readHeader_sound cursor head
        cases body : readBody limits window index header initial payload with
        | error reason =>
          simp only [body] at read
          cases read
          obtain ⟨fault, atBlock, site⟩ := readBody_error next body
          exact ⟨preceded split position fault, ⟨0, by omega, by simpa using atBlock⟩,
            index, initial, before, .none _ _ _, atBlock, fun command equal => ⟨header, payload, head, site command equal⟩⟩
        | ok pair =>
          obtain ⟨state, after⟩ := pair
          simp only [body] at read
          obtain ⟨fits, _, _, _, _, _, consumed, nextCursor, bodyPosition⟩ :=
            readBody_sound next outFits (withinBits_ok bits) body
          split at read
          · cases stop : finish limits after with
            | ok _ => simp only [stop] at read; cases read
            | error reason =>
              simp only [stop] at read
              cases read
              have fault := preceded consumed bodyPosition (here (block := some index) (command := none) nextCursor (.finish stop))
              exact ⟨preceded split position fault, ⟨0, by omega, by simp⟩,
                index, initial, before, .none _ _ _, rfl, by simp⟩
          · rename_i more
            obtain ⟨fault, ⟨passed, fit, atBlock⟩, current, final, reader, path, equal, cmd⟩ := ih nextCursor fits read
            exact ⟨preceded split position (preceded consumed bodyPosition fault),
              ⟨passed + 1, by omega, by rw [atBlock]; congr 1; omega⟩,
              current, final, reader, .next head bits body (by simpa using more) path, equal, cmd⟩

theorem decode_error {limits : Stream.Limits} {bytes : List UInt8} {error : Stream.Error}
    (read : Stream.decode limits bytes = .error error) :
    FailureWire limits 0 (bytesBits bytes) error ∧
      (error.block = none ∧ error.command = none ∨
        (∃ index ≤ limits.blocks, error.block = some index) ∧ ∃ window reader,
          Brotli.Internal.readWindow (start bytes) = .ok (window, reader) ∧
          IndexedFailure limits window 0 Execute.State.start reader error) ∧
      error.cause ≠ .commandFuel := by
  have cursor : Cursor (start bytes) (bytesBits bytes) := by
    simp [Cursor, start, LSBReader.Rep, natBits]
  have noFuel {e : Stream.Error} (fault : FailureWire limits 0 (bytesBits bytes) e) :
      e.cause ≠ .commandFuel := by
    obtain ⟨_, _, site, _, _, _, _, operation⟩ := fault
    intro impossible
    rw [impossible] at operation
    cases operation with
    | byteBody =>
      rename_i size actionError
      unfold alignedBody at actionError
      cases aligned : Brotli.Internal.alignZero site with
      | error reason => simp [aligned, bind, Except.bind, Except.mapError] at actionError
      | ok after =>
        simp only [aligned, bind, Except.bind, Except.mapError] at actionError
        split at actionError
        · cases actionError
        · cases body : Brotli.Internal.takeBody size after <;> simp [body] at actionError
    | finish =>
      rename_i actionError
      unfold finish at actionError
      cases aligned : Brotli.Internal.alignZero site with
      | error reason => simp [aligned, bind, Except.bind, Except.mapError] at actionError
      | ok after =>
        simp only [aligned, bind, Except.bind, Except.mapError, withinBits] at actionError
        by_cases fits : after.totalRead ≤ limits.bits <;>
          by_cases empty : after.input.isEmpty = true <;> simp [fits, empty] at actionError
  suffices found : FailureWire limits 0 (bytesBits bytes) error ∧
      (error.block = none ∧ error.command = none ∨
        (∃ index ≤ limits.blocks, error.block = some index) ∧ ∃ window reader,
          Brotli.Internal.readWindow (start bytes) = .ok (window, reader) ∧
          IndexedFailure limits window 0 Execute.State.start reader error) from
    ⟨found.1, found.2, noFuel found.1⟩
  unfold Stream.decode at read
  dsimp only at read
  split at read
  · rename_i excess
    cases read
    exact ⟨here cursor (.inputLimit excess), .inl ⟨rfl, rfl⟩⟩
  · cases head : Brotli.Internal.readWindow (start bytes) with
    | error reason =>
      simp only [head, Except.mapError, bind, Except.bind, Function.comp_apply] at read
      cases read
      exact ⟨here cursor (.window head), .inl ⟨rfl, rfl⟩⟩
    | ok pair =>
      obtain ⟨window, reader⟩ := pair
      simp only [head, Except.mapError, bind, Except.bind] at read
      cases bits : withinBits limits reader with
      | error reason =>
        have cause : reason = .bitLimit := by
          unfold withinBits at bits
          split at bits
          · contradiction
          · cases bits; rfl
        subst reason
        simp only [bits] at read
        cases read
        exact ⟨here cursor (.windowBits head bits), .inl ⟨rfl, rfl⟩⟩
      | ok result =>
        cases result
        simp only [bits] at read
        split at read
        · rename_i excess
          cases read
          exact ⟨here cursor (.windowLimit head excess), .inl ⟨rfl, rfl⟩⟩
        · obtain ⟨_, _, _, split, next, position⟩ := readWindow_sound cursor head
          obtain ⟨fault, ⟨passed, fit, atBlock⟩, indexed⟩ := readBlocks_error next (Nat.zero_le _) read
          exact ⟨preceded split position fault, .inr ⟨⟨passed, fit, by simpa using atBlock⟩,
            window, reader, rfl, indexed⟩⟩

end Silmaril.Proofs.Formats.Compression.Brotli.Stream
