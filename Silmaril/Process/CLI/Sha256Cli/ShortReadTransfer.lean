module

public import Silmaril.Process.CLI.Sha256Cli.ShortRead
public import Silmaril.Process.Syscall.InputStreamSlices

/-! # Every admitted successful chunk of a short finite input

The copied prefix and immutable descriptor stream are tied to the actual
`Syscall.Step` read constructor. Success never fabricates bytes; error memory
continues to be governed by the existing read frame, separately from success.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.ShortReadTransfer

open Silmaril.Process (Byte Memory)
open Silmaril.Process.Syscall
open Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)

/-- The immutable finite input and current descriptor cursor at a read cut point. -/
def InputAt (s : Syscall.State) (message : List Byte) (fill : Nat) : Prop :=
  ∃ descriptor, s.descriptors 0 = some descriptor ∧ descriptor.readable = true ∧
    descriptor.input = .ofList message ∧ descriptor.cursor = fill

/-- Any positive successful read copies the exact next message bytes and
extends the memory prefix. This classifies all chunk lengths admitted by the
syscall contract; it does not select a convenient transfer. -/
theorem successful_chunk {before after : Syscall.State} {message : List Byte} {fill count : Nat}
    {event : Event} (short : message.length < 56) (cursorBound : fill ≤ message.length)
    (input : InputAt before message fill)
    (initialBytes : before.memory.readBytes 0x401620 fill = some (message.take fill))
    (readable : before.memory.Permitted .read 0x401620 64) (positive : 0 < count)
    (effect : Syscall.Step before (.read 0 (0x401620 + fill) (64 - fill)) event
      (.returned (.ok count)) after) :
    count ≤ message.length - fill ∧ event = .read 0 ((message.drop fill).take count) ∧
      InputAt after message (fill + count) ∧ after.exited = none ∧
      after.memory.readBytes 0x401620 (fill + count) = some (message.take (fill + count)) ∧
      X86.Ext.Stored before.memory after.memory (0x401620 + fill) ((message.drop fill).take count) := by
  obtain ⟨descriptor, opened, mode, stream, cursor⟩ := input
  generalize requestCount : 64 - fill = requested at effect
  generalize resultEq : Result.ok count = result at effect
  cases effect with
  | @readSome _ _ _ other bytes memory running openedOther modeOther matched nonempty bounded transfer accessible copied =>
    have countEq := Result.ok.inj resultEq
    subst count
    have same := Option.some.inj (openedOther.symm.trans opened)
    subst same
    have matches' : (InputStream.ofList message).Matches fill bytes := by
      simpa only [stream, cursor] using matched
    obtain ⟨fits, exactBytes⟩ := matches'.ofList_slice cursorBound
    have stored := X86.Ext.Stored.of_writeBytes copied
    have readPermission : before.memory.Permitted .read (0x401620 + fill) bytes.length :=
      X86.Ext.Memory.Permitted.sub readable nonempty (by omega) (by omega)
    have headRead := (stored.readWith_disjoint .read 0x401620 fill (Or.inl (by omega))).trans initialBytes
    have tailRead : memory.readBytes (0x401620 + fill) bytes.length = some bytes :=
      stored.readWith_self readPermission
    have combined := Memory.readBytes_append headRead tailRead
    refine ⟨fits, ?_, ?_, running, ?_, ?_⟩
    · exact congrArg (Event.read 0) exactBytes
    · refine ⟨{ other with cursor := other.cursor + bytes.length }, ?_, mode, stream, ?_⟩
      · simp [State.setDescriptor]
      · simp only [cursor]
    · have joined := congrArg (fun tail : List Byte => message.take fill ++ tail) exactBytes
      have finalList : message.take fill ++ bytes = message.take (fill + bytes.length) :=
        joined.trans List.take_add.symm
      exact combined.trans (congrArg some finalList)
    · exact Eq.mp (congrArg (X86.Ext.Stored before.memory memory (0x401620 + fill)) exactBytes) stored
  | readEof => have zero := Result.ok.inj resultEq; omega
  | readZero => omega
  | readError => cases resultEq
  | readBadDescriptor => cases resultEq
  | readBadAddress => cases resultEq

/-- A zero successful return from the positive-capacity read is genuine EOF,
which identifies the entire supplied finite message and preserves all state. -/
theorem zero_is_eof {before after : Syscall.State} {message : List Byte} {fill address count : Nat}
    {event : Event} (cursorBound : fill ≤ message.length) (input : InputAt before message fill)
    (positive : 0 < count)
    (effect : Syscall.Step before (.read 0 address count) event (.returned (.ok 0)) after) :
    fill = message.length ∧ event = .read 0 [] ∧ after = before := by
  obtain ⟨descriptor, opened, mode, stream, cursor⟩ := input
  generalize resultEq : Result.ok 0 = result at effect
  cases effect with
  | readSome _ _ _ _ nonempty => have zero := Result.ok.inj resultEq; omega
  | readEof running openedOther modeOther eof accessible =>
    have same := Option.some.inj (openedOther.symm.trans opened)
    subst same
    have ended : message.length ≤ fill := by
      apply List.getElem?_eq_none_iff.mp
      simpa only [stream, cursor, InputStream.ofList_byteAt] using eof
    exact ⟨by omega, rfl, rfl⟩
  | readZero => omega
  | readError => cases resultEq
  | readBadDescriptor => cases resultEq
  | readBadAddress => cases resultEq

end Silmaril.Process.CLI.Sha256Cli.ShortReadTransfer
