module

public import Silmaril.Process.CLI.Sha256Cli.Padding

/-! # The real zero-fill loop preserves an arbitrary message prefix

This refinement premise reuses `Padding.zero_iteration`, including its checked
bytes and actual ADD/store/CMP/JNE execution. The new invariant retains an
arbitrary readable prefix, rather than the empty message's fixed 0x80 prefix.
The entry index ranges from 1 to 55; index 56 takes a different driver branch.

The input bytes and leading 0x80 must already be in the block. Establishing
that fact from read events and the preceding message-copy/pad-store loop is
an explicit caller obligation. No Linux progress or whole-driver assumption
is needed by this local construction.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.PaddingStream

open Silmaril.Process (Byte Memory)
open Silmaril.Process.CLI
open Silmaril.Process.CLI.X86Linux
open Silmaril.Process.Syscall
open Silmaril.X86 (Word)
open Silmaril.X86.Ext (Stored)
open Padding (blockAddress iterationCore zeroFinished)

private theorem append_zero {before after : Memory} (index : Fin 55) {bytes : List Byte}
    (stored : Stored before after (blockAddress + index.val + 1) [0])
    (initialBytes : before.readBytes blockAddress (index.val + 1) = some bytes)
    (readable : before.Permitted .read blockAddress 64) :
    after.readBytes blockAddress (index.val + 2) = some (bytes ++ [0]) := by
  have low := (stored.readWith_disjoint .read blockAddress (index.val + 1)
    (Or.inl (by omega))).trans initialBytes
  have permission : before.Permitted .read (blockAddress + index.val + 1) 1 :=
    X86.Ext.Memory.Permitted.sub readable (by decide) (by omega) (by
      have bound := index.isLt
      omega)
  have high : after.readBytes (blockAddress + (index.val + 1)) 1 = some [0] := by
    simpa only [Nat.add_assoc, List.length_singleton, Memory.readBytes] using
      stored.readWith_self permission
  simpa only [Nat.add_assoc] using Memory.readBytes_append low high

set_option maxRecDepth 10000 in
/-- Actual loop execution appends zeros and leaves the supplied prefix intact.
Its footprint starts strictly after that prefix. `remaining + 1` is the exact
number of byte-store iterations constructed here. -/
theorem zero_fill_prefix (remaining : Nat) :
    ∀ (c : Core) (s : Syscall.State) (bytes : List Byte), remaining < 55 →
      s.exited = none → Output.Intact s.memory → c.rip = 0x400200 →
      c.read .rax = BitVec.ofNat 64 (55 - remaining) →
      s.memory.Permitted .write blockAddress 64 →
      s.memory.Permitted .read blockAddress 64 →
      s.memory.readBytes blockAddress (55 - remaining) = some bytes →
      ∃ after : Memory,
        Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
          ⟨zeroFinished c, { s with memory := after }⟩ ∧
        after.readBytes blockAddress 56 = some (bytes ++ List.replicate (remaining + 1) 0) ∧
        Memory.WritesWithin s.memory after
          (fun a => blockAddress + (55 - remaining) ≤ a ∧ a < blockAddress + 56) ∧
        Output.Intact after := by
  induction remaining with
  | zero =>
    intro c s bytes bound running intact pc rax writable readable initialBytes
    let index : Fin 55 := ⟨54, by decide⟩
    have permission : s.memory.Permitted .write (blockAddress + index.val + 1) 1 :=
      X86.Ext.Memory.Permitted.sub writable (by decide) (by dsimp [index]; omega)
        (by dsimp [index]; omega)
    obtain ⟨after, run, stored, code⟩ :=
      Padding.zero_iteration c s index running intact pc rax permission
    refine ⟨after, ?_, append_zero index stored initialBytes readable, ?_, code⟩
    · simpa [iterationCore, index, zeroFinished] using run
    · exact stored.writesWithin (by
        intro i hi
        simp only [List.length_singleton] at hi
        dsimp [index]
        omega)
  | succ remaining ih =>
    intro c s bytes bound running intact pc rax writable readable initialBytes
    let index : Fin 55 := ⟨54 - (remaining + 1), by omega⟩
    have indexValue : index.val + 1 = 55 - (remaining + 1) := by dsimp [index]; omega
    have nextValue : index.val + 2 = 55 - remaining := by dsimp [index]; omega
    have notLast : index.val ≠ 54 := by dsimp [index]; omega
    have permission : s.memory.Permitted .write (blockAddress + index.val + 1) 1 :=
      X86.Ext.Memory.Permitted.sub writable (by decide) (by omega) (by
        have indexBound := index.isLt
        omega)
    obtain ⟨middle, run, stored, code⟩ := Padding.zero_iteration c s index running intact pc
      (by simpa only [indexValue] using rax) permission
    have nextRead : middle.readBytes blockAddress (55 - remaining) = some (bytes ++ [0]) := by
      have firstRead : s.memory.readBytes blockAddress (index.val + 1) = some bytes := by
        simpa only [indexValue] using initialBytes
      simpa only [nextValue] using append_zero index stored firstRead readable
    obtain ⟨after, suffix, padded, frame, finalCode⟩ := ih (iterationCore c index)
      { s with memory := middle } (bytes ++ [0]) (by omega) running code
      (by simp [iterationCore, notLast])
      (by simp [iterationCore, nextValue, X86.State.read, X86.State.write])
      (stored.permitted writable) (stored.permitted readable) nextRead
    refine ⟨after, ?_, ?_, ?_, finalCode⟩
    · have combined := run.append suffix
      simpa only [List.nil_append, zeroFinished, iterationCore, X86.State.write,
        Machine.RegisterFile.write_shadow] using combined
    · simpa only [List.append_assoc, List.singleton_append, List.replicate_succ] using padded
    · exact (stored.writesWithin (by
        intro i hi
        simp only [List.length_singleton] at hi
        have indexBound := index.isLt
        omega)).trans (frame.mono (by intro a ha; omega))

/-- The same local fact indexed by the meaningful byte count. The first
`count` bytes are retained and the remaining bytes up to offset 56 become zero. -/
theorem fill_to_length (c : Core) (s : Syscall.State) (count : Nat) (bytes : List Byte)
    (positive : 1 ≤ count) (bound : count < 56)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400200) (rax : c.read .rax = BitVec.ofNat 64 count)
    (writable : s.memory.Permitted .write blockAddress 64)
    (readable : s.memory.Permitted .read blockAddress 64)
    (initialBytes : s.memory.readBytes blockAddress count = some bytes) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨zeroFinished c, { s with memory := after }⟩ ∧
      after.readBytes blockAddress 56 = some (bytes ++ List.replicate (56 - count) 0) ∧
      Memory.WritesWithin s.memory after
        (fun a => blockAddress + count ≤ a ∧ a < blockAddress + 56) ∧
      Output.Intact after := by
  have restored : 55 - (55 - count) = count := by omega
  have length : 55 - count + 1 = 56 - count := by omega
  simpa only [restored, length] using zero_fill_prefix (55 - count) c s bytes
    (by omega) running intact pc (by simpa only [restored] using rax)
    writable readable (by simpa only [restored] using initialBytes)

/-- Once the driver has copied a short message and stored its leading 0x80,
the actual zero-fill loop preserves those bytes and completes the first 56
padding bytes. This does not assume they came from a particular read event. -/
theorem after_message (c : Core) (s : Syscall.State) (message : List Byte)
    (short : message.length < 55)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400200)
    (rax : c.read .rax = BitVec.ofNat 64 (message.length + 1))
    (writable : s.memory.Permitted .write blockAddress 64)
    (readable : s.memory.Permitted .read blockAddress 64)
    (initialBytes : s.memory.readBytes blockAddress (message.length + 1) =
      some (message ++ [0x80])) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨zeroFinished c, { s with memory := after }⟩ ∧
      after.readBytes blockAddress 56 =
        some (message ++ (0x80 :: List.replicate (55 - message.length) 0)) ∧
      Memory.WritesWithin s.memory after
        (fun a => blockAddress + message.length + 1 ≤ a ∧ a < blockAddress + 56) ∧
      Output.Intact after := by
  have zeros : 56 - (message.length + 1) = 55 - message.length := by omega
  simpa only [zeros, List.append_assoc, List.singleton_append, Nat.add_assoc] using
    fill_to_length c s (message.length + 1) (message ++ [0x80]) (by omega) (by omega)
      running intact pc rax writable readable initialBytes

end Silmaril.Process.CLI.Sha256Cli.PaddingStream
