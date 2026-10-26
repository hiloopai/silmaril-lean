module

public import Silmaril.Process.CLI.Sha256Cli.HexLoop
public import Silmaril.Crypto.X86.Sha256O2.Reference

/-! # Binding the actual hex loop to the canonical SHA digest

The compression-state equality remains an explicit input. This module proves
only representation/formatting and the actual already-checked hex instruction
segment, for any message. It reuses the canonical endian roundtrip lemmas.

The reference bridge is the explicit external PR#3052 dependency pinned to
f69056ce06858f0e72bc8c6ae53c51603fd11282, without vendoring its source.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.HexReference

open Silmaril.Process (Byte Memory)
open Silmaril.Process.CLI Silmaril.Process.CLI.X86Linux Silmaril.Process.Syscall
open Silmaril.Crypto Silmaril.Crypto.X86.Sha256O2

private theorem or_reverse4 {n : Nat} (a b c d : BitVec n) :
    a ||| b ||| c ||| d = d ||| c ||| b ||| a := by
  rw [BitVec.or_comm (a ||| b ||| c) d, BitVec.or_comm (a ||| b) c, BitVec.or_comm a b]
  simp only [BitVec.or_assoc]

/-- Serializing a little-endian machine state word reverses its four bytes.
No new arithmetic encoding is introduced: reuse the reference parser bridge
and the canonical parser/serializer roundtrip. -/
theorem toBytes_leWordAt (bytes : List Byte) (word : Nat) :
    toBytesBE32 (UInt32.ofBitVec (leWordAt bytes word)) =
      (UInt8.ofBitVec (byteAt bytes (4 * word + 3)),
       UInt8.ofBitVec (byteAt bytes (4 * word + 2)),
       UInt8.ofBitVec (byteAt bytes (4 * word + 1)),
       UInt8.ofBitVec (byteAt bytes (4 * word))) := by
  have wordEq : UInt32.ofBitVec (leWordAt bytes word) =
      ofBytesBE32 (UInt8.ofBitVec (byteAt bytes (4 * word + 3)))
        (UInt8.ofBitVec (byteAt bytes (4 * word + 2)))
        (UInt8.ofBitVec (byteAt bytes (4 * word + 1)))
        (UInt8.ofBitVec (byteAt bytes (4 * word))) := by
    apply UInt32.eq_of_toBitVec_eq
    rw [UInt32.toBitVec_ofBitVec, ofBytesBE32_toBitVec]
    unfold leWordAt
    exact or_reverse4 _ _ _ _
  rw [wordEq, toBytesBE32_ofBytesBE32]

/-- XOR3 reverses each word independently, including the final word's byte31.
The finite indexing calculation is checked directly by Lean's kernel. -/
theorem sourceIndex_word_lane : ∀ i : Fin 32,
    HexLookup.sourceIndex i = 4 * (i.val / 4) + (3 - i.val % 4) := by decide

/-- Every state whose canonical interpretation is the reference hash yields
exactly the reference digest bytes under the compiled XOR3 traversal. -/
theorem permutation_reference (bytes message : List Byte)
    (value : (stateOf bytes).toState = SHA256.hash (message.map UInt8.ofBitVec)) :
    (List.finRange 32).map (fun i => UInt8.ofBitVec
      (bytes.getD (HexLookup.sourceIndex i) 0)) =
        SHA256.digest (message.map UInt8.ofBitVec) := by
  unfold SHA256.digest
  rw [← value]
  simp only [stateOf, SHA256.Kernel.InitHash.toState, toBytes_leWordAt]
  rfl

theorem formattedPrefix_reference (bytes message : List Byte)
    (value : (stateOf bytes).toState = SHA256.hash (message.map UInt8.ofBitVec)) :
    HexLoop.formattedPrefix bytes 32 = (Sha256.expected message).take 64 := by
  have range : (List.finRange 32).map (fun i : Fin 32 => i.val) = List.range 32 := by decide
  have normalized : HexLoop.formattedPrefix bytes 32 =
      ((List.finRange 32).map (fun i => UInt8.ofBitVec
        (bytes.getD (HexLookup.sourceIndex i) 0))).flatMap Sha256.hexByte := by
    rw [HexLoop.formattedPrefix, ← range, List.flatMap_map, List.flatMap_map]
    rfl
  rw [normalized, permutation_reference bytes message value]
  have length : ((SHA256.digest (message.map UInt8.ofBitVec)).flatMap Sha256.hexByte).length = 64 := by
    rw [Sha256.flatMap_hexByte_length, SHA256.digest_length]
  change _ = (((SHA256.digest (message.map UInt8.ofBitVec)).flatMap Sha256.hexByte) ++ [0x0a]).take 64
  rw [← length, List.take_left]

/-- From compression return to the real newline store, the actual loop
produces the canonical64 digits for any reference-correct machine state.
It retains the shared exact output-only frame for later composition. -/
theorem run (c : Core) (s : Syscall.State) (bytes message : List Byte)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x40022e)
    (stateRead : s.memory.readBytes 0x401660 32 = some bytes)
    (value : (stateOf bytes).toState = SHA256.hash (message.map UInt8.ofBitVec))
    (tableRead : s.memory.readBytes 0x4004b0 16 = some EmptySupport.hexDigits)
    (writable : s.memory.Permitted .write 0x4015c0 64)
    (readable : s.memory.Permitted .read 0x4015c0 64) :
    ∃ (next : Core) (after : Memory),
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨next, { s with memory := after }⟩ ∧
      next.rip = 0x400271 ∧ next.read .rax = 32 ∧
      after.readBytes 0x4015c0 64 = some ((Sha256.expected message).take 64) ∧
      Memory.WritesWithin s.memory after (HexLoop.Footprint 32) := by
  obtain ⟨next, after, loopRun, nextRip, nextValue, answer, frame⟩ :=
    HexLoop.loop_to (HexLoop.zeroCore c) s bytes running intact rfl (by simp [HexLoop.zeroCore])
      stateRead tableRead writable readable 32 (by decide)
  exact ⟨next, after, (HexLoop.start c s running intact pc).append loopRun, nextRip, nextValue,
    formattedPrefix_reference bytes message value ▸ answer, frame⟩

end Silmaril.Process.CLI.Sha256Cli.HexReference
