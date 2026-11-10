module

public import Silmaril.X86.SystemV.Defs

/-! # The x86-64 System V scalar C boundary: theorems

* `Frame.readBytes`: a caller reuses every byte slice disjoint from the callee's write
  footprint;
* boundary vectors: `signed_status_sanity` (the signed status `-2` is `-2`, not a large
  positive value), `high_bits_sanity` (a 32-bit status ignores the high register bits, a
  pointer does not), `seventh_argument` (the seventh INTEGER argument is on the stack).
-/

@[expose] public section

namespace Silmaril.X86.SystemV

open Silmaril.X86 (Word MState)
open CApi

/-- Clients can reuse every byte slice disjoint from the callee write footprint. -/
theorem Frame.readBytes {writes : Footprint} {call : Call} {final : MState}
    (frame : Frame writes call final) {address length : Nat}
    (disjoint : ∀ offset < length, ¬ writes (address + offset)) :
    final.memory.readBytes address length = call.initial.memory.readBytes address length :=
  Silmaril.Process.Memory.WritesWithin.readBytes frame disjoint

/-- Full pointer width and low-32 status width are intentionally different. -/
theorem high_bits_sanity :
    Encodes .int32 (BitVec.ofInt 32 (-2)) 0x12345678fffffffe ∧
    ¬ Encodes .pointer (BitVec.ofNat 64 0xfffffffe) 0x12345678fffffffe := by
  simp [Encodes]

/-- The seventh INTEGER argument is backed by the stack, not an absent register. -/
theorem seventh_argument (initial : MState) (value : Word) :
    ArgumentWord initial 6 value ↔
      initial.memory.readBytes ((initial.core.read .rsp).toNat + 8) 8 =
        some (Silmaril.Machine.LittleEndian.encodeWords [value]) := by
  simp [ArgumentWord, Silmaril.X86.sysv64]

namespace CApi

/-- Boundary sanity: the signed status `Z_STREAM_ERROR = -2` is not a large
positive status even though its register representation has many set bits. -/
theorem signed_status_sanity :
    Scalar.signed .int32 (BitVec.ofInt 32 (-2)) = -2 := by decide

end CApi

end Silmaril.X86.SystemV
