module

public import Silmaril.Compiler.Native.Correctness.LiteralLoader.Defs
/-! Direct installed-memory proofs for the explicit loader, independent of
instruction values and fetched-byte execution. The fixed 83-byte bound is the
literal template's layout, not a successful-run premise. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.LiteralLoader
open Silmaril Silmaril.X86
open Silmaril.Process (Memory)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
attribute [local cbv_eval] String.toUTF8_eq_toByteArray

theorem code_read (code : List Byte) (length : code.length = 83) :
    (image code).initial.memory.readBytes 0x1000 code.length = some code := by
  apply Memory.readWith_eq
  · change (image code).initial.memory.checkSpan .read 0x1000 code.length = true
    rw [length]
    cbv
  · intro index bound
    have bound' : index < 83 := by omega
    change (Memory.install (Memory.install (Memory.install ∅ 0x1000 code)
      0x2ff8 (Machine.LittleEndian.encodeWords [0x4000]))
      0x5000 ((Silmaril.Compile.Core.Spec.argBlock 0x5000 ["a.out"]).map
        fun byte => BitVec.ofNat 8 byte.toNat)).get? (0x1000 + index) = some code[index]
    rw [Memory.install_outside _ _ _ _ (.inl (by omega))]
    rw [Memory.install_outside _ _ _ _ (.inl (by omega))]
    exact Memory.install_get _ _ code index bound

theorem code_fetch (code : List Byte) (length : code.length = 83) :
    (image code).initial.memory.fetchBytes 0x1000 code.length = some code := by
  apply Memory.readWith_eq
  · change (image code).initial.memory.checkSpan .execute 0x1000 code.length = true
    rw [length]
    cbv
  · intro index bound
    exact Memory.readWith_get (code_read code length) index bound

theorem return_read (code : List Byte) :
    (image code).initial.memory.readBytes 0x2ff8 8 =
      some (Machine.LittleEndian.encodeWords [0x4000]) := by
  refine Memory.readWith_eq (image code).initial.memory .read 0x2ff8
    (Machine.LittleEndian.encodeWords [(0x4000 : Word)]) (by cbv) ?_
  intro index bound
  have bound' : index < 8 := bound
  change (Memory.install (Memory.install (Memory.install ∅ 0x1000 code)
    0x2ff8 (Machine.LittleEndian.encodeWords [0x4000]))
    0x5000 ((Silmaril.Compile.Core.Spec.argBlock 0x5000 ["a.out"]).map
      fun byte => BitVec.ofNat 8 byte.toNat)).get? (0x2ff8 + index) = _
  rw [Memory.install_outside _ _ _ _ (.inl (by omega))]
  exact Memory.install_get _ _ _ index bound

theorem arguments_read (code : List Byte) :
    (image code).initial.memory.readBytes 0x5000
      (Silmaril.Compile.Core.Spec.argBlock 0x5000 ["a.out"]).length =
      some ((Silmaril.Compile.Core.Spec.argBlock 0x5000 ["a.out"]).map
        fun byte => BitVec.ofNat 8 byte.toNat) := by
  have read := Memory.readWith_eq (image code).initial.memory .read 0x5000
    ((Silmaril.Compile.Core.Spec.argBlock 0x5000 ["a.out"]).map
      fun byte => BitVec.ofNat 8 byte.toNat) (by cbv) (by
        intro index bound
        exact Memory.install_get _ _ _ index bound)
  simpa only [Memory.readBytes, List.length_map] using read

theorem loaded (code : List Byte) (length : code.length = 83) :
    Loaded ["a.out"] (image code) := by
  refine ⟨rfl, by cbv, ?_, ?_, code_read code length, ?_, rfl, rfl,
    arguments_read code, return_read code, by cbv, rfl, rfl, rfl, rfl⟩
  · change 0x1000 < 0x1000 + code.length
    omega
  · right
    change 0x1000 + code.length ≤ 0x4000
    omega
  · change (image code).initial.memory.checkSpan .execute 0x1000 code.length = true
    rw [length]
    cbv

theorem stack_read (code : List Byte) :
    (image code).initial.memory.Permitted .read (0x2ff8 - 48) 56 := by cbv

theorem stack_write (code : List Byte) :
    (image code).initial.memory.Permitted .write (0x2ff8 - 48) 48 := by cbv

end Silmaril.Compiler.Native.Correctness.LiteralLoader
