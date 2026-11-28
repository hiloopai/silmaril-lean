module

import Silmaril.Elf.Corpus.SqliteOneByteVarint.Thms

namespace Silmaril.Elf.Corpus.SqliteOneByteVarint

open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.X86

private def bias : Word := 0x200000

private def inputBytes : Silmaril.Process.ByteMemory := Memory.install ∅ 0x4004 [0x7f]
private def stackBytes : Silmaril.Process.ByteMemory :=
  Memory.install inputBytes 0x8008 (encodeWords [0x9000])
private def calleeBytes : Silmaril.Process.ByteMemory := Memory.install stackBytes 0x210a40 calleeCode

private def memory : Memory :=
  let bytes := Memory.install calleeBytes 0x2117b0 callerCode
  ⟨[⟨0x4004, 1, ⟨true, false, false⟩⟩,
    ⟨0x5000, 24, ⟨false, true, false⟩⟩,
    ⟨0x8000, 8, ⟨true, true, false⟩⟩,
    ⟨0x8008, 8, ⟨true, false, false⟩⟩,
    ⟨0x210a40, calleeCode.length, ⟨true, false, true⟩⟩,
    ⟨0x2117b0, callerCode.length, ⟨true, false, true⟩⟩], bytes⟩

private def fixture : MState :=
  let core : State := ⟨fun _ => 0, 0x2117b0, Ext.undefinedFlags, 0⟩
  ⟨((core.write .rsi 0x4000).write .rdx 0x5000).write .rsp 0x8008, memory⟩

private theorem inputReadable : memory.readBytes 0x4004 1 = some [0x7f] := by
  refine Memory.readWith_eq memory .read 0x4004 [0x7f] (by decide +kernel) (fun i hi => ?_)
  have zero : i = 0 := by simpa using hi
  subst i
  unfold memory calleeBytes stackBytes
  rw [Memory.install_outside _ _ _ _ (.inl (by decide)),
    Memory.install_outside _ _ _ _ (.inl (by decide)),
    Memory.install_outside _ _ _ _ (.inl (by decide))]
  exact Memory.install_get _ _ _ _ hi

private theorem returnReadable :
    memory.readBytes 0x8008 8 = some (encodeWords [0x9000]) := by
  refine Memory.readWith_eq memory .read 0x8008 (encodeWords [0x9000]) (by decide +kernel) (fun i hi => ?_)
  have small : i < 8 := by simpa using hi
  unfold memory calleeBytes stackBytes
  rw [Memory.install_outside _ _ _ _ (.inl (by omega)),
    Memory.install_outside _ _ _ _ (.inl (by omega))]
  exact Memory.install_get _ _ _ _ hi

private theorem windowsLoaded (w : Window) :
    Ext.Loaded fixture.memory (bias + BitVec.ofNat 64 w.va) w.code := by
  cases w
  · exact Memory.readWith_eq _ _ _ _ (by decide +kernel) (Memory.install_get _ _ _)
  · refine Memory.readWith_eq _ _ _ _ (by decide +kernel) (fun i hi => ?_)
    have small : i < 56 := hi
    change (Memory.install calleeBytes 0x2117b0 callerCode).get? (0x210a40 + i) = _
    rw [Memory.install_outside _ _ _ _ (.inl (by omega))]
    exact Memory.install_get _ _ _ _ hi

private theorem admit : Entry bias fixture 0x7f := by
  constructor
  · rfl
  · refine ⟨by decide +kernel, ?_⟩
    have target : FnContract.retOf fixture.core fixture.memory = 0x9000 := by
      change ((memory.readBytes 0x8008 8).bind wordOfBytes?).getD 0 = 0x9000
      rw [returnReadable, Option.bind_some, wordOfBytes?_encodeWords]
      rfl
    rw [target]
    exact returnReadable
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact inputReadable
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · unfold writable within
    decide +kernel
  · intro i hi
    change ¬ ((0x8000 ≤ 0x8008 + i ∧ 0x8008 + i < 0x8008) ∨
      (0x5000 ≤ 0x8008 + i ∧ 0x8008 + i < 0x5018))
    omega
  · intro i _
    change ¬ (0x5000 ≤ 0x8000 + i ∧ 0x8000 + i < 0x5018)
    omega
  · intro window i hi
    cases window
    · change ¬ ((0x8000 ≤ 0x2117b0 + i ∧ 0x2117b0 + i < 0x8008) ∨
        (0x5000 ≤ 0x2117b0 + i ∧ 0x2117b0 + i < 0x5018))
      omega
    · change ¬ ((0x8000 ≤ 0x210a40 + i ∧ 0x210a40 + i < 0x8008) ∨
        (0x5000 ≤ 0x210a40 + i ∧ 0x210a40 + i < 0x5018))
      omega

-- The input has one readable byte. The next byte and the write-only output
-- cannot be read. The admitted path still reaches the outer RET.
example : memory.readBytes 0x4005 1 = none ∧ memory.readBytes 0x5000 1 = none := by decide +kernel

example : ∃ final, Result bias fixture final 0x7f :=
  firstReturn_of_loaded windowsLoaded admit

#print axioms file_codeAt
#print axioms symbol_at
#print axioms firstReturn
#print axioms firstReturn_of_loaded

end Silmaril.Elf.Corpus.SqliteOneByteVarint
