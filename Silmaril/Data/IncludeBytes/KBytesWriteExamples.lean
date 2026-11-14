module

public import Silmaril.Data.IncludeBytes.KBytesExamples
public import Silmaril.Prelude.Bytes.Write.Thms

/-! # Raw bytes and kernel bytes: writes

A write on kernel bytes is a statement about the raw `include_bytes` bytes it was built from,
with no byte decoded in the kernel: the bridge `hello.toByteArray_eq` and the specification
`toList_write` compose.
-/

@[expose] public section

namespace Silmaril.IncludeBytes.KBytesWriteExamples

open Silmaril.KBytes Silmaril.IncludeBytes.KBytesExamples

theorem hello_toList : hello.toList = helloRaw.data.toList := by
  rw [← hello.toByteArray_eq]; rfl

/-- Patching `e_entry` of the kernel bytes patches the raw file's bytes. -/
theorem patched_raw (v : Nat) :
    (hello.write 24 8 v).toList = splice helloRaw.data.toList 24 8 v := by
  rw [toList_write hello 24 8 v hello.wf_true (by rw [hello.len_eq]; decide), hello_toList]

/-- Byte 25 of the patched raw file is the second byte of the new entry point. -/
theorem patched_raw_byte (v : Nat) :
    (splice helloRaw.data.toList 24 8 v)[25]? = some (UInt8.ofNat (v / 256)) := by
  have hl : 24 + 8 ≤ helloRaw.data.toList.length := by
    rw [← hello_toList, length_toList hello hello.wf_true, hello.len_eq]; decide
  rw [getElem?_splice _ _ _ _ _ hl]
  simp

end Silmaril.IncludeBytes.KBytesWriteExamples
