module

public import Silmaril.Data.IncludeBytes
public import Silmaril.Data.IncludeBytes.Kernel

/-! # Raw bytes and kernel bytes: kernel-only examples

The pinned `hello-gcc` (as in `Silmaril.Prelude.Bytes.KernelExamples`), included as raw bytes,
then related to kernel bytes without decoding a byte in the kernel. These are the kernel-only
examples of hiloopai/silmaril-lean#125; its native-fallback examples are not here, and
`kbytes_rel` refuses those goals instead (last section).
-/

@[expose] public section

namespace Silmaril.IncludeBytes.KernelExamples

open Silmaril.KBytes

noncomputable def helloRaw : ByteArray := include_bytes "../../../examples/dyn/pinned/hello-gcc"

-- Kernel bytes from the raw definition's literals, with `hello.toByteArray_eq`.
kbytes_def hello of_include helloRaw

example : hello.toByteArray = helloRaw := hello.toByteArray_eq

-- Kernel bytes read straight from the file, related to the raw include by `kbytes_rel`.
kbytes_def helloFile from_file "../../../examples/dyn/pinned/hello-gcc"

theorem helloFile_raw : helloFile.toByteArray = helloRaw := by kbytes_rel

/-- A kernel read is a statement about the raw bytes. -/
theorem raw_magic : helloRaw.data.toList.take 4 = [0x7f, 0x45, 0x4c, 0x46] := by
  rw [← hello.toByteArray_eq]
  have h1 : hello.read 0 4 = 0x464c457f := by decide +kernel
  have h2 := unpack_read hello hello.wf_true (off := 0) (w := 4) (by rw [hello.len_eq]; decide)
  rw [h1, List.drop_zero] at h2
  show hello.toList.take 4 = _
  rw [← h2]
  decide

/-! ## No fallback -/

noncomputable def otherRaw : ByteArray := include_bytes "../../../examples/dyn/pinned/hello-clang"

/--
error: kbytes_rel: the kernel rejected `Silmaril.IncludeBytes.KernelExamples.hello.toByteArray = decode 4096 16008 Silmaril.IncludeBytes.KernelExamples.hello.chunks` for this right-hand side (its literals are not Silmaril.IncludeBytes.KernelExamples.hello's)
-/
#guard_msgs in
example : hello.toByteArray = otherRaw := by kbytes_rel

/--
error: kbytes_rel: the right-hand side does not unfold to `IncludeBytes.decode c n [literals]`; there is no fallback (no native evaluation)
-/
#guard_msgs in
example : hello.toByteArray = helloRaw.extract 0 helloRaw.size := by kbytes_rel

end Silmaril.IncludeBytes.KernelExamples
