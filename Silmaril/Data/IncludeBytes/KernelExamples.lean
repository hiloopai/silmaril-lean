module

public import Silmaril.Data.IncludeBytes
public import Silmaril.Data.IncludeBytes.Kernel
public import Silmaril.Prelude.Trust.Policy.Defs
-- A native run interprets `IncludeBytes.decode`, so its code must be loaded at elaboration time.
meta import Silmaril.Data.IncludeBytes.Types

/-! # Raw bytes and kernel bytes: examples

The same pinned `hello-gcc` as `Silmaril.Prelude.Bytes.Examples`, included as raw bytes, then
related to kernel bytes without decoding a byte in the kernel.
-/

@[expose] public section

-- These tests check each profile's behaviour, so they fix the profile they start from.
set_option silmaril.trust.profile "default"

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
  have h2 := unpack_read hello hello.wf (off := 0) (w := 4) (by rw [hello.len_eq]; decide)
  rw [h1, List.drop_zero] at h2
  show hello.toList.take 4 = _
  rw [← h2]
  decide

/-! ## Other raw terms: the native fallback -/

def helloRawC : ByteArray := include_bytes "../../../examples/dyn/pinned/hello-gcc"

kbytes_def helloC from_file "../../../examples/dyn/pinned/hello-gcc" computable

/-- `raw` is a computation, not chunk literals, so `kbytes_rel` runs `bytes.eqByteArray`
natively (default profile). -/
theorem helloC_extract : helloC.toByteArray = helloRawC.extract 0 helloRawC.size := by kbytes_rel

-- The paranoid profile has no way to check it: `bytes.eqByteArray` has no kernel fallback.
/--
error: edge_decide: bytes.eqByteArray may not run natively in Silmaril.Data.IncludeBytes.KernelExamples under profile paranoid, and it has no kernel fallback
-/
#guard_msgs in
set_option silmaril.trust.profile "paranoid" in
example : helloC.toByteArray = helloRawC.extract 0 helloRawC.size := by kbytes_rel

-- The structural bridge has no native axiom; the fallback has one.
/--
info: {"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.IncludeBytes.KernelExamples.helloFile_raw","dep_native":[],"kind":"audit","module":"Silmaril.Data.IncludeBytes.KernelExamples","native_axioms":[],"own_native":[]}
{"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.IncludeBytes.KernelExamples.raw_magic","dep_native":[],"kind":"audit","module":"Silmaril.Data.IncludeBytes.KernelExamples","native_axioms":[],"own_native":[]}
{"axioms":["propext","Classical.choice","Quot.sound"],"decl":"Silmaril.IncludeBytes.KernelExamples.helloC_extract","dep_native":[],"kind":"audit","module":"Silmaril.Data.IncludeBytes.KernelExamples","native_axioms":["_private.Silmaril.Data.IncludeBytes.KernelExamples.0.Silmaril.IncludeBytes.KernelExamples.helloC_extract._native.edge.bytes.eqByteArray.ax_1_1"],"own_native":["bytes.eqByteArray"]}
-/
#guard_msgs in
trust_audit helloFile_raw raw_magic helloC_extract

end Silmaril.IncludeBytes.KernelExamples
