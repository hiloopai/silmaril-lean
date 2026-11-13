module

public import Silmaril.Prelude.Bytes.Thms
public import Silmaril.Prelude.Trust.Elab.Defs
-- Native runs interpret these functions while elaborating, so their code is loaded as `meta`.
public meta import Silmaril.Prelude.Bytes.Thms

/-! # Native procedures on kernel bytes

The procedures `edge_decide` may run on `KBytes` (`Silmaril.Prelude.Trust`). Each one is a
`Bool` function with a soundness theorem in `Silmaril.Prelude.Bytes.Thms`. A native run of one
of them trusts the Lean compiler and runtime: GMP big-number arithmetic for `read`, and the
`@[csimp]` replacement of `unpack` by `unpackFast` (proved equal) for `toList`. The arguments
must be compiled too, so a `kbytes_def` used natively must be `computable`, and the modules
defining any function in the arguments must be imported with `meta import` (the interpreter
runs their code while the proof elaborates).
-/

/-- Same bytes, by windows (`KBytes.toList_eq_of_sameBytes`). Kernel fallback measured at
about 55 ms per MiB with 64 KiB windows (benchmarks/kernel-bytes). -/
native_decider bytes.sameBytes := Silmaril.KBytes.sameBytes with_kernel_fallback
  sound Silmaril.KBytes.toList_eq_of_sameBytes

/-- Structural equality (`KBytes.toList_eq_of_beq`). The kernel fallback is cheap; `rfl` is
cheaper still on canonical trees. -/
native_decider bytes.beq := Silmaril.KBytes.beq with_kernel_fallback
  sound Silmaril.KBytes.toList_eq_of_beq

/-- Cached lengths are correct (`KBytes.wf`). Cheap in the kernel. No soundness theorem is
registered: `wf` is a hypothesis of the specification theorems, not a fact they conclude. -/
native_decider bytes.wf := Silmaril.KBytes.wf with_kernel_fallback

/-- Kernel bytes equal a `ByteArray` (`KBytes.toByteArray_eq_of_eqByteArray`). There is no
kernel fallback: the kernel would build both byte lists one cell per byte. For bytes from
`include_bytes`, use the structural bridge (`kbytes_rel`) instead, which needs no evaluation. -/
native_decider bytes.eqByteArray := Silmaril.KBytes.eqByteArray
  sound Silmaril.KBytes.toByteArray_eq_of_eqByteArray
