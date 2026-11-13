module

public import Silmaril.Compiler.Native.Varargs.Reconstruction.Defs
/-! Actual full register-save slots, preceding the byte reconstruction layer.
No prologue execution or reconstructed value is part of these premises. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Varargs.SaveArea
open Silmaril.Machine.SystemV.Abi

/-- The fourteen complete slots written by the native entry emitter. The
strict endpoint bound covers the zero-byte subread at the last XMM endpoint. -/
structure SlotsAt (entry saved : Ffi.State) (base : Nat) : Prop where
  endpoint : base + saveBytes < 2 ^ 64
  gp : ∀ register ∈ gpArguments,
    Ffi.StoredAt saved (base + 8 * gpArguments.idxOf register)
      (Ffi.bytesOfNat (entry.machine.core.read register).toNat 0 8)
  fp : ∀ index < 8,
    Ffi.StoredAt saved (base + 48 + 16 * index)
      (Ffi.bytesOfNat (entry.vectors index).toNat 0 16)

end Silmaril.Compiler.Native.Varargs.SaveArea
