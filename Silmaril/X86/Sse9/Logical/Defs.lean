module

public import Init.Data.BitVec

/-!
# Legacy XMM XOR

Intel SDM Vol. 2, `PXOR` and `XORPS`: the legacy XMM forms read two 128-bit values
and combine them with bitwise XOR, irrespective of lane types. The operation needs
no flags, MXCSR, memory, or process state. The caller resolves operands and installs
the result in the low 128 bits of the destination only.
-/

@[expose] public section

namespace Silmaril.X86.Sse9.Logical

/-- Legacy 128-bit XMM forms only: no MMX or VEX/EVEX forms. -/
inductive Op where
  | pxor
  | xorps
  deriving DecidableEq, Repr

/-- Effective enablement of the legacy forms in the caller's 64-bit profile.
The caller accounts for hardware support and OS controls; these are not raw CPUID bits. -/
structure Profile where
  sse : Bool
  sse2 : Bool

/-- Whether the profile admits this operation. -/
def Op.enabled (op : Op) (profile : Profile) : Bool :=
  match op with
  | .pxor => profile.sse2
  | .xorps => profile.sse

/-- The destination value on defined execution, after both operands have been read. -/
def Op.eval (_ : Op) (dest source : BitVec 128) : BitVec 128 := dest ^^^ source

end Silmaril.X86.Sse9.Logical
