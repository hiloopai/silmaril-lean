module

public import Silmaril.X86.Features.Ext.X87.Semantics

/-!
# The x87 extension lane

`Fpu.ext` packages the x87 instructions for the feature-parametric machine.

## Features

Every x87 instruction requires the FPU (`Feature.x87`, CPUID.01H:EDX[0]).
FISTTP additionally requires SSE3 (SDM Vol. 2A, FISTTP: "#UD if
CPUID.01H:ECX.SSE3[bit 0] = 0"). FCMOVcc, FCOMI and FUCOMI(P) also list CMOV
(CPUID.01H:EDX[15]); `Feature` has no CMOV entry because CMOV is part of the
x86-64 baseline (every processor that supports 64-bit mode has it, as it has
the FPU, SSE and SSE2), so in 64-bit mode their requirement is `x87`.
-/

@[expose] public section

namespace Silmaril.X86.Features.Fpu

/-- The features an x87 instruction requires. -/
def requires : Instr → List Feature
  | .fisttp _ _ => [.x87, .sse3]
  | _ => [.x87]

/-- The x87 extension. -/
def ext : Extension where
  name := "x87"
  Syntax := Instr
  decoder := byteDecoder
  requires := requires
  exec := exec

theorem ext_decode : ext.decoder.decode = decode := rfl
theorem ext_exec : ext.exec = exec := rfl

end Silmaril.X86.Features.Fpu
