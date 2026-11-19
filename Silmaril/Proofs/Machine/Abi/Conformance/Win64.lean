module

public import Silmaril.Machine.Abi.Conformance.Win64.Defs
public import Silmaril.Proofs.Machine.Abi.Conformance.SysvInt

/-!
# The Microsoft x64 INTEGER fragment: result read-back

`win64Int` reads a 32-bit result from the low half of RAX, exactly as `sysvInt` does
(`Machine.Abi.Win64.win64_resultAt_iff`, `SysvInt.chunk32_iff`).
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Abi.Conformance.Win64

open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi.Conformance

theorem resultAt_int32 (args : List Silmaril.C.Api.Scalar)
    (h : args.length ≤ Silmaril.Machine.Abi.SystemV.maxArity) (s s' : Ffi.State) (r : BitVec 32) :
    win64Int.conv.ResultAt ⟨⟨args, some .int32⟩, h⟩ s s' r ↔
      (s'.machine.core.read .rax).setWidth 32 = r := by
  refine (Silmaril.Machine.Abi.Win64.win64_resultAt_iff _ _ _ _).trans ?_
  constructor
  · rintro ⟨w, enc, ch⟩
    change w = _ at enc
    subst enc
    exact (SysvInt.chunk32_iff s' .rax r).1 ch
  · exact fun e => ⟨_, rfl, (SysvInt.chunk32_iff s' .rax r).2 e⟩

theorem resultAt_uint32 (args : List Silmaril.C.Api.Scalar)
    (h : args.length ≤ Silmaril.Machine.Abi.SystemV.maxArity) (s s' : Ffi.State) (r : BitVec 32) :
    win64Int.conv.ResultAt ⟨⟨args, some .uint32⟩, h⟩ s s' r ↔
      (s'.machine.core.read .rax).setWidth 32 = r := by
  refine (Silmaril.Machine.Abi.Win64.win64_resultAt_iff _ _ _ _).trans ?_
  constructor
  · rintro ⟨w, enc, ch⟩
    change w = _ at enc
    subst enc
    exact (SysvInt.chunk32_iff s' .rax r).1 ch
  · exact fun e => ⟨_, rfl, (SysvInt.chunk32_iff s' .rax r).2 e⟩

end Silmaril.Proofs.Machine.Abi.Conformance.Win64

end
