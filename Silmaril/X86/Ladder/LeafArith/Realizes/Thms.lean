module

public import Silmaril.X86.Ladder.LeafArith.Thms
import Silmaril.Proofs.X86.Ladder.LeafArith.Realizes

/-!
# Ladder rung 01 (gcc -O2): the contracts as integer System V `Realizes` certificates

`bswap32_manual`, `sat_add_u32`, `clamp_i32` and `gcd_u32` as `Silmaril.Machine.SystemV.Realizes`
certificates (`FnContract.toRealizes`), for the C signatures `u32(u32)`, `u32(u32, u32)` and
`int(int, int, int)`. Split from `Silmaril.X86.Ladder.LeafArith.Thms` because the proofs import
the System V adapter `Silmaril.X86.FnContract.SystemV`, whose import closure cannot be loaded
together with the `Silmaril.Machine.X86` copies of the same declarations; the contracts and
certificate checks stay importable without it. The names are unchanged.
-/

@[expose] public section

namespace Silmaril.X86.Ladder.LeafArith

/-- `bswap32_manual` realizes `u32 bswap32_manual(u32)`. -/
theorem bswap32_manual_realizes :
    Silmaril.Machine.SystemV.Realizes sigU1 bswapResult noWrites (loadedAt 0xb0)
      (fun call final => Silmaril.Machine.Execution.Reaches Open.step call.initial final) :=
  Silmaril.Proofs.X86.Ladder.LeafArith.bswap_realizes

/-- `sat_add_u32` realizes `u32 sat_add_u32(u32, u32)`. -/
theorem sat_add_u32_realizes :
    Silmaril.Machine.SystemV.Realizes sigU2 satResult noWrites (loadedAt 0x90)
      (fun call final => Silmaril.Machine.Execution.Reaches Open.step call.initial final) :=
  Silmaril.Proofs.X86.Ladder.LeafArith.sat_realizes

/-- `clamp_i32` realizes `int clamp_i32(int, int, int)`. -/
theorem clamp_i32_realizes :
    Silmaril.Machine.SystemV.Realizes sigI3 clampResult noWrites (loadedAt 0x30)
      (fun call final => Silmaril.Machine.Execution.Reaches Open.step call.initial final) :=
  Silmaril.Proofs.X86.Ladder.LeafArith.clamp_realizes

/-- `gcd_u32` realizes `u32 gcd_u32(u32, u32)`. -/
theorem gcd_u32_realizes :
    Silmaril.Machine.SystemV.Realizes sigU2 gcdResult noWrites (loadedAt 0x0)
      (fun call final => Silmaril.Machine.Execution.Reaches Open.step call.initial final) :=
  Silmaril.Proofs.X86.Ladder.LeafArith.gcd_realizes

end Silmaril.X86.Ladder.LeafArith

end
