module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VInv.Ctx
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.VInv.StepB

/-!
# Round 7, memory SIMD: the backend whole step without memory SIMD instructions

`sstepB_withVBytes_iff_noMS`: on values whose left-hand side has no memory SIMD instruction at any
depth, the backend whole step `SStepB` reads alike at `withVBytes B` and at `B`
(`sstepB_withVBytes_iff` at the concrete invariant `stepInvB_noMS`). `sreadB_withVBytes_iff_noMS`
is the same for `Step_read`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VInv

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Round6.Reading (SStepB SReadB)

/-- **On values without memory SIMD instructions in the left-hand side, the backend whole step
reads alike at `withVBytes B` and at `B`.** -/
theorem sstepB_withVBytes_iff_noMS (B : Builtins) {c c' : Value}
    (hq : LhsNoAtoms msAtoms (.tuple [c, c'])) :
    SStepB (simEnv (MemSimd.withVBytes B)) c c' ↔ SStepB (simEnv B) c c' :=
  sstepB_withVBytes_iff B stepInvB_noMS hq

/-- The same, stated on the source alone. -/
theorem sstepB_withVBytes_iff_of_noAtoms (B : Builtins) {c c' : Value} (hc : NoAtoms msAtoms c) :
    SStepB (simEnv (MemSimd.withVBytes B)) c c' ↔ SStepB (simEnv B) c c' :=
  sstepB_withVBytes_iff_noMS B ⟨c, c', rfl, hc⟩

/-- **Backend `Step_read` without memory SIMD instructions in the source reads alike at
`withVBytes B` and at `B`.** -/
theorem sreadB_withVBytes_iff_of_noAtoms (B : Builtins) {c : Value} {js : List Value}
    (hc : NoAtoms msAtoms c) :
    SReadB (simEnv (MemSimd.withVBytes B)) c js ↔ SReadB (simEnv B) c js :=
  ⟨sreadB_agree (VAgree.agreeOff_withVBytes B) stepInvB_noMS ⟨c, _, rfl, hc⟩,
    sreadB_agree (VAgree.agreeOff_symm (VAgree.agreeOff_withVBytes B)) stepInvB_noMS
      ⟨c, _, rfl, hc⟩⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.VInv
