module

public import Silmaril.RiscV.LPS.FpuOps
public import Silmaril.RiscV.LPS.FpuIeee

/-!
# The lattice of RISC-V floating-point variants

Four FPUs for the LPS RISC-V semantics (`execWith`, `stepAccessesWith`), ordered by
`FpuOps.Refines` (finer below):

```
                 chaos                  every request unmodeled
                   │
                agreed                  answered iff LPS and IEEE agree
               ╱      ╲
            lps        ieee             the literal LPS kernel; Silmaril IEEE 754
```

* `FpuOps.lps` is `Silmaril.RiscV.LPS.Fpu`, the literal port of LPS's `Riscv/Fpu.v`
  (`stepAccessesWith_lps`: the machine is exactly `step_accesses`).
* `FpuOps.ieee` is `Silmaril.RiscV.LPS.Ieee`, the same operations over Silmaril's IEEE
  754 model and RISC-V profile (`Profile.riscvFD`).
* `FpuOps.agreed` answers a request only when the two compute the same bits and flags,
  and declines (unmodeled) otherwise. It is decidable per request, needs no theorem
  about either kernel to be sound, and is refined by both (`lps_refines_agreed`,
  `ieee_refines_agreed`).
* `FpuOps.chaos` declines every request.

By `stepAccessesWith_refines`, a statement about a modeled step of the `agreed`
machine holds for the literal LPS machine and for the IEEE machine alike: on modeled
steps they all coincide (`stepAccesses_eq_ieee_of_agreed`). The set of requests where
`agreed` declines is exactly the set of disagreements between the kernels. It is small:
`Silmaril.RiscV.LPS.FpuAgreeAll` proves that `agreed` answers, as `lps` does, every
covered request (`FpuOps.agreed_of_covered`), and `Silmaril.RiscV.LPS.FpuCoverage` proves
that every request the machine issues is covered except divisions whose exact quotient is
nonzero and below `2 ^ emin`, where the kernels can disagree on UF
(`Silmaril.RiscV.LPS.FpuFindings`). The TestFloat tables
(`Silmaril.RiscV.LPS.FpuTestFloat`) check both kernels against SoftFloat.

These statements are per step. `Process/LPS/Machines/RiscVLPSFpuRun` lifts them to LPS's
run semantics: a run of the coarse machine that never reaches an unmodeled configuration
has the same behaviour (traces, errors, all-errors) under every refinement.
-/

@[expose] public section

namespace Silmaril.RiscV.LPS

/-- Silmaril's IEEE 754 RISC-V F/D (`Silmaril.RiscV.LPS.Ieee`). -/
def FpuImpl.ieee : FpuImpl where
  add := Ieee.fpAdd
  sub := Ieee.fpSub
  mul := Ieee.fpMul
  div := Ieee.fpDiv
  sqrt := Ieee.fpSqrt
  fma := Ieee.fpFma
  minMax := Ieee.fpMinMax
  eq := Ieee.fpEq
  lt := Ieee.fpLt
  le := Ieee.fpLe
  cls := Ieee.fpClass
  toInt := Ieee.fpToInt
  ofInt := Ieee.fpOfInt
  convert := Ieee.fpConvert

namespace FpuOps

/-- Silmaril's IEEE 754 FPU. -/
def ieee : FpuOps := FpuImpl.ieee.ops

/-- Answer only where the literal LPS kernel and Silmaril IEEE agree. -/
def agreed : FpuOps := fun r =>
  let x := FpuImpl.lps.run r
  if x = FpuImpl.ieee.run r then some x else none

theorem lps_refines_agreed : Refines lps agreed := by
  intro r v h
  simp only [agreed] at h
  split at h
  · exact h
  · cases h

theorem ieee_refines_agreed : Refines ieee agreed := by
  intro r v h
  simp only [agreed] at h
  split at h
  · next he => cases h; simp only [ieee, FpuImpl.ops, ← he]
  · cases h

theorem agreed_refines_chaos : Refines agreed chaos := refines_chaos _

/-- `agreed` answers a request exactly when the kernels agree on it. -/
theorem agreed_eq_some_iff (r : FpReq) :
    (agreed r).isSome ↔ FpuImpl.lps.run r = FpuImpl.ieee.run r := by
  simp only [agreed]
  split <;> simp_all

end FpuOps

/-- On every step the `agreed` machine models, the literal LPS machine (`step_accesses`)
and the Silmaril IEEE machine take the same step. -/
theorem stepAccesses_eq_ieee_of_agreed (segs : List Segment) (st : MachineState)
    (hu : stepAccessesWith FpuOps.agreed segs st ≠ .unmodeled) :
    stepAccesses segs st = stepAccessesWith FpuOps.agreed segs st ∧
      stepAccessesWith FpuOps.ieee segs st = stepAccessesWith FpuOps.agreed segs st :=
  ⟨(stepAccessesWith_lps segs st).symm.trans
      (stepAccessesWith_refines FpuOps.lps_refines_agreed segs st hu),
    stepAccessesWith_refines FpuOps.ieee_refines_agreed segs st hu⟩

end Silmaril.RiscV.LPS
