module

public import Silmaril.Process.LPS.Machines.RiscVLPS
public import Silmaril.RiscV.LPS.FpuLattice

/-!
# `riscvLps` over each floating-point variant

`riscvLpsWith fpu` is `riscvLps` with its step taken over the FPU `fpu`
(`Silmaril.RiscV.LPS.stepAccessesWith`); every other field is `riscvLps`'s. The variants of
`Silmaril.RiscV.LPS.FpuLattice` give four RISC-V process machines:

* `riscvLpsWith .lps = riscvLps` (`riscvLpsWith_lps`): the literal LPS machine;
* `riscvLpsIeee`: the same machine with Silmaril's IEEE 754 floating point;
* `riscvLpsAgreed`: floating-point steps where the two kernels disagree are unmodeled;
* `riscvLpsWith .chaos`: every floating-point step that reaches the FPU is unmodeled.

`riscvLpsWith_refines` lifts `FpuOps.Refines` to the process layer: wherever the coarser
machine's step is modeled, the finer machine takes the same step. In particular, every
step `riscvLpsAgreed` models is taken identically by `riscvLps` and by `riscvLpsIeee`
(`riscvLpsAgreed_step`). These are per-step statements; `Machines/RiscVLPSFpuRun` lifts
them to runs and behaviours.
-/

@[expose] public section

namespace Silmaril.Process.LPS.Machines

open Silmaril.RiscV.LPS (FpuOps stepAccessesWith)

/-- `riscvLps` with the floating-point unit `fpu`. -/
def riscvLpsWith (fpu : FpuOps) : UserIsa where
  State := RiscV.LPS.MachineState
  step segs st := ofLpsResult (stepAccessesWith fpu (lpsSegments segs) st)
  svcPending st := st.svcPending
  syscallArgs := lpsSyscallArgs
  readByte _ st := st.readByte
  writableByte segs st := RiscV.LPS.MachineState.writableByte (lpsSegments segs) st
  applyEffect := lpsApplyEffect
  advancePastSvc := lpsAdvancePastSvc
  init := lpsInit
  reportsAccesses := true
  entryFetchable := lpsEntryFetchable

/-- Silmaril's IEEE 754 floating point under LPS's RISC-V machine. -/
def riscvLpsIeee : UserIsa := riscvLpsWith FpuOps.ieee

/-- LPS's RISC-V machine, unmodeled wherever the two FPU kernels disagree. -/
def riscvLpsAgreed : UserIsa := riscvLpsWith FpuOps.agreed

theorem riscvLpsWith_lps_step (segs : List Segment) (st : RiscV.LPS.MachineState) :
    (riscvLpsWith FpuOps.lps).step segs st = riscvLps.step segs st := by
  change ofLpsResult _ = ofLpsResult _
  rw [RiscV.LPS.stepAccessesWith_lps]

/-- Over the literal LPS kernel, the machine is `riscvLps`. -/
theorem riscvLpsWith_lps : riscvLpsWith FpuOps.lps = riscvLps := by
  unfold riscvLpsWith riscvLps
  congr 1
  funext segs st
  exact riscvLpsWith_lps_step segs st

theorem ofLpsResult_ne_unmodeled {α : Type}
    {r : RiscV.LPS.MachineResult (RiscV.LPS.AccessReport α)}
    (h : ofLpsResult r ≠ .unmodeled) : r ≠ .unmodeled := by
  rintro rfl
  exact h rfl

/-- Refinement of the FPU lifts to the process machine: every step the coarse machine
models is the fine machine's step. -/
theorem riscvLpsWith_refines {fine coarse : FpuOps} (h : FpuOps.Refines fine coarse)
    (segs : List Segment) (st : RiscV.LPS.MachineState)
    (hu : (riscvLpsWith coarse).step segs st ≠ .unmodeled) :
    (riscvLpsWith fine).step segs st = (riscvLpsWith coarse).step segs st := by
  change ofLpsResult _ = ofLpsResult _
  rw [RiscV.LPS.stepAccessesWith_refines h _ st (ofLpsResult_ne_unmodeled hu)]

/-- Every step `riscvLpsAgreed` models is the step of `riscvLps` and of `riscvLpsIeee`. -/
theorem riscvLpsAgreed_step (segs : List Segment) (st : RiscV.LPS.MachineState)
    (hu : riscvLpsAgreed.step segs st ≠ .unmodeled) :
    riscvLps.step segs st = riscvLpsAgreed.step segs st ∧
      riscvLpsIeee.step segs st = riscvLpsAgreed.step segs st := by
  refine ⟨?_, riscvLpsWith_refines FpuOps.ieee_refines_agreed segs st hu⟩
  rw [← riscvLpsWith_lps_step]
  exact riscvLpsWith_refines FpuOps.lps_refines_agreed segs st hu

end Silmaril.Process.LPS.Machines
