module

public import Silmaril.X86.MemoryModel.Lattice.Witness.Defs
public import Silmaril.X86.MemoryModel.Lattice.Thms
import Silmaril.Proofs.X86.MemoryModel.Lattice.Witness

/-!
# The lattice's witness executions: verdicts

PROVED (standard axioms only). For every hardware litmus test of `tools/litmus-hw/lattice_hw.c`,
the verdicts of the six models on its witness outcome (`Witness.Defs`). `top` allows every
execution.
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Lattice.Witness

open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Axiomatic.Sanity
open Silmaril.X86.MemoryModel.Lattice

/-- `Exec.row` is exact when `hb` and `hbL` are closed. -/
theorem verdict_of_row (x : Exec) (hc : x.hbClosedB = true) (hcL : x.hbLClosedB = true) :
    Verdict x x.row := Proofs.verdict_of_row x hc hcL

/-- A computed row is the verdict row. -/
theorem verdict_of_check {x : Exec} {r : Row} (hc : x.hbClosedB = true)
    (hcL : x.hbLClosedB = true) (h : x.row = r) : Verdict x r := h ▸ verdict_of_row x hc hcL

/-- SB: TSO and everything above it allow the weak outcome; SC forbids it. -/
theorem sb_row : Verdict sb ⟨false, true, true, true, true, true⟩ :=
  verdict_of_check (by decide) (by decide) (by decide)

/-- SB+mfences: only RA (which ignores fences) and the catch-fire models (it is racy) allow it. -/
theorem sbMfence_row : Verdict sbMfence ⟨false, false, true, false, true, true⟩ :=
  verdict_of_check (by decide) (by decide) (by decide)

/-- SB+xchgs: as SB+mfences. -/
theorem sbXchg_row : Verdict sbXchg ⟨false, false, true, false, true, true⟩ :=
  verdict_of_check (by decide) (by decide) (by decide)

/-- MP: forbidden by every model but `top` (race-free). -/
theorem mp_row : Verdict mp ⟨false, false, false, false, false, false⟩ :=
  verdict_of_check (by decide) (by decide) (by decide)

/-- LB: forbidden by every model but `top` (race-free). -/
theorem lb_row : Verdict lb ⟨false, false, false, false, false, false⟩ :=
  verdict_of_check (by decide) (by decide) (by decide)

/-- IRIW: allowed by RA and the catch-fire models, forbidden by SC, TSO and XL. -/
theorem iriw_row : Verdict iriw ⟨false, false, true, false, true, true⟩ :=
  verdict_of_check (by decide) (by decide) (by decide)

/-- 2+2W: as IRIW. -/
theorem w22_row : Verdict w22 ⟨false, false, true, false, true, true⟩ :=
  verdict_of_check (by decide) (by decide) (by decide)

/-- MP+movnti: allowed by XL only (race-free, so the catch-fire models forbid it). -/
theorem mpNt_row : Verdict mpNt ⟨false, false, false, true, false, false⟩ :=
  verdict_of_check (by decide) (by decide) (by decide)

/-- MP+movnti+sfence: forbidden by every model but `top`. -/
theorem mpNtSfence_row : Verdict mpNtSfence ⟨false, false, false, false, false, false⟩ :=
  verdict_of_check (by decide) (by decide) (by decide)

/-- A torn misaligned store: allowed by XL and (split accesses) the catch-fire models. -/
theorem torn_row : Verdict torn ⟨false, false, false, true, true, true⟩ :=
  verdict_of_check (by decide) (by decide) (by decide)

/-- Two unlocked increments losing one: sequentially consistent. -/
theorem inc2_row : Verdict inc2 ⟨true, true, true, true, true, true⟩ :=
  verdict_of_check (by decide) (by decide) (by decide)

/-- Two `lock inc` losing one: allowed by `cfPlain` only (racy for `hb`, race-free for `hbL`). -/
theorem lockInc_row : Verdict lockInc ⟨false, false, false, false, false, true⟩ :=
  verdict_of_check (by decide) (by decide) (by decide)

/-- CoWR in one thread: forbidden by every model but `top`. -/
theorem coWR_row : Verdict coWR ⟨false, false, false, false, false, false⟩ :=
  verdict_of_check (by decide) (by decide) (by decide)

/-- CoWR with a second writer, reading the initial value: allowed by the catch-fire models
only (the writes race). -/
theorem coWR2_row : Verdict coWR2 ⟨false, false, false, false, true, true⟩ :=
  verdict_of_check (by decide) (by decide) (by decide)

/-- CoWR with a second writer, reading it but ending with its own write: as `coWR2`. -/
theorem coWR2b_row : Verdict coWR2b ⟨false, false, false, false, true, true⟩ :=
  verdict_of_check (by decide) (by decide) (by decide)

end Silmaril.X86.MemoryModel.Lattice.Witness
