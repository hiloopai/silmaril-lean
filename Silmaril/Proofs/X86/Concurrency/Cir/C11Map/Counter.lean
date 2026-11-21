module

public import Silmaril.X86.Concurrency.Cir.C11.Defs
public import Silmaril.X86.Concurrency.Cir.Rc11.Thms
public import Silmaril.X86.MemoryModel.Xl.Thms

/-!
# The x86 mapping is correct for RC11: why `Cells` is needed

`pfx` is a well-formed x86-TSO-consistent execution with relaxed roles
that is not RC11-consistent: thread 0 stores byte 0 and loads the two bytes 0–1, taking byte 0
from its own store (partial store forwarding) and byte 1 from the initial state; thread 1
stores byte 1 and loads byte 0 from the initial state (store buffering). RC11 sees
`r₁ →fr w₀ →rf r₀ →fr w₁` across the two bytes and `w₁ →po r₁`, a coherence violation; TSO
has no cycle because the two `po` edges are write-to-read. Its memory units overlap without
being one cell, which the units of CIR runs never do (`units` splits such accesses into bytes).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.C11Map

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.MemoryModel.Axiomatic

/-- The partial-forwarding execution. -/
def pfx : Exec where
  evs := [{ tid := 0, pos := 0, act := .write, addr := 0, size := 1, data := [1] },
          { tid := 0, pos := 1, act := .read, addr := 0, size := 2 },
          { tid := 1, pos := 0, act := .write, addr := 1, size := 1, data := [1] },
          { tid := 1, pos := 1, act := .read, addr := 0, size := 1 }]
  rf := fun r y => if r = 1 ∧ y = 0 then some 0 else none
  co := fun y => if y = 0 then [0] else if y = 1 then [2] else []

theorem pfx_wf : pfx.Wf = true := by decide

theorem pfx_tso : pfx.Tso := by decide

theorem pfx_not_rc11 : ¬ Rc11.Consistent (fun _ => .acc .rlx) pfx := by
  have h : Rc11.judge (fun _ => .acc .rlx) pfx = some (false, false) := by decide
  intro hc
  have := ((Rc11.judge_spec h).1).mpr hc
  cases this

theorem pfx_mapRoles : C11.MapRoles (fun _ => .acc .rlx) pfx := by
  intro a
  simp [Role.sc, Role.isF]

theorem pfx_not_cells : ¬ C11.Cells pfx := by
  intro h
  have := h ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) (by decide) 0 (by decide) (by decide)
  simp [pfx, Exec.ev] at this

end Silmaril.Proofs.X86.Concurrency.Cir.C11Map
