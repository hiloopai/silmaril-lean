module

public import Silmaril.Compiler.C.Sem.TargetsFit.Defs
public import Silmaril.Compiler.C.Sem.InterpCounterexample.Defs
@[expose] public section

/-!
# Small-instance checks of the image-fit targets

The earlier counterexample's one-byte image fits when the memory bound is 4096.
Both terminating premises are then inhabited. Its original zero-sized memory
violates the new premise, so the repair excludes that counterexample.
-/

namespace Silmaril.Compile.Mir.FitChecks

open Silmaril.Machine
open InterpCounterexample (units linked)

def cfg : Config := ⟨⟨4095, 0⟩, 4096⟩

theorem link_eq (t : Lir.Term Nat) : link cfg.layout (units t) = .ok (linked t) :=
  InterpCounterexample.link_eq t

theorem image_fits (t : Lir.Term Nat) :
    ∀ l, link cfg.layout (units t) = .ok l →
      ∀ i < l.image.size, l.dataBase + i < cfg.memSize := by
  intro l hl i hi
  rw [link_eq] at hl
  cases hl
  change i < 1 at hi
  change 4095 + i < 4096
  omega

theorem original_image_does_not_fit (t : Lir.Term Nat) :
    ¬ (∀ l, link InterpCounterexample.cfg.layout (units t) = .ok l →
      ∀ i < l.image.size, l.dataBase + i < InterpCounterexample.cfg.memSize) := by
  intro h
  have bad := h (linked t) (InterpCounterexample.link_eq t) 0 (by change 0 < 1; decide)
  exact (by decide : ¬ (4095 + 0 < 0)) bad

theorem run_returned :
    run cfg 1 (units (.ret [])) =
      .ok (.returned [] (Interp.initMem cfg (linked (.ret [])))) := by
  rw [run, link_eq]
  rfl

theorem run_trapped :
    run cfg 1 (units .trap) = .ok (.trapped (Interp.initMem cfg (linked .trap))) := by
  rw [run, link_eq]
  rfl

end Silmaril.Compile.Mir.FitChecks
