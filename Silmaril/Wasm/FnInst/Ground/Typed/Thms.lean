module

public import Silmaril.Proofs.Wasm.FnInst.Ground.Typed
public import Silmaril.Wasm.FnInst.Ground.Forced.Thms
public import Silmaril.Wasm.Binaryen.CodeSimTyped

@[expose] public section

/-! # The typed bridge: `drop-get` at every profile, reads of several locals

Header of `Silmaril.Proofs.Wasm.FnInst.Ground.Typed`.

* `gTypedSim`: typed pairs (`GoodT`: stack-only left side, equal runs where the right side's
  leading reads hold values) satisfy silmaril's `TypedBaseSim` at every numerical profile;
  `refines_of_goodT` is the transfer to export refinement (`exportRefines_of_typedBodiesRel`).
* **`dropGet_sound_ground_any`**: `drop-get` restated at **every** profile, forward through
  the frame-free bridge (`good_dropGet`), backward through the typed one (`goodT_nopGetDrop`).
  an earlier step and 2 stated the grounded `drop-get` at deterministic profiles only.
* `goodT_nopReads`: a right side that reads **two different locals** (`local.get x;
  local.get y; drop; drop`, against `nop`), so `nopReads_refines`: the module without the dead
  reads refines the one with them, at every profile. The frame-free bridge cannot state this:
  in an untyped frame `y` may be missing.
-/

namespace Silmaril.Wasm.FnInst.Ground

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {m m' : Module}

/-- **The typed transfer**: a family of rules whose pairs are all typed pairs. -/
theorem refines_of_goodT {BI : List Instr → List Instr → Prop} (hBI : ∀ x y, BI x y → GTI x y)
    (hrel : ModuleBodiesRel BI m m') (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportRefines (· = ·) P (closedHost (H := H)) m m' :=
  exportRefines_of_typedBodiesRel gTypedSim
    (closedHost_codeParametric.respects (fun f => FuncRel.refl f)) (bodiesRel_mono hBI hrel) hm hm'

/-! ## Rule lemmas -/

theorem stkOp_nop : StkOp [.nop] := ⟨by simp [GInstr.stk], ⟨.nop, by simp, rfl⟩⟩

/-- `nop` against a dropped read: equal runs wherever the read holds a value. -/
theorem goodT_nopGetDrop (x : LocalIdx) : GoodT [.nop] [.localGet x, .drop] := by
  refine ⟨stkOp_nop, fun f st r ⟨⟨v, hv⟩, _⟩ h => ?_⟩
  have hr : r = (f, st) := (Option.some.inj h).symm
  rw [hr]
  show run ([.localGet x] ++ [.drop]) f st = some (f, st)
  rw [run_append, run_get hv]
  rfl

/-- `nop` against two dropped reads of (possibly different) locals. -/
theorem goodT_nopReads (x y : LocalIdx) :
    GoodT [.nop] [.localGet x, .localGet y, .drop, .drop] := by
  refine ⟨stkOp_nop, fun f st r ⟨⟨v, hv⟩, ⟨w, hw⟩, _⟩ h => ?_⟩
  have hr : r = (f, st) := (Option.some.inj h).symm
  rw [hr]
  show run ([.localGet x] ++ ([.localGet y] ++ [.drop, .drop])) f st = some (f, st)
  rw [run_append, run_get hv, Option.bind_some, run_append, run_get hw]
  rfl

/-- The reversed `drop-get` pairs (result on the left) are typed pairs. -/
theorem dgBI_goodT_rev : ∀ x y, Silmaril.Wasm.Binaryen.DropGet.dgBI y x → GTI x y
  | _, _, .mk x => ⟨_, _, goodT_nopGetDrop x, rfl, rfl⟩

/-- **`drop-get`, restated at every profile**: `good_dropGet` through the frame-free bridge,
`goodT_nopGetDrop` through the typed bridge. -/
theorem dropGet_sound_ground_any {m : BModule} (hm : m.Ok)
    (hm' : (Silmaril.Wasm.Binaryen.DropGet.dropGet m).Ok) :
    ExportEquiv (· = ·) P (closedHost (H := H)) m.lower
      (Silmaril.Wasm.Binaryen.DropGet.dropGet m).lower :=
  equiv_of_refines
    (refines_of_good dgBI_good (Silmaril.Wasm.Binaryen.DropGet.dropGet_bodiesRel m) hm hm')
    (refines_of_goodT dgBI_goodT_rev (Silmaril.Wasm.Binaryen.DropGet.dropGet_bodiesRel m).flip hm' hm)

/-- Removing two dead reads: the module without them refines the one with them, at every
profile (the right side reads two locals; typing supplies both values). -/
theorem nopReads_refines {x y : LocalIdx}
    (hrel : ModuleBodiesRel (Pair [.nop] [.localGet x, .localGet y, .drop, .drop]) m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportRefines (· = ·) P (closedHost (H := H)) m m' := by
  refine refines_of_goodT ?_ hrel hm hm'
  rintro _ _ ⟨rfl, rfl⟩
  exact ⟨_, _, goodT_nopReads x y, rfl, rfl⟩

end Silmaril.Wasm.FnInst.Ground
