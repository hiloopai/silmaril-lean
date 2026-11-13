module

public import Silmaril.Proofs.Wasm.FnInst.Ground.ForcedRules
public import Silmaril.Wasm.FnInst.Ground.Rules.Thms
public import Silmaril.Wasm.Binaryen.TeeForm.Thms

@[expose] public section

/-! # Grounding at every profile, and left sides that write locals

Header of `Silmaril.Proofs.Wasm.FnInst.Ground.{Forced,ForcedRules}`.

* `wDeferredSim` (**the deferred bridge**): `GoodW` pairs (local code with equal runs that
  cannot get stuck after its first non-constant step; it may write locals and read several)
  satisfy `Silmaril.Wasm.Binaryen.Deferred.DeferredBaseSim` at every numerical profile;
  `exportRefines_of_goodW` is the transfer to export refinement.
* `refines_of_good`: the frame-free bridge `gBaseSim` also gives export refinement at
  **every** profile through silmaril's `exportRefines_of_bodiesRel` (the deterministic
  restriction of `exportEquiv_of_good` comes only from silmaril's closed-host converse).
  With a rule lemma for each direction, a rule holds at every profile (`equiv_of_refines`).
* Restated stages at every profile: `teeForm_sound_ground_any` (deferred bridge, both
  directions), `rseLine_sound_ground_any` (frame-free bridge forward, deferred bridge
  backward), and the module forms `neutralC_module_any`, `eqz3_module_any`,
  `twoSets_module_any` (the pair that `not_baseSim_twoSets` excludes from `BaseSim`).
-/

namespace Silmaril.Wasm.FnInst.Ground

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {m m' : Module}

/-- **The frame-free transfer at every profile**: one direction, through `gBaseSim`. -/
theorem refines_of_good {BI : List Instr → List Instr → Prop} (hBI : ∀ x y, BI x y → GBI x y)
    (hrel : ModuleBodiesRel BI m m') (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportRefines (· = ·) P (closedHost (H := H)) m m' :=
  exportRefines_of_bodiesRel gBaseSim (closedHost_codeParametric.respects (fun f => FuncRel.refl f))
    (bodiesRel_mono hBI hrel) hm hm'

/-- **The deferred transfer**, for a family of rules whose pairs are all `GoodW`. -/
theorem refines_of_goodW {BI : List Instr → List Instr → Prop} (hBI : ∀ x y, BI x y → GWI x y)
    (hrel : ModuleBodiesRel BI m m') (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportRefines (· = ·) P (closedHost (H := H)) m m' :=
  exportRefines_of_goodW (bodiesRel_mono hBI hrel) hm hm'

/-- Refinement both ways is equivalence. -/
theorem equiv_of_refines {host : HostSemantics H} (h₁ : ExportRefines (· = ·) P host m m')
    (h₂ : ExportRefines (· = ·) P host m' m) : ExportEquiv (· = ·) P host m m' :=
  ⟨h₁, h₂.mono fun _ _ h => h.symm⟩

theorem pair_flip {a b : List GInstr} {x y : List Instr} (h : Pair a b y x) : Pair b a x y :=
  ⟨h.2, h.1⟩

/-- One frame-free rule with a rule lemma in each direction, at every profile. -/
theorem exportEquiv_any_of_pair {a b : List GInstr} (h : Good a b) (h' : Good b a)
    (hrel : ModuleBodiesRel (Pair a b) m m') (hm : ∃ mt, ModuleOk m mt)
    (hm' : ∃ mt, ModuleOk m' mt) : ExportEquiv (· = ·) P (closedHost (H := H)) m m' := by
  refine equiv_of_refines (refines_of_good ?_ hrel hm hm') (refines_of_good ?_ hrel.flip hm' hm)
  · rintro _ _ ⟨rfl, rfl⟩
    exact gbi_of_good h
  · rintro _ _ hp
    obtain ⟨rfl, rfl⟩ := pair_flip hp
    exact gbi_of_good h'

/-- One rule of the deferred bridge with a rule lemma in each direction, at every profile. -/
theorem exportEquiv_any_of_pairW {a b : List GInstr} (h : GoodW a b) (h' : GoodW b a)
    (hrel : ModuleBodiesRel (Pair a b) m m') (hm : ∃ mt, ModuleOk m mt)
    (hm' : ∃ mt, ModuleOk m' mt) : ExportEquiv (· = ·) P (closedHost (H := H)) m m' := by
  refine equiv_of_refines (refines_of_goodW ?_ hrel hm hm') (refines_of_goodW ?_ hrel.flip hm' hm)
  · rintro _ _ ⟨rfl, rfl⟩
    exact ⟨a, b, h, rfl, rfl⟩
  · rintro _ _ hp
    obtain ⟨rfl, rfl⟩ := pair_flip hp
    exact ⟨b, a, h', rfl, rfl⟩

/-! ## Stages restated at every profile -/

/-- The `tee-form` source pairs (result on the left) are `GoodW`. -/
theorem tfBI_goodW : ∀ x y, Silmaril.Wasm.Binaryen.TeeForm.tfBI x y → GWI x y
  | _, _, .mk x => ⟨_, _, goodW_teeSet x, rfl, rfl⟩

/-- The reversed `tee-form` pairs (original on the left) are `GoodW`. -/
theorem tfBI_goodW_rev : ∀ x y, Silmaril.Wasm.Binaryen.TeeForm.tfBI y x → GWI x y
  | _, _, .mk x => ⟨_, _, goodW_setTee x, rfl, rfl⟩

/-- **`tee-form`, restated at every profile**: rule lemmas `goodW_teeSet`, `goodW_setTee` +
the deferred transfer. -/
theorem teeForm_sound_ground_any {m : BModule} (hm : m.Ok)
    (hm' : (Silmaril.Wasm.Binaryen.TeeForm.teeForm m).Ok) :
    ExportEquiv (· = ·) P (closedHost (H := H)) (Silmaril.Wasm.Binaryen.TeeForm.teeForm m).lower
      m.lower :=
  equiv_of_refines
    (refines_of_goodW tfBI_goodW (Silmaril.Wasm.Binaryen.TeeForm.teeForm_bodiesRel m) hm' hm)
    (refines_of_goodW tfBI_goodW_rev (Silmaril.Wasm.Binaryen.TeeForm.teeForm_bodiesRel m).flip hm hm')

/-- The reversed `rse-line` pairs (original on the left) are `GoodW`. -/
theorem rsBI_goodW_rev : ∀ x y, RedundantSetLine.rsBI y x → GWI x y
  | _, _, .set x => ⟨_, _, goodW_getSet x, rfl, rfl⟩
  | _, _, .tee x => ⟨_, _, goodW_getTee x, rfl, rfl⟩

/-- **`rse-line`, restated at every profile**: `good_rseSet`, `good_rseTee` through the
frame-free bridge, `goodW_getSet`, `goodW_getTee` through the deferred one. -/
theorem rseLine_sound_ground_any {m : BModule} (hm : m.Ok)
    (hm' : (RedundantSetLine.rseLine m).Ok) :
    ExportEquiv (· = ·) P (closedHost (H := H)) (RedundantSetLine.rseLine m).lower m.lower :=
  equiv_of_refines
    (refines_of_good rsBI_good (Silmaril.Wasm.Binaryen.RseLine.rseLine_bodiesRel m) hm' hm)
    (refines_of_goodW rsBI_goodW_rev (Silmaril.Wasm.Binaryen.RseLine.rseLine_bodiesRel m).flip hm hm')

/-- `neutral-ops` with a consumer of the fragment, at every profile. -/
theorem neutralC_module_any {b : Bin} {k : BitVec 32} (hk : Neutral b k) {X : GInstr}
    (hX : Consumer X) (hrel : ModuleBodiesRel (Pair [.const k, .bin b, X] [X]) m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportEquiv (· = ·) P (closedHost (H := H)) m m' :=
  exportEquiv_any_of_pair (good_neutralC hk hX) (good_neutralC_rev hk hX) hrel hm hm'

/-- `eqz-pair` with consumer `i32.eqz`, at every profile. -/
theorem eqz3_module_any (hrel : ModuleBodiesRel (Pair [.eqz, .eqz, .eqz] [.eqz]) m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportEquiv (· = ·) P (closedHost (H := H)) m m' :=
  exportEquiv_any_of_pair good_eqz3 good_eqz3_rev hrel hm hm'

/-- Two stores to one local are one store, at every profile (no `BaseSim` exists for this
pair, `not_baseSim_twoSets`; the deferred bridge proves it). -/
theorem twoSets_module_any (hrel : ModuleBodiesRel (Pair twoSets oneSet) m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportEquiv (· = ·) P (closedHost (H := H)) m m' :=
  exportEquiv_any_of_pairW goodW_twoSets goodW_oneSet hrel hm hm'

/-- A repeated copy `local.get x; local.set y` (`y ≤ x`) is one copy, at every profile: two
locals, each accessed twice. -/
theorem copyTwice_module_any {x y : LocalIdx} (hyx : y.toNat ≤ x.toNat)
    (hrel : ModuleBodiesRel (Pair [.localGet x, .localSet y, .localGet x, .localSet y]
      [.localGet x, .localSet y]) m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportEquiv (· = ·) P (closedHost (H := H)) m m' :=
  exportEquiv_any_of_pairW (goodW_copyTwice hyx) (goodW_copyOnce hyx) hrel hm hm'

/-- A second read of a local that is dropped, at every profile (a read, then stack-only
code: the second kind of runtime pair). -/
theorem getGetDrop_module_any {x : LocalIdx}
    (hrel : ModuleBodiesRel (Pair [.localGet x, .localGet x, .drop] [.localGet x]) m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportEquiv (· = ·) P (closedHost (H := H)) m m' :=
  exportEquiv_any_of_pairW (goodW_getGetDrop x) (goodW_getGetDrop_rev x) hrel hm hm'

/-- A self-copy `local.get x; local.set x` is removed: module refinement at every profile. -/
theorem selfCopy_module_refines {x : LocalIdx}
    (hrel : ModuleBodiesRel (Pair [.localGet x, .localSet x] []) m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportRefines (· = ·) P (closedHost (H := H)) m m' := by
  refine refines_of_goodW ?_ hrel hm hm'
  rintro _ _ ⟨rfl, rfl⟩
  exact ⟨_, _, goodW_selfCopy x, rfl, rfl⟩

end Silmaril.Wasm.FnInst.Ground
