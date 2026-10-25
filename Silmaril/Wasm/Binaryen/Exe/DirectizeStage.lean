module

public import Silmaril.Wasm.Binaryen.Exe.StageContract
public import Silmaril.Wasm.Binaryen.Pass.Directize
public import Silmaril.Wasm.Binaryen.Pass.DirectizeMid
public import Silmaril.Wasm.Binaryen.Pass.DirectizeInst

@[expose] public section

/-! # Directize: the stage contract

`directize_stageOk` proves the `StageOk` contract of the registry row (`PassRegistry.lean`).
Directize is the identity unless the module has tables, `Directize.frozen`,
`Directize.elemsOk` and `Directize.i32Only` (i32 tables and offsets, `ref.func` entries)
hold, its data segments satisfy `profileData`, and the validator accepts the rewrite;
then the output is valid
(`Exe.validOk_sound`) and export equivalent to the input under the closed host: the
instantiations of the two modules correspond (`DirectizeMid.pre_inst`, from the element
segments on) and their runs are related by the call-site simulation
(`DirSim.exportEquiv_of_instCorr`, `Binaryen/DirectizeRun.lean`).
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binaryen Numerics

variable {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type}

/-- Directize is the identity on a module of the base profile. -/
theorem directize_of_inProfileBase {m : BModule} (h : m.inProfileBase = true) :
    directize m = m := by
  have ht : m.base.tables.isEmpty = true :=
    List.isEmpty_iff.mpr (BModule.inProfileBase_sound h).tables
  simp [directize, ht]

theorem directize_bodiesRel (m : BModule) :
    ModuleBodiesRel (fun _ _ => True) m.lower (Directize.run m).lower ∧
      DirectizeInst.BodiesRel (Directize.siteOk m (DirectizeMid.tysOf m)) m.lower.funcs
        (Directize.run m).lower.funcs := by
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · simp only [BModule.lower, Directize.run, List.map_map]
    exact List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr
      (List.forall₂_same.mpr fun f _ => ⟨rfl, rfl, Execution.Core.Sim.InstrsRel.base trivial⟩))
  · simp only [BModule.lower, Directize.run, List.map_map]
    exact List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr
      (List.forall₂_same.mpr fun f _ => ⟨rfl, rfl, fun mi => Directize.exprs_rel mi f.body⟩))

/-- **Directize is a sound stage.** -/
theorem directize_stageOk : StageOk o H directize := fun m hm => by
  unfold directize
  split
  · exact ⟨hm.ok, exportEquiv_refl _⟩
  · rename_i hd
    have hdata : m.base.data.all profileData = true := by simpa using hd
    split
    · exact ⟨hm.ok, exportEquiv_refl _⟩
    · rename_i hc
      simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hc
      obtain ⟨⟨⟨-, hfz⟩, hel⟩, h32⟩ := hc
      split
      · rename_i hv
        refine ⟨validOk_sound hv, ?_⟩
        obtain ⟨hrel, hd⟩ := directize_bodiesRel m
        have hm' : ∃ mt, Validation.ModuleOk (Directize.run m).lower mt := validOk_sound hv
        have hprof := hm.inGcProfile
        refine DirSim.exportEquiv_of_instCorr ⟨fun s xas c hs hi => ?_, fun s xas c' hs hi' => ?_⟩
        · obtain ⟨c', hi', hfr, hcode, hSR⟩ := DirectizeInst.instantiate_dir hrel hd hm' hi
          exact ⟨c', _, _, hi', DirectizeMid.pre_inst hprof hfz hel h32 hdata hs hi hfr hcode hSR⟩
        · obtain ⟨c, hi, hfr, hcode, hSR⟩ := DirectizeInst.instantiate_dir' hrel hd hm.ok hi'
          exact ⟨c, _, _, hi, DirectizeMid.pre_inst hprof hfz hel h32 hdata hs hi hfr hcode hSR⟩
      · exact ⟨hm.ok, exportEquiv_refl _⟩

end Silmaril.Wasm.Binaryen.Exe
