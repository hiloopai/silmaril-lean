module

public import Silmaril.Wasm.Binaryen.DirectizeProfilePre
public import Silmaril.Wasm.Binaryen.Exe.DirectizeStage
public import Silmaril.Wasm.Binaryen.Contracts

@[expose] public section

/-! # Directize preserves exports under arbitrary numerical profiles

This proves the complete existing transformation on every valid Binaryen module.
Its table, element, data-offset and candidate-validator filters are unchanged.
The initialization proof uses locally forced steps and absorbing trap cleanup;
the run proof matches the choices of actual executions in both directions.
-/

namespace Silmaril.Wasm.Binaryen.Directize

open Silmaril.Wasm Execution.Core Numerics

/-- Directize preserves validity and closed-host export observations for every numerical
profile. Applicability is determined entirely by the existing executable filters. -/
theorem directize_sound_profile (m : BModule) (hm : m.Ok) (P : Profile) (H : Type) :
    (directize m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) (directize m).lower m.lower := by
  have hrefl : ExportEquiv (· = ·) P (closedHost (H := H)) m.lower m.lower :=
    Contract.equiv_refl Contract.Rel.eq _
  unfold directize
  split
  · exact ⟨hm, hrefl⟩
  · rename_i hd
    have hdata : m.base.data.all profileData = true := by simpa using hd
    split
    · exact ⟨hm, hrefl⟩
    · rename_i hc
      simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hc
      obtain ⟨⟨⟨-, hfz⟩, hel⟩, h32⟩ := hc
      split
      · rename_i hv
        refine ⟨Exe.validOk_sound hv, ?_⟩
        obtain ⟨hrel, hbody⟩ := Exe.directize_bodiesRel m
        have hm' : ∃ mt, Validation.ModuleOk (Directize.run m).lower mt := Exe.validOk_sound hv
        refine DirSim.exportEquiv_of_instCorr_profile (P := P)
          ⟨fun s xas c hs hi => ?_, fun s xas c' hs hi' => ?_⟩
        · obtain ⟨c', hi', hfr, hcode, hSR⟩ := DirectizeInst.instantiate_dir hrel hbody hm' hi
          exact ⟨c', _, _, hi',
            DirectizeMid.pre_inst_profile hfz hel h32 hdata hs hi hfr hcode hSR⟩
        · obtain ⟨c, hi, hfr, hcode, hSR⟩ := DirectizeInst.instantiate_dir' hrel hbody hm hi'
          exact ⟨c, _, _, hi,
            DirectizeMid.pre_inst_profile hfz hel h32 hdata hs hi hfr hcode hSR⟩
      · exact ⟨hm, hrefl⟩

end Silmaril.Wasm.Binaryen.Directize
