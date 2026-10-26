module

public import Silmaril.Process.LPS.Problems.NativeX86Complete.Launch

/-!
# Every realistic valid input has an exact launch on a well-formed snapshot

`imageWf_realistic_entry`, from the witness launch of `NativeX86Complete.Launch`.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.NativeX86Complete

open Silmaril.Process.LPS Silmaril.Process.LPS.Shapes Silmaril.Process.LPS.Machines

/-- On a well-formed snapshot every realistic valid input has an exact realistic launch. -/
theorem imageWf_realistic_entry (isa : UserIsa) (snap : Snapshot)
    (wf : Problems.NativeX86.ImageWf isa snap) (inp : ProcInput)
    (valid : X86RealisticLaunch.ValidInput inp) :
    ∃ c en, X86RealisticLaunch.ValidEntry isa snap c en inp ∧ X86RealisticLaunch.Exact inp c := by
  obtain ⟨vsnap, brkOk, room⟩ := wf
  obtain ⟨brk, hbrk⟩ := imageBrkSatisfiable_sound _ brkOk
  obtain ⟨core, hw32⟩ := valid
  obtain ⟨ha, he, -, -, creds, -⟩ := core
  have small : ((X86RealisticLaunch.stringArea (witnessChoices inp) inp).length : Int) ≤ 2 ^ 30 := by
    have fa := Problems.NativeX86.flattenStrings_length inp.argv
    have fe := Problems.NativeX86.flattenStrings_length inp.envp
    have area := witness_area_length inp
    have := ha.2.2.1
    have := he.2.1
    omega
  have few : inp.argv.length + inp.envp.length ≤ 2 ^ 20 := by
    have := ha.2.1
    have := he.1
    omega
  have mm := witness_mmapBase snap brk inp
  have lo := witness_sp_low snap brk inp small few
  refine ⟨witnessChoices inp, witnessEntry snap brk inp,
    ⟨vsnap, witness_validChoices inp hw32 creds small, rfl,
      witness_table_fits snap brk inp small few, witness_table_below_top snap inp small few,
      hbrk, mm.1, mm.2.1, mm.2.2, witness_pageTop snap brk inp small few, ?_⟩,
    witness_exact inp⟩
  intro g mem
  have := room g mem
  unfold stackMaxSize at *
  omega

end Silmaril.Process.LPS.Problems.NativeX86Complete
