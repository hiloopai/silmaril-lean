module

public import Silmaril.Compiler.C.Sem.C7Ladder.Defs
public import Silmaril.Compiler.C.Sem.Targets.Defs
public import Silmaril.Compiler.C.Sem.C6Ladder.Defs
public import Silmaril.Compiler.C.Sem.C0Mono.Defs
public import Silmaril.Compiler.C.Sem.C2CoreProofs.Defs
public import Silmaril.Compiler.C.Sem.C3CoreProofs.Defs
public import Silmaril.Compiler.C.Sem.C4CoreProofs.Defs
public import Silmaril.Compiler.C.Sem.C1Mono.Defs
public import Silmaril.Compiler.C.Sem.C2Mono.Defs
public import Silmaril.Compiler.C.Sem.C3Mono.Defs
public import Silmaril.Compiler.C.Sem.C4Mono.Defs
public import Silmaril.Compiler.C.Sem.C5Mono.Defs
public import Silmaril.Compiler.C.Sem.TargetsMono.Defs
public import Silmaril.Compiler.C.Sem.LadderCheckSound.Defs
public import Silmaril.Compiler.C.Sem.LadderCheck3Sound.Defs
public import Silmaril.Compiler.C.Sem.C5CoreProofs.Defs
public import Silmaril.Compiler.C.Sem.TargetsC1.Defs
public import Silmaril.Compiler.C.Sem.TargetsCoreC1.Defs
public import Silmaril.Compiler.C.Sem.ElabC1Witness.Defs
public import Silmaril.Compiler.C.Sem.TargetsC2.Defs
public import Silmaril.Compiler.C.Sem.TargetsC3.Defs
public import Silmaril.Compiler.C.Sem.TargetsC4.Defs
public import Silmaril.Compiler.C.Sem.TargetsC5.Defs
public import Silmaril.Compiler.C.Sem.TargetsC6.Defs
public import Silmaril.Compiler.C.Sem.TargetsC7.Defs
public import Silmaril.Compiler.C.Sem.TargetsFit.Defs
public import Silmaril.Compiler.C.Sem.MirAdequacy.Defs
public import Silmaril.Compiler.C.Sem.MirStuck.Defs
public import Silmaril.Compiler.C.Sem.MirFitChecks.Defs
public import Silmaril.Compiler.Mir.InterpFrame.Defs
public import Silmaril.Compiler.Mir.InterpStart.Defs
public import Silmaril.Compiler.Mir.InterpMem.Defs
public import Silmaril.Compiler.C.Sem.InterpCounterexample.Defs
public import Silmaril.Compiler.C.Sem.TargetsRt.Defs
public import Silmaril.Compiler.C.Sem.TargetsCoreX86.Defs
public import Silmaril.Compiler.C.Sem.TargetsZoo.Defs
public import Silmaril.Compiler.C.Sem.CoreComp.Defs
public import Silmaril.Compiler.C.Sem.CoreCompArgs.Defs
public import Silmaril.Compiler.C.Sem.TriangleProofs.Defs
public import Silmaril.Compiler.C.Sem.Triangle2Proofs.Defs
public import Silmaril.Compiler.Target.RenameCounterexample.Defs
public import Silmaril.Compiler.Target.RenameComplete.Defs
public import Silmaril.Compiler.C.Sem.TargetsRename.Defs
@[expose] public section

/-!
# Proofs of the `csem` targets

One theorem `Proofs.x : Targets.x` per proved target of `Silmaril.Compile.C.Sem.Targets` and
`Silmaril.Compile.C.Sem.TargetsRt` (the evaluator's registry names them). New proofs of open targets may live here or anywhere,
under the name the registry expects.
-/

namespace Silmaril.Compile.Targets.Proofs

open Silmaril.Compile.Category Silmaril.Compile.Category.Syntax
open Silmaril.Compile.Targets

theorem c0_core_realises : Targets.c0_core_realises :=
  fun _ _ h => C.Sem.ElabC0.elaborate_sound h

theorem c1_core_realises : Targets.c1_core_realises :=
  ⟨C.Sem.ElabC1.exists_accepted, fun _ _ h => C.Sem.ElabC1.elaborate_sound h⟩

theorem refinesOn_trans : Targets.refinesOn_trans :=
  fun _ _ _ _ _ h₁ h₂ => RefinesOn.trans h₁ h₂

theorem refinesOn_union : Targets.refinesOn_union :=
  fun _ _ _ _ _ => refinesOn_union_iff

theorem refinesOn_inf : Targets.refinesOn_inf :=
  fun _ _ _ _ _ => refinesOn_inf_iff

theorem sup_refinesOn : Targets.sup_refinesOn :=
  fun _ _ _ _ _ => sup_refinesOn_iff

theorem overlap_eq_inter : Targets.overlap_eq_inter :=
  fun _ S T => Syntax.overlap_eq_inter S T

theorem refinesOn_iff_valid_cast : Targets.refinesOn_iff_valid_cast :=
  fun _ _ _ _ => Syntax.refinesOn_iff_valid_cast

theorem validOn_of_refinesOn : Targets.validOn_of_refinesOn :=
  fun _ _ _ _ _ _ _ hv h => hv.of_refinesOn h

theorem realises_factor : Targets.realises_factor :=
  fun _ _ _ _ _ _ _ he _ hp _ hv => he.factor hp hv

theorem realises_factor_of_le : Targets.realises_factor_of_le :=
  fun _ _ _ _ _ _ _ _ he h2 _ hp _ hv => he.factor_of_le h2 hp hv

theorem pipeline_sound : Targets.pipeline_sound :=
  fun _ _ _ P _ _ h => P.sound h

theorem roundTrip_endo_refines : Targets.roundTrip_endo_refines :=
  fun _ _ T E p => T.endo_refines E p

theorem mir_link_valid : Targets.mir_link_valid :=
  fun cfg us q h => (Mir.linkCompiler cfg).sound us q h

theorem mir_beh_deterministic : Targets.mir_beh_deterministic :=
  Mir.beh_subsingleton_or_univ

theorem mir_ssa_optimize_link_sound : Targets.mir_ssa_optimize_link_sound :=
  fun cfg E _ _ h => Mir.optimizeAndLink_sound cfg E h

theorem c0_run_mono : Targets.c0_run_mono :=
  C.Sem.C0.run_mono

theorem c0_deterministic : Targets.c0_deterministic :=
  C.Sem.C0.beh_subsingleton_or_univ

theorem renamer_key_lemma : Targets.renamer_key_lemma :=
  fun _ _ _ hc _ _ _ _ h b hb hns => Target.RegAlloc.rename_behaves hc h (b := b) hb hns

theorem renumber_decomposes : Targets.renumber_decomposes :=
  Target.RegAlloc.renumber_eq

/-- The frozen `renumber_certified` is false: a function whose entry label names no block can
have two parameters with one new number (`Target.RegAlloc.cex`). -/
theorem not_renumber_certified : ¬ Targets.renumber_certified :=
  Target.RegAlloc.not_renumber_certified

theorem renumber_checked_refines : Targets.renumber_checked_refines :=
  Target.RegAlloc.renumberChecked_refines

/-- The renamer checker accepts every program whose functions' entry labels name blocks
(`Target.RegAlloc.checkCert_total`), so its certificate covers `renumber` there. -/
theorem renumber_certified_wf : Targets.renumber_certified_wf :=
  Target.RegAlloc.renumber_certified_wf

theorem triangle_factor : Targets.triangle_factor :=
  fun _ _ _ h cfg ctl _ hp _ hv => ⟨_, C.Sem.factor h cfg ctl hp hv⟩

theorem ccomp_rt_tv_sound : Targets.ccomp_rt_tv_sound :=
  fun _ h => C.Sem.checkC0_sound h

theorem core_x86_valid_iff : Targets.core_x86_valid_iff :=
  C.Sem.CoreX86.core_x86_valid_iff

theorem core_compile_sound_iff_valid : Targets.core_compile_sound_iff_valid :=
  fun M _ elaborate compile hne =>
    C.Sem.CoreX86.core_compile_sound_iff_valid M elaborate compile hne

theorem lir_rtl_lift_refines : Targets.lir_rtl_lift_refines :=
  fun _ hp => Silmaril.Compile.Semantics.beh_ofLir_subset hp

theorem ssa_copyProp_behaves : Targets.ssa_copyProp_behaves :=
  fun _ _ _ _ _ hs _ =>
    Silmaril.Machine.RTL.SSA.CopyProp.behaves_copyProp_iff
      (Silmaril.Machine.RTL.SSA.CopyProp.Inv.start hs)

theorem ccomp_rt_tv_sound_c1 : Targets.ccomp_rt_tv_sound_c1 :=
  fun _ h => C.Sem.checkC1_sound h

theorem ccomp_rt_tv_sound_c2 : Targets.ccomp_rt_tv_sound_c2 :=
  fun _ h => C.Sem.checkC2_sound h

theorem ccomp_rt_tv_sound_c3 : Targets.ccomp_rt_tv_sound_c3 :=
  fun _ h => C.Sem.checkC3_sound h

theorem core_comp_sound_spec : Targets.core_comp_sound_spec :=
  fun _ hc => C.Sem.CoreComp.sound_spec hc

theorem core_comp_compile_valid : Targets.core_comp_compile_valid :=
  fun _ hc _ _ ha h hne => C.Sem.CoreComp.compile_valid hc ha h hne

theorem core_comp_route_valid : Targets.core_comp_route_valid :=
  fun _ _ hc _ _ _ helab ha h hne => C.Sem.CoreComp.route_valid hc helab ha h hne

theorem ccomp_rt_tv_sound_c4 : Targets.ccomp_rt_tv_sound_c4 :=
  fun _ h => C.Sem.checkC4_sound h

theorem c1_run_mono : Targets.c1_run_mono :=
  C.Sem.C1.run_mono

theorem c1_deterministic : Targets.c1_deterministic :=
  C.Sem.C1.beh_subsingleton_or_univ

theorem c2_run_mono : Targets.c2_run_mono :=
  C.Sem.C2.run_mono

theorem c2_deterministic : Targets.c2_deterministic :=
  C.Sem.C2.beh_subsingleton_or_univ

theorem c3_run_mono : Targets.c3_run_mono :=
  C.Sem.C3.run_mono

theorem c3_deterministic : Targets.c3_deterministic :=
  C.Sem.C3.beh_subsingleton_or_univ

theorem c4_run_mono : Targets.c4_run_mono :=
  C.Sem.C4.run_mono

theorem c4_deterministic : Targets.c4_deterministic :=
  C.Sem.C4.beh_subsingleton_or_univ

theorem c5_run_mono : Targets.c5_run_mono :=
  C.Sem.C5.run_mono

theorem c5_deterministic : Targets.c5_deterministic :=
  C.Sem.C5.beh_subsingleton_or_univ

theorem ladder_check_sound_c1 : Targets.ladder_check_sound_c1 :=
  ⟨⟨_, C.Sem.LadderCheckSound.ladderCheck1_voidProgram⟩,
    fun _ h => C.Sem.LadderCheckSound.ladderCheck1_sound h⟩

theorem ladder_check_sound_c2 : Targets.ladder_check_sound_c2 :=
  ⟨⟨_, C.Sem.LadderCheckSound.ladderCheck2_voidProgram⟩,
    fun _ h => C.Sem.LadderCheckSound.ladderCheck2_sound h⟩

theorem ladder_check_sound_c3 : Targets.ladder_check_sound_c3 :=
  ⟨⟨_, C.Sem.LadderCheckSound.ladderCheck3_voidProgram⟩,
    fun _ h => C.Sem.LadderCheckSound.ladderCheck3_sound h⟩

theorem ladder_check_sound_c4 : Targets.ladder_check_sound_c4 :=
  ⟨⟨_, C.Sem.LadderCheckSound.ladderCheck4_voidProgram⟩,
    fun _ h => C.Sem.LadderCheckSound.ladderCheck4_sound h⟩

theorem ladder_check_sound_c5 : Targets.ladder_check_sound_c5 :=
  ⟨⟨_, C.Sem.LadderCheckSound.ladderCheck5_voidProgram⟩,
    fun _ h => C.Sem.LadderCheckSound.ladderCheck5_sound h⟩

theorem ccomp_rt_tv_sound_c5 : Targets.ccomp_rt_tv_sound_c5 :=
  fun _ h => C.Sem.checkC5_sound h

theorem ccomp_rt_tv_sound_c6 : Targets.ccomp_rt_tv_sound_c6 :=
  fun _ h => C.Sem.checkC6_sound h

theorem ccomp_rt_tv_sound_c7 : Targets.ccomp_rt_tv_sound_c7 :=
  fun _ h => C.Sem.checkC7_sound h

end Silmaril.Compile.Targets.Proofs
