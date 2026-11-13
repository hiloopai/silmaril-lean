module

public import Silmaril.Compiler.C.Sem.TargetsTriangle2.Defs
public import Silmaril.Compiler.C.Sem.TriangleProofs.Defs
public import Silmaril.Compiler.C.Sem.C2CoreProofs.Defs
public import Silmaril.Compiler.C.Sem.C3CoreProofs.Defs
public import Silmaril.Compiler.C.Sem.C4CoreProofs.Defs
public import Silmaril.Compiler.C.Sem.LadderCheckSound.Defs
@[expose] public section

/-!
# C2–C4 and checked mixed C2/C0 compiler triangles

The same-rung triangles compose validator soundness with exact Core realisation.
The mixed triangle transports C2 validity along the two checked behaviour
equalities before applying the existing C0 factorization. Its existence witness
satisfies all three executable premises together, by kernel evaluation.

These proofs use the approved option-A statements: non-vacuity of the full
validator/elaborator conjunction remains the evaluator's separate corpus gate.
-/

namespace Silmaril.Compile.C.Sem.Triangle2Proofs

open Silmaril.Cerberus.Ail

set_option maxRecDepth 4096
set_option maxHeartbeats 800000
attribute [local cbv_eval] repeatM.Internal.eq_of_monadTail
  Std.Legacy.Range.forIn'_eq_forIn'_range'
  Std.HashMap.size_emptyWithCapacity
  Std.HashMap.contains_emptyWithCapacity Std.HashMap.contains_insert
  Std.HashMap.getElem?_emptyWithCapacity
  Std.HashMap.toList_emptyWithCapacity
  Std.HashSet.contains_emptyWithCapacity Std.HashSet.contains_insert

private theorem size_insert_bool {α β : Type} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α] (m : Std.HashMap α β) (k : α) (v : β) :
    (m.insert k v).size = if m.contains k then m.size else m.size + 1 := by
  simpa only [Std.HashMap.mem_iff_contains] using
    (Std.HashMap.size_insert (m := m) (k := k) (v := v))
attribute [local cbv_eval] size_insert_bool

private theorem elabC0_voidProgram :
    (elabC0 LadderCheckSound.voidProgram).isSome = true := by cbv

/-- One program simultaneously satisfies the elaborator and both ladder checks. -/
theorem mixed_nonempty : ∃ (p : TypedProgram)
    (q : Silmaril.Cerberus.Core.Dynamics.Program),
    elabC0 p = some q ∧ ladderCheck1 p = true ∧ ladderCheck2 p = true := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp elabC0_voidProgram
  exact ⟨LadderCheckSound.voidProgram, q, hq,
    LadderCheckSound.ladderCheck1_voidProgram, LadderCheckSound.ladderCheck2_voidProgram⟩

end Silmaril.Compile.C.Sem.Triangle2Proofs

namespace Silmaril.Compile.Targets.Proofs

open Silmaril.Compile.Category Silmaril.Compile.C.Sem

theorem ccomp_factors_through_core_c2 : Targets.ccomp_factors_through_core_c2 := by
  refine ⟨c2_core_realises.1, ?_⟩
  intro p q hc he
  obtain ⟨us, hus, hv, hne⟩ := checkC2_sound hc
  have hf := factor (S := C2.sem) (F := {p}) (elaborate := fun _ => q)
    (fun p' hp => by
      have eq : p' = p := hp
      subst p'
      exact (c2_core_realises.2 p q he).2)
    mirConfig ctlAddress (Set.mem_singleton p) hv
  exact ⟨us, hus, hf.1, hf.2, hne⟩

theorem ccomp_factors_through_core_c3 : Targets.ccomp_factors_through_core_c3 := by
  refine ⟨c3_core_realises.1, ?_⟩
  intro p q hc he
  obtain ⟨us, hus, hv, hne⟩ := checkC3_sound hc
  have hf := factor (S := C3.sem) (F := {p}) (elaborate := fun _ => q)
    (fun p' hp => by
      have eq : p' = p := hp
      subst p'
      exact (c3_core_realises.2 p q he).2)
    mirConfig ctlAddress (Set.mem_singleton p) hv
  exact ⟨us, hus, hf.1, hf.2, hne⟩

theorem ccomp_factors_through_core_c4 : Targets.ccomp_factors_through_core_c4 := by
  refine ⟨c4_core_realises.1, ?_⟩
  intro p q hc he
  obtain ⟨us, hus, hv, hne⟩ := checkC4_sound hc
  have hf := factor (S := C4.sem) (F := {p}) (elaborate := fun _ => q)
    (fun p' hp => by
      have eq : p' = p := hp
      subst p'
      exact (c4_core_realises.2 p q he).2)
    mirConfig ctlAddress (Set.mem_singleton p) hv
  exact ⟨us, hus, hf.1, hf.2, hne⟩

theorem ccomp_factors_through_core_mixed_c2c0 :
    Targets.ccomp_factors_through_core_mixed_c2c0 := by
  refine ⟨Triangle2Proofs.mixed_nonempty, ?_⟩
  intro p q hc he h1 h2
  obtain ⟨us, hus, hv, hne⟩ := checkC2_sound hc
  have hb : C2.beh p = C0.beh p :=
    (LadderCheckSound.ladderCheck2_sound h2).trans
      (LadderCheckSound.ladderCheck1_sound h1)
  have hv0 : Valid (Core.cAM C0.sem mirConfig ctlAddress) p us := by
    have hread := (valid_iff_readBack
      (Core.cAM_readBack C2.sem mirConfig ctlAddress) p us).mp hv
    apply (valid_iff_readBack
      (Core.cAM_readBack C0.sem mirConfig ctlAddress) p us).mpr
    refine ⟨rfl, ?_⟩
    change Core.readBack ctlAddress '' Mir.beh mirConfig us ⊆ C0.beh p
    rw [← hb]
    exact hread.2
  obtain ⟨hAC, hCM⟩ := factor_elabC0 he mirConfig ctlAddress hv0
  exact ⟨us, hus, hAC, hCM, hne⟩

end Silmaril.Compile.Targets.Proofs
