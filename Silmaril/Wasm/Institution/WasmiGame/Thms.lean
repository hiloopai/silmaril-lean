module

public import Silmaril.Wasm.Institution.WasmiGame.Defs
public import Silmaril.Wasm.Models.Game.Thms
public import Silmaril.Wasm.Wasmi.Thms

/-!
# wasmi 2.0.0 in the institution of game semantics: theorems

* `core_le_loose`, `wasmi_le_loose`: **both strategies refine the loose one** (the latter for
  hosts parametric in function code), from `Loose.core_le` and `Loose.wasmi_le`;
* `disagree`: the `◇` sentence `sen (returns [5])` holds of the wasmi strategy at the
  reproducer and fails of the Core strategy, at every profile; `disagree7` is the converse
  witness `sen (returns [7])`; `loose_both`: the loose strategy satisfies both;
* `not_le_core`, `not_le_wasmi`: neither strategy refines the other at the reproducer;
* `transfer`: a universal sentence of the loose strategy holds of both;
* `wasmi_eq_core_of_patFree`: without the pattern the two strategies are equal (the
  nonconformance is localised as in the atlas).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Wasmi.GInst

open Silmaril.Games Silmaril.Wasm.Models Silmaril.Wasm.Atlas Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- **Core refines the loose model**, in `GInst`. -/
theorem core_le_loose (P : Profile) (x : Core.Pt H) : coreStrat P x ≤ looseStrat P x :=
  obsStrat_mono (Loose.core_le P x)

/-- **wasmi refines the loose model**, in `GInst` (hosts parametric in function code). -/
theorem wasmi_le_loose (P : Profile) {x : Core.Pt H} (hh : HostParametric x.2) :
    wasmiStrat P x ≤ looseStrat P x :=
  obsStrat_mono (Loose.wasmi_le P hh)

theorem sen_iff_core (P : Profile) (b : Behaviour Val) :
    (sen b).holds (coreStrat P reproPt) ↔ b = .returns [Val.i32 7] := by
  rw [sen, GSen.holds_diaPlay, coreStrat, mem_callPlay_iff, core_f]
  rfl

theorem sen_iff_wasmi (P : Profile) (b : Behaviour Val) :
    (sen b).holds (wasmiStrat P reproPt) ↔ b = .returns [Val.i32 5] := by
  rw [sen, GSen.holds_diaPlay, wasmiStrat, mem_callPlay_iff, wasmi_f]
  rfl

/-- **Disagreement as a `◇` sentence**: wasmi may answer `5` to `f 5 1`, Core may not. -/
theorem disagree (P : Profile) :
    (sen (.returns [Val.i32 5])).holds (wasmiStrat P reproPt) ∧
      ¬ (sen (.returns [Val.i32 5])).holds (coreStrat P reproPt) := by
  refine ⟨(sen_iff_wasmi P _).mpr rfl, fun h => ?_⟩
  have h7 := (sen_iff_core P _).mp h
  exact absurd h7 (by decide)

/-- The converse witness: Core may answer `7`, wasmi may not. -/
theorem disagree7 (P : Profile) :
    (sen (.returns [Val.i32 7])).holds (coreStrat P reproPt) ∧
      ¬ (sen (.returns [Val.i32 7])).holds (wasmiStrat P reproPt) := by
  refine ⟨(sen_iff_core P _).mpr rfl, fun h => ?_⟩
  have h5 := (sen_iff_wasmi P _).mp h
  exact absurd h5 (by decide)

/-- **The loose strategy satisfies both `◇` sentences.** -/
theorem loose_both (P : Profile) :
    (sen (.returns [Val.i32 7])).holds (looseStrat P reproPt) ∧
      (sen (.returns [Val.i32 5])).holds (looseStrat P reproPt) :=
  ⟨GSen.dia_existential _ (core_le_loose P reproPt) (disagree7 P).1,
    GSen.dia_existential _ (wasmi_le_loose P repro_hostParametric) (disagree P).1⟩

/-- At the reproducer the wasmi strategy does not refine the Core strategy. -/
theorem not_le_core (P : Profile) : ¬ wasmiStrat P reproPt ≤ coreStrat P reproPt :=
  fun h => (disagree P).2 (GSen.dia_existential _ h (disagree P).1)

/-- At the reproducer the Core strategy does not refine the wasmi strategy. -/
theorem not_le_wasmi (P : Profile) : ¬ coreStrat P reproPt ≤ wasmiStrat P reproPt :=
  fun h => (disagree7 P).2 (GSen.dia_existential _ h (disagree7 P).1)

/-- **Transfer**: a universal sentence of the loose strategy holds of Core and of wasmi. -/
theorem transfer (P : Profile) {x : Core.Pt H} (hh : HostParametric x.2)
    {φ : GSen game.E game.F} (hu : φ.Universal) (h : φ.holds (looseStrat P x)) :
    φ.holds (coreStrat P x) ∧ φ.holds (wasmiStrat P x) :=
  ⟨hu (core_le_loose P x) h, hu (wasmi_le_loose P hh) h⟩

/-- **Localisation**: on stores without the pattern the two strategies are equal. -/
theorem wasmi_eq_core_of_patFree (P : Profile) {x : Core.Pt H} (h : StorePatFree x.1) :
    wasmiStrat P x = coreStrat P x := by
  unfold wasmiStrat coreStrat
  congr 1
  funext c
  exact obs_of_patFree P h c

end Silmaril.Wasm.Wasmi.GInst
