module

public import Silmaril.Proofs.Wasm.FnInst.Ground.NumRules
public import Silmaril.Wasm.FnInst.Ground.Forced.Thms
public import Silmaril.Wasm.FnInst.Ground.Inst.Thms

@[expose] public section

/-! # The full `neutral-ops` and `eqz-pair` stages through the stack bridge

Header of `Silmaril.Proofs.Wasm.FnInst.Ground.{NumRun,NumInv,NumSim,NumRules}`.

* `nBaseSim`: good pairs of the stack fragment (both integer types, all integer operators
  including the trapping ones, `drop`, `nop`, `select`, `br_if`) satisfy silmaril's
  `BaseSim` under the closed host, at **every** numerical profile;
  `refines_of_ngood` is the transfer to export refinement.
* **`neutralOps_sound_ground_any`**: the whole `neutral-ops` stage (`NeutralOps.nBI`: every
  neutral pair, `i32` and `i64`, every integer consumer), restated as the rule lemmas
  `good_neutral`, `good_neutral_rev` plus the transfer, exact export equivalence at every
  profile.
* **`eqzPair_sound_ground_any`**: the whole `eqz-pair` stage (`EqzPair.eBI`: consumers
  `br_if`, `select`, `i32.eqz`), from `good_eqz2`, `good_eqz2_rev`.
* `neutralOps_sat`, `eqzPair_sat`: the same stages as `checkInst` sentences, from
  `ModuleBodiesRel` and validity (`instRel_of_bodiesRel`).
-/

namespace Silmaril.Wasm.FnInst.Ground.Num

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.FnInst.Ground (bodiesRel_mono equiv_of_refines)
open Silmaril.Wasm.Binaryen.NeutralOps (nBI neutralOps neutralOps_bodiesRel topIntType_cases)
open Silmaril.Wasm.Binaryen.EqzPair (eBI eqzPair eqzPair_bodiesRel boolConsumer_cases)

variable {H : Type} {P : Profile} {m m' : Module}

/-- **The transfer** for a family of rules whose pairs are all good pairs of the stack
fragment, at every profile. -/
theorem refines_of_ngood {BI : List Instr → List Instr → Prop} (hBI : ∀ x y, BI x y → NBI x y)
    (hrel : ModuleBodiesRel BI m m') (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportRefines (· = ·) P (closedHost (H := H)) m m' :=
  exportRefines_of_bodiesRel nBaseSim (closedHost_codeParametric.respects (fun f => FuncRel.refl f))
    (bodiesRel_mono hBI hrel) hm hm'

/-! ## `neutral-ops` -/

/-- The `neutral-ops` source pairs (original on the left) are good. -/
theorem nBI_good : ∀ x y, nBI x y → NBI x y
  | _, _, .mk t op k X hn hX => by
    rcases topIntType_cases hX with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩
    · exact ⟨_, [.un t o], good_neutral hn (.un t o), rfl, rfl⟩
    · exact ⟨_, [.bin t o], good_neutral hn (.bin t o), rfl, rfl⟩
    · exact ⟨_, [.test t o], good_neutral hn (.test t o), rfl, rfl⟩
    · exact ⟨_, [.rel t o], good_neutral hn (.rel t o), rfl, rfl⟩

/-- The reversed `neutral-ops` pairs (result on the left) are good. -/
theorem nBI_good_rev : ∀ x y, nBI y x → NBI x y
  | _, _, .mk t op k X hn hX => by
    rcases topIntType_cases hX with ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩ | ⟨o, rfl⟩
    · exact ⟨[.un t o], _, good_neutral_rev hn (C := .un t o) rfl rfl, rfl, rfl⟩
    · exact ⟨[.bin t o], _, good_neutral_rev hn (C := .bin t o) rfl rfl, rfl, rfl⟩
    · exact ⟨[.test t o], _, good_neutral_rev hn (C := .test t o) rfl rfl, rfl, rfl⟩
    · exact ⟨[.rel t o], _, good_neutral_rev hn (C := .rel t o) rfl rfl, rfl, rfl⟩

/-- **`neutral-ops`, the whole stage, restated at every profile**: rule lemmas
`good_neutral`, `good_neutral_rev` + the transfer. -/
theorem neutralOps_sound_ground_any {m : BModule} (hm : m.Ok) (hm' : (neutralOps m).Ok) :
    ExportEquiv (· = ·) P (closedHost (H := H)) (neutralOps m).lower m.lower :=
  equiv_of_refines (refines_of_ngood nBI_good_rev (neutralOps_bodiesRel m).flip hm' hm)
    (refines_of_ngood nBI_good (neutralOps_bodiesRel m) hm hm')

/-! ## `eqz-pair` -/

/-- The `eqz-pair` source pairs (original on the left) are good. -/
theorem eBI_good : ∀ x y, eBI x y → NBI x y
  | _, _, .mk X hX => by
    rcases boolConsumer_cases hX with ⟨l, rfl⟩ | ⟨ts, rfl⟩ | rfl
    · exact ⟨_, [.brIf l], good_eqz2 (B := .brIf l) trivial, rfl, rfl⟩
    · exact ⟨_, [.select ts], good_eqz2 (B := .select ts) trivial, rfl, rfl⟩
    · exact ⟨_, [.test .i32 .eqz], good_eqz2 (B := .test .i32 .eqz) ⟨rfl, rfl⟩, rfl, rfl⟩

/-- The reversed `eqz-pair` pairs (result on the left) are good. -/
theorem eBI_good_rev : ∀ x y, eBI y x → NBI x y
  | _, _, .mk X hX => by
    rcases boolConsumer_cases hX with ⟨l, rfl⟩ | ⟨ts, rfl⟩ | rfl
    · exact ⟨[.brIf l], _, good_eqz2_rev (B := .brIf l) trivial rfl, rfl, rfl⟩
    · exact ⟨[.select ts], _, good_eqz2_rev (B := .select ts) trivial rfl, rfl, rfl⟩
    · exact ⟨[.test .i32 .eqz], _, good_eqz2_rev (B := .test .i32 .eqz) ⟨rfl, rfl⟩ rfl,
        rfl, rfl⟩

/-- **`eqz-pair`, the whole stage, restated at every profile**: rule lemmas `good_eqz2`,
`good_eqz2_rev` + the transfer. -/
theorem eqzPair_sound_ground_any {m : BModule} (hm : m.Ok) (hm' : (eqzPair m).Ok) :
    ExportEquiv (· = ·) P (closedHost (H := H)) (eqzPair m).lower m.lower :=
  equiv_of_refines (refines_of_ngood eBI_good_rev (eqzPair_bodiesRel m).flip hm' hm)
    (refines_of_ngood eBI_good (eqzPair_bodiesRel m) hm hm')

/-! ## As `checkInst` sentences -/

open Silmaril.Wasm.FnInst.Ground.Check (checkPlain InstRel modRefines_of_baseSim modEquiv_of_refines)

/-- Good pairs of the stack fragment: `m ⊑ m'` from `ModuleBodiesRel` and validity. -/
theorem sat_le_of_ngood {BI : List Instr → List Instr → Prop} {j : ℕ}
    (hBI : ∀ x y, BI x y → NBI x y) (hrel : ModuleBodiesRel BI m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) (P : Profile) :
    checkPlain.Sat (S := ⟨j⟩) (P, .eq) (.le m m') :=
  modRefines_of_baseSim nBaseSim
    (Silmaril.Wasm.FnInst.Ground.Inst.instRel_of_bodiesRel (bodiesRel_mono hBI hrel) hm hm') j

/-- **`neutral-ops` as a `checkInst` sentence**, valid in every model with `Rel.eq`. -/
theorem neutralOps_sat {m : BModule} {j : ℕ} (hm : m.Ok) (hm' : (neutralOps m).Ok)
    (P : Profile) : checkPlain.Sat (S := ⟨j⟩) (P, .eq) (.eqv (neutralOps m).lower m.lower) :=
  modEquiv_of_refines (sat_le_of_ngood nBI_good_rev (neutralOps_bodiesRel m).flip hm' hm P)
    (sat_le_of_ngood nBI_good (neutralOps_bodiesRel m) hm hm' P)

/-- **`eqz-pair` as a `checkInst` sentence**, valid in every model with `Rel.eq`. -/
theorem eqzPair_sat {m : BModule} {j : ℕ} (hm : m.Ok) (hm' : (eqzPair m).Ok)
    (P : Profile) : checkPlain.Sat (S := ⟨j⟩) (P, .eq) (.eqv (eqzPair m).lower m.lower) :=
  modEquiv_of_refines (sat_le_of_ngood eBI_good_rev (eqzPair_bodiesRel m).flip hm' hm P)
    (sat_le_of_ngood eBI_good (eqzPair_bodiesRel m) hm hm' P)

end Silmaril.Wasm.FnInst.Ground.Num
