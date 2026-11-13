module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecTypInt

/-!
# The vector operators as `Step`s at `vecNB P`, from `Good20B`

* **`sstepV_vecIntUnOp`**, `sstepV_vecIntBinOp`, `sstepV_vecIntRelOp`: under `VecNumAgree`, every
  V2 pure step of an integer vector operator is a `Step` of `simEnv20V B`, at every state typed in
  `simEnv20T B` that is `VOk`, when the operator instruction is a typed `admininstr` of
  `simEnv20T B` (moved to `simEnv20V B` by `VecAgree.typedV_TtoV`).
* **From `Good20B`** (`sstepV_vecFloatUnOp_good20B`, …, `sstepV_vecIntRelOp_good20B`): at a
  `Good20B` configuration, all six lifts hold at `vecNB P` with no hypothesis left about typing.
  The state is typed by `state_vecNB_of_good20B`; an integer operator instruction that occurs in
  the configuration's code is typed by `instr_vecNB_of_good20B`, and `VecNumAgree` holds at
  `vecNB P` (`VecNum.vecNumAgree_vecNB`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecTyp

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim (SStep cfgV TypedV stateT)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (adminsTy)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)
open Silmaril.Wasm.SpecTec.Sim20.VecLane (VecNumAgree)
open Silmaril.Wasm.SpecTec.Sim20.VecNum (vecNB vecNumAgree_vecNB)

variable {B : Builtins}

/-! ## Typing the source -/

theorem ffT_admin : VecAgree.ffT (.varT "admininstr" []) := by
  simp [VecAgree.ffT, Sim.Round7.Script.evTyp, Sim.Round7.Script.evArgs, ElseAgree.GoodT,
    ElseAgree.tyEvB, VecAgree.fams]

/-- Every instruction image is `VOk`. -/
theorem vOk_instrToV (i : V2.Instr) : VecAgree.VOk (instrToV i) := by
  have h := VecAgree.vOk_adminsToV [.plain i]
  cases h with
  | list h => exact h _ (by simp [adminsToV, adminToV])

/-- A typed `admininstr` of `simEnv20T B` is one of `simEnv20V B`. -/
theorem typedA_TtoV {i : V2.Instr}
    (hi : TypedV (simEnv20T B) (.varT "admininstr" []) (instrToV i)) :
    TypedV (simEnv20V B) (.varT "admininstr" []) (instrToV i) :=
  VecAgree.typedV_TtoV ffT_admin (vOk_instrToV i) hi

theorem typedV_src1I (c : BitVec 128) {i : V2.Instr}
    (hi : TypedV (simEnv20V B) (.varT "admininstr" []) (instrToV i)) :
    TypedV (simEnv20V B) adminsTy (.list (adminsToV [vconst c, .plain i])) := by
  refine Sim.typedV_list_iff.2 fun u hu => ?_
  simp only [Pure.adminsToV_eq_map, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact VecLane.typedV_vconstV c
  · exact hi

theorem typedV_src2I (c₁ c₂ : BitVec 128) {i : V2.Instr}
    (hi : TypedV (simEnv20V B) (.varT "admininstr" []) (instrToV i)) :
    TypedV (simEnv20V B) adminsTy (.list (adminsToV [vconst c₁, vconst c₂, .plain i])) := by
  refine Sim.typedV_list_iff.2 fun u hu => ?_
  simp only [Pure.adminsToV_eq_map, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl
  · exact VecLane.typedV_vconstV c₁
  · exact VecLane.typedV_vconstV c₂
  · exact hi

/-! ## The integer lifts -/

/-- **The integer `vunop`s are `Step`s of the corrected script.** -/
theorem sstepV_vecIntUnOp {P : Profile} (hA : VecNumAgree (simEnv20V B) P) {z : Value}
    (hz : TypedV (simEnv20T B) stateT z) (hv : VecAgree.VOk z) {s : IntShape} {op : VecIntUnOp}
    (hi : TypedV (simEnv20T B) (.varT "admininstr" []) (instrToV (.vecIntUnOp s op)))
    {c : BitVec 128} {code' : List Admin}
    (h : PureStep P [vconst c, .plain (.vecIntUnOp s op)] code') :
    SStep (simEnv20V B) (cfgV z (adminsToV [vconst c, .plain (.vecIntUnOp s op)]))
      (cfgV z (adminsToV code')) := by
  have hiV := typedA_TtoV hi
  have hf := fwd_vecIntUnOp20V hA hiV h
  obtain ⟨r, -, rfl⟩ := pureStep_vecIntUnOp_inv h
  exact VecLane.sstepV_of_fires hz hv (typedV_src1I c hiV) (VecAgree.typedV_admins_valV (.vec r)) hf

/-- **The integer `vbinop`s are `Step`s of the corrected script.** -/
theorem sstepV_vecIntBinOp {P : Profile} (hA : VecNumAgree (simEnv20V B) P) {z : Value}
    (hz : TypedV (simEnv20T B) stateT z) (hv : VecAgree.VOk z) {s : IntShape}
    {op : V2.VecIntBinOp}
    (hi : TypedV (simEnv20T B) (.varT "admininstr" []) (instrToV (.vecIntBinOp s op)))
    {c₁ c₂ : BitVec 128} {code' : List Admin}
    (h : PureStep P [vconst c₁, vconst c₂, .plain (.vecIntBinOp s op)] code') :
    SStep (simEnv20V B) (cfgV z (adminsToV [vconst c₁, vconst c₂, .plain (.vecIntBinOp s op)]))
      (cfgV z (adminsToV code')) := by
  have hiV := typedA_TtoV hi
  have hf := fwd_vecIntBinOp20V hA hiV h
  obtain ⟨r, -, rfl⟩ := pureStep_vecIntBinOp_inv h
  exact VecLane.sstepV_of_fires hz hv (typedV_src2I c₁ c₂ hiV)
    (VecAgree.typedV_admins_valV (.vec r)) hf

/-- **The integer `vrelop`s are `Step`s of the corrected script.** -/
theorem sstepV_vecIntRelOp {P : Profile} (hA : VecNumAgree (simEnv20V B) P) {z : Value}
    (hz : TypedV (simEnv20T B) stateT z) (hv : VecAgree.VOk z) {s : IntShape} {op : IntRelOp}
    (hi : TypedV (simEnv20T B) (.varT "admininstr" []) (instrToV (.vecIntRelOp s op)))
    {c₁ c₂ : BitVec 128} {code' : List Admin}
    (h : PureStep P [vconst c₁, vconst c₂, .plain (.vecIntRelOp s op)] code') :
    SStep (simEnv20V B) (cfgV z (adminsToV [vconst c₁, vconst c₂, .plain (.vecIntRelOp s op)]))
      (cfgV z (adminsToV code')) := by
  have hiV := typedA_TtoV hi
  have hf := fwd_vecIntRelOp20V hA hiV h
  rw [pureStep_vecIntRelOp_inv h] at hf ⊢
  exact VecLane.sstepV_of_fires hz hv (typedV_src2I c₁ c₂ hiV)
    (VecAgree.typedV_admins_valV (.vec _)) hf

/-! ## From `Good20B` -/

variable {H : Type} {hn : H → String}

/-- **An instruction in the code of a `Good20B` configuration is a typed `admininstr` of
`simEnv20T (vecNB P)`.** -/
theorem instr_vecNB_of_good20B {P : Profile} {cfg : Config H} (hg : StoreBulk.Good20B hn P cfg)
    {i : V2.Instr} (hm : Admin.plain i ∈ cfg.code) :
    TypedV (simEnv20T (vecNB P)) (.varT "admininstr" []) (instrToV i) :=
  Sim.typedV_list_iff.1 (code_vecNB_of_good20B hg) _ (by
    rw [Pure.adminsToV_eq_map]
    exact List.mem_map.2 ⟨_, hm, rfl⟩)

/-- **Float `vunop`, from `Good20B`.** -/
theorem sstepV_vecFloatUnOp_good20B {P : Profile} {cfg : Config H}
    (hg : StoreBulk.Good20B hn P cfg) {s : FloatShape} {op : FloatUnOp} {c : BitVec 128}
    {code' : List Admin} (h : PureStep P [vconst c, .plain (.vecFloatUnOp s op)] code') :
    SStep (simEnv20V (vecNB P)) (cfgV (stateV hn cfg.store cfg.frame)
      (adminsToV [vconst c, .plain (.vecFloatUnOp s op)]))
      (cfgV (stateV hn cfg.store cfg.frame) (adminsToV code')) :=
  VecNum.sstepV_vecFloatUnOp_vecNB (state_vecNB_of_good20B hg) (VecAgree.vOk_stateV hn _ _) h

/-- **Float `vbinop`, from `Good20B`.** -/
theorem sstepV_vecFloatBinOp_good20B {P : Profile} {cfg : Config H}
    (hg : StoreBulk.Good20B hn P cfg) {s : FloatShape} {op : V2.VecFloatBinOp}
    {c₁ c₂ : BitVec 128} {code' : List Admin}
    (h : PureStep P [vconst c₁, vconst c₂, .plain (.vecFloatBinOp s op)] code') :
    SStep (simEnv20V (vecNB P)) (cfgV (stateV hn cfg.store cfg.frame)
      (adminsToV [vconst c₁, vconst c₂, .plain (.vecFloatBinOp s op)]))
      (cfgV (stateV hn cfg.store cfg.frame) (adminsToV code')) :=
  VecNum.sstepV_vecFloatBinOp_vecNB (state_vecNB_of_good20B hg) (VecAgree.vOk_stateV hn _ _) h

/-- **Float `vrelop`, from `Good20B`.** -/
theorem sstepV_vecFloatRelOp_good20B {P : Profile} {cfg : Config H}
    (hg : StoreBulk.Good20B hn P cfg) {s : FloatShape} {op : FloatRelOp} {c₁ c₂ : BitVec 128}
    {code' : List Admin}
    (h : PureStep P [vconst c₁, vconst c₂, .plain (.vecFloatRelOp s op)] code') :
    SStep (simEnv20V (vecNB P)) (cfgV (stateV hn cfg.store cfg.frame)
      (adminsToV [vconst c₁, vconst c₂, .plain (.vecFloatRelOp s op)]))
      (cfgV (stateV hn cfg.store cfg.frame) (adminsToV code')) :=
  VecNum.sstepV_vecFloatRelOp_vecNB (state_vecNB_of_good20B hg) (VecAgree.vOk_stateV hn _ _) h

/-- **Integer `vunop`, from `Good20B`**, for an instruction of the configuration's code. -/
theorem sstepV_vecIntUnOp_good20B {P : Profile} {cfg : Config H}
    (hg : StoreBulk.Good20B hn P cfg) {s : IntShape} {op : VecIntUnOp}
    (hm : Admin.plain (.vecIntUnOp s op) ∈ cfg.code) {c : BitVec 128} {code' : List Admin}
    (h : PureStep P [vconst c, .plain (.vecIntUnOp s op)] code') :
    SStep (simEnv20V (vecNB P)) (cfgV (stateV hn cfg.store cfg.frame)
      (adminsToV [vconst c, .plain (.vecIntUnOp s op)]))
      (cfgV (stateV hn cfg.store cfg.frame) (adminsToV code')) :=
  sstepV_vecIntUnOp (vecNumAgree_vecNB P) (state_vecNB_of_good20B hg)
    (VecAgree.vOk_stateV hn _ _) (instr_vecNB_of_good20B hg hm) h

/-- **Integer `vbinop`, from `Good20B`**, for an instruction of the configuration's code. -/
theorem sstepV_vecIntBinOp_good20B {P : Profile} {cfg : Config H}
    (hg : StoreBulk.Good20B hn P cfg) {s : IntShape} {op : V2.VecIntBinOp}
    (hm : Admin.plain (.vecIntBinOp s op) ∈ cfg.code) {c₁ c₂ : BitVec 128} {code' : List Admin}
    (h : PureStep P [vconst c₁, vconst c₂, .plain (.vecIntBinOp s op)] code') :
    SStep (simEnv20V (vecNB P)) (cfgV (stateV hn cfg.store cfg.frame)
      (adminsToV [vconst c₁, vconst c₂, .plain (.vecIntBinOp s op)]))
      (cfgV (stateV hn cfg.store cfg.frame) (adminsToV code')) :=
  sstepV_vecIntBinOp (vecNumAgree_vecNB P) (state_vecNB_of_good20B hg)
    (VecAgree.vOk_stateV hn _ _) (instr_vecNB_of_good20B hg hm) h

/-- **Integer `vrelop`, from `Good20B`**, for an instruction of the configuration's code. -/
theorem sstepV_vecIntRelOp_good20B {P : Profile} {cfg : Config H}
    (hg : StoreBulk.Good20B hn P cfg) {s : IntShape} {op : IntRelOp}
    (hm : Admin.plain (.vecIntRelOp s op) ∈ cfg.code) {c₁ c₂ : BitVec 128} {code' : List Admin}
    (h : PureStep P [vconst c₁, vconst c₂, .plain (.vecIntRelOp s op)] code') :
    SStep (simEnv20V (vecNB P)) (cfgV (stateV hn cfg.store cfg.frame)
      (adminsToV [vconst c₁, vconst c₂, .plain (.vecIntRelOp s op)]))
      (cfgV (stateV hn cfg.store cfg.frame) (adminsToV code')) :=
  sstepV_vecIntRelOp (vecNumAgree_vecNB P) (state_vecNB_of_good20B hg)
    (VecAgree.vOk_stateV hn _ _) (instr_vecNB_of_good20B hg hm) h

end Silmaril.Wasm.SpecTec.Sim20.VecTyp
