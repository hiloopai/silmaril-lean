module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeCtx

/-!
# The vector redexes at `vecNB P`, from a configuration typed in `simEnv20V`

Rounds 7 and 8 lift each vector redex to a `Step` of the corrected script one by one, at a state
typed in `simEnv20T` (moved to `simEnv20V` by `VecAgree.typedV_TtoV`). For a forward theorem
through the context rules the invariant has to be read where the steps happen, in
`simEnv20V (vecNB P)`, because the float-only vector operators are not typed in `simEnv20T`
(`VecRefute.not_typedA_floatOnly20T`).

* `TypV B hn c`: the image of `c`'s state, and of its code, are typed in `simEnv20V B`.
* `VecSrc`: the vector redexes covered, as source code: the six operator families
  (`vunop`, `vbinop`, `vrelop`, at float and integer shapes) and `vextract_lane` at every shape
  (number lanes, packed lanes with a sign, float lanes). `VecBase P` is a V2 pure step from one.
* The builtins: `vecNB P` answers `$lanes_` (integer and float shapes) and every float
  primitive as `vecB P` does (`laneCalls20_vecNB`, `vecNB_lanesF`, `floatB_vecNB`).
* **`fwd_vecBase`**: every `VecBase P` step from a `TypV (vecNB P)` configuration is a `Step` of
  `simEnv20V (vecNB P)` between the images, and the successor is `TypV (vecNB P)`. An integer
  operator's typing is read off the typed code; no `VecNumAgree` or state hypothesis is left.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecWhole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.Wasm.SpecTec.Sim (SStep cfgV TypedV stateT)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (adminsTy)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V numShape)
open Silmaril.Wasm.SpecTec.Sim20.VecLane (Packed packShape fshapeOf lanesFV fshapeV)
open Silmaril.Wasm.SpecTec.Sim20.VecNum (vecNB vecNB_call_of_ne vecNumAgree_vecNB)

variable {H : Type} {hn : H → String} {B : Builtins}

/-! ## The invariant -/

/-- **The image of a configuration is typed in the corrected script**: its state and its code. -/
structure TypV (B : Builtins) (hn : H → String) (c : Config H) : Prop where
  state : TypedV (simEnv20V B) stateT (stateV hn c.store c.frame)
  code : TypedV (simEnv20V B) adminsTy (.list (adminsToV c.code))

/-! ## The redexes -/

/-- **The vector redexes covered**, as source code. -/
inductive VecSrc : List Admin → Prop where
  | funop (c : BitVec 128) (s : FloatShape) (op : FloatUnOp) :
      VecSrc [vconst c, .plain (.vecFloatUnOp s op)]
  | fbinop (c₁ c₂ : BitVec 128) (s : FloatShape) (op : V2.VecFloatBinOp) :
      VecSrc [vconst c₁, vconst c₂, .plain (.vecFloatBinOp s op)]
  | frelop (c₁ c₂ : BitVec 128) (s : FloatShape) (op : FloatRelOp) :
      VecSrc [vconst c₁, vconst c₂, .plain (.vecFloatRelOp s op)]
  | iunop (c : BitVec 128) (s : IntShape) (op : VecIntUnOp) :
      VecSrc [vconst c, .plain (.vecIntUnOp s op)]
  | ibinop (c₁ c₂ : BitVec 128) (s : IntShape) (op : V2.VecIntBinOp) :
      VecSrc [vconst c₁, vconst c₂, .plain (.vecIntBinOp s op)]
  | irelop (c₁ c₂ : BitVec 128) (s : IntShape) (op : IntRelOp) :
      VecSrc [vconst c₁, vconst c₂, .plain (.vecIntRelOp s op)]
  | extractNum (t : IntType) (c : BitVec 128) (i : LaneIdx) :
      VecSrc [vconst c, .plain (.vecExtractLane (.int (numShape t)) none i)]
  | extractPack {sz : PackSize} (hp : Packed sz) (s : Signedness) (c : BitVec 128) (i : LaneIdx) :
      VecSrc [vconst c, .plain (.vecExtractLane (.int (packShape sz)) (some s) i)]
  | extractF (t : FloatType) (c : BitVec 128) (i : LaneIdx) :
      VecSrc [vconst c, .plain (.vecExtractLane (.float (fshapeOf t)) none i)]

/-- **A V2 pure step from a covered vector redex**, at an unchanged store and frame. -/
inductive VecBase (P : Profile) : Config H → Config H → Prop where
  | mk {s : Store H} {f : Frame} {is is' : List Admin} (hs : VecSrc is) (h : PureStep P is is') :
      VecBase P ⟨s, f, is⟩ ⟨s, f, is'⟩

/-- Every covered step is a V2 step. -/
theorem VecBase.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : VecBase P c c') : Step P host c c' := by
  cases h with
  | mk _ h => exact .pure h

/-! ## The builtins -/

/-- `vecNB P` answers the integer lanes and `$ibytes_` as `storeB P`. -/
theorem laneCalls20_vecNB (P : Profile) : Whole.LaneCalls20 (vecNB P) where
  lanes sz c := by
    rw [vecNB_call_of_ne (by decide) (by decide) (by decide)]
    exact (VecLane.laneCalls20_vecB P).lanes sz c
  ibytes N k := by
    rw [vecNB_call_of_ne (by decide) (by decide) (by decide)]
    exact (VecLane.laneCalls20_vecB P).ibytes N k

/-- `$lanes_` at float shapes, at `vecNB P`. -/
theorem vecNB_lanesF (P : Profile) (t : FloatType) (c : BitVec 128) :
    (vecNB P).call "lanes_" [.val (fshapeV t), .val (pctV c.toNat)] =
      some (.list (lanesFV t c)) := by
  rw [vecNB_call_of_ne (by decide) (by decide) (by decide)]
  exact VecLane.vecB_lanesF P t c

/-- `vecNB P` answers every float primitive as `P` does. -/
theorem floatB_vecNB (P : Profile) : Sim.Floats.FloatB P (vecNB P) := by
  intro x ws v h
  by_cases h₁ : x = "vunop_"
  · subst h₁; simp [Sim.Floats.floatCall, Sim.Floats.floatNames] at h
  by_cases h₂ : x = "vbinop_"
  · subst h₂; simp [Sim.Floats.floatCall, Sim.Floats.floatNames] at h
  by_cases h₃ : x = "vrelop_"
  · subst h₃; simp [Sim.Floats.floatCall, Sim.Floats.floatNames] at h
  rw [vecNB_call_of_ne h₁ h₂ h₃]
  exact VecLane.floatB_vecB P x ws v h

/-! ## The base lift -/

/-- A firing of a `Step_pure` rule, between typed codes at a state typed in `simEnv20V`, is a
`Step`. -/
theorem sstepV_of_firesV {k : Nat} {z : Value} {is js : List Value}
    (hz : TypedV (simEnv20V B) stateT z) (his : TypedV (simEnv20V B) adminsTy (.list is))
    (hjs : TypedV (simEnv20V B) adminsTy (.list js))
    (hf : Sim.Fires (simEnv20V B) "Step_pure" k (.tuple [.list is, .list js])) :
    SStep (simEnv20V B) (cfgV z is) (cfgV z js) := by
  obtain ⟨ty, rules, hrel⟩ := VecAgree.findRel_pure20V B
  exact VecAgree.sstepV_pure hz his hjs ((Sim.dderives_iff_fires hrel).2 ⟨k, hf⟩)

/-- The last instruction of a typed redex is a typed `admininstr`. -/
theorem typedA_of_code {pre : List Admin} {i : V2.Instr}
    (h : TypedV (simEnv20V B) adminsTy (.list (adminsToV (pre ++ [.plain i])))) :
    TypedV (simEnv20V B) (.varT "admininstr" []) (instrToV i) :=
  Sim.typedV_list_iff.1 h _ (by
    rw [Pure.adminsToV_eq_map]
    exact List.mem_map.2 ⟨.plain i, by simp, rfl⟩)

/-- The step from typed source code to a value, as `TypV` and a `Step`. -/
theorem fwd_toVal {k : Nat} {s : Store H} {f : Frame} {is : List Admin} {v : Val}
    (ht : TypV B hn ⟨s, f, is⟩)
    (hf : Sim.Fires (simEnv20V B) "Step_pure" k
      (.tuple [.list (adminsToV is), .list (adminsToV [v.toAdmin])])) :
    TypV B hn ⟨s, f, [v.toAdmin]⟩ ∧
      SStep (simEnv20V B) (configV hn ⟨s, f, is⟩) (configV hn ⟨s, f, [v.toAdmin]⟩) :=
  ⟨⟨ht.state, VecAgree.typedV_admins_valV v⟩,
    sstepV_of_firesV ht.state ht.code (VecAgree.typedV_admins_valV v) hf⟩

/-- The conclusion of the base lift, at a source `is`. -/
def BaseGoal (P : Profile) (hn : H → String) (s : Store H) (f : Frame) (is is' : List Admin) :
    Prop :=
  TypV (vecNB P) hn ⟨s, f, is'⟩ ∧
    SStep (simEnv20V (vecNB P)) (configV hn ⟨s, f, is⟩) (configV hn ⟨s, f, is'⟩)

variable {P : Profile} {s : Store H} {f : Frame} {is' : List Admin}

theorem fwdV_funop {c : BitVec 128} {sh : FloatShape} {op : FloatUnOp}
    (ht : TypV (vecNB P) hn ⟨s, f, [vconst c, .plain (.vecFloatUnOp sh op)]⟩)
    (hp : PureStep P [vconst c, .plain (.vecFloatUnOp sh op)] is') :
    BaseGoal P hn s f [vconst c, .plain (.vecFloatUnOp sh op)] is' := by
  have hf := VecLane.fwd_vecFloatUnOp20V (vecNumAgree_vecNB P) hp
  obtain ⟨r, -, rfl⟩ := VecLane.pureStep_vecFloatUnOp_inv hp
  exact fwd_toVal (v := .vec r) ht hf

theorem fwdV_fbinop {c₁ c₂ : BitVec 128} {sh : FloatShape} {op : V2.VecFloatBinOp}
    (ht : TypV (vecNB P) hn ⟨s, f, [vconst c₁, vconst c₂, .plain (.vecFloatBinOp sh op)]⟩)
    (hp : PureStep P [vconst c₁, vconst c₂, .plain (.vecFloatBinOp sh op)] is') :
    BaseGoal P hn s f [vconst c₁, vconst c₂, .plain (.vecFloatBinOp sh op)] is' := by
  have hf := VecLane.fwd_vecFloatBinOp20V (vecNumAgree_vecNB P) hp
  obtain ⟨r, -, rfl⟩ := VecLane.pureStep_vecFloatBinOp_inv hp
  exact fwd_toVal (v := .vec r) ht hf

theorem fwdV_frelop {c₁ c₂ : BitVec 128} {sh : FloatShape} {op : FloatRelOp}
    (ht : TypV (vecNB P) hn ⟨s, f, [vconst c₁, vconst c₂, .plain (.vecFloatRelOp sh op)]⟩)
    (hp : PureStep P [vconst c₁, vconst c₂, .plain (.vecFloatRelOp sh op)] is') :
    BaseGoal P hn s f [vconst c₁, vconst c₂, .plain (.vecFloatRelOp sh op)] is' := by
  have hf := VecLane.fwd_vecFloatRelOp20V (vecNumAgree_vecNB P) hp
  rw [VecLane.pureStep_vecFloatRelOp_inv hp] at hf ⊢
  exact fwd_toVal (v := .vec _) ht hf

theorem fwdV_iunop {c : BitVec 128} {sh : IntShape} {op : VecIntUnOp}
    (ht : TypV (vecNB P) hn ⟨s, f, [vconst c, .plain (.vecIntUnOp sh op)]⟩)
    (hp : PureStep P [vconst c, .plain (.vecIntUnOp sh op)] is') :
    BaseGoal P hn s f [vconst c, .plain (.vecIntUnOp sh op)] is' := by
  have hf := VecTyp.fwd_vecIntUnOp20V (vecNumAgree_vecNB P)
    (typedA_of_code (pre := [vconst c]) ht.code) hp
  obtain ⟨r, -, rfl⟩ := VecTyp.pureStep_vecIntUnOp_inv hp
  exact fwd_toVal (v := .vec r) ht hf

theorem fwdV_ibinop {c₁ c₂ : BitVec 128} {sh : IntShape} {op : V2.VecIntBinOp}
    (ht : TypV (vecNB P) hn ⟨s, f, [vconst c₁, vconst c₂, .plain (.vecIntBinOp sh op)]⟩)
    (hp : PureStep P [vconst c₁, vconst c₂, .plain (.vecIntBinOp sh op)] is') :
    BaseGoal P hn s f [vconst c₁, vconst c₂, .plain (.vecIntBinOp sh op)] is' := by
  have hf := VecTyp.fwd_vecIntBinOp20V (vecNumAgree_vecNB P)
    (typedA_of_code (pre := [vconst c₁, vconst c₂]) ht.code) hp
  obtain ⟨r, -, rfl⟩ := VecTyp.pureStep_vecIntBinOp_inv hp
  exact fwd_toVal (v := .vec r) ht hf

theorem fwdV_irelop {c₁ c₂ : BitVec 128} {sh : IntShape} {op : IntRelOp}
    (ht : TypV (vecNB P) hn ⟨s, f, [vconst c₁, vconst c₂, .plain (.vecIntRelOp sh op)]⟩)
    (hp : PureStep P [vconst c₁, vconst c₂, .plain (.vecIntRelOp sh op)] is') :
    BaseGoal P hn s f [vconst c₁, vconst c₂, .plain (.vecIntRelOp sh op)] is' := by
  have hf := VecTyp.fwd_vecIntRelOp20V (vecNumAgree_vecNB P)
    (typedA_of_code (pre := [vconst c₁, vconst c₂]) ht.code) hp
  rw [VecTyp.pureStep_vecIntRelOp_inv hp] at hf ⊢
  exact fwd_toVal (v := .vec _) ht hf

theorem fwdV_extractNum {t : IntType} {c : BitVec 128} {i : LaneIdx}
    (ht : TypV (vecNB P) hn ⟨s, f, [vconst c, .plain (.vecExtractLane (.int (numShape t)) none i)]⟩)
    (hp : PureStep P [vconst c, .plain (.vecExtractLane (.int (numShape t)) none i)] is') :
    BaseGoal P hn s f [vconst c, .plain (.vecExtractLane (.int (numShape t)) none i)] is' := by
  have hf := VecFix.fwd_vextractLaneNum (VecFix.extractEnv20V (laneCalls20_vecNB P)) t hp
  obtain ⟨-, rfl⟩ := VecFix.pureStep_extract_inv hp
  exact fwd_toVal ht hf

theorem fwdV_extractPack {sz : PackSize} (hpk : Packed sz) {sx : Signedness} {c : BitVec 128}
    {i : LaneIdx}
    (ht : TypV (vecNB P) hn
      ⟨s, f, [vconst c, .plain (.vecExtractLane (.int (packShape sz)) (some sx) i)]⟩)
    (hp : PureStep P [vconst c, .plain (.vecExtractLane (.int (packShape sz)) (some sx) i)] is') :
    BaseGoal P hn s f [vconst c, .plain (.vecExtractLane (.int (packShape sz)) (some sx) i)]
      is' := by
  have hf := VecLane.fwd_vextractLanePack
    (VecLane.packEnv20V (laneCalls20_vecNB P) (floatB_vecNB P)) hpk hp
  obtain ⟨-, rfl⟩ := VecLane.pureStep_extractSx_inv hp
  exact fwd_toVal ht hf

theorem fwdV_extractF {t : FloatType} {c : BitVec 128} {i : LaneIdx}
    (ht : TypV (vecNB P) hn
      ⟨s, f, [vconst c, .plain (.vecExtractLane (.float (fshapeOf t)) none i)]⟩)
    (hp : PureStep P [vconst c, .plain (.vecExtractLane (.float (fshapeOf t)) none i)] is') :
    BaseGoal P hn s f [vconst c, .plain (.vecExtractLane (.float (fshapeOf t)) none i)] is' := by
  have hf := VecLane.fwd_vextractLaneF (VecLane.fExtractEnv20V (vecNB_lanesF P)) t hp
  obtain ⟨-, rfl⟩ := VecFix.pureStep_extract_inv hp
  exact fwd_toVal ht hf

/-- **Every covered vector step from a configuration typed in `simEnv20V (vecNB P)` is a `Step`
of that script between the images**, and the successor is typed there. -/
theorem fwd_vecBase {c c' : Config H} (h : VecBase P c c') (ht : TypV (vecNB P) hn c) :
    TypV (vecNB P) hn c' ∧ SStep (simEnv20V (vecNB P)) (configV hn c) (configV hn c') := by
  obtain ⟨hsrc, hp⟩ := h
  cases hsrc with
  | funop => exact fwdV_funop ht hp
  | fbinop => exact fwdV_fbinop ht hp
  | frelop => exact fwdV_frelop ht hp
  | iunop => exact fwdV_iunop ht hp
  | ibinop => exact fwdV_ibinop ht hp
  | irelop => exact fwdV_irelop ht hp
  | extractNum => exact fwdV_extractNum ht hp
  | extractPack hpk => exact fwdV_extractPack hpk ht hp
  | extractF => exact fwdV_extractF ht hp

end Silmaril.Wasm.SpecTec.Sim20.VecWhole
