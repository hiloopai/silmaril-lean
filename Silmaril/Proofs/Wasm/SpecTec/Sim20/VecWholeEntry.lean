module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeValid

/-!
# Entering the vector fragment: typing from validity, and an earlier membership hypothesis

* `typedA_of_vecOkI`, **`typedV_code_of_vecOk`**: every instruction, and so every code sequence,
  of straight-line vector code is typed in `simEnv20V B`. Constants are typed as values, the float
  operators  (`VecFix.typedA_floatVec20V`), `extract_lane` from validity 
  (`VecFix.typedA_extract20V`), and the integer operators from validity (`VecWholeValid`).
* **`typV_of_good20B`**: at the state of any `Good20B` configuration, straight-line vector code
  gives a `TypV (vecNB P)` configuration. **`wholeRunVec_good20B`**: every V2 run of such code
  from that state is a run of `simEnv20V (vecNB P)` between the images.
* **`not_mem_vecIntUnOp_good20B`**, `not_mem_vecIntBinOp_good20B`,
  `not_mem_vecIntRelOp_good20B`: the code of a `Good20B` configuration contains no integer vector
  operator, so the membership hypothesis 's `VecTyp.sstepV_vecInt*_good20B` cannot hold,
  and those three theorems are vacuous. `sstepV_vecIntUnOp_valid`, … restate them with V2
  validity in place of membership.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecWhole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim (SStep cfgV TypedV stateT)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (adminsTy)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)
open Silmaril.Wasm.SpecTec.Sim20.VecNum (vecNB)

variable {H : Type} {hn : H → String} {B : Builtins}

/-! ## Straight-line vector code is typed -/

/-- A value, as an `admininstr` of `simEnv20V`. -/
theorem typedA_val (v : Val) :
    TypedV (simEnv20V B) (.varT "admininstr" []) (adminToV v.toAdmin) :=
  typedV_adminsV_single_iff.1 (VecAgree.typedV_admins_valV v)

/-- **Every instruction of straight-line vector code is a typed `admininstr` of `simEnv20V B`.** -/
theorem typedA_of_vecOkI {i : V2.Instr} (h : vecOkI i = true) :
    TypedV (simEnv20V B) (.varT "admininstr" []) (instrToV i) := by
  cases i <;> simp only [vecOkI, Bool.false_eq_true] at h
  case intConst t b => exact typedA_val (.num ⟨.int t, b⟩)
  case floatConst t b => exact typedA_val (.num ⟨.float t, b⟩)
  case vecConst b => exact typedA_val (.vec b)
  case refNull t => exact typedA_val (.ref (.null t))
  case vecFloatUnOp => exact VecFix.typedA_floatVec20V trivial
  case vecFloatBinOp => exact VecFix.typedA_floatVec20V trivial
  case vecFloatRelOp => exact VecFix.typedA_floatVec20V trivial
  case vecIntUnOp => exact typedA_vecIntUnOp_valid h
  case vecIntBinOp => exact typedA_vecIntBinOp_valid h
  case vecIntRelOp => exact typedA_vecIntRelOp_valid h
  case vecExtractLane => exact VecFix.typedA_extract20V _ _ _ (by simpa [V2.Instr.immediatesValid] using h)

/-- Every administrative instruction of straight-line vector code is typed. -/
theorem typedA_of_vecOkA {a : Admin} (h : vecOkA a = true) :
    TypedV (simEnv20V B) (.varT "admininstr" []) (adminToV a) := by
  cases a <;> simp only [vecOkA, Bool.false_eq_true] at h
  case plain i => exact typedA_of_vecOkI h
  case refFuncAddr a => exact typedA_val (.ref (.funcAddr a))
  case refHostAddr a => exact typedA_val (.ref (.hostAddr a))

/-- **Straight-line vector code is a typed `admininstr*` of `simEnv20V B`.** -/
theorem typedV_code_of_vecOk {code : List Admin} (h : code.all vecOkA = true) :
    TypedV (simEnv20V B) adminsTy (.list (adminsToV code)) := by
  refine Sim.typedV_list_iff.2 fun u hu => ?_
  rw [Pure.adminsToV_eq_map] at hu
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hu
  exact typedA_of_vecOkA (List.all_eq_true.1 h a ha)

/-- A configuration with straight-line vector code and a typed state is `TypV`. -/
theorem typV_of_vecOk {s : Store H} {f : Frame} {code : List Admin}
    (hz : TypedV (simEnv20V B) stateT (stateV hn s f)) (h : code.all vecOkA = true) :
    TypV B hn ⟨s, f, code⟩ :=
  ⟨hz, typedV_code_of_vecOk h⟩

/-- **At the state of a `Good20B` configuration, straight-line vector code is `TypV (vecNB P)`.** -/
theorem typV_of_good20B {P : Profile} {c : Config H} (hg : StoreBulk.Good20B hn P c)
    {code : List Admin} (h : code.all vecOkA = true) :
    TypV (vecNB P) hn ⟨c.store, c.frame, code⟩ :=
  typV_of_vecOk (VecAgree.typedV_TtoV VecAgree.ffT_state (VecAgree.vOk_stateV hn _ _)
    (VecTyp.state_vecNB_of_good20B hg)) h

/-- **Every V2 run of straight-line vector code, from the state of a `Good20B` configuration, is
a run of `simEnv20V (vecNB P)` between the images.** -/
theorem wholeRunVec_good20B {P : Profile} {host : HostSemantics H} {c : Config H}
    (hg : StoreBulk.Good20B hn P c) {code : List Admin} (h : code.all vecOkA = true)
    {c' : Config H} (hr : Steps P host ⟨c.store, c.frame, code⟩ c') :
    Relation.ReflTransGen (SStep (simEnv20V (vecNB P)))
      (configV hn ⟨c.store, c.frame, code⟩) (configV hn c') :=
  (wholeRunVec hr h (typV_of_good20B hg h)).2.2

/-! ## an earlier membership hypothesis -/

/-- `okB` admits no integer vector operator. -/
theorem okB_vecInt {m : ModuleInst} {i : V2.Instr}
    (hi : (∃ s op, i = .vecIntUnOp s op) ∨ (∃ s op, i = .vecIntBinOp s op) ∨
      (∃ s op, i = .vecIntRelOp s op)) :
    StoreBulk.okB m (.plain i) = false := by
  rcases hi with ⟨s, op, rfl⟩ | ⟨s, op, rfl⟩ | ⟨s, op, rfl⟩ <;>
    simp [StoreBulk.okB, StoreBulk.ctrlOkB, StoreBulk.bulkOkI, StoreDeep.ctrlOkD,
      GoodMerge.ctrlOkM, CallIndGood.ctrlOkI, Whole.ctrlOk, StoreGood.storeOkI]

theorem not_mem_good20B {P : Profile} {c : Config H} (hg : StoreBulk.Good20B hn P c)
    {i : V2.Instr} (hi : StoreBulk.okB c.frame.module (.plain i) = false) :
    Admin.plain i ∉ c.code := fun hm => by
  simp [List.all_eq_true.1 hg.ok _ hm] at hi

/-- **No `Good20B` configuration has an integer `vunop` in its code.** -/
theorem not_mem_vecIntUnOp_good20B {P : Profile} {c : Config H} (hg : StoreBulk.Good20B hn P c)
    (s : IntShape) (op : VecIntUnOp) : Admin.plain (.vecIntUnOp s op) ∉ c.code :=
  not_mem_good20B hg (okB_vecInt (.inl ⟨s, op, rfl⟩))

/-- **No `Good20B` configuration has an integer `vbinop` in its code.** -/
theorem not_mem_vecIntBinOp_good20B {P : Profile} {c : Config H} (hg : StoreBulk.Good20B hn P c)
    (s : IntShape) (op : V2.VecIntBinOp) : Admin.plain (.vecIntBinOp s op) ∉ c.code :=
  not_mem_good20B hg (okB_vecInt (.inr (.inl ⟨s, op, rfl⟩)))

/-- **No `Good20B` configuration has an integer `vrelop` in its code.** -/
theorem not_mem_vecIntRelOp_good20B {P : Profile} {c : Config H} (hg : StoreBulk.Good20B hn P c)
    (s : IntShape) (op : IntRelOp) : Admin.plain (.vecIntRelOp s op) ∉ c.code :=
  not_mem_good20B hg (okB_vecInt (.inr (.inr ⟨s, op, rfl⟩)))

/-- **Integer `vunop` at a `Good20B` state, from validity.** -/
theorem sstepV_vecIntUnOp_valid {P : Profile} {cfg : Config H} (hg : StoreBulk.Good20B hn P cfg)
    {s : IntShape} {op : VecIntUnOp} (hv : op.valid s = true) {c : BitVec 128}
    {code' : List Admin} (h : PureStep P [vconst c, .plain (.vecIntUnOp s op)] code') :
    SStep (simEnv20V (vecNB P)) (cfgV (stateV hn cfg.store cfg.frame)
      (adminsToV [vconst c, .plain (.vecIntUnOp s op)]))
      (cfgV (stateV hn cfg.store cfg.frame) (adminsToV code')) :=
  (fwd_vecBase (.mk (.iunop c s op) h)
    (typV_of_good20B hg (by simp [vecOkA, vecOkI, hv]))).2

/-- **Integer `vbinop` at a `Good20B` state, from validity.** -/
theorem sstepV_vecIntBinOp_valid {P : Profile} {cfg : Config H} (hg : StoreBulk.Good20B hn P cfg)
    {s : IntShape} {op : V2.VecIntBinOp} (hv : op.valid s = true) {c₁ c₂ : BitVec 128}
    {code' : List Admin} (h : PureStep P [vconst c₁, vconst c₂, .plain (.vecIntBinOp s op)] code') :
    SStep (simEnv20V (vecNB P)) (cfgV (stateV hn cfg.store cfg.frame)
      (adminsToV [vconst c₁, vconst c₂, .plain (.vecIntBinOp s op)]))
      (cfgV (stateV hn cfg.store cfg.frame) (adminsToV code')) :=
  (fwd_vecBase (.mk (.ibinop c₁ c₂ s op) h)
    (typV_of_good20B hg (by simp [vecOkA, vecOkI, hv]))).2

/-- **Integer `vrelop` at a `Good20B` state, from validity.** -/
theorem sstepV_vecIntRelOp_valid {P : Profile} {cfg : Config H} (hg : StoreBulk.Good20B hn P cfg)
    {s : IntShape} {op : IntRelOp} (hv : op.validShape s = true) {c₁ c₂ : BitVec 128}
    {code' : List Admin} (h : PureStep P [vconst c₁, vconst c₂, .plain (.vecIntRelOp s op)] code') :
    SStep (simEnv20V (vecNB P)) (cfgV (stateV hn cfg.store cfg.frame)
      (adminsToV [vconst c₁, vconst c₂, .plain (.vecIntRelOp s op)]))
      (cfgV (stateV hn cfg.store cfg.frame) (adminsToV code')) :=
  (fwd_vecBase (.mk (.irelop c₁ c₂ s op) h)
    (typV_of_good20B hg (by simp [vecOkA, vecOkI, hv]))).2

end Silmaril.Wasm.SpecTec.Sim20.VecWhole
