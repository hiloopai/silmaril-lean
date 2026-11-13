module

public import Silmaril.Proofs.Wasm.FnInst.Ground.NumSim
public import Silmaril.Wasm.Binaryen.EqzPair.Thms

@[expose] public section

/-! # Rule lemmas of the stack fragment: the full `neutral-ops` and `eqz-pair` rules

* `good_neutral`, `good_neutral_rev`: `t.const k; t.op; C` ⟷ `C` for every neutral pair
  (`op`, `k`) of `NeutralOps.neutral` (`add`, `sub`, `or`, `xor`, `shl`, `shr_s`, `shr_u`,
  `rotl`, `rotr` with `0`, `mul` with `1`, `and` with all ones), both integer types, and every
  consumer `C` that takes a `t` operand on top (`TopT`: unary, binary, test and comparison
  operators of type `t`, including the trapping `div` and `rem`);
* `good_eqz2`, `good_eqz2_rev`: `i32.eqz; i32.eqz; B` ⟷ `B` for every boolean consumer `B`
  (`br_if`, `select`, `i32.eqz`; `BoolC`).

Each is a computation with `run`; the bridge and silmaril's closure do the rest.
-/

namespace Silmaril.Wasm.FnInst.Ground.Num

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Exec.Pure (asInt asInt_eq_some)
open Silmaril.Wasm.Binaryen.NeutralOps (neutral neutral_sound)

/-- Consumers of a `t` operand on top. -/
def TopT (t : IntType) : NInstr → Prop
  | .un t' _ | .bin t' _ | .test t' _ | .rel t' _ => t' = t
  | _ => False

/-- Boolean consumers: their outcome depends on their top `i32` only through whether it is
zero. -/
def BoolC : NInstr → Prop
  | .brIf _ | .select _ => True
  | .test t op => t = .i32 ∧ op = .eqz
  | _ => False

/-- A consumer of a `t` operand gets stuck unless the top value is a `t` integer. -/
theorem top_of_nstep {t : IntType} {C : NInstr} (hC : TopT t C) {st : List Val} {o : Out1}
    (h : nstep C st = some o) : ∃ v S x, st = v :: S ∧ asInt t v = some x := by
  cases C <;> simp only [TopT] at hC <;> subst hC <;>
    rcases st with _ | ⟨v, _ | ⟨w, S⟩⟩ <;>
    simp only [nstep, Option.map_eq_some_iff, Option.bind_eq_some_iff, reduceCtorEq] at h <;>
    first
    | (obtain ⟨x, hx, -⟩ := h; exact ⟨_, _, x, rfl, hx⟩)
    | (obtain ⟨y, -, x, hx, -⟩ := h; exact ⟨_, _, x, rfl, hx⟩)

/-- A boolean consumer gets stuck unless the top value is an `i32`. -/
theorem top_of_nstep_bool {B : NInstr} (hB : BoolC B) {st : List Val} {o : Out1}
    (h : nstep B st = some o) : ∃ v S x, st = v :: S ∧ asInt .i32 v = some x := by
  cases B <;> simp only [BoolC] at hB
  case test t op =>
    obtain ⟨rfl, -⟩ := hB
    exact top_of_nstep (C := .test .i32 op) rfl h
  all_goals
    rcases st with _ | ⟨c, _ | ⟨b, _ | ⟨a, S⟩⟩⟩ <;>
      simp only [nstep, Option.map_eq_some_iff, reduceCtorEq] at h <;>
      obtain ⟨x, hx, -⟩ := h <;> exact ⟨_, _, x, rfl, hx⟩

/-! ## `neutral-ops` -/

/-- **The neutral operation leaves its other operand.** -/
theorem run_neutral {t : IntType} {op : IntBinOp} {k : BitVec t.width} (hn : neutral op k = true)
    {v : Val} {x : BitVec t.width} (hv : asInt t v = some x) (c : List NInstr) (S : List Val) :
    run (.const t k :: .bin t op :: c) (v :: S) = run c (v :: S) := by
  have hk : asInt t (.num ⟨.int t, k⟩) = some k := asInt_eq_some.mpr rfl
  have hz := neutral_sound hn x
  obtain rfl := asInt_eq_some.mp hv
  show (nstep (.bin t op) (.num ⟨.int t, k⟩ :: .num ⟨.int t, x⟩ :: S)).bind _ = _
  simp only [nstep, asInt_eq_some.mpr rfl, Option.bind_some, Option.map_some, hz]

theorem run_consumer {t : IntType} {C : NInstr} (hC : TopT t C) {c : List NInstr}
    {st : List Val} {o : Out} (h : run (C :: c) st = some o) :
    ∃ v S x, st = v :: S ∧ asInt t v = some x := by
  obtain ⟨o₁, h₁, -⟩ := Option.bind_eq_some_iff.mp h
  exact top_of_nstep hC h₁

/-- `t.const k; t.op; C` ⟶ `C` (any `C`: the left side is stuck unless the top is a `t`). -/
theorem good_neutral {t : IntType} {op : IntBinOp} {k : BitVec t.width} (hn : neutral op k = true)
    (C : NInstr) : NGood [.const t k, .bin t op, C] [C] := by
  refine ⟨⟨.bin t op, by simp, rfl⟩, fun st o h => ?_⟩
  rcases st with _ | ⟨v, S⟩
  · cases h
  · cases hv : asInt t v with
    | none =>
      have h' : (nstep (.bin t op) (.num ⟨.int t, k⟩ :: v :: S)).bind _ = some o := h
      simp [nstep, hv] at h'
    | some x => rwa [run_neutral hn hv] at h

/-- `C` ⟶ `t.const k; t.op; C`. -/
theorem good_neutral_rev {t : IntType} {op : IntBinOp} {k : BitVec t.width}
    (hn : neutral op k = true) {C : NInstr} (hC : TopT t C) (hc : C.isConst = false) :
    NGood [C] [.const t k, .bin t op, C] := by
  refine ⟨⟨C, by simp, hc⟩, fun st o h => ?_⟩
  obtain ⟨v, S, x, rfl, hv⟩ := run_consumer hC h
  rw [run_neutral hn hv]
  exact h

/-! ## `eqz-pair` -/

theorem eqz_eqz_zero (c : BitVec 32) :
    intTestOp .i32 .eqz (intTestOp .i32 .eqz c) = 0 ↔ c = 0 :=
  Silmaril.Wasm.Binaryen.EqzPair.eqz_eqz_eq_zero c

/-- Two `eqz` on an `i32`. -/
theorem run_eqz2 {v : Val} {x : BitVec 32} (hv : asInt .i32 v = some x) (c : List NInstr)
    (S : List Val) :
    run (.test .i32 .eqz :: .test .i32 .eqz :: c) (v :: S) =
      run c (Val.i32 (intTestOp .i32 .eqz (intTestOp .i32 .eqz x)) :: S) := by
  obtain rfl := asInt_eq_some.mp hv
  rfl

theorem ite_zero_congr {α : Type} {a b : BitVec 32} (hab : a = 0 ↔ b = 0) (y z : α) :
    (if a = 0 then y else z) = (if b = 0 then y else z) := by
  by_cases ha : a = 0
  · rw [ite_eq_left ha, ite_eq_left (hab.mp ha)]
  · rw [ite_eq_right ha, ite_eq_right (fun hb => ha (hab.mpr hb))]

theorem run_bool_select {ts : Option (List ValType)} {a b : BitVec 32} (hab : a = 0 ↔ b = 0)
    (c : List NInstr) (S : List Val) :
    run (.select ts :: c) (Val.i32 a :: S) = run (.select ts :: c) (Val.i32 b :: S) := by
  rcases S with _ | ⟨y, _ | ⟨z, S⟩⟩
  · rfl
  · rfl
  · show run c ((if a = 0 then y else z) :: S) = run c ((if b = 0 then y else z) :: S)
    rw [ite_zero_congr hab]

theorem run_bool_brIf {l : LabelIdx} {a b : BitVec 32} (hab : a = 0 ↔ b = 0)
    (c : List NInstr) (S : List Val) :
    run (.brIf l :: c) (Val.i32 a :: S) = run (.brIf l :: c) (Val.i32 b :: S) := by
  show (some (if a = 0 then Out1.ok S else .stop S (.plain (.br l)))).bind _ =
    (some (if b = 0 then Out1.ok S else .stop S (.plain (.br l)))).bind _
  rw [ite_zero_congr hab]

theorem run_bool_eqz {a b : BitVec 32} (hab : a = 0 ↔ b = 0) (c : List NInstr) (S : List Val) :
    run (.test .i32 .eqz :: c) (Val.i32 a :: S) = run (.test .i32 .eqz :: c) (Val.i32 b :: S) := by
  show run c (Val.i32 (intTestOp .i32 .eqz a) :: S) = run c (Val.i32 (intTestOp .i32 .eqz b) :: S)
  rw [Silmaril.Wasm.Binaryen.EqzPair.eqz_congr hab]

/-- A boolean consumer sees only whether its condition is zero. -/
theorem run_bool {B : NInstr} (hB : BoolC B) {a b : BitVec 32} (hab : a = 0 ↔ b = 0)
    (c : List NInstr) (S : List Val) :
    run (B :: c) (Val.i32 a :: S) = run (B :: c) (Val.i32 b :: S) := by
  cases B <;> simp only [BoolC] at hB
  case test t op =>
    obtain ⟨rfl, -⟩ := hB
    cases op
    exact run_bool_eqz hab c S
  case select ts => exact run_bool_select hab c S
  case brIf l => exact run_bool_brIf hab c S

/-- `i32.eqz; i32.eqz; B` ⟶ `B`. -/
theorem good_eqz2 {B : NInstr} (hB : BoolC B) :
    NGood [.test .i32 .eqz, .test .i32 .eqz, B] [B] := by
  refine ⟨⟨.test .i32 .eqz, by simp, rfl⟩, fun st o h => ?_⟩
  rcases st with _ | ⟨v, S⟩
  · cases h
  · cases hv : asInt .i32 v with
    | none =>
      have h' : (nstep (.test .i32 .eqz) (v :: S)).bind _ = some o := h
      simp [nstep, hv] at h'
    | some x =>
      rw [run_eqz2 hv, run_bool hB (eqz_eqz_zero x)] at h
      obtain rfl := asInt_eq_some.mp hv
      exact h

/-- `B` ⟶ `i32.eqz; i32.eqz; B`. -/
theorem good_eqz2_rev {B : NInstr} (hB : BoolC B) (hc : B.isConst = false) :
    NGood [B] [.test .i32 .eqz, .test .i32 .eqz, B] := by
  refine ⟨⟨B, by simp, hc⟩, fun st o h => ?_⟩
  obtain ⟨o₁, h₁, -⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨v, S, x, rfl, hv⟩ := top_of_nstep_bool hB h₁
  rw [run_eqz2 hv, run_bool hB (eqz_eqz_zero x)]
  obtain rfl := asInt_eq_some.mp hv
  exact h

end Silmaril.Wasm.FnInst.Ground.Num
