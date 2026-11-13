module

public import Silmaril.Wasm.FnInst.Ground.Defs

@[expose] public section

/-! # The straight-line interpreter of the grounded fragment: algebra

Facts about `run` and `step1` that do not mention the small-step machine: composition,
leading constants, and the two properties of stack-only code the bridge needs: it keeps the
frame and it does not depend on it, and a run that succeeds keeps succeeding, unchanged,
over a deeper stack.
-/

namespace Silmaril.Wasm.FnInst.Ground

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

theorem run_nil (f : Frame) (st : List Val) : run [] f st = some (f, st) := rfl

theorem run_cons (i : GInstr) (c : List GInstr) (f : Frame) (st : List Val) :
    run (i :: c) f st = (step1 i f st).bind fun r => run c r.1 r.2 := rfl

theorem run_append (c d : List GInstr) (f : Frame) (st : List Val) :
    run (c ++ d) f st = (run c f st).bind fun r => run d r.1 r.2 := by
  induction c generalizing f st with
  | nil => rfl
  | cons i c ih =>
    show (step1 i f st).bind (fun r => run (c ++ d) r.1 r.2) =
      ((step1 i f st).bind fun r => run c r.1 r.2).bind fun r => run d r.1 r.2
    cases step1 i f st with
    | none => rfl
    | some r => exact ih r.1 r.2

/-- Constants as values. -/
def kvals (ks : List (BitVec 32)) : List Val := ks.map Val.i32

theorem run_consts (ks : List (BitVec 32)) (c : List GInstr) (f : Frame) (st : List Val) :
    run (ks.map GInstr.const ++ c) f st = run c f ((kvals ks).reverse ++ st) := by
  induction ks generalizing st with
  | nil => rfl
  | cons k ks ih =>
    have h : run (ks.map GInstr.const ++ c) f (Val.i32 k :: st) =
        run c f ((kvals ks).reverse ++ Val.i32 k :: st) := ih (Val.i32 k :: st)
    have e : (kvals (k :: ks)).reverse ++ st = (kvals ks).reverse ++ Val.i32 k :: st := by
      simp [kvals]
    rw [e]
    exact h

theorem expression_consts (ks : List (BitVec 32)) :
    expression (lower (ks.map GInstr.const)) = vals (kvals ks) := by
  simp only [expression, lower, kvals, vals, List.map_map]
  rfl

/-- Code that is not all constants starts with constants and then a non-constant. -/
theorem split_op {a : List GInstr} (h : ∃ i ∈ a, i.isConst = false) :
    ∃ (ks : List (BitVec 32)) (i : GInstr) (a₁ : List GInstr),
      a = ks.map GInstr.const ++ i :: a₁ ∧ i.isConst = false := by
  induction a with
  | nil => simp at h
  | cons j a ih =>
    cases hj : j.isConst with
    | false => exact ⟨[], j, a, rfl, hj⟩
    | true =>
      obtain ⟨k, rfl⟩ : ∃ k, j = .const k := by cases j <;> simp_all [GInstr.isConst]
      have h' : ∃ i ∈ a, i.isConst = false := by
        obtain ⟨i, hi, hc⟩ := h
        rcases List.mem_cons.mp hi with rfl | hi
        · simp [GInstr.isConst] at hc
        · exact ⟨i, hi, hc⟩
      obtain ⟨ks, i, a₁, rfl, hc⟩ := ih h'
      exact ⟨k :: ks, i, a₁, rfl, hc⟩

/-- Code that is all constants. -/
theorem all_consts {a : List GInstr} (h : ¬ ∃ i ∈ a, i.isConst = false) :
    ∃ ks : List (BitVec 32), a = ks.map GInstr.const := by
  induction a with
  | nil => exact ⟨[], rfl⟩
  | cons j a ih =>
    obtain ⟨k, rfl⟩ : ∃ k, j = .const k := by
      cases j <;> simp_all [GInstr.isConst]
    obtain ⟨ks, rfl⟩ := ih (fun ⟨i, hi, hc⟩ => h ⟨i, by simp [hi], hc⟩)
    exact ⟨k :: ks, rfl⟩

theorem asI32_eq_some {v : Val} {x : BitVec 32} (h : asI32 v = some x) : v = Val.i32 x := by
  unfold asI32 at h
  split at h
  · obtain rfl := Option.some.inj h
    rfl
  · cases h

theorem step1_of_stk {i : GInstr} (hi : i.stk = true) (f : Frame) (st : List Val) :
    step1 i f st = (stepS i st).map fun st' => (f, st') := by
  cases i <;> simp [GInstr.stk] at hi <;> rfl

/-- A binary operator on two `i32` operands. -/
theorem stepS_bin_inv {b : Bin} {X Y : List Val} (h : stepS (.bin b) X = some Y) :
    ∃ x y X', X = Val.i32 y :: Val.i32 x :: X' ∧ Y = Val.i32 (b.eval x y) :: X' := by
  rcases X with _ | ⟨vy, _ | ⟨vx, X'⟩⟩
  · cases h
  · cases h
  · obtain ⟨x, hx, h₂⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp h₂
    obtain rfl : vx = Val.i32 x := asI32_eq_some hx
    obtain rfl : vy = Val.i32 y := asI32_eq_some hy
    exact ⟨x, y, X', rfl, rfl⟩

/-- `i32.eqz` on an `i32` operand. -/
theorem stepS_eqz_inv {X Y : List Val} (h : stepS .eqz X = some Y) :
    ∃ x X', X = Val.i32 x :: X' ∧ Y = Val.i32 (Numerics.intTestOp .i32 .eqz x) :: X' := by
  rcases X with _ | ⟨vx, X'⟩
  · cases h
  · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain rfl : vx = Val.i32 x := asI32_eq_some hx
    exact ⟨x, X', rfl, rfl⟩

/-- `drop` on one operand. -/
theorem stepS_drop_inv {X Y : List Val} (h : stepS .drop X = some Y) :
    ∃ v, X = v :: Y := by
  rcases X with _ | ⟨v, X'⟩
  · cases h
  · exact ⟨v, by rw [Option.some.inj h]⟩

/-- **A stack-only step is stable under a deeper stack.** -/
theorem stepS_append {i : GInstr} {X Y : List Val} (h : stepS i X = some Y) (S : List Val) :
    stepS i (X ++ S) = some (Y ++ S) := by
  cases i with
  | const k => rw [← Option.some.inj h]; rfl
  | nop => rw [← Option.some.inj h]; rfl
  | drop =>
    obtain ⟨v, rfl⟩ := stepS_drop_inv h
    rfl
  | eqz =>
    obtain ⟨x, X', rfl, rfl⟩ := stepS_eqz_inv h
    rfl
  | bin b =>
    obtain ⟨x, y, X', rfl, rfl⟩ := stepS_bin_inv h
    rfl
  | localGet _ | localSet _ | localTee _ => cases h

/-- **A stack-only step keeps the frame, ignores it, and is stable under a deeper stack.** -/
theorem step1_stk {i : GInstr} (hi : i.stk = true) {f f' : Frame} {X Y : List Val}
    (h : step1 i f X = some (f', Y)) :
    f' = f ∧ ∀ f₀ S, step1 i f₀ (X ++ S) = some (f₀, Y ++ S) := by
  rw [step1_of_stk hi] at h
  obtain ⟨Y', hY', he⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  refine ⟨rfl, fun f₀ S => ?_⟩
  rw [step1_of_stk hi, stepS_append hY' S]
  rfl

/-- **A stack-only run keeps the frame, ignores it, and is stable under a deeper stack.** -/
theorem run_stk {c : List GInstr} (hc : ∀ i ∈ c, i.stk = true) {f f' : Frame}
    {X Y : List Val} (h : run c f X = some (f', Y)) :
    f' = f ∧ ∀ f₀ S, run c f₀ (X ++ S) = some (f₀, Y ++ S) := by
  induction c generalizing f X with
  | nil =>
    have e : (f, X) = (f', Y) := Option.some.inj h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    exact ⟨rfl, fun _ _ => rfl⟩
  | cons i c ih =>
    obtain ⟨⟨f₁, X₁⟩, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rfl, hs⟩ := step1_stk (hc i (by simp)) h₁
    obtain ⟨rfl, hr⟩ := ih (fun j hj => hc j (by simp [hj])) h₂
    refine ⟨rfl, fun f₀ S => ?_⟩
    rw [run_cons, hs f₀ S]
    exact hr f₀ S

/-- The non-trapping operators agree with silmaril's numerics. -/
theorem Bin.intBinOp_eq (b : Bin) (x y : BitVec 32) :
    Numerics.intBinOp .i32 b.op x y = .ok (b.eval x y) := by
  cases b <;> rfl

end Silmaril.Wasm.FnInst.Ground
