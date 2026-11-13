module

public import Silmaril.Proofs.Wasm.FnInst.Ground.Sim

@[expose] public section

/-! # Rule lemmas of the grounded fragment

Each rule is one `Good` lemma: the side condition on its left side (stack-only, or one
`local.get` followed by stack-only code that never gets stuck) and its equal runs
(`RunRef`), a computation with `run`. Everything else is the bridge (`gBaseSim`) and
silmaril's closure.

* `good_dropGet`: `local.get x; drop` ⟶ `nop` (wasm-opt's `drop-get` stage);
* `good_rseSet`, `good_rseTee`: `local.get x; drop` ⟵ `local.get x; local.set x` and
  `local.get x` ⟵ `local.get x; local.tee x` (the `rse-line` stage, rewritten side on the
  left);
* `good_neutral`: `i32.const k; op` ⟶ nothing for a right-neutral `k` (`neutral-ops`, the
  `i32` operators of the fragment);
* `good_eqz3`: `i32.eqz; i32.eqz; i32.eqz` ⟶ `i32.eqz` (`eqz-pair`, consumer `i32.eqz`);
* `good_fold`: `i32.const a; i32.const b; op` ⟶ `i32.const (a op b)` (constant folding);
* `good_constDrop`: `i32.const k; drop` ⟶ nothing.
-/

namespace Silmaril.Wasm.FnInst.Ground

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

/-- A read is followed by a `drop`, which never gets stuck. -/
theorem drop_total : ∀ (f : Frame) (v : Val) (X : List Val), (run [.drop] f (v :: X)).isSome :=
  fun _ _ _ => rfl

/-- The result of a read followed by a `drop`. -/
theorem run_getDrop {x : LocalIdx} {f : Frame} {st : List Val} {r : Frame × List Val}
    (h : run [.localGet x, .drop] f st = some r) :
    ∃ v, f.local? x = some (some v) ∧ r = (f, st) := by
  obtain ⟨⟨f₁, X₁⟩, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨v, hv, rfl, rfl⟩ := step1_get_inv h₁
  exact ⟨v, hv, (Option.some.inj h₂).symm⟩

theorem good_dropGet (x : LocalIdx) : Good [.localGet x, .drop] [.nop] := by
  refine Or.inr ⟨⟨x, [.drop], rfl, by simp [GInstr.stk], drop_total⟩, ?_⟩
  intro f st r h
  obtain ⟨v, -, rfl⟩ := run_getDrop h
  rfl

/-- Reading a local and writing it back: the frame does not change. -/
theorem run_getSet {x : LocalIdx} {f : Frame} {v : Val} (hv : f.local? x = some (some v))
    (st : List Val) (tee : Bool) :
    run [.localGet x, if tee then .localTee x else .localSet x] f st =
      some (f, if tee then v :: st else st) := by
  have hx : x.toNat < f.locals.length := (List.getElem?_eq_some_iff.mp hv).1
  have h₁ : step1 (.localGet x) f st = some (f, v :: st) := by
    show (f.local? x).bind (fun o => o.map fun v => (f, v :: st)) = _
    rw [hv]
    rfl
  rw [run_cons, h₁]
  cases tee
  · show (if x.toNat < f.locals.length then some (f.setLocal x v, st) else none).bind _ = _
    rw [RedundantSetLine.setLocal_self hv]
    split <;> rfl
  · show (if x.toNat < f.locals.length then some (f.setLocal x v, v :: st) else none).bind _ = _
    rw [RedundantSetLine.setLocal_self hv]
    split <;> rfl

theorem good_rseSet (x : LocalIdx) : Good [.localGet x, .drop] [.localGet x, .localSet x] := by
  refine Or.inr ⟨⟨x, [.drop], rfl, by simp [GInstr.stk], drop_total⟩, ?_⟩
  intro f st r h
  obtain ⟨v, hv, rfl⟩ := run_getDrop h
  exact run_getSet hv st false

theorem good_rseTee (x : LocalIdx) : Good [.localGet x] [.localGet x, .localTee x] := by
  refine Or.inr ⟨⟨x, [], rfl, by simp, fun _ _ _ => rfl⟩, ?_⟩
  intro f st r h
  obtain ⟨⟨f₁, X₁⟩, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨v, hv, rfl, rfl⟩ := step1_get_inv h₁
  obtain rfl : (f, v :: st) = r := Option.some.inj h₂
  exact run_getSet hv st true

/-- `k` is a right-neutral element of the operator. -/
def Neutral (b : Bin) (k : BitVec 32) : Prop := ∀ x, b.eval x k = x

theorem neutral_add : Neutral .add 0 := fun x => BitVec.add_zero x
theorem neutral_sub : Neutral .sub 0 := fun x => BitVec.sub_zero x
theorem neutral_mul : Neutral .mul 1 := fun x => BitVec.mul_one x
theorem neutral_and : Neutral .and (BitVec.allOnes 32) := fun _ => BitVec.and_allOnes
theorem neutral_or : Neutral .or 0 := fun _ => BitVec.or_zero
theorem neutral_xor : Neutral .xor 0 := fun _ => BitVec.xor_zero

theorem good_neutral {b : Bin} {k : BitVec 32} (hk : Neutral b k) :
    Good [.const k, .bin b] [] := by
  refine Or.inl ⟨⟨by simp [GInstr.stk], ⟨.bin b, by simp, rfl⟩⟩, ?_⟩
  intro f st r h
  have h₀ : run [.bin b] f (Val.i32 k :: st) = some r := h
  obtain ⟨⟨f₁, X₁⟩, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h₀
  obtain ⟨rfl, h₁'⟩ := step1_stk_inv rfl h₁
  obtain ⟨x, y, X', hX, rfl⟩ := stepS_bin_inv h₁'
  obtain ⟨hk', rfl⟩ := List.cons.inj hX
  obtain rfl : k = y := Option.some.inj (congrArg asI32 hk' : some k = some y)
  obtain rfl : (f, Val.i32 (b.eval x k) :: X') = r := Option.some.inj h₂
  rw [hk x]
  rfl

/-- `i32.eqz` three times is `i32.eqz` once. -/
theorem eqz_bool32 (c : Bool) : intTestOp .i32 .eqz (bool32 c) = bool32 (!c) := by
  cases c <;> decide

theorem eqz_eqz_eqz (x : BitVec 32) :
    intTestOp .i32 .eqz (intTestOp .i32 .eqz (intTestOp .i32 .eqz x)) = intTestOp .i32 .eqz x := by
  show intTestOp .i32 .eqz (intTestOp .i32 .eqz (bool32 (x == 0))) = bool32 (x == 0)
  rw [eqz_bool32, eqz_bool32, Bool.not_not]

theorem good_eqz3 : Good [.eqz, .eqz, .eqz] [.eqz] := by
  refine Or.inl ⟨⟨by simp [GInstr.stk], ⟨.eqz, by simp, rfl⟩⟩, ?_⟩
  intro f st r h
  obtain ⟨⟨f₁, X₁⟩, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨rfl, h₁'⟩ := step1_stk_inv rfl h₁
  obtain ⟨x, X, rfl, rfl⟩ := stepS_eqz_inv h₁'
  have h₃ : some (f, Val.i32 (intTestOp .i32 .eqz (intTestOp .i32 .eqz
      (intTestOp .i32 .eqz x))) :: X) = some r := h₂
  rw [eqz_eqz_eqz] at h₃
  exact h₃

theorem good_fold (b : Bin) (x y : BitVec 32) :
    Good [.const x, .const y, .bin b] [.const (b.eval x y)] :=
  Or.inl ⟨⟨by simp [GInstr.stk], ⟨.bin b, by simp, rfl⟩⟩, fun _ _ _ h => h⟩

theorem good_constDrop (k : BitVec 32) : Good [.const k, .drop] [] :=
  Or.inl ⟨⟨by simp [GInstr.stk], ⟨.drop, by simp, rfl⟩⟩, fun _ _ _ h => h⟩

end Silmaril.Wasm.FnInst.Ground
