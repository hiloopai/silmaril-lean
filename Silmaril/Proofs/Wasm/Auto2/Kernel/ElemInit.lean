module

public import Silmaril.Proofs.Wasm.Auto2.Kernel.MemInit

/-!
# `tableInitLoop` in closed form

`tableInitLoop_fast`: on the fast path (both ranges in bounds, no address wraps) the reference
loop of `table.init` writes the whole segment at once; `tableInitLoopK_eq` follows. The proof
follows `memoryInitLoop_fast`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto2.Kernel

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Verify.Kernel
open Silmaril.Wasm.Auto2.Kernel

variable {H : Type}

theorem table?_setTable {s : Store H} {f : Frame} {x : TableIdx} {ta : Nat} {ti : TableInst}
    (h : s.table? f x = some (ta, ti)) (ti' : TableInst) :
    (s.setTable ta ti').table? f x = some (ta, ti') := by
  simp only [Store.table?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, b, hb, he⟩ := h
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hlt : a < s.tables.length := (List.getElem?_eq_some_iff.mp hb).1
  simp [Store.table?, Store.setTable, ha, hlt]

theorem elem?_setTable (s : Store H) (f : Frame) (y : ElemIdx) (ta : Nat) (ti : TableInst) :
    (s.setTable ta ti).elem? f y = s.elem? f y := rfl

theorem setTable_setTable (s : Store H) (a : Nat) (t₁ t₂ : TableInst) :
    (s.setTable a t₁).setTable a t₂ = s.setTable a t₂ := by
  simp [Store.setTable]

theorem set_eq_writeL {α : Type} (l : List α) (i : Nat) (b : α) (h : i < l.length) :
    l.set i b = writeL l i [b] := by
  rw [writeL_eq _ _ _ (by simpa using Nat.succ_le_of_lt h), List.set_eq_take_append_cons_drop]
  simp [h]

theorem length_writeL {α : Type} (l : List α) (i : Nat) (bs : List α)
    (h : i + bs.length ≤ l.length) : (writeL l i bs).length = l.length := by
  rw [writeL_eq _ _ _ h]
  simp only [List.length_append, List.length_take, List.length_drop]
  omega

theorem drop_take_succ' {α : Type} (l : List α) (j k : Nat) (h : j < l.length) :
    (l.drop j).take (k + 1) = l[j] :: (l.drop (j + 1)).take k := by
  rw [List.drop_eq_getElem_cons h]
  rfl

/-- The table after one step of the loop, as a write of one reference. -/
theorem tableStep {s : Store H} {ta : Nat} {ti : TableInst} {i : Nat} {r : Ref}
    (hi : i < ti.refs.length) :
    s.setTable ta { ti with refs := ti.refs.set i r } =
      s.setTable ta { ti with refs := writeL ti.refs i [r] } := by
  rw [set_eq_writeL _ _ _ hi]

/-- The last step of the loop: the segment so far, then one more reference. -/
theorem tableLast (s : Store H) (ta : Nat) (ti : TableInst) (i : Nat) (r : Ref) (l : List Ref)
    (k : Nat) (hk : k ≠ 0) :
    (s.setTable ta { ti with refs := writeL ti.refs i [r] }).setTable ta
        { ti with refs := writeL (writeL ti.refs i [r]) (i + 1) (l.take k) } =
      s.setTable ta { ti with refs := writeL ti.refs i (r :: l.take k) } := by
  have _ := hk
  rw [setTable_setTable, writeL_cons]

/-- **`tableInitLoop` on the fast path**: the whole segment written at once. -/
theorem tableInitLoop_fast {f : Frame} {x : TableIdx} {y : ElemIdx} {a : AddrType} {ta ea : Nat}
    {ei : ElemInst} : ∀ (k : Nat) (s : Store H) (ti : TableInst) (i : BitVec a.intType.width)
      (j n : BitVec 32), n.toNat = k → s.table? f x = some (ta, ti) →
      s.elem? f y = some (ea, ei) → i.toNat + k ≤ ti.refs.length → j.toNat + k ≤ ei.refs.length →
      i.toNat + k < 2 ^ a.intType.width → j.toNat + k < 2 ^ 32 →
      tableInitLoop s f x y a i j n =
        if k = 0 then some s
        else some (s.setTable ta
          { ti with refs := writeL ti.refs i.toNat ((ei.refs.drop j.toNat).take k) })
  | 0, s, ti, i, j, n, hn, ht, he, hi, hj, _, _ => by
    have hn0 : n = 0 := BitVec.eq_of_toNat_eq (by simpa using hn)
    subst hn0
    rw [tableInitLoop]
    simp only [ht, he]
    simp [show i.toNat ≤ ti.refs.length by omega, show j.toNat ≤ ei.refs.length by omega]
  | k + 1, s, ti, i, j, n, hn, ht, he, hi, hj, hiw, hjw => by
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp at hn
    have hjl : j.toNat < ei.refs.length := by omega
    have hil : i.toNat < ti.refs.length := by omega
    have hb : ei.refs[j.toNat]? = some ei.refs[j.toNat] := List.getElem?_eq_getElem hjl
    have hk : (n - 1).toNat = k := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
      simp
      omega
    have hi1 := toNat_add_one i (by omega)
    have hj1 := toNat_add_one j (by omega)
    have hsz : (writeL ti.refs i.toNat [ei.refs[j.toNat]]).length = ti.refs.length :=
      length_writeL _ _ _ (by simp; omega)
    have hc : i.toNat + n.toNat ≤ ti.refs.length ∧ j.toNat + n.toNat ≤ ei.refs.length :=
      ⟨by omega, by omega⟩
    have hstep := tableStep (s := s) (ta := ta) (r := ei.refs[j.toNat]) hil
    rw [tableInitLoop]
    simp only [ht, he, hc, and_self, ↓reduceIte, hn0, ↓reduceDIte, hb, hstep]
    rw [tableInitLoop_fast k _ { ti with refs := _ } (i + 1) (j + 1) (n - 1) hk
      (table?_setTable ht _) (by rw [elem?_setTable]; exact he) (by rw [hsz, hi1]; omega)
      (by rw [hj1]; omega) (by rw [hi1]; omega) (by rw [hj1]; omega)]
    simp only [Nat.succ_ne_zero k, ↓reduceIte]
    rw [drop_take_succ' _ _ _ hjl, hi1, hj1]
    by_cases hk0 : k = 0
    · subst hk0
      simp only [↓reduceIte, List.take_zero]
    · simp only [hk0, ↓reduceIte]
      exact congrArg some (tableLast s ta ti i.toNat _ _ k hk0)

/-- **`tableInitLoopK = tableInitLoop`.** -/
theorem tableInitLoopK_eq : @tableInitLoopK H = @tableInitLoop H := by
  funext s f x y a i j n
  unfold tableInitLoopK
  split
  · rename_i ta ti ea ei ht he
    split
    · rename_i hfast
      simp only [tinitFast, Bool.and_eq_true, lenGe_eq, decide_eq_true_eq] at hfast
      obtain ⟨⟨⟨hi, hj⟩, hiw⟩, hjw⟩ := hfast
      rw [tableInitLoop_fast n.toNat s ti i j n rfl ht he hi hj hiw hjw]
    · rfl
  · rfl

end Silmaril.Proofs.Wasm.Auto2.Kernel
