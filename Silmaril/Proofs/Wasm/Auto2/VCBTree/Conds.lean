module

public import Silmaril.Wasm.Auto2.VCBTree.Defs
public import Silmaril.Wasm.Auto2.VCGen.Thms
public import Silmaril.Wasm.Logic.Words.Thms

/-!
# The B-tree library's array functions through VC generator 4: the conditions

The 2 conditions of `oba_get` and the 7 of `oba_find` (loop entry, the length's load, the two
exits, the element's load, invariant step, variant), from the `OBA` facts.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCBTree

open Silmaril.Wasm Silmaril.Wasm.Execution
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Logic.Words
open Silmaril.WasmSpec.BTree (OBA BA FindsAt int32Max)

theorem ldW_wd' (B : ByteArray) (a : Nat) : ldW 32 4 .unsigned B a = wd B a := by
  simp [ldW, rd, wd]

/-- An address `x + 4 k` inside an array of capacity `n` does not wrap. -/
theorem addr_toNat {x k : BitVec 32} {n : Nat} (hx : x.toNat + 4 + 4 * n ≤ int32Max)
    (hk : k.toNat ≤ n) : (x + k * 4#32).toNat = x.toNat + 4 * k.toNat := by
  simp only [int32Max] at hx
  bv_omega

/-- The length word of an array. -/
theorem oba_len {B : ByteArray} {x n : Nat} {α : List (BitVec 32)} (h : OBA B x n α) :
    (wd B x).toNat = α.length := by
  obtain ⟨⟨hl, -, hn, hx, -⟩, -⟩ := h
  simp only [int32Max] at hx
  rw [hl, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

/-- An element of an array. -/
theorem oba_elem {B : ByteArray} {x n k : Nat} {α : List (BitVec 32)} (h : OBA B x n α)
    (hk : k < α.length) : wd B (x + 4 + 4 * k) = α.getD k 0 := by
  obtain ⟨⟨-, hw, -, -, -⟩, -⟩ := h
  conv_rhs => rw [← hw]
  rw [getD_words hk]

theorem oba_bound {B : ByteArray} {x : BitVec 32} {n : Nat} {α : List (BitVec 32)} {k : BitVec 32}
    (h : OBA B x.toNat n α) (hk : k.toNat < α.length) : (x + k * 4#32).toNat + 8 ≤ B.size := by
  obtain ⟨⟨-, -, hn, hx, hb⟩, -⟩ := h
  rw [addr_toNat hx (by omega)]
  omega

/-! ## `oba_get` -/

theorem g_bound {M0 : ByteArray} {x k : BitVec 32} (h : btFns.pr 0 M0 [x, k]) :
    (x + k * 4#32).toNat + 8 ≤ M0.size := by
  obtain ⟨n, α, hoba, hk⟩ := h
  exact oba_bound hoba hk

theorem g_post {M0 : ByteArray} {x k : BitVec 32} (_h : btFns.pr 0 M0 [x, k]) :
    btFns.pr 1 M0 [x, k, ldW 32 4 .unsigned M0 ((x + k * 4#32).toNat + 4)] := by
  intro n α hoba hk
  have hx := hoba.1.2.2.2.1
  rw [ldW_wd', addr_toNat hx (by have := hoba.1.2.2.1; omega),
    show x.toNat + 4 * k.toNat + 4 = x.toNat + 4 + 4 * k.toNat by omega, oba_elem hoba hk]

/-! ## `oba_find` -/

theorem f_entry {M0 : ByteArray} {x e : BitVec 32} (_h : btFns.pr 4 M0 [x, e]) :
    btFns.pr 2 M0 [x, e, 0#32] := by
  intro n α _
  exact ⟨by simp, fun j hj => by simp at hj⟩

theorem f_len_bound {M0 : ByteArray} {x e i : BitVec 32}
    (h : btFns.pr 2 M0 [x, e, i] ∧ btFns.pr 4 M0 [x, e]) : x.toNat + 4 ≤ M0.size := by
  obtain ⟨-, n, α, ⟨-, -, -, -, hb⟩, -⟩ := h
  omega

theorem f_exit_len {M0 : ByteArray} {x e i : BitVec 32}
    (h : (ldW 32 4 .unsigned M0 (x.toNat + 0)).toNat ≤ i.toNat ∧ btFns.pr 2 M0 [x, e, i] ∧
      btFns.pr 4 M0 [x, e]) : btFns.pr 3 M0 [x, e, i] := by
  obtain ⟨hle, hinv, -⟩ := h
  intro n α hoba
  obtain ⟨hi, hlt⟩ := hinv n α hoba
  rw [Nat.add_zero, ldW_wd', oba_len hoba] at hle
  exact ⟨hi, hlt, fun j hj hj' => by omega⟩

theorem f_elem_bound {M0 : ByteArray} {x e i : BitVec 32}
    (h : ¬(ldW 32 4 .unsigned M0 (x.toNat + 0)).toNat ≤ i.toNat ∧ btFns.pr 2 M0 [x, e, i] ∧
      btFns.pr 4 M0 [x, e]) : (x + i * 4#32).toNat + 8 ≤ M0.size := by
  obtain ⟨hlt, -, n, α, hoba⟩ := h
  rw [Nat.add_zero, ldW_wd', oba_len hoba] at hlt
  exact oba_bound hoba (by omega)

/-- The element at `i` of every array at `x`. -/
theorem f_elem_eq {M0 : ByteArray} {x i : BitVec 32} {n : Nat} {α : List (BitVec 32)}
    (hoba : OBA M0 x.toNat n α) (hi : i.toNat < α.length) :
    ldW 32 4 .unsigned M0 ((x + i * 4#32).toNat + 4) = α.getD i.toNat 0 := by
  have hx := hoba.1.2.2.2.1
  rw [ldW_wd', addr_toNat hx (by have := hoba.1.2.2.1; omega),
    show x.toNat + 4 * i.toNat + 4 = x.toNat + 4 + 4 * i.toNat by omega, oba_elem hoba hi]

theorem f_exit_found {M0 : ByteArray} {x e i : BitVec 32}
    (h : e.toInt ≤ (ldW 32 4 .unsigned M0 ((x + i * 4#32).toNat + 4)).toInt ∧
      ¬(ldW 32 4 .unsigned M0 (x.toNat + 0)).toNat ≤ i.toNat ∧ btFns.pr 2 M0 [x, e, i] ∧
      btFns.pr 4 M0 [x, e]) : btFns.pr 3 M0 [x, e, i] := by
  obtain ⟨hge, hlt, hinv, -⟩ := h
  intro n α hoba
  obtain ⟨hi, hbelow⟩ := hinv n α hoba
  rw [Nat.add_zero, ldW_wd', oba_len hoba] at hlt
  rw [f_elem_eq hoba (by omega)] at hge
  refine ⟨hi, hbelow, fun j hj hj' => ?_⟩
  have hs := sortedS_iff_getElem.1 hoba.2
  rcases Nat.lt_or_eq_of_le hj with hj | rfl
  · have := hs i.toNat j (by omega) hj' hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i.toNat < α.length)]
      at hge
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
    simp only [Option.getD_some] at hge ⊢
    omega
  · exact hge

theorem f_step {M0 : ByteArray} {x e i i' : BitVec 32}
    (h : i' = i + 1#32 ∧ ¬e.toInt ≤ (ldW 32 4 .unsigned M0 ((x + i * 4#32).toNat + 4)).toInt ∧
      ¬(ldW 32 4 .unsigned M0 (x.toNat + 0)).toNat ≤ i.toNat ∧ btFns.pr 2 M0 [x, e, i] ∧
      btFns.pr 4 M0 [x, e]) : btFns.pr 2 M0 [x, e, i'] := by
  obtain ⟨rfl, hgt, hlt, hinv, -⟩ := h
  intro n α hoba
  obtain ⟨hi, hbelow⟩ := hinv n α hoba
  rw [Nat.add_zero, ldW_wd', oba_len hoba] at hlt
  have hsucc : (i + 1#32).toNat = i.toNat + 1 := by
    have h₁ := hoba.1.2.2.2.1
    have h₂ := hoba.1.2.2.1
    simp only [int32Max] at h₁
    bv_omega
  rw [f_elem_eq hoba (by omega)] at hgt
  rw [hsucc]
  refine ⟨by omega, fun j hj => ?_⟩
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
  · exact hbelow j hj
  · omega

theorem f_var {M0 : ByteArray} {x e i i' : BitVec 32}
    (h : i' = i + 1#32 ∧ ¬e.toInt ≤ (ldW 32 4 .unsigned M0 ((x + i * 4#32).toNat + 4)).toInt ∧
      ¬(ldW 32 4 .unsigned M0 (x.toNat + 0)).toNat ≤ i.toNat ∧ btFns.pr 2 M0 [x, e, i] ∧
      btFns.pr 4 M0 [x, e]) : (4294967295#32 - i').toNat < (4294967295#32 - i).toNat := by
  obtain ⟨rfl, -, hlt, -, -⟩ := h
  have := (ldW 32 4 .unsigned M0 (x.toNat + 0)).isLt
  bv_omega

set_option maxRecDepth 100000 in
/-- **The conditions of `oba_get`.** -/
theorem get_vcs : AllValid btFns (genFunc getSpecV Silmaril.WasmSpec.BTree.getFunc btFuel) := by
  vcgen4
  · exact fun h => g_bound h
  · exact fun h => g_post h

set_option maxRecDepth 100000 in
/-- **The conditions of `oba_find`.** -/
theorem find_vcs : AllValid btFns (genFunc findSpecV Silmaril.WasmSpec.BTree.findFunc btFuel) := by
  vcgen4
  · exact fun h => f_entry h
  · exact fun h => f_len_bound h
  · exact fun h => f_exit_len h
  · exact fun h => f_elem_bound h
  · exact fun h => f_exit_found h
  · exact fun h => f_step h
  · exact fun h => f_var h

end Silmaril.Wasm.Auto2.VCBTree
