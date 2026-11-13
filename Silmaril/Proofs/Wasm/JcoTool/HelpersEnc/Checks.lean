module

public import Silmaril.Proofs.Wasm.JcoTool.HelpersEnc.Fixup

/-!
# `shimAst tys` and `fixupAst tys` pass the checks of `Silmaril.Wasm.JcoTool.Helpers`

`shimAst_isShim` and `fixupAst_isFixup`, for fewer than `2 ^ 32` slots each of fewer than
`2 ^ 32` parameters.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.HelpersEnc

open Silmaril.Wasm
open Silmaril.Wasm.Component (CoreFuncTy)
open Helpers (ix)

theorem ix_ixn {k : IndexKind} {n : Nat} (h : n < 2 ^ 32) : ix (ixn n : Idx k) = n := by
  simp only [ix, ixn, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt h

theorem tableTy_ok {n : Nat} (h : n < 2 ^ 32) : Helpers.tableOk n (tableTy n) = true := by
  have h64 : n < 18446744073709551616 := Nat.lt_trans h (by decide)
  simp [Helpers.tableOk, tableTy, h64]

theorem trampAst_get_lt {p i j : Nat} (hj : j < p) :
    (trampAst p i)[j]? = some (.localGet (ixn j)) := by
  unfold trampAst
  rw [List.getElem?_append_left (by simpa using hj)]
  simp [hj]

theorem trampAst_get_p (p i : Nat) :
    (trampAst p i)[p]? = some (.intConst .i32 (BitVec.ofNat 32 i)) := by
  unfold trampAst
  rw [List.getElem?_append_right (by simp)]
  simp

theorem trampAst_get_p1 (p i : Nat) :
    (trampAst p i)[p + 1]? = some (.callIndirect (ixn 0) (ixn i)) := by
  unfold trampAst
  rw [List.getElem?_append_right (by simp)]
  simp

/-- **The trampoline's body passes the check.** -/
theorem trampAst_check {p i : Nat} (hp : p ≤ 2 ^ 32) (hi : i < 2 ^ 32) :
    Helpers.trampOk p i (trampAst p i) = true := by
  have hlen : (trampAst p i).length = p + 2 := by simp [trampAst]
  have hc : Helpers.isI32Const i (.intConst .i32 (BitVec.ofNat 32 i)) = true := by
    have ht : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
    exact beq_iff_eq.mpr ht
  have hci : Helpers.isCallIndirect i (.callIndirect (ixn 0) (ixn i)) = true := by
    simp [Helpers.isCallIndirect, ix_ixn hi, ix_ixn (show 0 < 2 ^ 32 by decide)]
  unfold Helpers.trampOk
  simp only [hlen, trampAst_get_p, trampAst_get_p1, hc, hci, beq_self_eq_true, Bool.and_true,
    Bool.true_and]
  refine List.all_eq_true.mpr fun j hj => ?_
  have hj' : j < p := List.mem_range.mp hj
  rw [trampAst_get_lt hj']
  simp [Helpers.isLocalGet, ix_ixn (Nat.lt_of_lt_of_le hj' hp)]

/-! ## The shim -/

theorem shimFuncsA_length (tys : List CoreFuncTy) : (shimFuncsA tys).length = tys.length := by
  simp [shimFuncsA]

theorem shimFuncsA_get {tys : List CoreFuncTy} {i : Nat} (hi : i < tys.length) :
    (shimFuncsA tys)[i]? = some ⟨ixn i, [], trampAst tys[i].params.length i⟩ := by
  simp [shimFuncsA, hi]

theorem ftAst_funcType (t : CoreFuncTy) :
    Helpers.funcTypeOf (ftAst t) = some ⟨t.params.map .num, t.results.map .num⟩ := rfl

theorem shimExportsA_get_lt {n i : Nat} (hi : i < n) :
    (shimExportsA n)[i]? = some ⟨toString i, .func (ixn i)⟩ := by
  unfold shimExportsA
  rw [List.getElem?_append_left (by simpa using hi)]
  simp [hi]

theorem shimExportsA_get_n (n : Nat) :
    (shimExportsA n)[n]? = some ⟨"$imports", .table (ixn 0)⟩ := by
  unfold shimExportsA
  rw [List.getElem?_append_right (by simp)]
  simp

theorem shim_slot_ok {tys : List CoreFuncTy} (hn : tys.length < 2 ^ 32)
    (hp : ∀ t ∈ tys, t.params.length ≤ 2 ^ 32) {i : Nat} (hi : i < tys.length) :
    (match (shimFuncsA tys)[i]?, ((tys.map ftAst)[i]?).bind Helpers.funcTypeOf with
      | some f, some ft => ix f.type == i && f.locals.isEmpty &&
          Helpers.trampOk ft.params.length i f.body
      | _, _ => false) = true := by
  have hi32 : i < 2 ^ 32 := Nat.lt_trans hi hn
  have ht : ((tys.map ftAst)[i]?).bind Helpers.funcTypeOf =
      some ⟨tys[i].params.map .num, tys[i].results.map .num⟩ := by
    simp [hi, ftAst_funcType]
  rw [shimFuncsA_get hi, ht]
  simp only [ix_ixn hi32, beq_self_eq_true, Bool.true_and, List.length_map]
  exact trampAst_check (hp _ (List.getElem_mem hi)) hi32

theorem shim_export_ok {n : Nat} (hn : n < 2 ^ 32) {i : Nat} (hi : i < n + 1) :
    (match (shimExportsA n)[i]? with
      | some e => Helpers.shimExportOk n i e
      | none => false) = true := by
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · rw [shimExportsA_get_lt hi]
    simp [Helpers.shimExportOk, hi, ix_ixn (Nat.lt_trans hi hn)]
  · rw [shimExportsA_get_n]
    simp [Helpers.shimExportOk, ix_ixn (show 0 < 2 ^ 32 by decide)]

/-- **`shimAst tys` is a shim.** -/
theorem shimAst_isShim {tys : List CoreFuncTy} (hn : tys.length < 2 ^ 32)
    (hp : ∀ t ∈ tys, t.params.length ≤ 2 ^ 32) : Helpers.isShim (shimAst tys) = true := by
  have hty : (tys.map ftAst).all (fun r => (Helpers.funcTypeOf r).isSome) = true :=
    List.all_eq_true.mpr fun r hr => by
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hr
      rfl
  unfold Helpers.isShim
  simp only [shimAst_types, shimAst_imports, shimAst_tags, shimAst_globals, shimAst_memories,
    shimAst_data, shimAst_elems, shimAst_start, shimAst_tables, shimAst_funcs, shimAst_exports,
    List.length_map, hty, tableTy_ok hn, shimFuncsA_length]
  simp only [List.isEmpty_nil, Option.isNone_none, beq_self_eq_true, Bool.true_and, Bool.and_true,
    List.all_eq_true, List.mem_range, Bool.and_eq_true]
  have hlen : ((shimExportsA tys.length).length == tys.length + 1) = true := by
    simp [shimExportsA]
  exact ⟨⟨fun x hx => shim_slot_ok hn hp hx, hlen⟩, fun x hx => shim_export_ok hn hx⟩

/-! ## The fixup -/

theorem fixupImportsA_get_lt {n i : Nat} (hi : i < n) :
    (fixupImportsA n)[i]? = some ⟨"actual", toString i, .func (ixn i)⟩ := by
  unfold fixupImportsA
  rw [List.getElem?_append_left (by simpa using hi)]
  simp [hi]

theorem fixupImportsA_get_n (n : Nat) :
    (fixupImportsA n)[n]? = some ⟨"shim", "$imports", .table (tableTy n)⟩ := by
  unfold fixupImportsA
  rw [List.getElem?_append_right (by simp)]
  simp

theorem fixup_import_ok {n : Nat} (hn : n < 2 ^ 32) {i : Nat} (hi : i < n + 1) :
    (match (fixupImportsA n)[i]? with
      | some im => Helpers.fixupImportOk n i im
      | none => false) = true := by
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · rw [fixupImportsA_get_lt hi]
    simp [Helpers.fixupImportOk, hi, ix_ixn (Nat.lt_trans hi hn)]
  · rw [fixupImportsA_get_n]
    simp [Helpers.fixupImportOk, tableTy_ok hn]

theorem fixup_init_ok {n i : Nat} (hn : n < 2 ^ 32) (hi : i < n) :
    (match ((List.range n).map fun j => ([.refFunc (ixn j)] : Expr))[i]? with
      | some x => Helpers.isRefFunc i x
      | none => false) = true := by
  simp [hi, Helpers.isRefFunc, ix_ixn (Nat.lt_trans hi hn)]

/-- **`fixupAst tys` is a fixup.** -/
theorem fixupAst_isFixup {tys : List CoreFuncTy} (hn : tys.length < 2 ^ 32) :
    Helpers.isFixup (fixupAst tys) = true := by
  have hty : (tys.map ftAst).all (fun r => (Helpers.funcTypeOf r).isSome) = true :=
    List.all_eq_true.mpr fun r hr => by
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hr
      rfl
  have hlen : ((fixupImportsA tys.length).length == tys.length + 1) = true := by
    simp [fixupImportsA]
  have hc : Helpers.isI32Const 0 (.intConst .i32 (BitVec.ofNat 32 0)) = true := rfl
  have h0 : ix (ixn 0 : Idx .table) = 0 := ix_ixn (by decide)
  show Helpers.isFixup (Module.mk (tys.map ftAst) (fixupImportsA tys.length) [] [] [] [] [] []
    [fixupElem tys.length] none []) = true
  unfold Helpers.isFixup
  simp only [hty, hlen, List.isEmpty_nil, Option.isNone_none, Bool.true_and, Bool.and_true,
    List.length_map, Bool.and_eq_true, List.all_eq_true, List.mem_range, fixupElem, hc, h0,
    beq_self_eq_true, List.length_range]
  exact ⟨fun x hx => fixup_import_ok hn hx, fun x hx => fixup_init_ok hn hx⟩

end Silmaril.Wasm.JcoTool.HelpersEnc
