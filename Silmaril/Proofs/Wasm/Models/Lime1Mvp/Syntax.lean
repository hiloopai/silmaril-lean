module

public import Silmaril.Wasm.Models.Lime1Mvp.Defs
public import Silmaril.Wasm.Models.Syntax.Thms

/-!
# `InFeatM`: the amended restriction against `InFeat`

* `constExprB_normInit`: erasing a canonical MVP initialiser keeps a constant expression in `S`;
* `constExprB_of_normInit`: with `refTypes`, the erased initialiser was in `S` already;
* `inFeatM_of_inFeat`: a module of `S` is a module of `S` up to MVP initialisers;
* `inFeat_of_inFeatM`: with `refTypes`, the converse;
* `inFeatM_mono`: monotonicity in `S`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.Lime1Mvp

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Models.Lime1Mvp

variable {S T : FeatureSet}

@[simp] theorem constExprB_nil (S : FeatureSet) : constExprB S [] = true := rfl

theorem normInit_of_mvp {e : Expr} (h : isMvpInit e = true) : normInit e = [] := by
  simp [normInit, h]

theorem normInit_of_not {e : Expr} (h : isMvpInit e = false) : normInit e = e := by
  simp [normInit, h]

/-- Erasing a canonical MVP initialiser keeps a constant expression in `S`. -/
theorem constExprB_normInit {e : Expr} (hs : constExprB S e = true) :
    constExprB S (normInit e) = true := by
  cases h : isMvpInit e
  · rwa [normInit_of_not h]
  · rw [normInit_of_mvp h, constExprB_nil]

/-- The canonical MVP initialisers are constant expressions of every `S` with `refTypes`. -/
theorem constExprB_of_mvp (hr : S.has .refTypes = true) {e : Expr} (h : isMvpInit e = true) :
    constExprB S e = true := by
  unfold isMvpInit at h
  split at h
  · show (S.has .refTypes && (AbsHeapType.inFeatB S .func) && true &&
      (true || S.has .extConst)) = true
    simp [AbsHeapType.inFeatB, hr]
  · show (S.has .refTypes && true && (true || S.has .extConst)) = true
    simp [hr]
  · cases h

/-- With `refTypes`, the erased initialiser was a constant expression of `S` already. -/
theorem constExprB_of_normInit (hr : S.has .refTypes = true) {e : Expr}
    (hs : constExprB S (normInit e) = true) : constExprB S e = true := by
  cases h : isMvpInit e
  · rwa [normInit_of_not h] at hs
  · exact constExprB_of_mvp hr h

theorem table_norm {t : Table} (h : Table.inFeatB S t = true) :
    Table.inFeatB S { t with init := normInit t.init } = true := by
  simp only [Table.inFeatB, Bool.and_eq_true] at h ⊢
  exact ⟨h.1, constExprB_normInit h.2⟩

theorem table_denorm (hr : S.has .refTypes = true) {t : Table}
    (h : Table.inFeatB S { t with init := normInit t.init } = true) : Table.inFeatB S t = true := by
  simp only [Table.inFeatB, Bool.and_eq_true] at h ⊢
  exact ⟨h.1, constExprB_of_normInit hr h.2⟩

theorem elem_norm {e : Elem} (h : Elem.inFeatB S e = true) :
    Elem.inFeatB S { e with init := e.init.map normInit } = true := by
  simp only [Elem.inFeatB, Bool.and_eq_true, List.all_map, List.all_eq_true,
    Function.comp_apply] at h ⊢
  exact ⟨⟨h.1.1, fun x hx => constExprB_normInit (h.1.2 x hx)⟩, h.2⟩

theorem elem_denorm (hr : S.has .refTypes = true) {e : Elem}
    (h : Elem.inFeatB S { e with init := e.init.map normInit } = true) :
    Elem.inFeatB S e = true := by
  simp only [Elem.inFeatB, Bool.and_eq_true, List.all_map, List.all_eq_true,
    Function.comp_apply] at h ⊢
  exact ⟨⟨h.1.1, fun x hx => constExprB_of_normInit hr (h.1.2 x hx)⟩, h.2⟩

/-- `Module.inFeatB` of the normalised module: only the table and element conjuncts change. -/
theorem inFeatB_mvpNorm (S : FeatureSet) (m : Module) :
    Module.inFeatB S (mvpNorm m) =
      (m.types.all (RecType.inFeatB S) &&
      m.imports.all (fun i => ExternType.inFeatB S i.type) &&
      (m.tags.isEmpty || S.has .exn) &&
      m.globals.all (Global.inFeatB S) &&
      m.memories.all (MemoryType.inFeatB S) &&
      m.tables.all (fun t => Table.inFeatB S { t with init := normInit t.init }) &&
      m.funcs.all (Func.inFeatB S) &&
      m.elems.all (fun e => Elem.inFeatB S { e with init := e.init.map normInit }) &&
      m.data.all (Data.inFeatB S) &&
      (decide (m.memories.length + (m.imports.filter Import.isMemory).length ≤ 1) ||
        S.has .multiMemory) &&
      (decide (m.tables.length + (m.imports.filter Import.isTable).length ≤ 1) ||
        S.has .refTypes)) := by
  simp only [Module.inFeatB, mvpNorm, List.all_map, Function.comp_def, List.length_map]
  rfl

/-- **A module of `S` is a module of `S` up to the canonical MVP initialisers.** -/
theorem inFeatM_of_inFeat {m : Module} (h : Module.InFeat S m) : InFeatM S m := by
  unfold InFeatM Module.InFeat
  rw [inFeatB_mvpNorm]
  unfold Module.InFeat Module.inFeatB at h
  exact band_mono' (band_mono' (band_mono' (band_mono' (band_mono' (band_mono' id
    (all_mono fun _ => table_norm)) id) (all_mono fun _ => elem_norm)) id) id) id h

/-- **With `refTypes`, a module of `S` up to MVP initialisers is a module of `S`.** -/
theorem inFeat_of_inFeatM (hr : S.has .refTypes = true) {m : Module} (h : InFeatM S m) :
    Module.InFeat S m := by
  unfold InFeatM Module.InFeat at h
  rw [inFeatB_mvpNorm] at h
  unfold Module.InFeat Module.inFeatB
  exact band_mono' (band_mono' (band_mono' (band_mono' (band_mono' (band_mono' id
    (all_mono fun _ => table_denorm hr)) id) (all_mono fun _ => elem_denorm hr)) id) id) id h

/-- Monotonicity of the amended restriction. -/
theorem inFeatM_mono (h : S ≤ T) {m : Module} (hs : InFeatM S m) : InFeatM T m :=
  module_mono h _ hs

end Silmaril.Proofs.Wasm.Models.Lime1Mvp
