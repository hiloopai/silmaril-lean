module

public import Silmaril.Proofs.Wasm.Models.V2Core.ReflErase

/-!
# Core contexts that are images of 2.0 contexts

`Rel C D`: the Core 3.0 validation context `D` is the image of the 2.0 context `C`, field by field,
except that the initialisation status of locals is free (a Core sequence typing initialises
locals as it goes, and 2.0 has no such status). Every lookup in `D` is then the image of a lookup
in `C` (`Rel.funcs_get`, …), `Rel` survives `initLocals` and `withLabel`, and `D` is
well-formed (`Rel.wf`), so the Core metatheory (`InstrsOk.regular`, `er_sub`) applies.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2Core.Reflect

open Silmaril.Wasm.V2.Validation (globalToC tableToC resultToC)
open Silmaril.Wasm.Validation (TypeCtx defKind compAbs)

/-- Core context `D` is the image of the 2.0 context `C` (up to the status of locals). -/
structure Rel (C : Silmaril.Wasm.V2.Validation.Context) (D : Silmaril.Wasm.Validation.Context) :
    Prop where
  types : D.types = C.types.map Silmaril.Wasm.V2.FuncType.toDefType
  recs : D.recs = []
  tags : D.tags = []
  funcs : D.funcs = C.funcs.map Silmaril.Wasm.V2.FuncType.toDefType
  globals : D.globals = C.globals.map globalToC
  tables : D.tables = C.tables.map tableToC
  mems : D.mems = C.mems.map Silmaril.Wasm.V2.MemoryType.toCore
  elems : D.elems = C.elems.map Silmaril.Wasm.V2.RefType.toC
  datas : D.datas = C.datas
  locals : ∀ y : Nat, (D.locals[y]?).map Silmaril.Wasm.Validation.LocalType.type = (C.locals[y]?).map Silmaril.Wasm.V2.ValType.toC
  labels : D.labels = C.labels.map resultToC
  return_ : D.return_ = C.return_.map resultToC
  refs : D.refs = C.refs.map Silmaril.Wasm.Idx.toNat

/-- A lookup in a mapped list is the image of a lookup. -/
theorem getElem?_map_some {α β : Type} {f : α → β} {l : List α} {n : Nat} {b : β}
    (h : (l.map f)[n]? = some b) : ∃ a, l[n]? = some a ∧ f a = b := by
  rw [List.getElem?_map] at h
  exact Option.map_eq_some_iff.mp h

namespace Rel

variable {C : Silmaril.Wasm.V2.Validation.Context} {D : Silmaril.Wasm.Validation.Context}

theorem types_get (hR : Rel C D) {x : Nat} {d : Silmaril.Wasm.Validation.DefType}
    (h : D.types[x]? = some d) : ∃ ft, C.types[x]? = some ft ∧ ft.toDefType = d :=
  getElem?_map_some (hR.types ▸ h)

theorem funcs_get (hR : Rel C D) {x : Nat} {d : Silmaril.Wasm.Validation.DefType}
    (h : D.funcs[x]? = some d) : ∃ ft, C.funcs[x]? = some ft ∧ ft.toDefType = d :=
  getElem?_map_some (hR.funcs ▸ h)

theorem globals_get (hR : Rel C D) {x : Nat} {g : Silmaril.Wasm.Validation.CGlobalType}
    (h : D.globals[x]? = some g) : ∃ gt, C.globals[x]? = some gt ∧ globalToC gt = g :=
  getElem?_map_some (hR.globals ▸ h)

theorem tables_get (hR : Rel C D) {x : Nat} {t : Silmaril.Wasm.Validation.CTableType}
    (h : D.tables[x]? = some t) : ∃ tt, C.tables[x]? = some tt ∧ tableToC tt = t :=
  getElem?_map_some (hR.tables ▸ h)

theorem mems_get (hR : Rel C D) {x : Nat} {m : Silmaril.Wasm.MemoryType}
    (h : D.mems[x]? = some m) : ∃ mt, C.mems[x]? = some mt ∧ mt.toCore = m :=
  getElem?_map_some (hR.mems ▸ h)

theorem elems_get (hR : Rel C D) {x : Nat} {r : Silmaril.Wasm.Validation.CRefType}
    (h : D.elems[x]? = some r) : ∃ rt, C.elems[x]? = some rt ∧ rt.toC = r :=
  getElem?_map_some (hR.elems ▸ h)

theorem labels_get (hR : Rel C D) {x : Nat} {ts : List KVal}
    (h : D.labels[x]? = some ts) : ∃ us, C.labels[x]? = some us ∧ resultToC us = ts :=
  getElem?_map_some (hR.labels ▸ h)

theorem datas_get (hR : Rel C D) {x : Nat} (h : D.datas[x]? = some ()) : C.datas[x]? = some () :=
  hR.datas ▸ h

theorem locals_get (hR : Rel C D) {x : Nat} {lt : Silmaril.Wasm.Validation.LocalType}
    (h : D.locals[x]? = some lt) :
    ∃ t, C.locals[x]? = some t ∧ Silmaril.Wasm.V2.ValType.toC t = lt.type := by
  have e := hR.locals x
  rw [h] at e
  obtain ⟨t, ht, he⟩ := Option.map_eq_some_iff.mp e.symm
  exact ⟨t, ht, he⟩

theorem return_get (hR : Rel C D) {ts : List KVal} (h : D.return_ = some ts) :
    ∃ us, C.return_ = some us ∧ resultToC us = ts := by
  rw [hR.return_] at h
  exact Option.map_eq_some_iff.mp h

theorem refs_mem (hR : Rel C D) {x : Silmaril.Wasm.FuncIdx} (h : x.toNat ∈ D.refs) :
    x ∈ C.refs := by
  rw [hR.refs] at h
  obtain ⟨y, hy, e⟩ := List.mem_map.mp h
  have hyx : y = x := by
    cases x; cases y
    simp only [Silmaril.Wasm.Idx.toNat] at e
    exact congrArg _ (Fin.ext e)
  exact hyx ▸ hy

/-- `Rel` survives the local initialisation of `Instrs_ok/seq`. -/
theorem initLocals (hR : Rel C D) (xs : List Nat) : Rel C (D.initLocals xs) :=
  { hR with
    types := by obtain ⟨L, hL, -⟩ := D.initLocals_spec xs; rw [hL]; exact hR.types
    recs := by
      have e := Silmaril.Wasm.Validation.Context.initLocals_toTypeCtx D xs
      rw [← hR.recs]; exact congrArg Silmaril.Wasm.Validation.TypeCtx.recs e
    tags := by obtain ⟨L, hL, -⟩ := D.initLocals_spec xs; rw [hL]; exact hR.tags
    funcs := by obtain ⟨L, hL, -⟩ := D.initLocals_spec xs; rw [hL]; exact hR.funcs
    globals := by obtain ⟨L, hL, -⟩ := D.initLocals_spec xs; rw [hL]; exact hR.globals
    tables := by obtain ⟨L, hL, -⟩ := D.initLocals_spec xs; rw [hL]; exact hR.tables
    mems := by obtain ⟨L, hL, -⟩ := D.initLocals_spec xs; rw [hL]; exact hR.mems
    elems := by obtain ⟨L, hL, -⟩ := D.initLocals_spec xs; rw [hL]; exact hR.elems
    datas := by obtain ⟨L, hL, -⟩ := D.initLocals_spec xs; rw [hL]; exact hR.datas
    locals := fun y => by
      rw [Silmaril.Wasm.Validation.Context.initLocals_locals, ← hR.locals y]
      split <;> cases D.locals[y]? <;> rfl
    labels := by rw [Silmaril.Wasm.Validation.Context.initLocals_labels]; exact hR.labels
    return_ := by rw [Silmaril.Wasm.Validation.Context.initLocals_return]; exact hR.return_
    refs := by obtain ⟨L, hL, -⟩ := D.initLocals_spec xs; rw [hL]; exact hR.refs }

/-- `Rel` survives entering a block. -/
theorem withLabel (hR : Rel C D) (ts : List VVal) :
    Rel (C.withLabel ts) (D.withLabel (resultToC ts)) :=
  { hR with
    labels := by
      simp [Silmaril.Wasm.V2.Validation.Context.withLabel,
        Silmaril.Wasm.Validation.Context.withLabel, hR.labels] }

/-- The type context of an image context is well formed. -/
theorem typesOk (hR : Rel C D) : D.toTypeCtx.Ok := by
  intro d hd
  have hd' : d ∈ C.types.map Silmaril.Wasm.V2.FuncType.toDefType := hR.types ▸ hd
  obtain ⟨ft, -, rfl⟩ := List.mem_map.mp hd'
  exact ⟨Silmaril.Wasm.V2.FuncType.toDefType_closed ft,
    Silmaril.Wasm.V2.Validation.tyOk_toDefType _ ft⟩

theorem recs_nil (hR : Rel C D) : D.toTypeCtx.recs = [] := hR.recs

/-- **An image context is well formed.** -/
theorem wf (hR : Rel C D) : D.Wf where
  types := hR.typesOk
  tags := fun d hd => by rw [hR.tags] at hd; cases hd
  globals := fun g hg => by
    rw [hR.globals] at hg
    obtain ⟨gt, -, rfl⟩ := List.mem_map.mp hg
    exact Silmaril.Wasm.V2.Validation.tyOk_toC _ _
  tables := fun t ht => by
    rw [hR.tables] at ht
    obtain ⟨tt, -, rfl⟩ := List.mem_map.mp ht
    exact Silmaril.Wasm.V2.Validation.tyOk_toC_ref _ _
  funcs := fun d hd => by
    rw [hR.funcs] at hd
    obtain ⟨ft, -, rfl⟩ := List.mem_map.mp hd
    exact Silmaril.Wasm.V2.Validation.tyOk_toDefType _ ft
  locals := fun lt hlt => by
    obtain ⟨y, hy⟩ := List.mem_iff_getElem?.mp hlt
    obtain ⟨t, -, ht⟩ := hR.locals_get hy
    exact ht ▸ Silmaril.Wasm.V2.Validation.tyOk_toC _ t
  labels := fun ts hts => by
    rw [hR.labels] at hts
    obtain ⟨us, -, rfl⟩ := List.mem_map.mp hts
    exact Silmaril.Wasm.V2.Validation.resultOk_toC _ us
  return_ := fun ts hts => by
    obtain ⟨us, -, rfl⟩ := hR.return_get hts
    exact Silmaril.Wasm.V2.Validation.resultOk_toC _ us
  elems := fun r hr => by
    rw [hR.elems] at hr
    obtain ⟨rt, -, rfl⟩ := List.mem_map.mp hr
    exact Silmaril.Wasm.V2.Validation.tyOk_toC_ref _ _

end Rel

/-! ## Function types -/

/-- The expansion of the defined type of a 2.0 function type. -/
theorem expand_toDefType_inv {ft : Silmaril.Wasm.V2.FuncType}
    {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    (h : Silmaril.Wasm.Validation.Expand ft.toDefType (.func ps rs)) :
    ps.toList = ft.params.map Silmaril.Wasm.V2.ValType.toC ∧
      rs.toList = ft.results.map Silmaril.Wasm.V2.ValType.toC := by
  have e := (Silmaril.Wasm.Validation.Expand.iff.mp h).symm.trans
    (Silmaril.Wasm.V2.FuncType.toDefType_expand ft)
  simp only [Option.some.injEq, Silmaril.Wasm.Validation.Ty.func.injEq] at e
  rw [e.1, e.2]
  simp

/-- A defined 2.0 function type is in the function hierarchy. -/
theorem defKind_toDefType (ft : Silmaril.Wasm.V2.FuncType) :
    defKind ft.toDefType = some .func := by
  have e := Silmaril.Wasm.V2.FuncType.toDefType_expand ft
  simp only [Silmaril.Wasm.Validation.DefType.expand?, Option.map_eq_some_iff] at e
  obtain ⟨st, hst, hb⟩ := e
  simp [defKind, hst, hb, compAbs]

/-- `er` of the reference that `ref.func` pushes. -/
@[simp] theorem er_defHeap (Δ : TypeCtx) (n : Bool) (ft : Silmaril.Wasm.V2.FuncType) :
    er Δ (.refv (.ref n (.defHeap ft.toDefType))) = .val .funcref := by
  rw [er_refv, Silmaril.Wasm.Validation.Ty.defHeap, erHeap_use]
  simp [TypeCtx.resolve, defKind_toDefType]

end Silmaril.Proofs.Wasm.Models.V2Core.Reflect
