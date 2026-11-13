module

public import Silmaril.Wasm.Models.FXRename.Thms

/-!
# Exception renaming: stores, lookups, updates and reference typing

For `ExnRen n s t` (the store `t` is `s` with exception addresses from `n` on moved up by one
and one unreferenced exception at `n`):

* the frame and module views: `rnFrame` keeps the module, renames the locals, and commutes with
  `local?`/`setLocal`;
* lookups: `global?`, `table?`, `elem?`, `mem?`, `data?`, `tag?`, functions, structures,
  arrays and exceptions of `t` are the renamed lookups of `s` (`exns_rn`: the exception at
  `rnIdx n a` of `t` is the renamed exception at `a` of `s`, also when there is none);
* updates: `setGlobal`, `setTable`, `setElem`, `setMem`, `setData`, `setStructField`,
  `setArrayField`, `addStruct`, `addArray` and `addExn` with renamed contents keep `ExnRen n`;
  `addExn` allocates at `rnIdx n s.exns.length` in `t`;
* `refOk_rn`: reference typing is invariant under the renaming;
* code: the renaming on the shapes that the reduction rules mention.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXRenameSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FXRename
open Silmaril.Proofs.Wasm.Models.FXRename (rnIdx_injective rnIdx_ne rnAdmins_append rnAdmin_toAdmin
  rnAdmins_vals rnAdmins_expression)

variable {H : Type} {n : Nat} {s t : Store H}

/-! ## Renamed store components -/

/-- A renamed global. -/
def rnGlobal (n : Nat) (g : GlobalInst) : GlobalInst := { g with value := rnVal n g.value }

/-- A renamed table. -/
def rnTable (n : Nat) (ti : TableInst) : TableInst := { ti with refs := ti.refs.map (rnRef n) }

/-- A renamed element segment. -/
def rnElem (n : Nat) (ei : ElemInst) : ElemInst := { ei with refs := ei.refs.map (rnRef n) }

/-- A renamed structure. -/
def rnStruct (n : Nat) (si : StructInst) : StructInst :=
  { si with fields := si.fields.map (rnField n) }

/-- A renamed array. -/
def rnArray (n : Nat) (ai : ArrayInst) : ArrayInst :=
  { ai with fields := ai.fields.map (rnField n) }

/-! ## Code -/

@[simp] theorem rnAdmin_plain (i : Instr) : rnAdmin n (.plain i) = .plain i := rfl
@[simp] theorem rnAdmin_trap : rnAdmin n .trap = .trap := rfl
@[simp] theorem rnAdmin_ref (r : Ref) : rnAdmin n (.ref r) = .ref (rnRef n r) := rfl
@[simp] theorem rnAdmin_callRefType (d : DefType) :
    rnAdmin n (.callRefType d) = .callRefType d := rfl
@[simp] theorem rnAdmin_returnCallRefType (d : DefType) :
    rnAdmin n (.returnCallRefType d) = .returnCallRefType d := rfl
@[simp] theorem rnAdmin_label (k : Nat) (cont : List Instr) (body : List Admin) :
    rnAdmin n (.label k cont body) = .label k cont (rnAdmins n body) := rfl
@[simp] theorem rnAdmin_handler (k : Nat) (cs : List Catch) (body : List Admin) :
    rnAdmin n (.handler k cs body) = .handler k cs (rnAdmins n body) := rfl
@[simp] theorem rnAdmin_frame (k : Nat) (f : Frame) (body : List Admin) :
    rnAdmin n (.frame k f body) = .frame k (rnFrame n f) (rnAdmins n body) := rfl
@[simp] theorem rnAdmins_nil : rnAdmins n [] = [] := rfl
@[simp] theorem rnAdmins_cons (a : Admin) (l : List Admin) :
    rnAdmins n (a :: l) = rnAdmin n a :: rnAdmins n l := rfl
@[simp] theorem rnAdmin_constI32 (c : BitVec 32) : rnAdmin n (constI32 c) = constI32 c := rfl
@[simp] theorem rnAdmin_toAdmin' (v : Val) : rnAdmin n v.toAdmin = (rnVal n v).toAdmin :=
  rnAdmin_toAdmin n v
@[simp] theorem rnAdmins_append' (l l' : List Admin) :
    rnAdmins n (l ++ l') = rnAdmins n l ++ rnAdmins n l' := rnAdmins_append n l l'
@[simp] theorem rnAdmins_vals' (vs : List Val) :
    rnAdmins n (vals vs) = vals (vs.map (rnVal n)) := rnAdmins_vals n vs
@[simp] theorem rnAdmins_expression' (es : List Instr) :
    rnAdmins n (expression es) = expression es := rnAdmins_expression n es
@[simp] theorem rnRef_null : rnRef n .null = .null := rfl
@[simp] theorem rnRef_func (a : Nat) : rnRef n (.func a) = .func a := rfl
@[simp] theorem rnRef_struct (a : Nat) : rnRef n (.struct a) = .struct a := rfl
@[simp] theorem rnRef_array (a : Nat) : rnRef n (.array a) = .array a := rfl
@[simp] theorem rnRef_i31 (b : BitVec 31) : rnRef n (.i31 b) = .i31 b := rfl
@[simp] theorem rnRef_exn (a : Nat) : rnRef n (.exn a) = .exn (rnIdx n a) := rfl
@[simp] theorem rnRef_extern (r : Ref) : rnRef n (.extern r) = .extern (rnRef n r) := rfl
@[simp] theorem rnVal_ref (r : Ref) : rnVal n (.ref r) = .ref (rnRef n r) := rfl

theorem rnRef_injective (n : Nat) : Function.Injective (rnRef n) := by
  intro r₁ r₂ h
  induction r₁ generalizing r₂ with
  | exn a => cases r₂ <;> simp_all [rnRef, rnIdx_injective n |>.eq_iff]
  | extern r ih =>
    cases r₂ with
    | extern r₂ => simp only [rnRef, Ref.extern.injEq] at h ⊢; exact ih h
    | _ => simp [rnRef] at h
  | _ => cases r₂ <;> simp_all [rnRef]

theorem rnRef_eq_null {r : Ref} : rnRef n r = .null ↔ r = .null := by
  cases r <;> simp [rnRef]

theorem rnVal_injective (n : Nat) : Function.Injective (rnVal n) := by
  intro v₁ v₂ h
  cases v₁ <;> cases v₂ <;> simp_all [rnVal, (rnRef_injective n).eq_iff]

/-- The renaming on the code of a result. -/
theorem rnAdmins_result (r : Result) : rnAdmins n r.toAdmin = (rnResult n r).toAdmin := by
  cases r <;> simp [Result.toAdmin, rnResult]

theorem rnResult_toBehaviour (r : Result) :
    (rnResult n r).toBehaviour = rnBeh n r.toBehaviour := by
  cases r <;> rfl

/-! ## Frames -/

@[simp] theorem rnFrame_module (f : Frame) : (rnFrame n f).module = f.module := rfl

theorem rnFrame_local? (f : Frame) (x : LocalIdx) :
    (rnFrame n f).local? x = (f.local? x).map (Option.map (rnVal n)) := by
  simp [rnFrame, Frame.local?]

theorem rnFrame_setLocal (f : Frame) (x : LocalIdx) (v : Val) :
    rnFrame n (f.setLocal x v) = (rnFrame n f).setLocal x (rnVal n v) := by
  simp [rnFrame, Frame.setLocal, List.map_set]

theorem rnFrame_locals_length (f : Frame) : (rnFrame n f).locals.length = f.locals.length := by
  simp [rnFrame]

@[simp] theorem rnFrame_type? (f : Frame) (x : TypeIdx) : (rnFrame n f).type? x = f.type? x :=
  rfl

theorem rnVal_default (ct : CValType) : (defaultVal? ct).map (rnVal n) = defaultVal? ct := by
  unfold defaultVal?; split <;> rfl

theorem rnFrame_forCall (m : ModuleInst) (vs : List Val) (ls : List ValType) :
    rnFrame n (Frame.forCall m vs ls) = Frame.forCall m (vs.map (rnVal n)) ls := by
  simp only [rnFrame, Frame.forCall, List.map_append, List.map_map]
  congr 2
  exact List.map_congr_left fun l _ => rnVal_default _

theorem map_modify {α β : Type} (F : α → α) (F' : β → β) (G : α → β)
    (hc : ∀ x, G (F x) = F' (G x)) :
    ∀ (l : List α) (i : Nat), (l.modify i F).map G = (l.map G).modify i F'
  | [], _ => by simp
  | a :: l, 0 => by simp [hc]
  | a :: l, i + 1 => by simp [map_modify F F' G hc l i]

/-! ## Lookups -/

section Lookups

variable (h : ExnRen n s t) {f : Frame}
include h

theorem global_rn {x : GlobalIdx} {a : Nat} {g : GlobalInst} (hl : s.global? f x = some (a, g)) :
    t.global? (rnFrame n f) x = some (a, rnGlobal n g) := by
  simp only [Store.global?, rnFrame_module, h.globals] at hl ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.getElem?_map, Option.map_eq_some_iff] at hl ⊢
  obtain ⟨a', ha, g', hg, he⟩ := hl
  cases he
  exact ⟨a, ha, rnGlobal n g, ⟨g, hg, rfl⟩, rfl⟩

theorem table_rn {x : TableIdx} {a : Nat} {ti : TableInst} (hl : s.table? f x = some (a, ti)) :
    t.table? (rnFrame n f) x = some (a, rnTable n ti) := by
  simp only [Store.table?, rnFrame_module, h.tables] at hl ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.getElem?_map, Option.map_eq_some_iff] at hl ⊢
  obtain ⟨a', ha, g', hg, he⟩ := hl
  cases he
  exact ⟨a, ha, rnTable n ti, ⟨ti, hg, rfl⟩, rfl⟩

theorem elem_rn {x : ElemIdx} {a : Nat} {ei : ElemInst} (hl : s.elem? f x = some (a, ei)) :
    t.elem? (rnFrame n f) x = some (a, rnElem n ei) := by
  simp only [Store.elem?, rnFrame_module, h.elems] at hl ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.getElem?_map, Option.map_eq_some_iff] at hl ⊢
  obtain ⟨a', ha, g', hg, he⟩ := hl
  cases he
  exact ⟨a, ha, rnElem n ei, ⟨ei, hg, rfl⟩, rfl⟩

theorem mem_rn {x : MemIdx} {a : Nat} {mi : MemInst} (hl : s.mem? f x = some (a, mi)) :
    t.mem? (rnFrame n f) x = some (a, mi) := by
  simpa only [Store.mem?, rnFrame_module, h.mems] using hl

theorem data_rn {x : DataIdx} {a : Nat} {di : DataInst} (hl : s.data? f x = some (a, di)) :
    t.data? (rnFrame n f) x = some (a, di) := by
  simpa only [Store.data?, rnFrame_module, h.datas] using hl

theorem tag_rn {x : TagIdx} {a : Nat} {ti : TagInst} (hl : s.tag? f x = some (a, ti)) :
    t.tag? (rnFrame n f) x = some (a, ti) := by
  simpa only [Store.tag?, rnFrame_module, h.tags] using hl

theorem funcs_rn {a : Nat} {fi : FuncInst H} (hl : s.funcs[a]? = some fi) :
    t.funcs[a]? = some fi := by
  rw [h.funcs]; exact hl

theorem structs_rn {a : Nat} {si : StructInst} (hl : s.structs[a]? = some si) :
    t.structs[a]? = some (rnStruct n si) := by
  rw [h.structs, List.getElem?_map, hl]; rfl

theorem arrays_rn {a : Nat} {ai : ArrayInst} (hl : s.arrays[a]? = some ai) :
    t.arrays[a]? = some (rnArray n ai) := by
  rw [h.arrays, List.getElem?_map, hl]; rfl

/-- **Exceptions**: the exception at `rnIdx n a` of `t` is the renamed exception at `a`. -/
theorem exns_rn (a : Nat) : t.exns[rnIdx n a]? = (s.exns[a]?).map (rnExn n) := by
  obtain ⟨junk, hj⟩ := h.exns
  have hle := h.le
  rw [hj]
  unfold rnIdx
  split
  · rename_i ha
    have hl : ((s.exns.take n).map (rnExn n)).length = n := by
      simp; omega
    rw [List.getElem?_append_left (by omega), List.getElem?_map, List.getElem?_take_of_lt ha]
  · rename_i ha
    have hl : ((s.exns.take n).map (rnExn n)).length = n := by
      simp; omega
    rw [List.getElem?_append_right (by omega), hl, show a + 1 - n = (a - n) + 1 by omega,
      List.getElem?_cons_succ, List.getElem?_map, List.getElem?_drop,
      show n + (a - n) = a by omega]

theorem exns_length : t.exns.length = s.exns.length + 1 := by
  obtain ⟨junk, hj⟩ := h.exns
  have hle := h.le
  rw [hj]
  simp; omega

theorem exns_length_rn : t.exns.length = rnIdx n s.exns.length := by
  rw [exns_length h]
  unfold rnIdx
  have := h.le
  split <;> omega

/-- **Reference typing is invariant.** -/
theorem refOk_rn {r : Ref} {rt : CRefType} (hr : RefOk s r rt) : RefOk t (rnRef n r) rt := by
  induction hr with
  | null => exact .null
  | i31 b => exact .i31 b
  | @struct a si hs => exact RefOk.struct (si := rnStruct n si) (structs_rn h hs)
  | @array a ai ha => exact RefOk.array (ai := rnArray n ai) (arrays_rn h ha)
  | func hf => exact .func (funcs_rn h hf)
  | @exn a e he =>
    exact RefOk.exn (a := rnIdx n a) (e := rnExn n e) (by rw [exns_rn h, he]; rfl)
  | host a => exact .host a
  | extern _ hn ih => exact .extern ih (by rwa [Ne, rnRef_eq_null])
  | sub _ hok hs ih => exact .sub ih hok hs

theorem refOk_back_struct {r : Ref} {a : Nat} {si : StructInst} (hq : rnRef n r = .struct a)
    (hs : t.structs[a]? = some si) : RefOk s r (.ref false (.defHeap si.type)) := by
  cases r <;> simp [rnRef] at hq
  subst hq
  rw [h.structs, List.getElem?_map, Option.map_eq_some_iff] at hs
  obtain ⟨si', hsi, rfl⟩ := hs
  exact RefOk.struct (si := si') hsi

theorem refOk_back_array {r : Ref} {a : Nat} {ai : ArrayInst} (hq : rnRef n r = .array a)
    (ha : t.arrays[a]? = some ai) : RefOk s r (.ref false (.defHeap ai.type)) := by
  cases r <;> simp [rnRef] at hq
  subst hq
  rw [h.arrays, List.getElem?_map, Option.map_eq_some_iff] at ha
  obtain ⟨ai', hai, rfl⟩ := ha
  exact RefOk.array (ai := ai') hai

theorem refOk_back_func {r : Ref} {a : Nat} {fi : FuncInst H} (hq : rnRef n r = .func a)
    (hf : t.funcs[a]? = some fi) : RefOk s r (.ref false (.defHeap fi.type)) := by
  cases r <;> simp [rnRef] at hq
  subst hq
  rw [h.funcs] at hf
  exact .func hf

theorem refOk_back_exn {r : Ref} {a : Nat} {e : ExnInst} (hq : rnRef n r = .exn a)
    (he : t.exns[a]? = some e) : RefOk s r (.ref false (.abs .exn)) := by
  cases r <;> simp [rnRef] at hq
  subst hq
  rw [exns_rn h, Option.map_eq_some_iff] at he
  obtain ⟨e', he', _⟩ := he
  exact .exn he'

omit h in
theorem refOk_back_simple {r q : Ref} (hq : rnRef n r = q)
    (hs : ∀ a, q ≠ .exn a) (he : ∀ r', q ≠ .extern r') : r = q := by
  cases r <;> cases q <;> simp_all [rnRef]

omit h in
theorem refOk_back_extern {r r' : Ref} (hq : rnRef n r = .extern r') :
    ∃ r₀, r = .extern r₀ ∧ rnRef n r₀ = r' := by
  cases r <;> simp_all [rnRef]

theorem refOk_rn_back {r : Ref} {rt : CRefType} (hr : RefOk t (rnRef n r) rt) : RefOk s r rt := by
  generalize hq : rnRef n r = q at hr
  induction hr generalizing r with
  | null => exact (refOk_back_simple hq (by simp) (by simp)) ▸ .null
  | i31 b => exact (refOk_back_simple hq (by simp) (by simp)) ▸ .i31 b
  | struct hs => exact refOk_back_struct h hq hs
  | array ha => exact refOk_back_array h hq ha
  | func hf => exact refOk_back_func h hq hf
  | exn he => exact refOk_back_exn h hq he
  | host a => exact (refOk_back_simple hq (by simp) (by simp)) ▸ .host a
  | extern _ hn ih =>
    obtain ⟨r₀, hr₀, hq₀⟩ := refOk_back_extern hq
    exact hr₀ ▸ .extern (ih hq₀) (fun h₀ => hn (by rw [← hq₀, h₀]; rfl))
  | sub _ hok hs ih => exact .sub (ih hq) hok hs

theorem refOk_iff {r : Ref} {rt : CRefType} : RefOk t (rnRef n r) rt ↔ RefOk s r rt :=
  ⟨refOk_rn_back h, refOk_rn h⟩

end Lookups

/-! ## Updates -/

section Updates

variable (h : ExnRen n s t)
include h

theorem setGlobal_rn (a : Nat) (v : Val) :
    ExnRen n (s.setGlobal a v) (t.setGlobal a (rnVal n v)) := by
  refine { h with globals := ?_ }
  simp only [Store.setGlobal, h.globals]
  symm; apply map_modify; intro; rfl

theorem setTable_rn (a : Nat) (ti : TableInst) :
    ExnRen n (s.setTable a ti) (t.setTable a (rnTable n ti)) :=
  { h with tables := by simp only [Store.setTable, h.tables, List.map_set]; rfl }

theorem setElem_rn (a : Nat) (refs : List Ref) :
    ExnRen n (s.setElem a refs) (t.setElem a (refs.map (rnRef n))) := by
  refine { h with elems := ?_ }
  simp only [Store.setElem, h.elems]
  symm; apply map_modify; intro; rfl

theorem setMem_rn (a : Nat) (mi : MemInst) : ExnRen n (s.setMem a mi) (t.setMem a mi) :=
  { h with mems := by simp only [Store.setMem, h.mems] }

theorem setData_rn (a : Nat) (b : ByteArray) : ExnRen n (s.setData a b) (t.setData a b) :=
  { h with datas := by simp only [Store.setData, h.datas] }

theorem setStructField_rn (a i : Nat) (fv : FieldVal) :
    ExnRen n (s.setStructField a i fv) (t.setStructField a i (rnField n fv)) := by
  refine { h with structs := ?_ }
  simp only [Store.setStructField, h.structs]
  symm; apply map_modify; intro; simp [List.map_set]

theorem setArrayField_rn (a i : Nat) (fv : FieldVal) :
    ExnRen n (s.setArrayField a i fv) (t.setArrayField a i (rnField n fv)) := by
  refine { h with arrays := ?_ }
  simp only [Store.setArrayField, h.arrays]
  symm; apply map_modify; intro; simp [List.map_set]

theorem addStruct_rn (si : StructInst) :
    ExnRen n (s.addStruct si) (t.addStruct (rnStruct n si)) :=
  { h with structs := by simp only [Store.addStruct, h.structs, List.map_append]; rfl }

theorem addArray_rn (ai : ArrayInst) :
    ExnRen n (s.addArray ai) (t.addArray (rnArray n ai)) :=
  { h with arrays := by simp only [Store.addArray, h.arrays, List.map_append]; rfl }

theorem addExn_rn (e : ExnInst) : ExnRen n (s.addExn e) (t.addExn (rnExn n e)) := by
  obtain ⟨junk, hj⟩ := h.exns
  have hle := h.le
  refine { h with le := ?_, exns := ⟨junk, ?_⟩ }
  · simp [Store.addExn]; omega
  · simp only [Store.addExn, hj, List.take_append_of_le_length hle,
      List.drop_append_of_le_length hle, List.map_append, List.append_assoc, List.cons_append]
    rfl

end Updates

end Silmaril.Proofs.Wasm.Models.FXRenameSim
