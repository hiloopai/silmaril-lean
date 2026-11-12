module

public import Silmaril.Proofs.Wasm.Component.Reference.CoreShift
public import Silmaril.Wasm.Game.Linking.Thms

/-!
# Relocated Core steps

`Linked2.toRef` instantiates the importer's core module in the core store that already holds
the exporter (`reloc s₀ t`, `CoreShift`), while the IR runs it alone in `t`. This file shows that
host-free Core 3.0 steps commute with the relocation: `step_shift` (every profile): a host-free
step `c ⟶ c'` of a thread whose frames have module instances without tags, memories, tables,
element or data segments and whose code holds no exception or host references (`Own.FrameGood`,
`Own.CodeGood` of `Silmaril.Wasm.Game.Linking`'s store split, for any ownership) is matched by one
host-free step of the relocated configuration `shC s₀ c ⟶ shC s₀ c'` (store `reloc s₀`, frame and
code shifted by `sh s₀`). Goodness is preserved along such steps by `Linking.Split.step_sim`.

* `Shift.code`: the shift of administrative code (references and frames);
* `reloc` lookups (`funcs_reloc`, `structs_reloc`, `arrays_reloc`), updates (`reloc_setGlobal`,
  `reloc_setStructField`, `reloc_setArrayField`) and run-time type checks (`refOk_reloc_iff`,
  for every reference);
* the families: `ParametricStep.shift`, `NumericStep.shift_eq`, `VectorStep.shift_eq`,
  `VariableStep.shift`, `RefStep.shift`, `AggregateStep.shift`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own noHost elem?_none data?_none TableStep.not_good
  MemoryStep.not_good)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

namespace Shift

variable (δ : Shift)

/-- Shift administrative code: its references and frames. -/
def code : List Admin → List Admin
  | [] => []
  | .ref r :: l => .ref (δ.ref r) :: code l
  | .label n c b :: l => .label n c (code b) :: code l
  | .handler n cs b :: l => .handler n cs (code b) :: code l
  | .frame n f b :: l => .frame n (δ.frame f) (code b) :: code l
  | a :: l => a :: code l

@[simp] theorem code_nil : δ.code [] = [] := by simp [code]
@[simp] theorem code_plain (i : Instr) (l : List Admin) :
    δ.code (.plain i :: l) = .plain i :: δ.code l := by simp [code]
@[simp] theorem code_ref (r : Ref) (l : List Admin) :
    δ.code (.ref r :: l) = .ref (δ.ref r) :: δ.code l := by simp [code]
@[simp] theorem code_callRefType (d : DefType) (l : List Admin) :
    δ.code (.callRefType d :: l) = .callRefType d :: δ.code l := by simp [code]
@[simp] theorem code_returnCallRefType (d : DefType) (l : List Admin) :
    δ.code (.returnCallRefType d :: l) = .returnCallRefType d :: δ.code l := by simp [code]
@[simp] theorem code_trap (l : List Admin) : δ.code (.trap :: l) = .trap :: δ.code l := by
  simp [code]
@[simp] theorem code_label (n : Nat) (c : List Instr) (b l : List Admin) :
    δ.code (.label n c b :: l) = .label n c (δ.code b) :: δ.code l := by simp [code]
@[simp] theorem code_handler (n : Nat) (cs : List Catch) (b l : List Admin) :
    δ.code (.handler n cs b :: l) = .handler n cs (δ.code b) :: δ.code l := by simp [code]
@[simp] theorem code_frame (n : Nat) (f : Frame) (b l : List Admin) :
    δ.code (.frame n f b :: l) = .frame n (δ.frame f) (δ.code b) :: δ.code l := by simp [code]

@[simp] theorem code_append (l₁ l₂ : List Admin) :
    δ.code (l₁ ++ l₂) = δ.code l₁ ++ δ.code l₂ := by
  induction l₁ with
  | nil => simp
  | cons a as ih => cases a <;> simp [ih]

@[simp] theorem code_cons_toAdmin (v : Val) (l : List Admin) :
    δ.code (v.toAdmin :: l) = (δ.val v).toAdmin :: δ.code l := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, val]

@[simp] theorem code_vals (vs : List Val) : δ.code (vals vs) = vals (vs.map δ.val) := by
  induction vs with
  | nil => simp [vals]
  | cons v vs ih => simpa [vals] using ih

@[simp] theorem code_expression (es : List Instr) : δ.code (expression es) = expression es := by
  induction es with
  | nil => simp [expression]
  | cons i es ih => simpa [expression] using ih

@[simp] theorem code_map_ref (l : List Ref) :
    δ.code (l.map Admin.ref) = (l.map δ.ref).map Admin.ref := by
  induction l with
  | nil => simp
  | cons r l ih => simp [ih]

@[simp] theorem code_constI32 (b : BitVec 32) (l : List Admin) :
    δ.code (constI32 b :: l) = constI32 b :: δ.code l := by
  simp [constI32, Val.i32, Val.toAdmin]

@[simp] theorem val_i32 (b : BitVec 32) : δ.val (Val.i32 b) = Val.i32 b := rfl
@[simp] theorem ref_exn (a : Nat) : δ.ref (.exn a) = .exn (δ.ex + a) := rfl
@[simp] theorem ref_host (a : Nat) : δ.ref (.host a) = .host a := rfl
@[simp] theorem fval_val (v : Val) : δ.fval (.val v) = .val (δ.val v) := rfl
@[simp] theorem fval_pack (p : PackType) (b : BitVec p.width) :
    δ.fval (.pack p b) = .pack p b := rfl
@[simp] theorem frame_locals (f : Frame) :
    (δ.frame f).locals = f.locals.map (Option.map δ.val) := rfl

theorem code_eq_nil_iff {l : List Admin} : δ.code l = [] ↔ l = [] := by
  cases l with
  | nil => simp
  | cons a l => cases a <;> simp

theorem code_callRef {c : Admin} (hc : c.IsCallRef) (l : List Admin) :
    δ.code (c :: l) = c :: δ.code l := by
  cases c <;> simp_all [Admin.IsCallRef]

theorem code_returnCallRef {c : Admin} (hc : c.IsReturnCallRef) (l : List Admin) :
    δ.code (c :: l) = c :: δ.code l := by
  cases c <;> simp_all [Admin.IsReturnCallRef]

theorem code_retToCallIn {c : Admin} (hc : c.IsReturnCallRef) (m : ModuleInst)
    (l : List Admin) : δ.code (c.retToCallIn m :: l) = c.retToCallIn m :: δ.code l := by
  rcases c with ⟨_⟩ | _ | _ | _ | _ | _ | _ | _ <;>
    simp_all [Admin.IsReturnCallRef, Admin.retToCallIn]
  rename_i i
  cases i <;> simp_all
  split <;> simp

theorem retToCallIn_minst (c : Admin) (m : ModuleInst) :
    c.retToCallIn (δ.minst m) = c.retToCallIn m := by
  rcases c with ⟨_⟩ | _ | _ | _ | _ | _ | _ | _ <;> simp [Admin.retToCallIn]

theorem frame_forCall (m : ModuleInst) (vs : List Val) (ls : List ValType) :
    δ.frame (Frame.forCall m vs ls) = Frame.forCall (δ.minst m) (vs.map δ.val) ls := by
  simp only [frame, Frame.forCall, List.map_append, List.map_map, Frame.mk.injEq, and_true,
    minst_types]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply]
  cases h : defaultVal? ((liftVal t).substAll (m.types.map .dt)) with
  | none => rfl
  | some v => simp [val_defaultVal δ h]

@[simp] theorem frame_setLocal (f : Frame) (x : LocalIdx) (v : Val) :
    δ.frame (f.setLocal x v) = (δ.frame f).setLocal x (δ.val v) := by
  simp [frame, Frame.setLocal, List.map_set]

theorem unpackField_fval (sx : Option Signedness) (fv : FieldVal) :
    unpackField sx (δ.fval fv) = δ.val (unpackField sx fv) := by
  rcases fv with _ | ⟨_, _⟩ <;> rcases sx with _ | ⟨_ | _⟩ <;> rfl

theorem unpackable_fval (z : CStorageType) (sx : Option Signedness) (fv : FieldVal) :
    unpackable z sx (δ.fval fv) = unpackable z sx fv := by
  rcases fv with _ | ⟨_, _⟩ <;> rcases z with _ | _ <;> rcases sx with _ | _ <;> rfl

theorem ref_injective {r₁ r₂ : Ref} (h : δ.ref r₁ = δ.ref r₂) : r₁ = r₂ := by
  induction r₁ generalizing r₂ with
  | extern r ih => cases r₂ <;> simp [ref] at h ⊢; exact ih h
  | _ => cases r₂ <;> simp_all [ref]

theorem sinst_new (d : DefType) (fs : List CFieldType) (vs : List Val) :
    δ.sinst ⟨d, (fs.zip vs).map fun (ft, v) => packField (fieldStorage ft) v⟩ =
      ⟨d, (fs.zip (vs.map δ.val)).map fun (ft, v) => packField (fieldStorage ft) v⟩ := by
  simp only [sinst, StructInst.mk.injEq, true_and, List.map_map, List.zip_map_right]
  apply List.map_congr_left
  rintro ⟨ft, v⟩ -
  simp [fval_packField]

theorem ainst_new (d : DefType) (z : CStorageType) (vs : List Val) :
    δ.ainst ⟨d, vs.map (packField z)⟩ = ⟨d, (vs.map δ.val).map (packField z)⟩ := by
  simp [ainst, List.map_map, Function.comp_def, fval_packField]

end Shift

/-! ## Lookups and updates in the relocated store -/

theorem map_modify' {α β : Type} (g : α → β) (f : α → α) (f' : β → β)
    (h : ∀ x, g (f x) = f' (g x)) :
    ∀ (l : List α) (n : Nat), (l.modify n f).map g = (l.map g).modify n f'
  | [], n => by simp
  | x :: l, 0 => by simp [h]
  | x :: l, n + 1 => by simp [map_modify' g f f' h l n]

theorem append_modify' {β : Type} (f' : β → β) :
    ∀ (l₀ l : List β) (n : Nat), l₀ ++ l.modify n f' = (l₀ ++ l).modify (l₀.length + n) f'
  | [], l, n => by simp
  | x :: l₀, l, n => by
    rw [List.cons_append, List.cons_append, List.length_cons, Nat.add_right_comm,
      append_modify' f' l₀ l n]
    simp

section Reloc

variable (s₀ : Store H)

/-- A configuration with its store relocated past `s₀`, and its frame and code shifted. -/
def shC (c : Config H) : Config H :=
  ⟨reloc s₀ c.store, (sh s₀).frame c.frame, (sh s₀).code c.code⟩

theorem funcs_reloc (t : Store H) (a : Nat) :
    (reloc s₀ t).funcs[s₀.funcs.length + a]? = (t.funcs[a]?).map (sh s₀).finst := by
  rw [reloc_funcs, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_map]

theorem structs_reloc (t : Store H) (a : Nat) :
    (reloc s₀ t).structs[s₀.structs.length + a]? = (t.structs[a]?).map (sh s₀).sinst := by
  rw [reloc_structs, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_map]

theorem arrays_reloc (t : Store H) (a : Nat) :
    (reloc s₀ t).arrays[s₀.arrays.length + a]? = (t.arrays[a]?).map (sh s₀).ainst := by
  rw [reloc_arrays, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_map]

theorem exns_reloc (t : Store H) (a : Nat) :
    (reloc s₀ t).exns[s₀.exns.length + a]? = (t.exns[a]?).map (sh s₀).xninst := by
  show (s₀.exns ++ t.exns.map (sh s₀).xninst)[s₀.exns.length + a]? = _
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_map]

theorem structs_length_reloc (t : Store H) :
    (reloc s₀ t).structs.length = s₀.structs.length + t.structs.length := by simp

theorem arrays_length_reloc (t : Store H) :
    (reloc s₀ t).arrays.length = s₀.arrays.length + t.arrays.length := by simp

theorem funcs_minst (m : ModuleInst) (x : Nat) :
    ((sh s₀).minst m).funcs[x]? = (m.funcs[x]?).map (s₀.funcs.length + ·) := by
  simp [List.getElem?_map]

theorem reloc_setGlobal (t : Store H) (a : Nat) (v : Val) :
    reloc s₀ (t.setGlobal a v) = (reloc s₀ t).setGlobal (s₀.globals.length + a) ((sh s₀).val v) := by
  simp only [reloc, Store.app, Shift.store, Store.setGlobal, Store.mk.injEq, and_true, true_and]
  rw [map_modify' (sh s₀).ginst (fun g => { g with value := v })
    (fun g => { g with value := (sh s₀).val v }) (fun _ => rfl), append_modify']

theorem reloc_setStructField (t : Store H) (a i : Nat) (fv : FieldVal) :
    reloc s₀ (t.setStructField a i fv) =
      (reloc s₀ t).setStructField (s₀.structs.length + a) i ((sh s₀).fval fv) := by
  simp only [reloc, Store.app, Shift.store, Store.setStructField, Store.mk.injEq, and_true,
    true_and]
  rw [map_modify' _ _ (fun x => { x with fields := x.fields.set i ((sh s₀).fval fv) })
    (fun _ => by simp [Shift.sinst, List.map_set]), append_modify']

theorem reloc_setArrayField (t : Store H) (a i : Nat) (fv : FieldVal) :
    reloc s₀ (t.setArrayField a i fv) =
      (reloc s₀ t).setArrayField (s₀.arrays.length + a) i ((sh s₀).fval fv) := by
  simp only [reloc, Store.app, Shift.store, Store.setArrayField, Store.mk.injEq, and_true,
    true_and]
  rw [map_modify' _ _ (fun x => { x with fields := x.fields.set i ((sh s₀).fval fv) })
    (fun _ => by simp [Shift.ainst, List.map_set]), append_modify']

theorem arrays_reloc_of {t : Store H} {a : Nat} {ai : ArrayInst} (h : t.arrays[a]? = some ai) :
    (reloc s₀ t).arrays[s₀.arrays.length + a]? = some ((sh s₀).ainst ai) := by
  rw [arrays_reloc, h, Option.map_some]

theorem structs_reloc_of {t : Store H} {a : Nat} {si : StructInst} (h : t.structs[a]? = some si) :
    (reloc s₀ t).structs[s₀.structs.length + a]? = some ((sh s₀).sinst si) := by
  rw [structs_reloc, h, Option.map_some]

theorem funcs_reloc_of {t : Store H} {a : Nat} {fi : FuncInst H} (h : t.funcs[a]? = some fi) :
    (reloc s₀ t).funcs[s₀.funcs.length + a]? = some ((sh s₀).finst fi) := by
  rw [funcs_reloc, h, Option.map_some]

theorem exns_reloc_of {t : Store H} {a : Nat} {e : ExnInst} (h : t.exns[a]? = some e) :
    (reloc s₀ t).exns[s₀.exns.length + a]? = some ((sh s₀).xninst e) := by
  rw [exns_reloc, h, Option.map_some]

@[simp] theorem shC_mk (s : Store H) (f : Frame) (l : List Admin) :
    shC s₀ ⟨s, f, l⟩ = ⟨reloc s₀ s, (sh s₀).frame f, (sh s₀).code l⟩ := rfl

/-! ### Run-time type checks -/

theorem refOk_reloc {t : Store H} {r : Ref} {τ : CRefType} (h : RefOk t r τ) :
    RefOk (reloc s₀ t) ((sh s₀).ref r) τ := by
  induction h with
  | null => exact .null
  | i31 b => exact .i31 b
  | @struct a si hs => exact RefOk.struct (si := (sh s₀).sinst si) (structs_reloc_of s₀ hs)
  | @array a ai ha => exact RefOk.array (ai := (sh s₀).ainst ai) (arrays_reloc_of s₀ ha)
  | @func a fi hf => exact RefOk.func (fi := (sh s₀).finst fi) (funcs_reloc_of s₀ hf)
  | @exn a e he => exact RefOk.exn (e := (sh s₀).xninst e) (exns_reloc_of s₀ he)
  | host a => exact .host a
  | extern _ hn ih => exact .extern ih (by rwa [Ne, Shift.ref_eq_null_iff])
  | sub _ hok hs ih => exact .sub ih hok hs

theorem Shift.ref_eq_i31_inv {δ : Shift} {r : Ref} {b : BitVec 31} (h : δ.ref r = .i31 b) :
    r = .i31 b := by
  cases r <;> simp_all [Shift.ref]

theorem Shift.ref_eq_struct_inv {δ : Shift} {r : Ref} {a' : Nat} (h : δ.ref r = .struct a') :
    ∃ a, r = .struct a ∧ δ.st + a = a' := by
  cases r <;> simp_all [Shift.ref]

theorem Shift.ref_eq_array_inv {δ : Shift} {r : Ref} {a' : Nat} (h : δ.ref r = .array a') :
    ∃ a, r = .array a ∧ δ.ar + a = a' := by
  cases r <;> simp_all [Shift.ref]

theorem Shift.ref_eq_func_inv {δ : Shift} {r : Ref} {a' : Nat} (h : δ.ref r = .func a') :
    ∃ a, r = .func a ∧ δ.fn + a = a' := by
  cases r <;> simp_all [Shift.ref]

theorem Shift.ref_eq_exn_inv {δ : Shift} {r : Ref} {a' : Nat} (h : δ.ref r = .exn a') :
    ∃ a, r = .exn a ∧ δ.ex + a = a' := by
  cases r <;> simp_all [Shift.ref]

theorem Shift.ref_eq_host_inv {δ : Shift} {r : Ref} {a : Nat} (h : δ.ref r = .host a) :
    r = .host a := by
  cases r <;> simp_all [Shift.ref]

theorem Shift.ref_eq_extern_inv {δ : Shift} {r r' : Ref} (h : δ.ref r = .extern r') :
    ∃ r₀, r = .extern r₀ ∧ δ.ref r₀ = r' := by
  cases r <;> simp_all [Shift.ref]

theorem refOk_reloc_back {t : Store H} {r' : Ref} {τ : CRefType} (h : RefOk (reloc s₀ t) r' τ) :
    ∀ r, (sh s₀).ref r = r' → RefOk t r τ := by
  induction h with
  | null =>
    intro r hr
    rw [(Shift.ref_eq_null_iff _).mp hr]
    exact .null
  | i31 b =>
    intro r hr
    rw [Shift.ref_eq_i31_inv hr]
    exact .i31 b
  | @struct a' si' hs =>
    intro r hr
    obtain ⟨a, rfl, rfl⟩ : ∃ a, r = .struct a ∧ (sh s₀).st + a = a' := Shift.ref_eq_struct_inv hr
    obtain ⟨si, h1, rfl⟩ : ∃ si, t.structs[a]? = some si ∧ (sh s₀).sinst si = si' :=
      Option.map_eq_some_iff.mp ((structs_reloc s₀ t a).symm.trans hs)
    exact RefOk.struct (si := si) h1
  | @array a' ai' hs =>
    intro r hr
    obtain ⟨a, rfl, rfl⟩ : ∃ a, r = .array a ∧ (sh s₀).ar + a = a' := Shift.ref_eq_array_inv hr
    obtain ⟨ai, h1, rfl⟩ : ∃ ai, t.arrays[a]? = some ai ∧ (sh s₀).ainst ai = ai' :=
      Option.map_eq_some_iff.mp ((arrays_reloc s₀ t a).symm.trans hs)
    exact RefOk.array (ai := ai) h1
  | @func a' fi' hf =>
    intro r hr
    obtain ⟨a, rfl, rfl⟩ : ∃ a, r = .func a ∧ (sh s₀).fn + a = a' := Shift.ref_eq_func_inv hr
    obtain ⟨fi, h1, rfl⟩ : ∃ fi, t.funcs[a]? = some fi ∧ (sh s₀).finst fi = fi' :=
      Option.map_eq_some_iff.mp ((funcs_reloc s₀ t a).symm.trans hf)
    exact RefOk.func (fi := fi) h1
  | @exn a' e' he =>
    intro r hr
    obtain ⟨a, rfl, rfl⟩ : ∃ a, r = .exn a ∧ (sh s₀).ex + a = a' := Shift.ref_eq_exn_inv hr
    obtain ⟨e, h1, -⟩ : ∃ e, t.exns[a]? = some e ∧ (sh s₀).xninst e = e' :=
      Option.map_eq_some_iff.mp ((exns_reloc s₀ t a).symm.trans he)
    exact RefOk.exn h1
  | host a =>
    intro r hr
    rw [Shift.ref_eq_host_inv hr]
    exact .host a
  | @extern r₁ _ hn ih =>
    intro r hr
    obtain ⟨r₀, rfl, rfl⟩ : ∃ r₀, r = .extern r₀ ∧ (sh s₀).ref r₀ = r₁ :=
      Shift.ref_eq_extern_inv hr
    exact .extern (ih r₀ rfl) (fun h0 => hn (by rw [h0]; rfl))
  | sub _ hok hs ih => intro r hr; exact .sub (ih r hr) hok hs

theorem refOk_reloc_iff {t : Store H} {r : Ref} {τ : CRefType} :
    RefOk (reloc s₀ t) ((sh s₀).ref r) τ ↔ RefOk t r τ :=
  ⟨fun h => refOk_reloc_back s₀ h r rfl, refOk_reloc s₀⟩

end Reloc

/-! ## The families -/

section Families

variable (s₀ : Store H)

@[simp] theorem ainst_fields_length (δ : Shift) (ai : ArrayInst) :
    (δ.ainst ai).fields.length = ai.fields.length := by simp [Shift.ainst]

@[simp] theorem sinst_fields_length (δ : Shift) (si : StructInst) :
    (δ.sinst si).fields.length = si.fields.length := by simp [Shift.sinst]

@[simp] theorem finst_type (δ : Shift) (fi : FuncInst H) : (δ.finst fi).type = fi.type := rfl
@[simp] theorem finst_code (δ : Shift) (fi : FuncInst H) : (δ.finst fi).code = fi.code := rfl
@[simp] theorem finst_module (δ : Shift) (fi : FuncInst H) :
    (δ.finst fi).module = δ.minst fi.module := rfl

theorem instRef_minst (δ : Shift) (m : ModuleInst) (rt : RefType) :
    (δ.minst m).instRef rt = m.instRef rt := rfl

theorem blockType?_minst (δ : Shift) (m : ModuleInst) (bt : BlockType) :
    (δ.minst m).blockType? bt = m.blockType? bt := by
  cases bt <;> rfl

theorem ParametricStep.shift {is is' : List Admin} (h : ParametricStep is is') (δ : Shift) :
    ParametricStep (δ.code is) (δ.code is') := by
  cases h with
  | unreachable => simpa using ParametricStep.unreachable
  | nop => simpa using ParametricStep.nop
  | drop v => simpa using ParametricStep.drop (δ.val v)
  | selectTrue hc => simpa using ParametricStep.selectTrue (v₁ := δ.val _) (v₂ := δ.val _) hc
  | selectFalse v₁ v₂ ts => simpa using ParametricStep.selectFalse (δ.val v₁) (δ.val v₂) ts

theorem NumericStep.shift_eq {P : Profile} {is is' : List Admin} (h : NumericStep P is is')
    (δ : Shift) : δ.code is = is ∧ δ.code is' = is' := by
  cases h <;> simp

theorem VectorStep.shift_eq {P : Profile} {is is' : List Admin} (h : VectorStep P is is')
    (δ : Shift) : δ.code is = is ∧ δ.code is' = is' := by
  cases h <;> simp

theorem VariableStep.shift {P : Profile} {c c' : Config H} (h : VariableStep c c') :
    Step P noHost (shC s₀ c) (shC s₀ c') := by
  cases h with
  | @localGet s f x v hl =>
    have hl' : ((sh s₀).frame f).local? x = some (some ((sh s₀).val v)) := by
      have hl₀ : f.locals[x.toNat]? = some (some v) := hl
      simp [Frame.local?, List.getElem?_map, hl₀]
    simpa [shC] using Step.variable (P := P) (host := noHost)
      (VariableStep.localGet (s := reloc s₀ s) hl')
  | @localSet s f x v hx =>
    simpa [shC] using Step.variable (P := P) (host := noHost)
      (VariableStep.localSet (s := reloc s₀ s) (f := (sh s₀).frame f) (v := (sh s₀).val v)
        (x := x) (by simpa using hx))
  | @localTee s f x v =>
    simpa [shC] using Step.variable (P := P) (host := noHost)
      (VariableStep.localTee (s := reloc s₀ s) (f := (sh s₀).frame f) (v := (sh s₀).val v) (x := x))
  | @globalGet s f x a g hg =>
    have hg' : (reloc s₀ s).global? ((sh s₀).frame f) x =
        some ((sh s₀).gl + a, (sh s₀).ginst g) := by rw [global?_reloc, hg]; rfl
    simpa [shC, Shift.ginst] using Step.variable (P := P) (host := noHost)
      (VariableStep.globalGet (s := reloc s₀ s) (f := (sh s₀).frame f) hg')
  | @globalSet s f x a g v hg =>
    have hg' : (reloc s₀ s).global? ((sh s₀).frame f) x =
        some ((sh s₀).gl + a, (sh s₀).ginst g) := by rw [global?_reloc, hg]; rfl
    simpa [shC, reloc_setGlobal] using Step.variable (P := P) (host := noHost)
      (VariableStep.globalSet (s := reloc s₀ s) (f := (sh s₀).frame f) (v := (sh s₀).val v) hg')

theorem RefStep.shift {P : Profile} {c c' : Config H} (h : RefStep c c') :
    Step P noHost (shC s₀ c) (shC s₀ c') := by
  cases h with
  | @refNull s f ht =>
    simpa [shC] using Step.reference (P := P) (host := noHost)
      (RefStep.refNull (s := reloc s₀ s) (f := (sh s₀).frame f) ht)
  | @refFunc s f x a hx =>
    have hx' : ((sh s₀).frame f).module.funcs[x.toNat]? = some (s₀.funcs.length + a) := by
      simp [List.getElem?_map, hx]
    simpa [shC] using Step.reference (P := P) (host := noHost)
      (RefStep.refFunc (s := reloc s₀ s) (f := (sh s₀).frame f) hx')
  | @refI31 s f i =>
    simpa [shC] using Step.reference (P := P) (host := noHost)
      (RefStep.refI31 (s := reloc s₀ s) (f := (sh s₀).frame f) i)
  | @isNullTrue s f =>
    simpa [shC] using Step.reference (P := P) (host := noHost)
      (RefStep.isNullTrue (s := reloc s₀ s) (f := (sh s₀).frame f))
  | @isNullFalse s f r hr =>
    simpa [shC] using Step.reference (P := P) (host := noHost)
      (RefStep.isNullFalse (s := reloc s₀ s) (f := (sh s₀).frame f) (r := (sh s₀).ref r)
        (by rwa [Ne, Shift.ref_eq_null_iff]))
  | @asNonNullNull s f =>
    simpa [shC] using Step.reference (P := P) (host := noHost)
      (RefStep.asNonNullNull (s := reloc s₀ s) (f := (sh s₀).frame f))
  | @asNonNullAddr s f r hr =>
    simpa [shC] using Step.reference (P := P) (host := noHost)
      (RefStep.asNonNullAddr (s := reloc s₀ s) (f := (sh s₀).frame f) (r := (sh s₀).ref r)
        (by rwa [Ne, Shift.ref_eq_null_iff]))
  | @eqNull s f =>
    simpa [shC] using Step.reference (P := P) (host := noHost)
      (RefStep.eqNull (s := reloc s₀ s) (f := (sh s₀).frame f))
  | @eqTrue s f r hr =>
    simpa [shC] using Step.reference (P := P) (host := noHost)
      (RefStep.eqTrue (s := reloc s₀ s) (f := (sh s₀).frame f) (r := (sh s₀).ref r)
        (by rwa [Ne, Shift.ref_eq_null_iff]))
  | @eqFalse s f r₁ r₂ hr =>
    simpa [shC] using Step.reference (P := P) (host := noHost)
      (RefStep.eqFalse (s := reloc s₀ s) (f := (sh s₀).frame f) (r₁ := (sh s₀).ref r₁)
        (r₂ := (sh s₀).ref r₂) (fun e => hr (Shift.ref_injective _ e)))
  | @testTrue s f r rt hr =>
    simpa [shC] using Step.reference (P := P) (host := noHost)
      (RefStep.testTrue (s := reloc s₀ s) (f := (sh s₀).frame f) (r := (sh s₀).ref r) (rt := rt)
        ((refOk_reloc_iff s₀).mpr hr))
  | @testFalse s f r rt hr =>
    simpa [shC] using Step.reference (P := P) (host := noHost)
      (RefStep.testFalse (s := reloc s₀ s) (f := (sh s₀).frame f) (r := (sh s₀).ref r) (rt := rt)
        (fun h' => hr ((refOk_reloc_iff s₀).mp h')))
  | @castSucceed s f r rt hr =>
    simpa [shC] using Step.reference (P := P) (host := noHost)
      (RefStep.castSucceed (s := reloc s₀ s) (f := (sh s₀).frame f) (r := (sh s₀).ref r)
        (rt := rt) ((refOk_reloc_iff s₀).mpr hr))
  | @castFail s f r rt hr =>
    simpa [shC] using Step.reference (P := P) (host := noHost)
      (RefStep.castFail (s := reloc s₀ s) (f := (sh s₀).frame f) (r := (sh s₀).ref r) (rt := rt)
        (fun h' => hr ((refOk_reloc_iff s₀).mp h')))
  | @i31GetNull s f sx =>
    simpa [shC] using Step.reference (P := P) (host := noHost)
      (RefStep.i31GetNull (s := reloc s₀ s) (f := (sh s₀).frame f) sx)
  | @i31GetNum s f sx i =>
    simpa [shC] using Step.reference (P := P) (host := noHost)
      (RefStep.i31GetNum (s := reloc s₀ s) (f := (sh s₀).frame f) sx i)
  | @externConvertNull s f =>
    simpa [shC] using Step.reference (P := P) (host := noHost)
      (RefStep.externConvertNull (s := reloc s₀ s) (f := (sh s₀).frame f))
  | @externConvertAddr s f r hr =>
    simpa [shC] using Step.reference (P := P) (host := noHost)
      (RefStep.externConvertAddr (s := reloc s₀ s) (f := (sh s₀).frame f) (r := (sh s₀).ref r)
        (by rwa [Ne, Shift.ref_eq_null_iff]))
  | @anyConvertNull s f =>
    simpa [shC] using Step.reference (P := P) (host := noHost)
      (RefStep.anyConvertNull (s := reloc s₀ s) (f := (sh s₀).frame f))
  | @anyConvertAddr s f r =>
    simpa [shC] using Step.reference (P := P) (host := noHost)
      (RefStep.anyConvertAddr (s := reloc s₀ s) (f := (sh s₀).frame f) ((sh s₀).ref r))

end Families

section Aggregate

variable (s₀ : Store H)

private theorem structNew_shift {P : Profile} {s : Store H} {f : Frame} {x : TypeIdx}
    {d : DefType} {fs : Ty (.list .field)} {vs : List Val} (hd : f.type? x = some d)
    (he : Expand d (.struct fs)) (hn : vs.length = fs.length)
    (hp : ∀ p ∈ fs.toList.zip vs, packable (fieldStorage p.1) p.2) :
    Step P noHost (shC s₀ ⟨s, f, vals vs ++ [.plain (.structNew x)]⟩)
      (shC s₀ ⟨s.addStruct ⟨d, (fs.toList.zip vs).map fun (ft, v) => packField (fieldStorage ft) v⟩,
        f, [.ref (.struct s.structs.length)]⟩) := by
  have hp' : ∀ q ∈ fs.toList.zip (vs.map (sh s₀).val), packable (fieldStorage q.1) q.2 := by
    intro q hq
    have hq' : q ∈ (fs.toList.zip vs).map (Prod.map id (sh s₀).val) := by
      simpa only [List.zip_map_right] using hq
    obtain ⟨⟨ft, v⟩, hm, hq''⟩ := List.mem_map.mp hq'
    exact hq'' ▸ by simpa [Shift.packable_val] using hp _ hm
  have hst : Step P noHost
      ⟨reloc s₀ s, (sh s₀).frame f, vals (vs.map (sh s₀).val) ++ [.plain (.structNew x)]⟩
      ⟨(reloc s₀ s).addStruct ⟨d, (fs.toList.zip (vs.map (sh s₀).val)).map
          fun (ft, v) => packField (fieldStorage ft) v⟩, (sh s₀).frame f,
        [.ref (.struct (reloc s₀ s).structs.length)]⟩ :=
    Step.aggregate (AggregateStep.structNew (by simpa [type?_frame] using hd) he
      (by simpa using hn) hp')
  show Step P noHost ⟨reloc s₀ s, (sh s₀).frame f, (sh s₀).code (vals vs ++ _)⟩
    ⟨reloc s₀ (s.addStruct _), (sh s₀).frame f, (sh s₀).code _⟩
  rw [reloc_addStruct, Shift.sinst_new, Shift.code_append, Shift.code_vals]
  simpa [structs_length_reloc] using hst

private theorem arrayNewFixed_shift {P : Profile} {s : Store H} {f : Frame} {x : TypeIdx}
    {n : Fin (2 ^ 32)} {d : DefType} {ft : CFieldType} {vs : List Val}
    (hd : f.type? x = some d) (he : Expand d (.array ft)) (hn : vs.length = n.val)
    (hp : ∀ v ∈ vs, packable (fieldStorage ft) v) :
    Step P noHost (shC s₀ ⟨s, f, vals vs ++ [.plain (.arrayNewFixed x n)]⟩)
      (shC s₀ ⟨s.addArray ⟨d, vs.map (packField (fieldStorage ft))⟩, f,
        [arrRef s.arrays.length]⟩) := by
  have hp' : ∀ v ∈ vs.map (sh s₀).val, packable (fieldStorage ft) v := by
    intro v hv
    obtain ⟨w, hw, hv'⟩ := List.mem_map.mp hv
    exact hv' ▸ by simpa [Shift.packable_val] using hp w hw
  have hst : Step P noHost
      ⟨reloc s₀ s, (sh s₀).frame f, vals (vs.map (sh s₀).val) ++ [.plain (.arrayNewFixed x n)]⟩
      ⟨(reloc s₀ s).addArray ⟨d, (vs.map (sh s₀).val).map (packField (fieldStorage ft))⟩,
        (sh s₀).frame f, [arrRef (reloc s₀ s).arrays.length]⟩ :=
    Step.aggregate (AggregateStep.arrayNewFixed (by simpa [type?_frame] using hd) he
      (by simpa using hn) hp')
  show Step P noHost ⟨reloc s₀ s, (sh s₀).frame f, (sh s₀).code (vals vs ++ _)⟩
    ⟨reloc s₀ (s.addArray _), (sh s₀).frame f, (sh s₀).code _⟩
  rw [reloc_addArray, Shift.ainst_new, Shift.code_append, Shift.code_vals]
  simpa [arrays_length_reloc] using hst

/-- **Aggregate steps commute with the relocation**, for frames without element and data
segments. -/
theorem AggregateStep.shift {P : Profile} {c c' : Config H} (h : AggregateStep c c')
    (he₀ : c.frame.module.elems = []) (hd₀ : c.frame.module.datas = []) :
    Step P noHost (shC s₀ c) (shC s₀ c') := by
  cases h with
  | structNew hd he hn hp => exact structNew_shift s₀ hd he hn hp
  | @structNewDefault s f x d fs vs hd he hdef =>
    simpa [shC, Shift.map_val_mapM_default _ _ hdef] using Step.aggregate (P := P)
      (host := noHost) (AggregateStep.structNewDefault (s := reloc s₀ s) (f := (sh s₀).frame f)
        (by simpa [type?_frame] using hd) he hdef)
  | @structGetNull s f sx x i =>
    simpa [shC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.structGetNull (s := reloc s₀ s) (f := (sh s₀).frame f) (sx := sx) (x := x)
        (i := i))
  | @structGetStruct s f sx x i a si fv d fs ft hs hfv hd he hi hu =>
    simpa [shC, Shift.unpackField_fval] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.structGetStruct (s := reloc s₀ s) (f := (sh s₀).frame f) (sx := sx) (i := i)
        (fv := (sh s₀).fval fv) (structs_reloc_of s₀ hs) (by simp [Shift.sinst, hfv])
        (by simpa [type?_frame] using hd) he hi (by rwa [Shift.unpackable_fval]))
  | @structSetNull s f x i v =>
    simpa [shC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.structSetNull (s := reloc s₀ s) (f := (sh s₀).frame f) (x := x) (i := i)
        (v := (sh s₀).val v))
  | @structSetStruct s f x i v a d fs ft si hd he hi hs hfl hp =>
    simpa [shC, reloc_setStructField, Shift.fval_packField] using Step.aggregate (P := P)
      (host := noHost) (AggregateStep.structSetStruct (s := reloc s₀ s) (f := (sh s₀).frame f)
        (v := (sh s₀).val v) (by simpa [type?_frame] using hd) he hi (structs_reloc_of s₀ hs)
        (by simpa using hfl) (by rwa [Shift.packable_val]))
  | @arrayNew s f x v n =>
    simpa [shC, List.map_replicate] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayNew (s := reloc s₀ s) (f := (sh s₀).frame f) (x := x) ((sh s₀).val v) n)
  | @arrayNewDefault s f x n d ft v hd he hv =>
    simpa [shC, List.map_replicate, Shift.val_defaultVal _ hv] using Step.aggregate (P := P)
      (host := noHost) (AggregateStep.arrayNewDefault (s := reloc s₀ s) (f := (sh s₀).frame f)
        (by simpa [type?_frame] using hd) he hv)
  | arrayNewFixed hd he hn hp => exact arrayNewFixed_shift s₀ hd he hn hp
  | arrayNewElemOob he => exact nomatch (elem?_none he₀).symm.trans he
  | arrayNewElemAlloc he => exact nomatch (elem?_none he₀).symm.trans he
  | arrayNewDataOob _ _ hdat => exact nomatch (data?_none hd₀).symm.trans hdat
  | arrayNewDataNum _ _ hdat => exact nomatch (data?_none hd₀).symm.trans hdat
  | @arrayGetNull s f sx x i =>
    simpa [shC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayGetNull (s := reloc s₀ s) (f := (sh s₀).frame f) (sx := sx) (x := x)
        (i := i))
  | @arrayGetOob s f sx x i a ai ha hl =>
    simpa [shC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayGetOob (s := reloc s₀ s) (f := (sh s₀).frame f) (sx := sx) (x := x)
        (arrays_reloc_of s₀ ha) (by simpa using hl))
  | @arrayGetArray s f sx x i a ai fv d ft ha hfv hd he hu =>
    simpa [shC, Shift.unpackField_fval] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayGetArray (s := reloc s₀ s) (f := (sh s₀).frame f) (sx := sx) (i := i)
        (fv := (sh s₀).fval fv) (arrays_reloc_of s₀ ha) (by simp [Shift.ainst, hfv])
        (by simpa [type?_frame] using hd) he (by rwa [Shift.unpackable_fval]))
  | @arraySetNull s f x i v =>
    simpa [shC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arraySetNull (s := reloc s₀ s) (f := (sh s₀).frame f) (x := x) (i := i)
        (v := (sh s₀).val v))
  | @arraySetOob s f x i v a ai ha hl =>
    simpa [shC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arraySetOob (s := reloc s₀ s) (f := (sh s₀).frame f) (x := x)
        (v := (sh s₀).val v) (arrays_reloc_of s₀ ha) (by simpa using hl))
  | @arraySetArray s f x i v a ai d ft ha hl hd he hp =>
    simpa [shC, reloc_setArrayField, Shift.fval_packField] using Step.aggregate (P := P)
      (host := noHost) (AggregateStep.arraySetArray (s := reloc s₀ s) (f := (sh s₀).frame f)
        (v := (sh s₀).val v) (arrays_reloc_of s₀ ha) (by simpa using hl)
        (by simpa [type?_frame] using hd) he (by rwa [Shift.packable_val]))
  | @arrayLenNull s f =>
    simpa [shC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayLenNull (s := reloc s₀ s) (f := (sh s₀).frame f))
  | @arrayLenArray s f a ai ha =>
    simpa [shC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayLenArray (s := reloc s₀ s) (f := (sh s₀).frame f)
        (arrays_reloc_of s₀ ha))
  | @arrayFillNull s f x i n v =>
    simpa [shC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayFillNull (s := reloc s₀ s) (f := (sh s₀).frame f) (x := x) (i := i)
        (n := n) (v := (sh s₀).val v))
  | @arrayFillOob s f x i n v a ai ha hl =>
    simpa [shC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayFillOob (s := reloc s₀ s) (f := (sh s₀).frame f) (x := x)
        (v := (sh s₀).val v) (arrays_reloc_of s₀ ha) (by simpa using hl))
  | @arrayFillZero s f x i v a ai ha hl =>
    simpa [shC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayFillZero (s := reloc s₀ s) (f := (sh s₀).frame f) (x := x)
        (v := (sh s₀).val v) (arrays_reloc_of s₀ ha) (by simpa using hl))
  | @arrayFillSucc s f x i n v a ai ha hl hn =>
    simpa [shC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayFillSucc (s := reloc s₀ s) (f := (sh s₀).frame f) (x := x)
        (v := (sh s₀).val v) (arrays_reloc_of s₀ ha) (by simpa using hl) hn)
  | @arrayCopyNull₁ s f x₁ x₂ i₁ i₂ n r =>
    simpa [shC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayCopyNull₁ (s := reloc s₀ s) (f := (sh s₀).frame f) (x₁ := x₁)
        (x₂ := x₂) (i₁ := i₁) (i₂ := i₂) (n := n) (r := (sh s₀).ref r))
  | @arrayCopyNull₂ s f x₁ x₂ i₁ i₂ n r =>
    simpa [shC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayCopyNull₂ (s := reloc s₀ s) (f := (sh s₀).frame f) (x₁ := x₁)
        (x₂ := x₂) (i₁ := i₁) (i₂ := i₂) (n := n) (r := (sh s₀).ref r))
  | @arrayCopyOob₁ s f x₁ x₂ i₁ i₂ n a₁ a₂ ai₁ ha hl =>
    simpa [shC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayCopyOob₁ (s := reloc s₀ s) (f := (sh s₀).frame f) (x₁ := x₁)
        (x₂ := x₂) (i₂ := i₂) (a₂ := s₀.arrays.length + a₂) (arrays_reloc_of s₀ ha)
        (by simpa using hl))
  | @arrayCopyOob₂ s f x₁ x₂ i₁ i₂ n a₁ a₂ ai₂ ha hl =>
    simpa [shC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayCopyOob₂ (s := reloc s₀ s) (f := (sh s₀).frame f) (x₁ := x₁)
        (x₂ := x₂) (i₁ := i₁) (a₁ := s₀.arrays.length + a₁) (arrays_reloc_of s₀ ha)
        (by simpa using hl))
  | @arrayCopyZero s f x₁ x₂ i₁ i₂ a₁ a₂ ai₁ ai₂ ha₁ ha₂ hl =>
    simpa [shC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayCopyZero (s := reloc s₀ s) (f := (sh s₀).frame f) (x₁ := x₁)
        (x₂ := x₂) (arrays_reloc_of s₀ ha₁) (arrays_reloc_of s₀ ha₂) (by simpa using hl))
  | @arrayCopyLe s f x₁ x₂ i₁ i₂ n a₁ a₂ ai₁ ai₂ d₂ ft₂ ha₁ ha₂ hl hn hd he hle =>
    simpa [shC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayCopyLe (s := reloc s₀ s) (f := (sh s₀).frame f)
        (arrays_reloc_of s₀ ha₁) (arrays_reloc_of s₀ ha₂) (by simpa using hl) hn
        (by simpa [type?_frame] using hd) he hle)
  | @arrayCopyGt s f x₁ x₂ i₁ i₂ n a₁ a₂ ai₁ ai₂ d₂ ft₂ ha₁ ha₂ hl hn hd he hgt =>
    simpa [shC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayCopyGt (s := reloc s₀ s) (f := (sh s₀).frame f)
        (arrays_reloc_of s₀ ha₁) (arrays_reloc_of s₀ ha₂) (by simpa using hl) hn
        (by simpa [type?_frame] using hd) he hgt)
  | @arrayInitElemNull s f x y i j n =>
    simpa [shC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayInitElemNull (s := reloc s₀ s) (f := (sh s₀).frame f) (x := x) (y := y)
        (i := i) (j := j) (n := n))
  | @arrayInitElemOob₁ s f x y i j n a ai ha hl =>
    simpa [shC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayInitElemOob₁ (s := reloc s₀ s) (f := (sh s₀).frame f) (x := x) (y := y)
        (j := j) (arrays_reloc_of s₀ ha) (by simpa using hl))
  | arrayInitElemOob₂ he => exact nomatch (elem?_none he₀).symm.trans he
  | arrayInitElemZero _ he => exact nomatch (elem?_none he₀).symm.trans he
  | arrayInitElemSucc _ he => exact nomatch (elem?_none he₀).symm.trans he
  | @arrayInitDataNull s f x y i j n =>
    simpa [shC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayInitDataNull (s := reloc s₀ s) (f := (sh s₀).frame f) (x := x) (y := y)
        (i := i) (j := j) (n := n))
  | @arrayInitDataOob₁ s f x y i j n a ai ha hl =>
    simpa [shC] using Step.aggregate (P := P) (host := noHost)
      (AggregateStep.arrayInitDataOob₁ (s := reloc s₀ s) (f := (sh s₀).frame f) (x := x) (y := y)
        (j := j) (arrays_reloc_of s₀ ha) (by simpa using hl))
  | arrayInitDataOob₂ _ _ hdat => exact nomatch (data?_none hd₀).symm.trans hdat
  | arrayInitDataZero _ hdat => exact nomatch (data?_none hd₀).symm.trans hdat
  | arrayInitDataNum _ _ _ hdat => exact nomatch (data?_none hd₀).symm.trans hdat

end Aggregate

/-! ## One step -/

section Main

variable (s₀ : Store H)

/-- **A host-free Core step commutes with the relocation past `s₀`**, for threads whose module
instances have no tags, memories, tables, element or data segments and whose code holds no
exception or host references (for any ownership `O`). -/
theorem step_shift {P : Profile} {c c' : Config H} (h : Step P noHost c c') {O : Own} :
    O.FrameGood c.frame → O.CodeGood c.code → Step P noHost (shC s₀ c) (shC s₀ c') := by
  induction h with
  | parametric h =>
    intro _ _
    exact Step.parametric (ParametricStep.shift h (sh s₀))
  | numeric h =>
    intro _ _
    obtain ⟨e1, e2⟩ : (sh s₀).code _ = _ ∧ (sh s₀).code _ = _ := NumericStep.shift_eq h (sh s₀)
    simp only [shC, e1, e2]
    exact .numeric h
  | vector h =>
    intro _ _
    obtain ⟨e1, e2⟩ : (sh s₀).code _ = _ ∧ (sh s₀).code _ = _ := VectorStep.shift_eq h (sh s₀)
    simp only [shC, e1, e2]
    exact .vector h
  | «variable» h => intro _ _; exact VariableStep.shift s₀ h
  | table h => intro hf _; exact (TableStep.not_good h hf).elim
  | memory h => intro hf _; exact (MemoryStep.not_good h hf).elim
  | reference h => intro _ _; exact RefStep.shift s₀ h
  | aggregate h => intro hf _; exact AggregateStep.shift s₀ h hf.1.elems hf.1.datas
  | @ctxtInstrs s s' f f' vs is is' rest _ hne ih =>
    intro hf hc
    have hci : O.CodeGood is := (O.codeGood_append.mp (O.codeGood_append.mp hc).1).2
    have hst : Step P noHost (shC s₀ ⟨s, f, is⟩) (shC s₀ ⟨s', f', is'⟩) := ih hf hci
    simp only [shC, Shift.code_append, Shift.code_vals]
    exact Step.ctxtInstrs hst (by simpa [Shift.code_eq_nil_iff] using hne)
  | @ctxtLabel s s' f f' n cont is is' _ ih =>
    intro hf hc
    have hst : Step P noHost (shC s₀ ⟨s, f, is⟩) (shC s₀ ⟨s', f', is'⟩) :=
      ih hf ((O.codeGood_single_label ..).mp hc)
    simpa using Step.ctxtLabel (n := n) (cont := cont) hst
  | @ctxtHandler s s' f f' n cs is is' _ ih =>
    intro hf hc
    have hst : Step P noHost (shC s₀ ⟨s, f, is⟩) (shC s₀ ⟨s', f', is'⟩) :=
      ih hf ((O.codeGood_single_handler ..).mp hc)
    simpa using Step.ctxtHandler (n := n) (cs := cs) hst
  | @ctxtFrame s s' f fi fi' n is is' _ ih =>
    intro hf hc
    obtain ⟨hfi, hcb⟩ : O.FrameGood fi ∧ O.CodeGood is := (O.codeGood_single_frame ..).mp hc
    have hst : Step P noHost (shC s₀ ⟨s, fi, is⟩) (shC s₀ ⟨s', fi', is'⟩) := ih hfi hcb
    simpa using Step.ctxtFrame (f := (sh s₀).frame f) (n := n) hst
  | @block s f bt body vs t₁ t₂ hbt hm =>
    intro _ _
    simpa [shC] using Step.block (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (vs := vs.map (sh s₀).val) (body := body)
      (by rwa [Shift.frame_module, blockType?_minst]) (by simpa using hm)
  | @loop s f bt body vs t₁ t₂ hbt hm =>
    intro _ _
    simpa [shC] using Step.loop (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (vs := vs.map (sh s₀).val) (body := body)
      (by rwa [Shift.frame_module, blockType?_minst]) (by simpa using hm)
  | @ifTrue s f c bt b₁ b₂ hc0 =>
    intro _ _
    simpa [shC] using Step.ifTrue (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (bt := bt) (b₁ := b₁) (b₂ := b₂) hc0
  | @ifFalse s f bt b₁ b₂ =>
    intro _ _
    simpa [shC] using Step.ifFalse (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (bt := bt) (b₁ := b₁) (b₂ := b₂)
  | @labelVals s f n cont vs =>
    intro _ _
    simpa [shC] using Step.labelVals (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (n := n) (cont := cont) (vs := vs.map (sh s₀).val)
  | @brLabelZero s f n cont vs' vs l rest hl hn =>
    intro _ _
    simpa [shC] using Step.brLabelZero (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (cont := cont) (vs' := vs'.map (sh s₀).val)
      (vs := vs.map (sh s₀).val) (rest := (sh s₀).code rest) hl (by simpa using hn)
  | @brLabelSucc s f n cont vs l rest hl =>
    intro _ _
    simpa [shC] using Step.brLabelSucc (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (n := n) (cont := cont) (vs := vs.map (sh s₀).val)
      (rest := (sh s₀).code rest) hl
  | @brHandler s f n cs vs l rest =>
    intro _ _
    simpa [shC] using Step.brHandler (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (n := n) (cs := cs) (vs := vs.map (sh s₀).val) (l := l)
      (rest := (sh s₀).code rest)
  | @brIfTrue s f c l hc0 =>
    intro _ _
    simpa [shC] using Step.brIfTrue (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (l := l) hc0
  | @brIfFalse s f l =>
    intro _ _
    simpa [shC] using Step.brIfFalse (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (l := l)
  | @brTableLt s f i ls l' l hi =>
    intro _ _
    simpa [shC] using Step.brTableLt (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (l' := l') hi
  | @brTableGe s f i ls l' hi =>
    intro _ _
    simpa [shC] using Step.brTableGe (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (l' := l') hi
  | @brOnNullNull s f l =>
    intro _ _
    simpa [shC] using Step.brOnNullNull (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (l := l)
  | @brOnNullAddr s f v l hv =>
    intro _ _
    have hv' : (sh s₀).val v ≠ .ref .null := by
      cases v <;> simp_all [Shift.ref_eq_null_iff]
    simpa [shC] using Step.brOnNullAddr (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (l := l) hv'
  | @brOnNonNullNull s f l =>
    intro _ _
    simpa [shC] using Step.brOnNonNullNull (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (l := l)
  | @brOnNonNullAddr s f v l hv =>
    intro _ _
    have hv' : (sh s₀).val v ≠ .ref .null := by
      cases v <;> simp_all [Shift.ref_eq_null_iff]
    simpa [shC] using Step.brOnNonNullAddr (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (l := l) hv'
  | @brOnCastSucceed s f r l rt₁ rt₂ hr =>
    intro _ _
    simpa [shC] using Step.brOnCastSucceed (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (l := l) (rt₁ := rt₁) (r := (sh s₀).ref r) (rt₂ := rt₂)
      ((refOk_reloc_iff s₀).mpr hr)
  | @brOnCastFail s f r l rt₁ rt₂ hr =>
    intro _ _
    simpa [shC] using Step.brOnCastFail (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (l := l) (rt₁ := rt₁) (r := (sh s₀).ref r) (rt₂ := rt₂)
      (fun h' => hr ((refOk_reloc_iff s₀).mp h'))
  | @brOnCastFailSucceed s f r l rt₁ rt₂ hr =>
    intro _ _
    simpa [shC] using Step.brOnCastFailSucceed (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (l := l) (rt₁ := rt₁) (r := (sh s₀).ref r) (rt₂ := rt₂)
      ((refOk_reloc_iff s₀).mpr hr)
  | @brOnCastFailFail s f r l rt₁ rt₂ hr =>
    intro _ _
    simpa [shC] using Step.brOnCastFailFail (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (l := l) (rt₁ := rt₁) (r := (sh s₀).ref r) (rt₂ := rt₂)
      (fun h' => hr ((refOk_reloc_iff s₀).mp h'))
  | @call s f x a fi hx hfi =>
    intro _ _
    simpa [shC] using Step.call (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (x := x) (by simp [List.getElem?_map, hx]) (funcs_reloc_of s₀ hfi)
  | @callRefNull s f c hcr =>
    intro _ _
    simpa [shC, Shift.code_callRef _ hcr] using Step.callRefNull (P := P) (host := noHost)
      (s := reloc s₀ s) (f := (sh s₀).frame f) hcr
  | @callRefFunc s f c vs a fi ps rs code hcr hfi he hn hcode =>
    intro _ _
    simpa [shC, Shift.code_callRef _ hcr, Shift.frame_forCall] using
      Step.callRefFunc (P := P) (host := noHost) (s := reloc s₀ s) (f := (sh s₀).frame f)
        (vs := vs.map (sh s₀).val) hcr (funcs_reloc_of s₀ hfi) he (by simpa using hn) hcode
  | callRefHost _ _ _ _ _ hhost => intro _ _; exact hhost.elim
  | callRefHostDiv _ _ _ _ _ hhost => intro _ _; exact hhost.elim
  | @returnCall s f x a fi hx hfi =>
    intro _ _
    simpa [shC] using Step.returnCall (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (x := x) (by simp [List.getElem?_map, hx]) (funcs_reloc_of s₀ hfi)
  | @returnCallRefLabel s f k cont vs c rest hcr =>
    intro _ _
    simpa [shC, Shift.code_returnCallRef _ hcr] using
      Step.returnCallRefLabel (P := P) (host := noHost) (s := reloc s₀ s) (f := (sh s₀).frame f)
        (k := k) (cont := cont) (vs := vs.map (sh s₀).val) (rest := (sh s₀).code rest) hcr
  | @returnCallRefHandler s f k cs vs c rest hcr =>
    intro _ _
    simpa [shC, Shift.code_returnCallRef _ hcr] using
      Step.returnCallRefHandler (P := P) (host := noHost) (s := reloc s₀ s)
        (f := (sh s₀).frame f) (k := k) (cs := cs) (vs := vs.map (sh s₀).val)
        (rest := (sh s₀).code rest) hcr
  | @returnCallRefFrameNull s f fi k vs c rest hcr =>
    intro _ _
    simpa [shC, Shift.code_returnCallRef _ hcr] using
      Step.returnCallRefFrameNull (P := P) (host := noHost) (s := reloc s₀ s)
        (f := (sh s₀).frame f) (fi := (sh s₀).frame fi) (k := k) (vs := vs.map (sh s₀).val)
        (rest := (sh s₀).code rest) hcr
  | @returnCallRefFrameAddr s f fi k vs' vs a c rest fn ps rs hcr hfn he hn =>
    intro _ _
    simpa [shC, Shift.code_returnCallRef _ hcr, Shift.code_retToCallIn _ hcr,
      Shift.retToCallIn_minst] using Step.returnCallRefFrameAddr (P := P) (host := noHost)
        (s := reloc s₀ s) (f := (sh s₀).frame f) (fi := (sh s₀).frame fi) (k := k)
        (vs' := vs'.map (sh s₀).val) (vs := vs.map (sh s₀).val) (rest := (sh s₀).code rest) hcr
        (funcs_reloc_of s₀ hfn) he (by simpa using hn)
  | @callIndirect s f x y =>
    intro _ _
    simpa [shC] using Step.callIndirect (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (x := x) (y := y)
  | @returnCallIndirect s f x y =>
    intro _ _
    simpa [shC] using Step.returnCallIndirect (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (x := x) (y := y)
  | @frameVals s f fi n vs hn =>
    intro _ _
    simpa [shC] using Step.frameVals (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (fi := (sh s₀).frame fi) (vs := vs.map (sh s₀).val)
      (by simpa using hn)
  | @returnFrame s f fi n vs' vs rest hn =>
    intro _ _
    simpa [shC] using Step.returnFrame (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (fi := (sh s₀).frame fi) (vs' := vs'.map (sh s₀).val)
      (vs := vs.map (sh s₀).val) (rest := (sh s₀).code rest) (by simpa using hn)
  | @returnLabel s f n cont vs rest =>
    intro _ _
    simpa [shC] using Step.returnLabel (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (n := n) (cont := cont) (vs := vs.map (sh s₀).val)
      (rest := (sh s₀).code rest)
  | @returnHandler s f n cs vs rest =>
    intro _ _
    simpa [shC] using Step.returnHandler (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (n := n) (cs := cs) (vs := vs.map (sh s₀).val)
      (rest := (sh s₀).code rest)
  | throw ht =>
    intro hf _
    exact absurd ht (by simp [Silmaril.Proofs.Wasm.Game.Linking.Split.tag?_none hf.1.tags])
  | @throwRefNull s f =>
    intro _ _
    simpa [shC] using Step.throwRefNull (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f)
  | throwRefInstrs _ =>
    intro _ hc
    exact (Own.not_codeGood_throwing hc (by simp [throwing]; exact .inr (.inl rfl))).elim
  | throwRefLabel =>
    intro _ hc
    exact (Own.not_codeGood_throwing ((O.codeGood_single_label ..).mp hc)
      (by simp [throwing]; try rfl)).elim
  | throwRefFrame =>
    intro _ hc
    exact (Own.not_codeGood_throwing ((O.codeGood_single_frame ..).mp hc).2
      (by simp [throwing]; try rfl)).elim
  | throwRefHandlerEmpty =>
    intro _ hc
    exact (Own.not_codeGood_throwing ((O.codeGood_single_handler ..).mp hc)
      (by simp [throwing]; try rfl)).elim
  | throwRefHandlerCatch _ _ =>
    intro _ hc
    exact (Own.not_codeGood_throwing ((O.codeGood_single_handler ..).mp hc)
      (by simp [throwing]; try rfl)).elim
  | throwRefHandlerCatchRef _ _ =>
    intro _ hc
    exact (Own.not_codeGood_throwing ((O.codeGood_single_handler ..).mp hc)
      (by simp [throwing]; try rfl)).elim
  | throwRefHandlerCatchAll =>
    intro _ hc
    exact (Own.not_codeGood_throwing ((O.codeGood_single_handler ..).mp hc)
      (by simp [throwing]; try rfl)).elim
  | throwRefHandlerCatchAllRef =>
    intro _ hc
    exact (Own.not_codeGood_throwing ((O.codeGood_single_handler ..).mp hc)
      (by simp [throwing]; try rfl)).elim
  | throwRefHandlerNext _ =>
    intro _ hc
    exact (Own.not_codeGood_throwing ((O.codeGood_single_handler ..).mp hc)
      (by simp [throwing]; try rfl)).elim
  | @tryTable s f bt cs body vs t₁ t₂ hbt hm =>
    intro _ _
    simpa [shC] using Step.tryTable (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (cs := cs) (body := body) (vs := vs.map (sh s₀).val)
      (by rwa [Shift.frame_module, blockType?_minst]) (by simpa using hm)
  | @handlerVals s f n cs vs =>
    intro _ _
    simpa [shC] using Step.handlerVals (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (n := n) (cs := cs) (vs := vs.map (sh s₀).val)
  | @trapInstrs s f vs rest hne =>
    intro _ _
    simpa [shC] using Step.trapInstrs (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (vs := vs.map (sh s₀).val) (rest := (sh s₀).code rest)
      (by simpa [Shift.code_eq_nil_iff] using hne)
  | @trapLabel s f n cont =>
    intro _ _
    simpa [shC] using Step.trapLabel (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (n := n) (cont := cont)
  | @trapHandler s f n cs =>
    intro _ _
    simpa [shC] using Step.trapHandler (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (n := n) (cs := cs)
  | @trapFrame s f fi n =>
    intro _ _
    simpa [shC] using Step.trapFrame (P := P) (host := noHost) (s := reloc s₀ s)
      (f := (sh s₀).frame f) (fi := (sh s₀).frame fi) (n := n)

end Main

/-! ## Runs -/

section Runs

open Silmaril.Proofs.Wasm.Game.Linking.Split (PartRel step_sim)

/-- **A configuration of the split fragment**: for some renaming, ownership and shared store
(`Linking.Split.PartRel`), its frame and code are good. Host-free steps preserve it
(`SplitGood.step`, from `Linking.Split.step_sim`). -/
def SplitGood (c : Config H) : Prop :=
  ∃ (ρ : Silmaril.Proofs.Wasm.Game.Linking.Split.Ren) (O : Own) (σ : Store H),
    PartRel ρ O c.store σ ∧ O.FrameGood c.frame ∧ O.CodeGood c.code

theorem SplitGood.step {P : Profile} {c c' : Config H} (h : Step P noHost c c')
    (hg : SplitGood c) : SplitGood c' := by
  obtain ⟨ρ, O, σ, hR, hf, hc⟩ := hg
  obtain ⟨ρ', O', σ', -, hR', hf', hc', -⟩ := step_sim h hR hf hc
  exact ⟨ρ', O', σ', hR', hf', hc'⟩

variable (s₀ : Store H)

/-- **Host-free runs of the split fragment commute with the relocation past `s₀`.** -/
theorem steps_shift {P : Profile} {c c' : Config H}
    (h : Relation.ReflTransGen (Step P noHost) c c') (hg : SplitGood c) :
    Relation.ReflTransGen (Step P noHost) (shC s₀ c) (shC s₀ c') ∧ SplitGood c' := by
  induction h with
  | refl => exact ⟨.refl, hg⟩
  | tail _ hst ih =>
    obtain ⟨hrun, hg₁⟩ := ih
    obtain ⟨ρ, O, σ, hR, hf, hc⟩ := hg₁
    exact ⟨hrun.tail (step_shift s₀ hst hf hc), SplitGood.step hst ⟨ρ, O, σ, hR, hf, hc⟩⟩

end Runs

end Silmaril.Proofs.Wasm.Component.Reference
