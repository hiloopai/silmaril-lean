module

public import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce

/-!
# Relocating a Core 3.0 instantiation after an existing store

In `Linked2.toRef` the importer's core module is instantiated in the core store that already
holds the exporter (`cs₀`), while its IR instance is instantiated alone. This file relates the
two: `reloc s₀ t` is the store `s₀` followed by `t`, every address of `t` shifted past the
objects of `s₀` (`Shift.ofStore s₀`: tags, globals, memories, tables, functions, data and
element segments, structures, arrays, exceptions). `instantiateOnce?_reloc`: for a module
without data and element segments, instantiating it in `reloc s₀ t` against the shifted
external addresses is instantiating it in `t` and relocating the resulting store and frame.

Layers: the shift of references, values, instances and stores (`Shift`), the allocation
functions (`allocMany_reloc`, `allocModule?_reloc`), constant evaluation (`constInstr?_reloc`,
`constExpr?_reloc`, `evalConst?_reloc`), the initialiser runs (`evalGlobals?_reloc`,
`evalExprs?_reloc`, `evalExprss?_reloc`), `prepare?_reloc` (any module) and, without segments,
`instantiateDirect?_reloc` and `instantiateOnce?_reloc`.

New proofs, in the pattern of `HostMap` (`instantiateOnce?_mapH`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

/-- Offsets of every address space of a Core store. -/
structure Shift where
  tg : Nat
  gl : Nat
  me : Nat
  ta : Nat
  fn : Nat
  da : Nat
  el : Nat
  st : Nat
  ar : Nat
  ex : Nat

namespace Shift

variable {H : Type} (δ : Shift)

/-- The offsets past the objects of a store. -/
def ofStore (s : Store H) : Shift :=
  ⟨s.tags.length, s.globals.length, s.mems.length, s.tables.length, s.funcs.length,
    s.datas.length, s.elems.length, s.structs.length, s.arrays.length, s.exns.length⟩

/-- Shift a reference. -/
def ref : Ref → Ref
  | .struct a => .struct (δ.st + a)
  | .array a => .array (δ.ar + a)
  | .func a => .func (δ.fn + a)
  | .exn a => .exn (δ.ex + a)
  | .extern r => .extern (ref r)
  | r => r

/-- Shift a value. -/
def val : Val → Val
  | .ref r => .ref (δ.ref r)
  | v => v

/-- Shift a field value. -/
def fval : FieldVal → FieldVal
  | .val v => .val (δ.val v)
  | p => p

/-- Shift an external address. -/
def xa : ExternAddr → ExternAddr
  | .tag a => .tag (δ.tg + a)
  | .global a => .global (δ.gl + a)
  | .mem a => .mem (δ.me + a)
  | .table a => .table (δ.ta + a)
  | .func a => .func (δ.fn + a)

/-- Shift an export instance. -/
def xinst (x : ExportInst) : ExportInst := { x with addr := δ.xa x.addr }

/-- Shift a module instance. -/
def minst (mi : ModuleInst) : ModuleInst :=
  { types := mi.types, tags := mi.tags.map (δ.tg + ·), globals := mi.globals.map (δ.gl + ·),
    mems := mi.mems.map (δ.me + ·), tables := mi.tables.map (δ.ta + ·),
    funcs := mi.funcs.map (δ.fn + ·), datas := mi.datas.map (δ.da + ·),
    elems := mi.elems.map (δ.el + ·), exports := mi.exports.map δ.xinst }

/-- Shift a function instance (its module instance). -/
def finst (fi : FuncInst H) : FuncInst H := { fi with module := δ.minst fi.module }

def ginst (g : GlobalInst) : GlobalInst := { g with value := δ.val g.value }
def tinst (t : TableInst) : TableInst := { t with refs := t.refs.map δ.ref }
def einst (e : ElemInst) : ElemInst := { e with refs := e.refs.map δ.ref }
def sinst (si : StructInst) : StructInst := { si with fields := si.fields.map δ.fval }
def ainst (ai : ArrayInst) : ArrayInst := { ai with fields := ai.fields.map δ.fval }
def xninst (e : ExnInst) : ExnInst := ⟨δ.tg + e.tag, e.fields.map δ.val⟩

/-- Shift a frame. -/
def frame (f : Frame) : Frame := ⟨f.locals.map (Option.map δ.val), δ.minst f.module⟩

/-- Shift every object of a store. -/
def store (t : Store H) : Store H :=
  { tags := t.tags, globals := t.globals.map δ.ginst, mems := t.mems,
    tables := t.tables.map δ.tinst, funcs := t.funcs.map δ.finst, datas := t.datas,
    elems := t.elems.map δ.einst, structs := t.structs.map δ.sinst,
    arrays := t.arrays.map δ.ainst, exns := t.exns.map δ.xninst }

@[simp] theorem val_num (v : NumVal) : δ.val (.num v) = .num v := rfl
@[simp] theorem val_vec (b : BitVec 128) : δ.val (.vec b) = .vec b := rfl
@[simp] theorem val_ref (r : Ref) : δ.val (.ref r) = .ref (δ.ref r) := rfl
@[simp] theorem ref_null : δ.ref .null = .null := rfl
@[simp] theorem ref_i31 (b : BitVec 31) : δ.ref (.i31 b) = .i31 b := rfl
@[simp] theorem ref_func (a : Nat) : δ.ref (.func a) = .func (δ.fn + a) := rfl
@[simp] theorem ref_struct (a : Nat) : δ.ref (.struct a) = .struct (δ.st + a) := rfl
@[simp] theorem ref_array (a : Nat) : δ.ref (.array a) = .array (δ.ar + a) := rfl
@[simp] theorem ref_extern (r : Ref) : δ.ref (.extern r) = .extern (δ.ref r) := rfl

theorem ref_eq_null_iff {r : Ref} : δ.ref r = .null ↔ r = .null := by
  cases r <;> simp [ref]

@[simp] theorem minst_types (mi : ModuleInst) : (δ.minst mi).types = mi.types := rfl
@[simp] theorem minst_funcs (mi : ModuleInst) : (δ.minst mi).funcs = mi.funcs.map (δ.fn + ·) :=
  rfl
@[simp] theorem minst_globals (mi : ModuleInst) :
    (δ.minst mi).globals = mi.globals.map (δ.gl + ·) := rfl
@[simp] theorem frame_module (f : Frame) : (δ.frame f).module = δ.minst f.module := rfl

theorem minst_empty : δ.minst ({} : ModuleInst) = {} := rfl

theorem fval_packField (st : CStorageType) (v : Val) :
    δ.fval (packField st v) = packField st (δ.val v) := by
  rcases st with _ | _
  · rfl
  · rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> rfl

theorem packable_val (st : CStorageType) (v : Val) : packable st (δ.val v) = packable st v := by
  rcases st with _ | _
  · rfl
  · rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> rfl

theorem int?_val (t : IntType) (v : Val) : (δ.val v).int? t = v.int? t := by
  rcases v with _ | _ | _ <;> rfl

theorem val_defaultVal {t : CValType} {v : Val} (h : defaultVal? t = some v) : δ.val v = v := by
  unfold defaultVal? at h
  split at h <;> first | (cases h; rfl) | cases h

theorem map_val_mapM_default {α : Type} (g : α → CValType) :
    ∀ {l : List α} {dvs : List Val}, l.mapM (fun x => defaultVal? (g x)) = some dvs →
      dvs.map δ.val = dvs
  | [], dvs, h => by cases h; rfl
  | x :: l, dvs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨v, hv, vs, hvs, rfl⟩ := h
    simp only [List.map_cons, val_defaultVal δ hv, map_val_mapM_default g hvs]

end Shift

namespace Store

variable {H : Type}

/-- The store `s₀` followed by `t`, field by field. -/
def app (s₀ t : Store H) : Store H :=
  { tags := s₀.tags ++ t.tags, globals := s₀.globals ++ t.globals, mems := s₀.mems ++ t.mems,
    tables := s₀.tables ++ t.tables, funcs := s₀.funcs ++ t.funcs, datas := s₀.datas ++ t.datas,
    elems := s₀.elems ++ t.elems, structs := s₀.structs ++ t.structs,
    arrays := s₀.arrays ++ t.arrays, exns := s₀.exns ++ t.exns }

end Store

variable {H : Type}

/-- **The store `s₀` followed by the store `t` relocated past it.** -/
def reloc (s₀ t : Store H) : Store H := Store.app s₀ ((Shift.ofStore s₀).store t)

/-- The shift past `s₀`. -/
abbrev sh (s₀ : Store H) : Shift := Shift.ofStore s₀

section Basic

variable (s₀ : Store H)

@[simp] theorem reloc_globals (t : Store H) :
    (reloc s₀ t).globals = s₀.globals ++ t.globals.map (sh s₀).ginst := rfl
@[simp] theorem reloc_funcs (t : Store H) :
    (reloc s₀ t).funcs = s₀.funcs ++ t.funcs.map (sh s₀).finst := rfl
@[simp] theorem reloc_structs (t : Store H) :
    (reloc s₀ t).structs = s₀.structs ++ t.structs.map (sh s₀).sinst := rfl
@[simp] theorem reloc_arrays (t : Store H) :
    (reloc s₀ t).arrays = s₀.arrays ++ t.arrays.map (sh s₀).ainst := rfl

@[simp] theorem sh_fn : (sh s₀).fn = s₀.funcs.length := rfl
@[simp] theorem sh_gl : (sh s₀).gl = s₀.globals.length := rfl
@[simp] theorem sh_st : (sh s₀).st = s₀.structs.length := rfl
@[simp] theorem sh_ar : (sh s₀).ar = s₀.arrays.length := rfl

theorem reloc_addStruct (t : Store H) (si : StructInst) :
    reloc s₀ (t.addStruct si) = (reloc s₀ t).addStruct ((sh s₀).sinst si) := by
  simp [reloc, Store.app, Shift.store, Store.addStruct]

theorem reloc_addArray (t : Store H) (ai : ArrayInst) :
    reloc s₀ (t.addArray ai) = (reloc s₀ t).addArray ((sh s₀).ainst ai) := by
  simp [reloc, Store.app, Shift.store, Store.addArray]

theorem global?_reloc (t : Store H) (f : Frame) (x : GlobalIdx) :
    (reloc s₀ t).global? ((sh s₀).frame f) x =
      (t.global? f x).map fun p => ((sh s₀).gl + p.1, (sh s₀).ginst p.2) := by
  simp only [Store.global?, Shift.frame_module, Shift.minst_globals, List.getElem?_map,
    Option.bind_eq_bind, reloc_globals]
  cases f.module.globals[x.toNat]? with
  | none => rfl
  | some a =>
    simp only [Option.map_some, Option.bind_some, sh_gl]
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getElem?_map]
    cases t.globals[a]? <;> rfl

theorem type?_frame (f : Frame) (x : TypeIdx) : ((sh s₀).frame f).type? x = f.type? x := rfl

end Basic

/-! ## Stacks -/

section Stacks

variable (δ : Shift)

theorem popN?_map (vs : List Val) (n : Nat) :
    popN? (vs.map δ.val) n = (popN? vs n).map fun p => (p.1.map δ.val, p.2.map δ.val) := by
  unfold popN?
  simp only [List.length_map]
  split <;> simp [List.map_take, List.map_drop]

theorem pop1?_map (vs : List Val) :
    pop1? (vs.map δ.val) = (pop1? vs).map fun p => (p.1.map δ.val, δ.val p.2) := by
  unfold pop1?
  simp only [popN?_map, Option.bind_eq_bind]
  cases popN? vs 1 with
  | none => rfl
  | some p =>
    obtain ⟨pre, args⟩ := p
    rcases args with _ | ⟨a, _ | _⟩ <;> rfl

theorem pop2?_map (vs : List Val) :
    pop2? (vs.map δ.val) =
      (pop2? vs).map fun p => (p.1.map δ.val, δ.val p.2.1, δ.val p.2.2) := by
  unfold pop2?
  simp only [popN?_map, Option.bind_eq_bind]
  cases popN? vs 2 with
  | none => rfl
  | some p =>
    obtain ⟨pre, args⟩ := p
    rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> rfl

end Stacks

/-! ## Constant evaluation -/

section Const

variable (s₀ : Store H)

/-- The relocation of a store and a value stack. -/
abbrev relSV (p : Store H × List Val) : Store H × List Val := (reloc s₀ p.1, p.2.map (sh s₀).val)

theorem zip_map_val {α : Type} (l : List α) (args : List Val) :
    l.zip (args.map (sh s₀).val) = (l.zip args).map fun p => (p.1, (sh s₀).val p.2) := by
  rw [List.zip_map_right]
  rfl

theorem structNew?_reloc (t : Store H) (f : Frame) (vs : List Val) (x : TypeIdx) :
    structNew? (reloc s₀ t) ((sh s₀).frame f) (vs.map (sh s₀).val) x =
      (structNew? t f vs x).map (relSV s₀) := by
  unfold structNew?
  simp only [type?_frame, popN?_map, Option.bind_eq_bind]
  cases f.type? x with
  | none => rfl
  | some d =>
    simp only [Option.bind_some]
    cases expandStruct? d with
    | none => rfl
    | some fs =>
      simp only [Option.bind_some]
      cases popN? vs fs.length with
      | none => rfl
      | some p =>
        obtain ⟨pre, args⟩ := p
        simp only [Option.map_some, Option.bind_some, zip_map_val, List.all_map,
          Function.comp_def, Shift.packable_val]
        split
        · simp [relSV, reloc_addStruct, Shift.sinst, Function.comp_def, Shift.fval_packField]
        · rfl

theorem arrayNewFixed?_reloc (t : Store H) (f : Frame) (vs : List Val) (x : TypeIdx)
    (n : Fin (2 ^ 32)) :
    arrayNewFixed? (reloc s₀ t) ((sh s₀).frame f) (vs.map (sh s₀).val) x n =
      (arrayNewFixed? t f vs x n).map (relSV s₀) := by
  unfold arrayNewFixed?
  simp only [type?_frame, popN?_map, Option.bind_eq_bind]
  cases f.type? x with
  | none => rfl
  | some d =>
    simp only [Option.bind_some]
    cases expandArray? d with
    | none => rfl
    | some ft =>
      simp only [Option.bind_some]
      cases popN? vs n.val with
      | none => rfl
      | some p =>
        obtain ⟨pre, args⟩ := p
        simp only [Option.map_some, Option.bind_some, List.all_map, Function.comp_def,
          Shift.packable_val]
        split
        · simp [relSV, reloc_addArray, Shift.ainst, Function.comp_def, Shift.fval_packField]
        · rfl

section Instr

variable (t : Store H) (f : Frame) (vs : List Val)

theorem constInstr?_reloc_intBinOp (tt : IntType) (op : IntBinOp) :
    constInstr? (reloc s₀ t) ((sh s₀).frame f) (vs.map (sh s₀).val) (.intBinOp tt op) =
      (constInstr? t f vs (.intBinOp tt op)).map (relSV s₀) := by
  simp only [constInstr?, pop2?_map, Option.bind_eq_bind]
  split
  · rcases pop2? vs with _ | ⟨pre, v₁, v₂⟩
    · rfl
    simp only [Option.map_some, Option.bind_some, Shift.int?_val]
    rcases v₁.int? tt with _ | x
    · rfl
    rcases v₂.int? tt with _ | y
    · rfl
    simp only [Option.bind_some]
    cases Numerics.intBinOp tt op x y <;> simp [relSV]
  · rfl

theorem constInstr?_reloc_anyConvertExtern :
    constInstr? (reloc s₀ t) ((sh s₀).frame f) (vs.map (sh s₀).val) .anyConvertExtern =
      (constInstr? t f vs .anyConvertExtern).map (relSV s₀) := by
  simp only [constInstr?, pop1?_map, Option.bind_eq_bind]
  rcases pop1? vs with _ | ⟨pre, _ | _ | r⟩
  · rfl
  · rfl
  · rfl
  · cases r <;> simp [relSV, Shift.ref]

theorem constInstr?_reloc_externConvertAny :
    constInstr? (reloc s₀ t) ((sh s₀).frame f) (vs.map (sh s₀).val) .externConvertAny =
      (constInstr? t f vs .externConvertAny).map (relSV s₀) := by
  simp only [constInstr?, pop1?_map, Option.bind_eq_bind]
  rcases pop1? vs with _ | ⟨pre, _ | _ | r⟩
  · rfl
  · rfl
  · rfl
  by_cases hr : r = .null
  · subst hr
    simp [relSV]
  have hr' : (sh s₀).ref r ≠ .null := fun h => hr ((Shift.ref_eq_null_iff _).1 h)
  simp [relSV, hr, hr']

theorem constInstr?_reloc_structNewDefault (x : TypeIdx) :
    constInstr? (reloc s₀ t) ((sh s₀).frame f) (vs.map (sh s₀).val) (.structNewDefault x) =
      (constInstr? t f vs (.structNewDefault x)).map (relSV s₀) := by
  simp only [constInstr?, type?_frame, Option.bind_eq_bind]
  rcases f.type? x with _ | d
  · rfl
  simp only [Option.bind_some]
  rcases expandStruct? d with _ | fs
  · rfl
  simp only [Option.bind_some]
  rcases hm : fs.toList.mapM (fun ft => defaultVal? (fieldStorage ft).unpack) with _ | dvs
  · rfl
  simp only [Option.bind_some]
  conv => lhs; rw [← (sh s₀).map_val_mapM_default _ hm]
  rw [← List.map_append, structNew?_reloc]

theorem constInstr?_reloc_arrayNew (x : TypeIdx) :
    constInstr? (reloc s₀ t) ((sh s₀).frame f) (vs.map (sh s₀).val) (.arrayNew x) =
      (constInstr? t f vs (.arrayNew x)).map (relSV s₀) := by
  simp only [constInstr?, pop2?_map, Option.bind_eq_bind]
  rcases pop2? vs with _ | ⟨pre, v, n⟩
  · rfl
  simp only [Option.map_some, Option.bind_some, Shift.int?_val]
  rcases n.int? .i32 with _ | k
  · rfl
  simp only [Option.bind_some]
  rw [← List.map_replicate, ← List.map_append, arrayNewFixed?_reloc]

theorem constInstr?_reloc_arrayNewDefault (x : TypeIdx) :
    constInstr? (reloc s₀ t) ((sh s₀).frame f) (vs.map (sh s₀).val) (.arrayNewDefault x) =
      (constInstr? t f vs (.arrayNewDefault x)).map (relSV s₀) := by
  simp only [constInstr?, pop1?_map, type?_frame, Option.bind_eq_bind]
  rcases pop1? vs with _ | ⟨pre, n⟩
  · rfl
  simp only [Option.map_some, Option.bind_some, Shift.int?_val]
  rcases n.int? .i32 with _ | k
  · rfl
  simp only [Option.bind_some]
  rcases f.type? x with _ | d
  · rfl
  simp only [Option.bind_some]
  rcases expandArray? d with _ | ft
  · rfl
  simp only [Option.bind_some]
  rcases hv : defaultVal? (fieldStorage ft).unpack with _ | v
  · rfl
  simp only [Option.bind_some]
  conv => lhs; rw [← (sh s₀).val_defaultVal hv]
  rw [← List.map_replicate, ← List.map_append, arrayNewFixed?_reloc]

end Instr

theorem constInstr?_reloc (t : Store H) (f : Frame) (vs : List Val) (i : Instr) :
    constInstr? (reloc s₀ t) ((sh s₀).frame f) (vs.map (sh s₀).val) i =
      (constInstr? t f vs i).map (relSV s₀) := by
  cases i with
  | refFunc x =>
    simp only [constInstr?, Shift.frame_module, Shift.minst_funcs, List.getElem?_map,
      Option.bind_eq_bind]
    cases f.module.funcs[x.toNat]? <;> simp [relSV]
  | refI31 =>
    simp only [constInstr?, pop1?_map, Option.bind_eq_bind]
    rcases pop1? vs with _ | ⟨pre, v⟩
    · rfl
    simp only [Option.map_some, Option.bind_some, Shift.int?_val]
    cases v.int? .i32 <;> simp [relSV]
  | globalGet x =>
    simp only [constInstr?, global?_reloc, Option.bind_eq_bind]
    cases t.global? f x <;> simp [relSV, Shift.ginst]
  | intBinOp tt op => exact constInstr?_reloc_intBinOp s₀ t f vs tt op
  | anyConvertExtern => exact constInstr?_reloc_anyConvertExtern s₀ t f vs
  | externConvertAny => exact constInstr?_reloc_externConvertAny s₀ t f vs
  | structNew x => exact structNew?_reloc s₀ t f vs x
  | structNewDefault x => exact constInstr?_reloc_structNewDefault s₀ t f vs x
  | arrayNew x => exact constInstr?_reloc_arrayNew s₀ t f vs x
  | arrayNewDefault x => exact constInstr?_reloc_arrayNewDefault s₀ t f vs x
  | arrayNewFixed x n => exact arrayNewFixed?_reloc s₀ t f vs x n
  | _ => simp [constInstr?, relSV]

end Const

/-! ## Initialiser runs -/

section Eval

variable (s₀ : Store H)

theorem constExpr?_reloc (t : Store H) (f : Frame) (e : Expr) :
    constExpr? (reloc s₀ t) ((sh s₀).frame f) e = (constExpr? t f e).map (relSV s₀) := by
  unfold constExpr?
  suffices ∀ (vs : List Val) (t : Store H),
      e.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 ((sh s₀).frame f) st.2 i)
          (reloc s₀ t, vs.map (sh s₀).val) =
        (e.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 f st.2 i) (t, vs)).map
          (relSV s₀) from this [] t
  induction e with
  | nil => intro vs t; rfl
  | cons i e ih =>
    intro vs t
    simp only [List.foldlM_cons, constInstr?_reloc, Option.bind_eq_bind]
    cases constInstr? t f vs i with
    | none => rfl
    | some p => exact ih p.2 p.1

/-- The relocation of a store and a value. -/
abbrev relSV1 (p : Store H × Val) : Store H × Val := (reloc s₀ p.1, (sh s₀).val p.2)

theorem evalConst?_reloc (t : Store H) (f : Frame) (e : Expr) :
    evalConst? (reloc s₀ t) ((sh s₀).frame f) e = (evalConst? t f e).map (relSV1 s₀) := by
  unfold evalConst?
  rw [constExpr?_reloc]
  rcases constExpr? t f e with _ | ⟨t', _ | ⟨v, _ | _⟩⟩ <;> rfl

theorem allocGlobal_reloc (t : Store H) (g : CGlobalType) (v : Val) :
    allocGlobal (reloc s₀ t) g ((sh s₀).val v) =
      (reloc s₀ (allocGlobal t g v).1, (sh s₀).gl + (allocGlobal t g v).2) := by
  simp [allocGlobal, reloc, Store.app, Shift.store, Shift.ginst, Shift.ofStore]

theorem frame_withGlobal (f : Frame) (a : Nat) :
    { (sh s₀).frame f with module := { ((sh s₀).frame f).module with
        globals := ((sh s₀).frame f).module.globals ++ [(sh s₀).gl + a] } } =
      (sh s₀).frame { f with module := { f.module with globals := f.module.globals ++ [a] } } := by
  simp [Shift.frame, Shift.minst]

/-- The relocation of the result of `$evalglobals`. -/
abbrev relG (p : Store H × Frame × List Val) : Store H × Frame × List Val :=
  (reloc s₀ p.1, (sh s₀).frame p.2.1, p.2.2.map (sh s₀).val)

theorem evalGlobals?_reloc (t : Store H) (f : Frame) (gs : List CGlobalType) (es : List Expr) :
    evalGlobals? evalConst? (reloc s₀ t) ((sh s₀).frame f) gs es =
      (evalGlobals? evalConst? t f gs es).map (relG s₀) := by
  induction gs generalizing t f es with
  | nil => cases es <;> rfl
  | cons g gs ih =>
    cases es with
    | nil => rfl
    | cons e es =>
      simp only [evalGlobals?, evalConst?_reloc]
      rcases evalConst? t f e with _ | ⟨t', v⟩
      · rfl
      · simp only [Option.map_some, relSV1, allocGlobal_reloc, frame_withGlobal, ih]
        rcases evalGlobals? evalConst? (allocGlobal t' g v).1 _ gs es with _ | ⟨s'', f'', vs⟩
        · rfl
        · rfl

/-- The relocation of the result of `$evalexprs`. -/
abbrev relE (p : Store H × Frame × List Ref) : Store H × Frame × List Ref :=
  (reloc s₀ p.1, (sh s₀).frame p.2.1, p.2.2.map (sh s₀).ref)

theorem evalExprs?_reloc (t : Store H) (f : Frame) (es : List Expr) :
    evalExprs? evalConst? (reloc s₀ t) ((sh s₀).frame f) es =
      (evalExprs? evalConst? t f es).map (relE s₀) := by
  induction es generalizing t with
  | nil => rfl
  | cons e es ih =>
    simp only [evalExprs?, evalConst?_reloc]
    rcases evalConst? t f e with _ | ⟨t', _ | _ | r⟩
    · rfl
    · rfl
    · rfl
    · simp only [Option.map_some, relSV1, Shift.val_ref, ih]
      rcases evalExprs? evalConst? t' f es with _ | ⟨s'', f'', rs⟩ <;> rfl

/-- The relocation of the result of `$evalexprss`. -/
abbrev relEs (p : Store H × Frame × List (List Ref)) : Store H × Frame × List (List Ref) :=
  (reloc s₀ p.1, (sh s₀).frame p.2.1, p.2.2.map (·.map (sh s₀).ref))

theorem evalExprss?_reloc (t : Store H) (f : Frame) (ess : List (List Expr)) :
    evalExprss? evalConst? (reloc s₀ t) ((sh s₀).frame f) ess =
      (evalExprss? evalConst? t f ess).map (relEs s₀) := by
  induction ess generalizing t f with
  | nil => rfl
  | cons es ess ih =>
    simp only [evalExprss?, evalExprs?_reloc]
    rcases evalExprs? evalConst? t f es with _ | ⟨t', f', rs⟩
    · rfl
    · simp only [Option.map_some, relE, ih]
      rcases evalExprss? evalConst? t' f' ess with _ | ⟨s'', f'', rss⟩ <;> rfl

end Eval

/-! ## Allocation -/

section Alloc

variable (s₀ : Store H)

theorem allocMany_reloc {α β : Type} (alloc₁ : Store H → β → Store H × Nat)
    (alloc₂ : Store H → α → Store H × Nat) (φ : α → β) (off : Nat)
    (h : ∀ t x, alloc₁ (reloc s₀ t) (φ x) = (reloc s₀ (alloc₂ t x).1, off + (alloc₂ t x).2))
    (t : Store H) (xs : List α) :
    allocMany alloc₁ (reloc s₀ t) (xs.map φ) =
      (reloc s₀ (allocMany alloc₂ t xs).1, (allocMany alloc₂ t xs).2.map (off + ·)) := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih => simp only [allocMany, List.map_cons, h, ih]

theorem allocTag_reloc (t : Store H) (d : DefType) :
    allocTag (reloc s₀ t) d = (reloc s₀ (allocTag t d).1, (sh s₀).tg + (allocTag t d).2) := by
  simp [allocTag, reloc, Store.app, Shift.store, Shift.ofStore]

theorem allocMem_reloc (t : Store H) (d : MemoryType) :
    allocMem (reloc s₀ t) d = (reloc s₀ (allocMem t d).1, (sh s₀).me + (allocMem t d).2) := by
  simp [allocMem, reloc, Store.app, Shift.store, Shift.ofStore]

theorem allocTable_reloc (t : Store H) (tt : CTableType) (r : Ref) :
    allocTable (reloc s₀ t) tt ((sh s₀).ref r) =
      (reloc s₀ (allocTable t tt r).1, (sh s₀).ta + (allocTable t tt r).2) := by
  simp [allocTable, reloc, Store.app, Shift.store, Shift.ofStore, Shift.tinst, List.map_replicate]

theorem allocData_reloc (t : Store H) (b : ByteArray) :
    allocData (reloc s₀ t) b = (reloc s₀ (allocData t b).1, (sh s₀).da + (allocData t b).2) := by
  simp [allocData, reloc, Store.app, Shift.store, Shift.ofStore]

theorem allocElem_reloc (t : Store H) (rt : CRefType) (refs : List Ref) :
    allocElem (reloc s₀ t) rt (refs.map (sh s₀).ref) =
      (reloc s₀ (allocElem t rt refs).1, (sh s₀).el + (allocElem t rt refs).2) := by
  simp [allocElem, reloc, Store.app, Shift.store, Shift.ofStore, Shift.einst]

theorem allocFunc_reloc (t : Store H) (d : DefType) (code : FuncCode H) (mi : ModuleInst) :
    allocFunc (reloc s₀ t) d code ((sh s₀).minst mi) =
      (reloc s₀ (allocFunc t d code mi).1, (sh s₀).fn + (allocFunc t d code mi).2) := by
  simp [allocFunc, reloc, Store.app, Shift.store, Shift.ofStore, Shift.finst]

variable (δ : Shift)

theorem tags_map : ∀ xas : List ExternAddr,
    ExternAddr.tags (xas.map δ.xa) = (ExternAddr.tags xas).map (δ.tg + ·)
  | [] => rfl
  | x :: xas => by cases x <;> simp [ExternAddr.tags, Shift.xa, tags_map xas]

theorem globals_map : ∀ xas : List ExternAddr,
    ExternAddr.globals (xas.map δ.xa) = (ExternAddr.globals xas).map (δ.gl + ·)
  | [] => rfl
  | x :: xas => by cases x <;> simp [ExternAddr.globals, Shift.xa, globals_map xas]

theorem mems_map : ∀ xas : List ExternAddr,
    ExternAddr.mems (xas.map δ.xa) = (ExternAddr.mems xas).map (δ.me + ·)
  | [] => rfl
  | x :: xas => by cases x <;> simp [ExternAddr.mems, Shift.xa, mems_map xas]

theorem tables_map : ∀ xas : List ExternAddr,
    ExternAddr.tables (xas.map δ.xa) = (ExternAddr.tables xas).map (δ.ta + ·)
  | [] => rfl
  | x :: xas => by cases x <;> simp [ExternAddr.tables, Shift.xa, tables_map xas]

theorem funcs_map : ∀ xas : List ExternAddr,
    ExternAddr.funcs (xas.map δ.xa) = (ExternAddr.funcs xas).map (δ.fn + ·)
  | [] => rfl
  | x :: xas => by cases x <;> simp [ExternAddr.funcs, Shift.xa, funcs_map xas]

theorem allocExport?_minst (mi : ModuleInst) (e : Export) :
    allocExport? (δ.minst mi) e = (allocExport? mi e).map δ.xinst := by
  unfold allocExport?
  rcases e with ⟨nm, ix⟩
  cases ix <;> simp [Shift.minst, Option.map_map, Function.comp_def, Shift.xinst, Shift.xa]

theorem mapM_map_some {α β : Type} (F : α → Option β) (G : α → Option β) (g : β → β)
    (h : ∀ a, G a = (F a).map g) : ∀ l : List α, l.mapM G = (l.mapM F).map (·.map g)
  | [] => rfl
  | a :: l => by
    simp only [List.mapM_cons, h, mapM_map_some F G g h l, Option.bind_eq_bind]
    cases F a with
    | none => rfl
    | some b =>
      cases l.mapM F with
      | none => rfl
      | some bs => rfl

theorem zip_map_snd {α β : Type} (l : List α) (vs : List β) (g : β → β) :
    l.zip (vs.map g) = (l.zip vs).map fun p => (p.1, g p.2) := by
  rw [List.zip_map_right]
  rfl

theorem reloc_funcs_length (t : Store H) :
    (reloc s₀ t).funcs.length = (sh s₀).fn + t.funcs.length := by
  simp

theorem allocMany_reloc_id {α : Type} (alloc : Store H → α → Store H × Nat) (off : Nat)
    (h : ∀ t x, alloc (reloc s₀ t) x = (reloc s₀ (alloc t x).1, off + (alloc t x).2))
    (t : Store H) (xs : List α) :
    allocMany alloc (reloc s₀ t) xs =
      (reloc s₀ (allocMany alloc t xs).1, (allocMany alloc t xs).2.map (off + ·)) := by
  simpa using allocMany_reloc s₀ alloc alloc id off h t xs

theorem exportsInst_minst (δ : Shift) (A₁ B₁ A₂ B₂ A₃ B₃ A₄ B₄ A₅ R : List Nat) (c : Nat) :
    ({ tags := A₁.map (fun x => δ.tg + x) ++ B₁.map (fun x => δ.tg + x)
       globals := A₂.map (fun x => δ.gl + x) ++ B₂.map (fun x => δ.gl + x)
       mems := A₃.map (fun x => δ.me + x) ++ B₃.map (fun x => δ.me + x)
       tables := A₄.map (fun x => δ.ta + x) ++ B₄.map (fun x => δ.ta + x)
       funcs := A₅.map (fun x => δ.fn + x) ++ R.map (fun x => δ.fn + c + x) } : ModuleInst) =
      δ.minst { tags := A₁ ++ B₁, globals := A₂ ++ B₂, mems := A₃ ++ B₃, tables := A₄ ++ B₄
                funcs := A₅ ++ R.map (fun x => c + x) } := by
  simp [Shift.minst, Function.comp_def, Nat.add_assoc]

theorem moduleInst_minst (δ : Shift) (dts : List DefType)
    (A₁ B₁ A₂ B₂ A₃ B₃ A₄ B₄ A₅ R D E : List Nat) (c : Nat) (X : List ExportInst) :
    ({ types := dts
       tags := A₁.map (fun x => δ.tg + x) ++ B₁.map (fun x => δ.tg + x)
       globals := A₂.map (fun x => δ.gl + x) ++ B₂.map (fun x => δ.gl + x)
       mems := A₃.map (fun x => δ.me + x) ++ B₃.map (fun x => δ.me + x)
       tables := A₄.map (fun x => δ.ta + x) ++ B₄.map (fun x => δ.ta + x)
       funcs := A₅.map (fun x => δ.fn + x) ++ R.map (fun x => δ.fn + c + x)
       datas := D.map (fun x => δ.da + x)
       elems := E.map (fun x => δ.el + x)
       exports := X.map δ.xinst } : ModuleInst) =
      δ.minst { types := dts, tags := A₁ ++ B₁, globals := A₂ ++ B₂, mems := A₃ ++ B₃
                tables := A₄ ++ B₄, funcs := A₅ ++ R.map (fun x => c + x), datas := D, elems := E
                exports := X } := by
  simp [Shift.minst, Function.comp_def, Nat.add_assoc]

theorem allocMany_reloc₂ {α : Type} (alloc₁ alloc₂ : Store H → α → Store H × Nat) (off : Nat)
    (h : ∀ t x, alloc₁ (reloc s₀ t) x = (reloc s₀ (alloc₂ t x).1, off + (alloc₂ t x).2))
    (t : Store H) (xs : List α) :
    allocMany alloc₁ (reloc s₀ t) xs =
      (reloc s₀ (allocMany alloc₂ t xs).1, (allocMany alloc₂ t xs).2.map (off + ·)) := by
  simpa using allocMany_reloc s₀ alloc₁ alloc₂ id off h t xs

theorem allocModule?_reloc (t : Store H) (m : Module) (xas : List ExternAddr) (valsG : List Val)
    (refsT : List Ref) (refsE : List (List Ref)) :
    allocModule? (reloc s₀ t) m (xas.map (sh s₀).xa) (valsG.map (sh s₀).val)
        (refsT.map (sh s₀).ref) (refsE.map (·.map (sh s₀).ref)) =
      (allocModule? t m xas valsG refsT refsE).map
        fun p => (reloc s₀ p.1, (sh s₀).minst p.2) := by
  simp only [allocModule?, Option.bind_eq_bind, zip_map_snd, reloc_funcs_length,
    allocMany_reloc_id s₀ allocTag _ (allocTag_reloc s₀),
    allocMany_reloc s₀ (fun s (p : CGlobalType × Val) => allocGlobal s p.1 p.2)
      (fun s (p : CGlobalType × Val) => allocGlobal s p.1 p.2) (fun p => (p.1, (sh s₀).val p.2))
      _ (fun t p => allocGlobal_reloc s₀ t p.1 p.2),
    allocMany_reloc_id s₀ allocMem _ (allocMem_reloc s₀),
    allocMany_reloc s₀ (fun s (p : CTableType × Ref) => allocTable s p.1 p.2)
      (fun s (p : CTableType × Ref) => allocTable s p.1 p.2) (fun p => (p.1, (sh s₀).ref p.2))
      _ (fun t p => allocTable_reloc s₀ t p.1 p.2),
    allocMany_reloc_id s₀ allocData _ (allocData_reloc s₀),
    allocMany_reloc s₀ (fun s (p : CRefType × List Ref) => allocElem s p.1 p.2)
      (fun s (p : CRefType × List Ref) => allocElem s p.1 p.2)
      (fun p => (p.1, p.2.map (sh s₀).ref)) _ (fun t p => allocElem_reloc s₀ t p.1 p.2),
    tags_map, globals_map, mems_map, tables_map, funcs_map, exportsInst_minst,
    mapM_map_some _ _ _ (allocExport?_minst (sh s₀) _)]
  generalize m.tags.mapM (fun x => (allocTypes m.types)[x.toNat]?) = T
  rcases T with _ | tagTypes
  · rfl
  simp only [Option.bind_some]
  generalize m.funcs.mapM (fun fn => (allocTypes m.types)[fn.type.toNat]?) = F
  rcases F with _ | funcTypes
  · rfl
  simp only [Option.bind_some]
  generalize List.mapM (allocExport? _) m.exports = X
  rcases X with _ | xi
  · rfl
  simp only [Option.map_some, Option.bind_some, Option.pure_def, moduleInst_minst,
    allocMany_reloc₂ s₀ (fun s (p : DefType × Func) => allocFunc s p.1 (.wasm p.2) ((sh s₀).minst _))
      (fun s (p : DefType × Func) => allocFunc s p.1 (.wasm p.2) _) _
      (fun t p => allocFunc_reloc s₀ t p.1 (.wasm p.2) _)]

end Alloc

/-! ## Instantiation -/

section Inst

variable (s₀ : Store H)

theorem frame_initial (t : Store H) (m : Module) (xas : List ExternAddr) :
    (⟨[], ModuleInst.initial (reloc s₀ t) m (xas.map (sh s₀).xa)⟩ : Frame) =
      (sh s₀).frame ⟨[], ModuleInst.initial t m xas⟩ := by
  simp [ModuleInst.initial, Shift.frame, Shift.minst, globals_map, funcs_map, Function.comp_def,
    Nat.add_assoc]

/-- The relocation of a configuration. -/
def relC (c : Config H) : Config H := ⟨reloc s₀ c.store, (sh s₀).frame c.frame, c.code⟩

theorem prepare?_reloc (t : Store H) (m : Module) (xas : List ExternAddr) :
    prepare? evalConst? (reloc s₀ t) m (xas.map (sh s₀).xa) =
      (prepare? evalConst? t m xas).map fun p => (relC s₀ p.1, p.2) := by
  unfold prepare?
  split_ifs
  · rw [frame_initial, evalGlobals?_reloc]
    rcases evalGlobals? evalConst? t _ _ _ with _ | ⟨s₁, f₁, valsG⟩
    · rfl
    · simp only [Option.map_some, relG]
      rw [evalExprs?_reloc]
      rcases evalExprs? evalConst? s₁ f₁ _ with _ | ⟨s₂, f₂, refsT⟩
      · rfl
      · simp only [Option.map_some, relE]
        rw [evalExprss?_reloc]
        rcases evalExprss? evalConst? s₂ f₂ _ with _ | ⟨s₃, f₃, refsE⟩
        · rfl
        · simp only [Option.map_some, relEs]
          rw [allocModule?_reloc]
          rcases allocModule? s₃ m xas valsG refsT refsE with _ | ⟨s₄, mi⟩ <;> rfl
  · rfl

/-- **Without segments, direct instantiation commutes with relocation.** -/
theorem instantiateDirect?_reloc (t : Store H) (m : Module) (xas : List ExternAddr)
    (hseg : m.data = [] ∧ m.elems = []) :
    instantiateDirect? (reloc s₀ t) m (xas.map (sh s₀).xa) =
      (instantiateDirect? t m xas).map fun p => (reloc s₀ p.1, (sh s₀).frame p.2.1, p.2.2) := by
  simp only [instantiateDirect?, prepareDirect?, prepare?_reloc]
  rcases prepare? evalConst? t m xas with _ | ⟨c, st⟩
  · rfl
  · simp [initSegments?, initElem?, initData?, initElemList?, initDataList?, hseg.1, hseg.2,
      relC]

theorem globalAddrs_reloc (t : Store H) (k : Nat) :
    globalAddrs (reloc s₀ t).globals.length k =
      (globalAddrs t.globals.length k).map (sh s₀).xa := by
  simp [globalAddrs, Shift.xa, Function.comp_def, Nat.add_assoc]

/-- **Instantiating after an existing store is instantiating alone, relocated**, for modules
without data and element segments: in `reloc s₀ t` against the shifted external addresses,
`instantiateOnce?` gives the relocated store and frame of its run in `t`. -/
theorem instantiateOnce?_reloc (t : Store H) (m : Module) (xas : List ExternAddr)
    (hseg : m.data = [] ∧ m.elems = []) :
    instantiateOnce? (reloc s₀ t) m (xas.map (sh s₀).xa) =
      (instantiateOnce? t m xas).map fun p => (reloc s₀ p.1, (sh s₀).frame p.2.1, p.2.2) := by
  unfold instantiateOnce?
  rw [frame_initial, evalGlobals?_reloc]
  rcases evalGlobals? evalConst? t _ _ _ with _ | ⟨s₁, f₁, vs⟩
  · rfl
  · simp only [Option.map_some, relG]
    rw [globalAddrs_reloc, ← List.map_append]
    exact instantiateDirect?_reloc s₀ s₁ _ _ hseg

end Inst
