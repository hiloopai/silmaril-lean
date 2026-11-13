module

public import Silmaril.Wasm.Jco.Styles.Lime.Defs
public import Silmaril.Wasm.Lime1.Validation.Modules

/-!
# Validation of `adaptorLime md` for every world: proofs

`adaptorLime_limeValid`: the adaptor of the first FFI style is a valid **Lime1** module for every
world whose imported names are distinct, with no world function named `cabi_realloc`, whose
functions have fewer than `2^32 - 2` flat parameters, and whose two function index spaces fit
(`2 * |world| + 2 < 2^32`: the shim of world function `i` has type and function index
`|world| + 2 + i`).

The proof types each function body by backward typing steps (`t_get`, `t_call`, …): each takes
the typing of the rest of the body on the new stack. The module context's function types are
the module's types (`funcs_eq`), because every import and function points at its own type.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Real.ValidAll

open Silmaril.Wasm
open Silmaril.Wasm.Lime1.Validation
open Silmaril.Wasm.Jco

/-- `i32` as a Lime1 value type. -/
abbrev I32 : Lime1.ValType := .int .i32

theorem mkIdx_toNat {k : IndexKind} (n : Nat) : (mkIdx n : Idx k).toNat = n % 2 ^ 32 := rfl

/-! ## Backward typing steps -/

section Steps

variable {C : Context} {is : List Lime1.Instr} {a st c : Lime1.ResultType}

theorem t_get {i : LocalIdx} {t : Lime1.ValType} (h : C.locals[i.toNat]? = some t)
    (k : ExprType C is (st ++ [t]) c) : ExprType C (.localGet i :: is) st c := by
  have hi := InstrType.frame st (InstrType.localGet (C := C) i h)
  rw [List.append_nil] at hi
  exact .cons hi k

theorem t_set {i : LocalIdx} {t : Lime1.ValType} (h : C.locals[i.toNat]? = some t)
    (ha : a = st ++ [t]) (k : ExprType C is st c) : ExprType C (.localSet i :: is) a c := by
  have hi := InstrType.frame st (InstrType.localSet (C := C) i h)
  rw [List.append_nil] at hi
  exact ha ▸ .cons hi k

theorem t_const (t : IntType) (b : BitVec t.width) (k : ExprType C is (st ++ [.int t]) c) :
    ExprType C (.intConst t b :: is) st c := by
  have hi := InstrType.frame st (InstrType.intConst (C := C) t b)
  rw [List.append_nil] at hi
  exact .cons hi k

theorem t_call {i : FuncIdx} {ft : Lime1.FuncType} (h : C.funcs[i.toNat]? = some ft)
    (ha : a = st ++ ft.params) (k : ExprType C is (st ++ ft.results) c) :
    ExprType C (.call i :: is) a c :=
  ha ▸ .cons (InstrType.frame st (InstrType.call i h)) k

theorem t_eqz (ha : a = st ++ [I32]) (k : ExprType C is (st ++ [I32]) c) :
    ExprType C (.intTestOp .i32 .eqz :: is) a c :=
  ha ▸ .cons (InstrType.frame st (InstrType.intTestOp .i32 .eqz)) k

theorem t_ltu (ha : a = st ++ [I32, I32]) (k : ExprType C is (st ++ [I32]) c) :
    ExprType C (.intRelOp .i32 (.lt .unsigned) :: is) a c :=
  ha ▸ .cons (InstrType.frame st (InstrType.intRelOp .i32 (.lt .unsigned))) k

theorem t_select (t : Lime1.ValType) (ha : a = st ++ [t, t, I32]) (k : ExprType C is (st ++ [t]) c) :
    ExprType C (.select :: is) a c :=
  ha ▸ .cons (InstrType.frame st (InstrType.select t)) k

theorem t_copy (hm : C.memories ≠ []) (ha : a = st ++ [I32, I32, I32]) (k : ExprType C is st c) :
    ExprType C (.memoryCopy :: is) a c := by
  have hi := InstrType.frame st (InstrType.memoryCopy (C := C) hm)
  rw [List.append_nil] at hi
  exact ha ▸ .cons hi k

theorem t_if {l r : List Lime1.Instr}
    (hl : ExprType (C.withLabel [I32]) l [] [I32]) (hr : ExprType (C.withLabel [I32]) r [] [I32])
    (ha : a = st ++ [I32]) (k : ExprType C is (st ++ [I32]) c) :
    ExprType C (.if_ (.value I32) l r :: is) a c :=
  ha ▸ .cons (InstrType.frame st (InstrType.if_ (ft := ⟨[], [I32]⟩) (.value I32) rfl hl hr)) k

theorem t_end (ha : a = c) : ExprType C [] a c := ha ▸ .nil a

/-- `local.get 0 … local.get (n - 1)` pushes the first `n` locals. -/
theorem t_gets (n : Nat) (hn : n ≤ C.locals.length) (hb : n ≤ 2 ^ 32) (st : Lime1.ResultType)
    (k : ExprType C is (st ++ C.locals.take n) c) :
    ExprType C ((List.range n).map (fun j => Lime1.Instr.localGet (mkIdx j)) ++ is) st c := by
  induction n generalizing is with
  | zero => simpa using k
  | succ n ih =>
    have hlt : n < C.locals.length := by omega
    have hget : C.locals[(mkIdx n : LocalIdx).toNat]? = some C.locals[n] := by
      rw [mkIdx_toNat, Nat.mod_eq_of_lt (by omega)]
      exact List.getElem?_eq_getElem hlt
    rw [List.range_succ, List.map_append, List.append_assoc]
    refine ih (by omega) (by omega) (t_get hget ?_)
    rwa [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, ← List.append_assoc]
      at k

end Steps

/-! ## Bodies -/

theorem toLimeL_eq (fi : String → Nat) (l : List XInstr) :
    XInstr.toLimeL fi l = l.map (XInstr.toLime fi) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [XInstr.toLimeL, ih, List.map_cons]

theorem afn_body (fi : String → Nat) (fn : AFn) (ty : Nat) :
    (fn.toX.toLime fi ty).body = fn.body.map (AInstr.toLime fi) := by
  simp only [XFn.toLime, AFn.toX, toLimeL_eq, List.map_map]
  rfl

theorem gets_toLime (fi : String → Nat) (n : Nat) :
    (gets n).map (AInstr.toLime fi) = (List.range n).map fun j => Lime1.Instr.localGet (mkIdx j) := by
  simp only [gets, List.map_map]
  rfl

/-! ## The type and function index spaces -/

/-- The types of an adaptor module: the allocator, the callees (`cT`), `cabi_realloc`, the shims
(`sT`). -/
def Tg (cT sT : Sig → Lime1.FuncType) (md : Meta) : List Lime1.FuncType :=
  allocType :: md.world.map cT ++ reallocType :: md.world.map sT

/-- The types of `adaptorLime md`. -/
abbrev T (md : Meta) : List Lime1.FuncType := Tg calleeType shimType md

/-- The imports of an adaptor module: the memory, the allocator, the world's functions. -/
def stdImports (md : Meta) : List Lime1.Import :=
  ⟨"m", "memory", .memory ⟨⟨0, none⟩⟩⟩ :: ⟨"m", md.alloc, .func (mkIdx 0)⟩ ::
    (md.world.zipIdx.map fun (s, i) => ⟨"m", s.name, .func (mkIdx (i + 1))⟩)

/-- The exports of an adaptor module: `cabi_realloc`, then the shims. -/
def stdExports (md : Meta) : List Lime1.Export :=
  ⟨"cabi_realloc", .func (mkIdx (md.world.length + 1))⟩ ::
    (md.world.zipIdx.map fun (s, i) => ⟨s.name, .func (mkIdx (md.world.length + 2 + i))⟩)

theorem types_eq (md : Meta) : (adaptorLime md).types = T md := rfl

section Index

variable {cT sT : Sig → Lime1.FuncType}

theorem T_callee (md : Meta) {i : Nat} (hi : i < md.world.length) :
    (Tg cT sT md)[i + 1]? = some (cT md.world[i]) := by
  rw [Tg, List.getElem?_append_left (by simpa using hi), List.getElem?_cons_succ,
    List.getElem?_map, List.getElem?_eq_getElem hi]
  rfl

theorem T_realloc (md : Meta) : (Tg cT sT md)[md.world.length + 1]? = some reallocType := by
  rw [Tg, List.getElem?_append_right (by simp), List.length_cons, List.length_map, Nat.sub_self]
  rfl

theorem T_shim (md : Meta) {i : Nat} (hi : i < md.world.length) :
    (Tg cT sT md)[md.world.length + 2 + i]? = some (sT md.world[i]) := by
  rw [Tg, List.getElem?_append_right (by simp; omega), List.length_cons, List.length_map,
    show md.world.length + 2 + i - (md.world.length + 1) = i + 1 by omega,
    List.getElem?_cons_succ, List.getElem?_map, List.getElem?_eq_getElem hi]
  rfl

/-- `filterMap` over an indexed list that never fails. -/
theorem filterMap_zipIdx {α β : Type} (l : List α) (f : α × Nat → Option β) (g : α → β)
    (h : ∀ i (hi : i < l.length), f (l[i], i) = some (g l[i])) :
    l.zipIdx.filterMap f = l.map g := by
  rw [(List.filterMap_eq_map_iff_forall_eq_some (g := g ∘ Prod.fst)).mpr ?_, ← List.map_map,
    List.zipIdx_map_fst]
  rintro ⟨x, i⟩ hx
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 (List.mk_mem_zipIdx_iff_getElem?.1 hx)
  exact h i hi

/-- An adaptor module: the standard imports and exports, types `Tg cT sT md`, and functions
`cabi_realloc` (`f0`) and the shims (`F`) at their own type indices. -/
structure Shape (m : Lime1.Module) (cT sT : Sig → Lime1.FuncType) (md : Meta) (f0 : Lime1.Func)
    (F : Sig × Nat → Lime1.Func) : Prop where
  types : m.types = Tg cT sT md
  imports : m.imports = stdImports md
  exports : m.exports = stdExports md
  funcs : m.funcs = f0 :: md.world.zipIdx.map F
  ty0 : f0.type = mkIdx (md.world.length + 1)
  tyF : ∀ p, (F p).type = mkIdx (md.world.length + 2 + p.2)
  tables : m.tables = []
  memories : m.memories = []
  globals : m.globals = []
  elems : m.elems = []
  data : m.data = []
  start : m.start = none

variable {m : Lime1.Module} {md : Meta} {f0 : Lime1.Func} {F : Sig × Nat → Lime1.Func}

/-- **The function types of the module context are the module's types.** -/
theorem funcs_eq (h : Shape m cT sT md f0 F) (hw : 2 * md.world.length + 2 < 2 ^ 32) :
    (moduleContext m).funcs = Tg cT sT md := by
  have hA : (Tg cT sT md)[(mkIdx 0 : TypeIdx).toNat]? = some allocType := rfl
  have hR : (Tg cT sT md)[(mkIdx (md.world.length + 1) : TypeIdx).toNat]? = some reallocType := by
    rw [mkIdx_toNat, Nat.mod_eq_of_lt (show md.world.length + 1 < 2 ^ 32 by omega)]
    exact T_realloc md
  simp only [moduleContext, h.types, h.imports, h.funcs, stdImports, List.filterMap_cons,
    List.filterMap_map, h.ty0, hA, hR]
  rw [filterMap_zipIdx _ _ cT, filterMap_zipIdx _ _ sT]
  · rfl
  · intro i hi
    show (Tg cT sT md)[(F (md.world[i], i)).type.toNat]? = _
    rw [h.tyF, mkIdx_toNat, Nat.mod_eq_of_lt (show md.world.length + 2 + i < 2 ^ 32 by omega)]
    exact T_shim md hi
  · intro i hi
    show (Tg cT sT md)[(mkIdx (i + 1) : TypeIdx).toNat]? = _
    rw [mkIdx_toNat, Nat.mod_eq_of_lt (show i + 1 < 2 ^ 32 by omega)]
    exact T_callee md hi

end Index

/-- `adaptorLime md` has the adaptor shape. -/
theorem shape_adaptorLime (md : Meta) :
    Shape (adaptorLime md) calleeType shimType md
      ((reallocShimX md.alloc).toLime (funcIdxOf md) (md.world.length + 1))
      (fun (s, i) => (exportShim md s).toX.toLime (funcIdxOf md) (md.world.length + 2 + i)) where
  types := rfl
  imports := rfl
  exports := rfl
  funcs := rfl
  ty0 := rfl
  tyF := fun ⟨_, _⟩ => rfl
  tables := rfl
  memories := rfl
  globals := rfl
  elems := rfl
  data := rfl
  start := rfl

/-! ## The functions -/

/-- **`cabi_realloc` (with `if`, `select` and `memory.copy`) is well typed** in every context
whose function at the allocator's index is the allocator and which has a memory. -/
theorem realloc_valid (C : Context) (md : Meta) (ty : Nat)
    (hT : C.types[(mkIdx ty : TypeIdx).toNat]? = some reallocType)
    (hA : C.funcs[(mkIdx (funcIdxOf md md.alloc) : FuncIdx).toNat]? = some allocType)
    (hm : C.memories ≠ []) :
    FuncValid C ((reallocShimX md.alloc).toLime (funcIdxOf md) ty) := by
  refine ⟨reallocType, hT, trivial, ?_⟩
  simp only [XFn.toLime, reallocShimX, XInstr.toLimeL, XInstr.toLime, AInstr.toLime]
  exact t_get (t := I32) rfl <| t_eqz (st := []) rfl <|
    t_if (st := []) (t_get (t := I32) rfl <| t_get (t := I32) rfl <| t_call (st := []) hA rfl <|
        t_end rfl)
      (t_get (t := I32) rfl <| t_get (t := I32) rfl <| t_call (st := []) hA rfl <|
        t_set (t := I32) (st := []) rfl rfl <| t_get (t := I32) rfl <| t_get (t := I32) rfl <|
        t_get (t := I32) rfl <| t_get (t := I32) rfl <| t_get (t := I32) rfl <|
        t_get (t := I32) rfl <| t_ltu (st := [I32, I32, I32, I32]) rfl <|
        t_select I32 (st := [I32, I32]) rfl <| t_copy hm (st := []) rfl <|
        t_get (t := I32) rfl <| t_end rfl) rfl <|
    t_end rfl

/-- The shim of a function with a memory result: allocate the out-pointer, forward, return it. -/
theorem outShim_valid (C : Context) (md : Meta) (s : Sig) (ty : Nat)
    (hm : inMem s.result = true)
    (hT : C.types[(mkIdx ty : TypeIdx).toNat]? = some (shimType s))
    (hA : C.funcs[(mkIdx (funcIdxOf md md.alloc) : FuncIdx).toNat]? = some allocType)
    (hS : C.funcs[(mkIdx (funcIdxOf md s.name) : FuncIdx).toNat]? = some (calleeType s))
    (hb : (flatParams s.params).length + 2 < 2 ^ 32) :
    FuncValid C ((exportShim md s).toX.toLime (funcIdxOf md) ty) := by
  have hsT : shimType s = ⟨flatParams s.params, [I32]⟩ := by simp [shimType, hm]
  have hcT : calleeType s = ⟨flatParams s.params ++ [I32], []⟩ := by simp [calleeType, hm]
  have he : exportShim md s =
      { params := (flatParams s.params).length, locals := 1,
        body := outShimBody md.alloc s.name (flatParams s.params).length } := by
    simp [exportShim, hm]
  rw [hsT] at hT
  rw [hcT] at hS
  refine ⟨_, hT, trivial, ?_⟩
  rw [afn_body, he]
  simp only [outShimBody, List.map_append, gets_toLime, List.map_cons, List.map_nil,
    AInstr.toLime, List.cons_append, List.nil_append]
  have hloc : (flatParams s.params ++ [I32])[(mkIdx (flatParams s.params).length : LocalIdx).toNat]?
      = some I32 := by
    rw [mkIdx_toNat, Nat.mod_eq_of_lt (by omega)]
    simp
  exact t_const .i32 _ <| t_const .i32 _ <| t_call (st := []) hA rfl <|
    t_set (st := []) hloc rfl <|
    t_gets _ (by simp [functionContext, XFn.toLime, AFn.toX]) (by omega) [] <|
    t_call (st := []) hS (by simp [functionContext, XFn.toLime, AFn.toX]) <|
    t_get hloc <| t_end rfl

/-- The shim of a function with a flat result: forward the parameters. -/
theorem flatShim_valid (C : Context) (md : Meta) (s : Sig) (ty : Nat)
    (hm : inMem s.result = false)
    (hT : C.types[(mkIdx ty : TypeIdx).toNat]? = some (shimType s))
    (hS : C.funcs[(mkIdx (funcIdxOf md s.name) : FuncIdx).toNat]? = some (calleeType s))
    (hb : (flatParams s.params).length + 2 < 2 ^ 32) :
    FuncValid C ((exportShim md s).toX.toLime (funcIdxOf md) ty) := by
  have hcT : calleeType s = shimType s := by simp [calleeType, hm]
  have hsT : (shimType s).params = flatParams s.params := by
    unfold shimType; split <;> rfl
  have he : exportShim md s =
      { params := (flatParams s.params).length,
        body := gets (flatParams s.params).length ++
          [.call s.name (flatParams s.params).length] } := by
    simp [exportShim, hm]
  rw [hcT] at hS
  refine ⟨_, hT, trivial, ?_⟩
  rw [afn_body, he]
  simp only [List.map_append, gets_toLime, List.map_cons, List.map_nil, AInstr.toLime]
  exact t_gets _ (by simp [functionContext, hsT]) (by omega) [] <|
    t_call (st := []) hS (by simp [functionContext, hsT]) <| t_end (by simp)

/-- **Every export shim is well typed.** -/
theorem shim_valid (C : Context) (md : Meta) (s : Sig) (ty : Nat)
    (hT : C.types[(mkIdx ty : TypeIdx).toNat]? = some (shimType s))
    (hA : C.funcs[(mkIdx (funcIdxOf md md.alloc) : FuncIdx).toNat]? = some allocType)
    (hS : C.funcs[(mkIdx (funcIdxOf md s.name) : FuncIdx).toNat]? = some (calleeType s))
    (hb : (flatParams s.params).length + 2 < 2 ^ 32) :
    FuncValid C ((exportShim md s).toX.toLime (funcIdxOf md) ty) := by
  cases hm : inMem s.result
  · exact flatShim_valid C md s ty hm hT hS hb
  · exact outShim_valid C md s ty hm hT hA hS hb

/-! ## The module -/

theorem funcIdxOf_alloc (md : Meta) : funcIdxOf md md.alloc = 0 := by
  simp [funcIdxOf, importNames]

theorem funcIdxOf_world (md : Meta) (hn : (importNames md).Nodup) {i : Nat}
    (hi : i < md.world.length) : funcIdxOf md md.world[i].name = i + 1 := by
  have hl : i + 1 < (importNames md).length := by simp [importNames, hi]
  have hg : (importNames md)[i + 1] = md.world[i].name := by simp [importNames]
  rw [funcIdxOf, ← hg]
  exact List.Nodup.idxOf_getElem hn _ hl

/-- An element of an indexed list. -/
theorem mem_zipIdx {α : Type} {l : List α} {x : α} {i : Nat} (h : (x, i) ∈ l.zipIdx) :
    ∃ hi : i < l.length, l[i] = x :=
  List.getElem?_eq_some_iff.1 (List.mk_mem_zipIdx_iff_getElem?.1 h)

section Module

variable {cT sT : Sig → Lime1.FuncType} {m : Lime1.Module} {md : Meta} {f0 : Lime1.Func}
  {F : Sig × Nat → Lime1.Func} (h : Shape m cT sT md f0 F) (hw : 2 * md.world.length + 2 < 2 ^ 32)

include h hw

/-- The allocator in the module context. -/
theorem ctx_alloc :
    (moduleContext m).funcs[(mkIdx (funcIdxOf md md.alloc) : FuncIdx).toNat]? =
      some allocType := by
  rw [funcs_eq h hw, funcIdxOf_alloc]
  rfl

/-- The callee of world function `i` in the module context. -/
theorem ctx_callee (hn : (importNames md).Nodup) {i : Nat} (hi : i < md.world.length) :
    (moduleContext m).funcs[(mkIdx (funcIdxOf md md.world[i].name) : FuncIdx).toNat]? =
      some (cT md.world[i]) := by
  rw [funcs_eq h hw, funcIdxOf_world md hn hi, mkIdx_toNat,
    Nat.mod_eq_of_lt (show i + 1 < 2 ^ 32 by omega)]
  exact T_callee md hi

omit hw in
theorem ctx_memories : (moduleContext m).memories ≠ [] := by
  simp [moduleContext, h.imports, h.memories, stdImports]

theorem imports_valid : ∀ i ∈ m.imports, ImportValid m.types i := by
  intro im him
  simp only [h.imports, stdImports, List.mem_cons, List.mem_map] at him
  rcases him with rfl | rfl | ⟨⟨s, i⟩, hmem, rfl⟩
  · exact ⟨_, rfl, by simp [ExternTypeValid, MemoryTypeValid, LimitsValid]⟩
  · exact ⟨.func allocType, by rw [h.types]; rfl, trivial⟩
  · obtain ⟨hi, rfl⟩ := mem_zipIdx hmem
    have hc : (Tg cT sT md)[(mkIdx (i + 1) : TypeIdx).toNat]? = some (cT md.world[i]) := by
      rw [mkIdx_toNat, Nat.mod_eq_of_lt (by omega)]
      exact T_callee md hi
    exact ⟨.func (cT md.world[i]), by simp [importType?, h.types, hc], trivial⟩

theorem exports_valid : ∀ e ∈ m.exports, ExportValid (moduleContext m) e := by
  intro e he
  simp only [h.exports, stdExports, List.mem_cons, List.mem_map] at he
  rcases he with rfl | ⟨⟨s, i⟩, hmem, rfl⟩
  · have hT : (Tg cT sT md)[(mkIdx (md.world.length + 1) : FuncIdx).toNat]? =
        some reallocType := by
      rw [mkIdx_toNat, Nat.mod_eq_of_lt (by omega)]
      exact T_realloc md
    exact ⟨.func reallocType, by simp [exportType?, funcs_eq h hw, hT]⟩
  · obtain ⟨hi, rfl⟩ := mem_zipIdx hmem
    have hT : (Tg cT sT md)[(mkIdx (md.world.length + 2 + i) : FuncIdx).toNat]? =
        some (sT md.world[i]) := by
      rw [mkIdx_toNat, Nat.mod_eq_of_lt (by omega)]
      exact T_shim md hi
    exact ⟨.func (sT md.world[i]), by simp [exportType?, funcs_eq h hw, hT]⟩

omit hw in
theorem export_names : m.exports.map V1.Export.name = "cabi_realloc" :: md.world.map (·.name) := by
  simp only [h.exports, stdExports, List.map_cons, List.map_map]
  congr 1
  conv_rhs => rw [← List.zipIdx_map_fst 0 md.world, List.map_map]
  apply List.map_congr_left
  rintro ⟨s, i⟩ _
  rfl

/-- **A module of the adaptor shape is valid when its functions are.** -/
theorem shape_valid (hn : (importNames md).Nodup) (hr : "cabi_realloc" ∉ md.world.map (·.name))
    (hf : ∀ f ∈ m.funcs, FuncValid (moduleContext m) f) : ModuleValid m where
  types _ _ := trivial
  imports := imports_valid h hw
  functions := hf
  tables := by simp [h.tables]
  memories := by simp [h.memories]
  globals := by simp [h.globals]
  elements := by simp [h.elems]
  data := by simp [h.data]
  start := by simp [StartValid, h.start]
  exports := exports_valid h hw
  uniqueExports := by
    rw [export_names h]
    exact List.nodup_cons.2 ⟨hr, (List.nodup_cons.1 hn).2⟩
  singleTable := by simp [moduleContext, h.imports, h.tables, stdImports]
  singleMemory := by simp [moduleContext, h.imports, h.memories, stdImports]

end Module

theorem funcs_valid (md : Meta) (hn : (importNames md).Nodup)
    (hp : ∀ s ∈ md.world, (flatParams s.params).length + 2 < 2 ^ 32)
    (hw : 2 * md.world.length + 2 < 2 ^ 32) :
    ∀ f ∈ (adaptorLime md).funcs, FuncValid (moduleContext (adaptorLime md)) f := by
  have h := shape_adaptorLime md
  intro f hf
  rw [h.funcs, List.mem_cons, List.mem_map] at hf
  rcases hf with rfl | ⟨⟨s, i⟩, hmem, rfl⟩
  · have hT : (T md)[(mkIdx (md.world.length + 1) : TypeIdx).toNat]? = some reallocType := by
      rw [mkIdx_toNat, Nat.mod_eq_of_lt (by omega)]
      exact T_realloc md
    exact realloc_valid _ md _ hT (ctx_alloc h hw) (ctx_memories h)
  · obtain ⟨hi, rfl⟩ := mem_zipIdx hmem
    have hT : (T md)[(mkIdx (md.world.length + 2 + i) : TypeIdx).toNat]? =
        some (shimType md.world[i]) := by
      rw [mkIdx_toNat, Nat.mod_eq_of_lt (by omega)]
      exact T_shim md hi
    exact shim_valid _ md _ _ hT (ctx_alloc h hw) (ctx_callee h hw hn hi)
      (hp _ (List.getElem_mem hi))

/-- **The adaptor of the first FFI style is a valid Lime1 module.** -/
theorem adaptorLime_limeValid (md : Meta) (hn : (importNames md).Nodup)
    (hr : "cabi_realloc" ∉ md.world.map (·.name))
    (hp : ∀ s ∈ md.world, (flatParams s.params).length + 2 < 2 ^ 32)
    (hw : 2 * md.world.length + 2 < 2 ^ 32) :
    ModuleValid (adaptorLime md) :=
  shape_valid (shape_adaptorLime md) hw hn hr (funcs_valid md hn hp hw)

end Silmaril.Proofs.Wasm.Jco.Real.ValidAll
