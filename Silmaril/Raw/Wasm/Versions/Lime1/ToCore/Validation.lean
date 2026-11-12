module

public import Silmaril.Raw.Wasm.Versions.Lime1.Validation
public import Silmaril.Wasm.Lime1.ToCore
public import Silmaril.Wasm.V1.ToCore.DefTypes
public import Silmaril.Wasm.Validation.Modules
public import Silmaril.Wasm.Validation.Instructions.Properties
public import Silmaril.Wasm.Component.Reference.Wasm.Lime1.Validation.FromV1.Thms

@[expose] public section

/-! # Lime1 validation is a subset of Core 3.0 validation

`Context.toCore` maps a Lime1 context to a closed Core context: function types
become their singleton-group defined types (`V1.FuncType.toDefType`), numeric
value types become `Ty.num`, tables are `funcref` tables at address type `i32`,
memories are `i32` memories, all locals are `SET`.

Lime1's instruction-level `frame` rule has no Core counterpart at the
instruction level (Core, like the spec, frames sequences), so single
instructions are transported to `InstrsOk … [i.toCore]`.

The converse fails in general (Core allows `global.get` of earlier defined
immutable globals in initializers), so only the forward direction is stated.
-/

namespace Silmaril.Wasm.Lime1.Validation

open Silmaril.Wasm.Validation

/-- The Core semantic value type of a Lime1 (numeric) value type. -/
abbrev valToC (t : ValType) : CValType := .num t

/-- A Lime1 table type as a closed Core table type (`funcref`, `i32`). -/
def tableToC (t : TableType) : CTableType := ⟨.i32, t.limits.toCore, Silmaril.Wasm.Validation.Ty.funcref⟩

def globalToC (g : GlobalType) : CGlobalType := ⟨g.mutability, .num g.value⟩

/-- The Core context of a Lime1 context. -/
def Silmaril.Wasm.Validation.Context.toCore (C : Silmaril.Wasm.Validation.Context) : Wasm.Validation.Context where
  types := C.types.map V1.FuncType.toDefType
  funcs := C.funcs.map V1.FuncType.toDefType
  tables := C.tables.map tableToC
  mems := C.memories.map V1.MemoryType.toCore
  globals := C.globals.map globalToC
  locals := C.locals.map fun t => ⟨.set, .num t⟩
  labels := C.labels.map (·.map valToC)
  return_ := C.returnType.map (·.map valToC)

@[simp] theorem Silmaril.Wasm.Validation.Context.withLabel_toCore (C : Silmaril.Wasm.Validation.Context) (ts : ResultType) :
    (C.withLabel ts).toCore = C.toCore.withLabel (ts.map valToC) := rfl

/-! ## Helpers -/

@[simp] theorem valToC_eq (t : ValType) : valToC t = Silmaril.Wasm.Validation.Ty.num t := rfl
@[simp] theorem map_valToC (ts : ResultType) : ts.map valToC = ts.map Silmaril.Wasm.Validation.Ty.num := rfl
@[simp] theorem addrI32_valType : AddrType.i32.valType = Silmaril.Wasm.Validation.Ty.num (.int .i32) := rfl
@[simp] theorem ty_i32_eq : Silmaril.Wasm.Validation.Ty.i32 = Silmaril.Wasm.Validation.Ty.num (.int .i32) := rfl
@[simp] theorem v1_i32_eq : V1.ValType.i32 = NumType.int .i32 := rfl

theorem prefix_getElem? {α : Type _} {l₁ l₂ : List α} (h : l₁ <+: l₂) {n : Nat} {a : α}
    (hn : l₁[n]? = some a) : l₂[n]? = some a := by
  obtain ⟨t, rfl⟩ := h
  have hlt : n < l₁.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hn
    cases hn
  rw [List.getElem?_append_left hlt]; exact hn

theorem prefix_map_getElem? {α β : Type _} {f : α → β} {l₁ : List α} {l₂ : List β}
    (h : l₁.map f <+: l₂) {n : Nat} {a : α} (hn : l₁[n]? = some a) : l₂[n]? = some (f a) :=
  prefix_getElem? h (by simp [hn])

/-- A Core context agrees with (the image of) a Lime1 context: its index spaces
extend the images, and locals, labels and return type are exactly the images. -/
structure Agrees (C : Silmaril.Wasm.Validation.Context) (D : Wasm.Validation.Context) : Prop where
  types : C.types.map V1.FuncType.toDefType <+: D.types
  funcs : C.funcs.map V1.FuncType.toDefType <+: D.funcs
  tables : C.tables.map tableToC <+: D.tables
  mems : C.memories.map V1.MemoryType.toCore <+: D.mems
  globals : C.globals.map globalToC <+: D.globals
  locals : D.locals = C.locals.map fun t => ⟨.set, .num t⟩
  labels : D.labels = C.labels.map (·.map valToC)
  return_ : D.return_ = C.returnType.map (·.map valToC)

theorem Agrees.refl (C : Silmaril.Wasm.Validation.Context) : Agrees C C.toCore :=
  ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _,
    List.prefix_refl _, rfl, rfl, rfl⟩

theorem Agrees.withLabel {C : Silmaril.Wasm.Validation.Context} {D : Wasm.Validation.Context} (h : Agrees C D)
    (ts : ResultType) : Agrees (C.withLabel ts) (D.withLabel (ts.map valToC)) :=
  ⟨h.types, h.funcs, h.tables, h.mems, h.globals, h.locals,
    by simp [Silmaril.Wasm.Validation.Context.withLabel, Wasm.Validation.Context.withLabel, h.labels], h.return_⟩

theorem resultOk_map (Δ : TypeCtx) (ts : ResultType) : ResultOk Δ (ts.map valToC) := by
  intro t ht
  simp only [List.mem_map] at ht
  obtain ⟨a, _, rfl⟩ := ht
  exact .num a

theorem withLocals_toTypeCtx : (C : Wasm.Validation.Context) → (xs : List Nat) →
    (lts : List LocalType) → (C.withLocals xs lts).toTypeCtx = C.toTypeCtx
  | C, x :: xs, lt :: lts => by
    rw [Wasm.Validation.Context.withLocals, withLocals_toTypeCtx]; rfl
  | C, [], _ => by simp [Wasm.Validation.Context.withLocals]
  | C, _ :: _, [] => by simp [Wasm.Validation.Context.withLocals]

theorem initLocals_toTypeCtx (C : Wasm.Validation.Context) (xs : List Nat) :
    (C.initLocals xs).toTypeCtx = C.toTypeCtx := withLocals_toTypeCtx _ _ _

@[simp] theorem initLocals_nil (C : Wasm.Validation.Context) : C.initLocals [] = C := by
  simp [Wasm.Validation.Context.initLocals, Wasm.Validation.Context.withLocals]

theorem single_gen {C : Wasm.Validation.Context} {i : Wasm.Instr} {a b : List CValType}
    {xs : List Nat} (h : InstrOk C i ⟨a, xs, b⟩) (hx : ∀ x ∈ xs, ∃ lt, C.locals[x]? = some lt)
    (hb : ResultOk C.toTypeCtx b) : InstrsOk C [i] ⟨a, xs, b⟩ := by
  have hn : InstrsOk (C.initLocals xs) [] ⟨b ++ [], [], b ++ []⟩ :=
    InstrsOk.frame InstrsOk.nil (by rw [initLocals_toTypeCtx]; exact hb)
  simp only [List.append_nil] at hn
  have := InstrsOk.cons h hx hn
  simpa using this

theorem single_plain {C : Wasm.Validation.Context} {i : Wasm.Instr} {a b : List CValType}
    (h : InstrOk C i (.plain a b)) (hb : ResultOk C.toTypeCtx b) : InstrsOk C [i] (.plain a b) :=
  single_gen h (by simp) hb

theorem drop_inits {C : Wasm.Validation.Context} {is : List Wasm.Instr} {a b : List CValType}
    {xs : List Nat} (h : InstrsOk C is ⟨a, xs, b⟩) (ha : ResultOk C.toTypeCtx a)
    (hb : ResultOk C.toTypeCtx b) : InstrsOk C is (.plain a b) :=
  InstrsOk.sub h ⟨ResultSub.refl _ _, ResultSub.refl _ _, by simp⟩ ⟨ha, hb, by simp⟩

theorem blockType_toCore {C : Silmaril.Wasm.Validation.Context} {D : Wasm.Validation.Context} (hA : Agrees C D)
    {bt : BlockType} {ft : FuncType}
    (h : blockType? C bt = some ft) :
    BlockTypeOk D bt.toCore (ft.params.map valToC) (ft.results.map valToC) := by
  cases bt with
  | empty =>
    simp only [blockType?, Option.some.injEq] at h
    subst h; exact .empty
  | value t =>
    simp only [blockType?, Option.some.injEq] at h
    subst h; exact .value (.num t)
  | typeIdx x =>
    simp only [blockType?] at h
    have hd : D.type? x = some ft.toDefType := prefix_map_getElem? hA.types h
    have he := Expand.iff.mpr (V1.FuncType.toDefType_expand ft)
    have := BlockTypeOk.typeIdx hd he
    simpa [Silmaril.Wasm.Validation.Ty.toList_ofList, BlockType.toCore] using this

theorem memArgOk_toCore (arg : MemArg) (N : Nat) (h : Aligned arg N) :
    MemArgOk arg.toCore .i32 N :=
  ⟨h, by show arg.offset.val < 2 ^ 32; exact arg.offset.isLt⟩

theorem mems_zero {C : Silmaril.Wasm.Validation.Context} {D : Wasm.Validation.Context} (hA : Agrees C D)
    (h : C.memories ≠ []) :
    ∃ l, D.mems[(⟨0⟩ : MemIdx).toNat]? = some ⟨.i32, l⟩ := by
  obtain ⟨m, ms, hm⟩ := List.exists_cons_of_ne_nil h
  exact ⟨m.limits.toCore, prefix_map_getElem? (f := V1.MemoryType.toCore) hA.mems
    (by simp [hm, Idx.toNat])⟩

theorem packSize_toCore_width (p : PackSize) : p.toCore.width = p.width := by
  cases p <;> rfl

/-! ## Transport -/

mutual

/-- Single-instruction transport into any agreeing Core context. -/
theorem Silmaril.Wasm.Validation.InstrType.toCore' {C : Silmaril.Wasm.Validation.Context} {D : Wasm.Validation.Context} (hA : Agrees C D)
    {i : Instr} {a b : ResultType} (h : Silmaril.Wasm.Validation.InstrType C i a b) :
    Wasm.Validation.InstrsOk D [i.toCore] (.plain (a.map valToC) (b.map valToC)) := by
  have R := resultOk_map D.toTypeCtx
  match h with
  | .frame pre h' =>
    have := InstrsOk.frame (Silmaril.Wasm.Validation.InstrType.toCore' hA h') (R pre)
    simpa using this
  | .nop => exact single_plain (.parametric .nop) (by simp [ResultOk])
  | .unreachable a b =>
    exact single_plain (.parametric (.unreachable ⟨R a, R b, by simp⟩)) (R b)
  | .drop t => exact single_plain (.parametric (.drop (.num t))) (by simp [ResultOk])
  | .select t =>
    exact single_plain (.parametric (.selectImpl (t' := .num t) (.num t)
      (Sub.refl _ (k := .val) trivial _) trivial)) (R [t])
  | .block bt type hb =>
    have ih := ExprType.toCore' (hA.withLabel _) hb
    exact single_plain (.block (blockType_toCore hA type) ih) (R _)
  | .loop bt type hb =>
    have ih := ExprType.toCore' (hA.withLabel _) hb
    exact single_plain (.loop (blockType_toCore hA type) ih) (R _)
  | .if_ bt type hl hr =>
    have ihl := ExprType.toCore' (hA.withLabel _) hl
    have ihr := ExprType.toCore' (hA.withLabel _) hr
    have := single_plain (.if_ (blockType_toCore hA type) ihl ihr) (R _)
    simpa [Instr.toCore] using this
  | @Silmaril.Wasm.Validation.InstrType.br _ l ts hl pre out =>
    have hl' : D.labels[l.toNat]? = some (ts.map valToC) := by
      rw [hA.labels]; simp [hl]
    have := single_plain (.br hl' ⟨R pre, R out, by simp⟩) (R out)
    simpa [Instr.toCore] using this
  | @Silmaril.Wasm.Validation.InstrType.brIf _ l ts hl =>
    have hl' : D.labels[l.toNat]? = some (ts.map valToC) := by
      rw [hA.labels]; simp [hl]
    have := single_plain (.brIf hl') (R _)
    simpa [Instr.toCore] using this
  | @Silmaril.Wasm.Validation.InstrType.brTable _ ls d ts hd hs pre out =>
    have := single_plain (.brTable (C := D) (ls := ls) (l' := d) (ts := ts.map valToC)
      (fun l hl => ⟨ts.map valToC, by rw [hA.labels]; simp [hs l hl], ResultSub.refl _ _⟩)
      ⟨ts.map valToC, by rw [hA.labels]; simp [hd], ResultSub.refl _ _⟩
      ⟨by simpa using R (pre ++ ts ++ [V1.ValType.i32]), R out, by simp⟩) (R out)
    simpa [Instr.toCore] using this
  | @Silmaril.Wasm.Validation.InstrType.return_ _ ts hr pre out =>
    have hr' : D.return_ = some (ts.map valToC) := by
      rw [hA.return_]; simp [hr]
    have := single_plain (.return_ hr' ⟨R pre, R out, by simp⟩) (R out)
    simpa [Instr.toCore] using this
  | .call f hf =>
    have hf' := prefix_map_getElem? hA.funcs hf
    have := single_plain (.call hf' (Expand.iff.mpr (V1.FuncType.toDefType_expand _))) (by
      simpa using R _)
    simpa [Silmaril.Wasm.Validation.Ty.toList_ofList, Instr.toCore] using this
  | .callIndirect y hy htab =>
    obtain ⟨t, ts, ht⟩ := List.exists_cons_of_ne_nil htab
    have htab' : D.tables[(⟨0⟩ : TableIdx).toNat]? =
        some ⟨.i32, t.limits.toCore, Silmaril.Wasm.Validation.Ty.funcref⟩ :=
      prefix_map_getElem? (f := tableToC) hA.tables (by simp [ht, Idx.toNat])
    have hy' : D.type? y = some (V1.FuncType.toDefType _) := prefix_map_getElem? hA.types hy
    have := single_plain (.callIndirect htab' (Sub.refl _ (k := .ref) trivial _) hy'
      (Expand.iff.mpr (V1.FuncType.toDefType_expand _))) (by simpa using R _)
    simpa [Silmaril.Wasm.Validation.Ty.toList_ofList, Instr.toCore] using this
  | @Silmaril.Wasm.Validation.InstrType.localGet _ x t hx =>
    have hx' : D.locals[x.toNat]? = some ⟨.set, valToC t⟩ := by
      rw [hA.locals]; simp [hx]
    exact single_plain (.variable (.localGet hx')) (R _)
  | @Silmaril.Wasm.Validation.InstrType.localSet _ x t hx =>
    have hx' : D.locals[x.toNat]? = some ⟨.set, valToC t⟩ := by
      rw [hA.locals]; simp [hx]
    exact drop_inits (single_gen (.variable (.localSet hx')) (by simp [hx'])
      (by simp [ResultOk])) (R _) (by simp [ResultOk])
  | @Silmaril.Wasm.Validation.InstrType.localTee _ x t hx =>
    have hx' : D.locals[x.toNat]? = some ⟨.set, valToC t⟩ := by
      rw [hA.locals]; simp [hx]
    exact drop_inits (single_gen (.variable (.localTee hx')) (by simp [hx'])
      (R [t])) (R _) (R _)
  | .globalGet x hx =>
    have hx' := prefix_map_getElem? hA.globals hx
    exact single_plain (.variable (.globalGet hx')) (R _)
  | .globalSet x hx =>
    have hx' := prefix_map_getElem? hA.globals hx
    exact single_plain (.variable (.globalSet hx')) (by simp [ResultOk])
  | .intLoad t p arg hm acc =>
    obtain ⟨l, hl⟩ := mems_zero hA hm
    rcases p with _ | ⟨sz, sx⟩
    · have := single_plain (.memory (.intLoad hl (memArgOk_toCore arg _ acc))) (R [.int t])
      simpa [Instr.toCore, loadPackToCore] using this
    · obtain ⟨hsz, hal⟩ := acc
      have := single_plain (.memory (.intLoadPack (sx := sx) hl
        (by rw [packSize_toCore_width]; exact hsz)
        (by rw [packSize_toCore_width]; exact memArgOk_toCore arg _ hal))) (R [.int t])
      simpa [Instr.toCore, loadPackToCore] using this
  | .floatLoad t arg hm al =>
    obtain ⟨l, hl⟩ := mems_zero hA hm
    have := single_plain (.memory (.floatLoad hl (memArgOk_toCore arg _ al))) (R [.float t])
    simpa [Instr.toCore] using this
  | .intStore t p arg hm acc =>
    obtain ⟨l, hl⟩ := mems_zero hA hm
    rcases p with _ | sz
    · have := single_plain (.memory (.intStore hl (memArgOk_toCore arg _ acc)))
        (by simp [ResultOk])
      simpa [Instr.toCore] using this
    · obtain ⟨hsz, hal⟩ := acc
      have := single_plain (.memory (.intStorePack hl
        (by rw [packSize_toCore_width]; exact hsz)
        (by rw [packSize_toCore_width]; exact memArgOk_toCore arg _ hal))) (by simp [ResultOk])
      simpa [Instr.toCore] using this
  | .floatStore t arg hm al =>
    obtain ⟨l, hl⟩ := mems_zero hA hm
    have := single_plain (.memory (.floatStore hl (memArgOk_toCore arg _ al))) (by simp [ResultOk])
    simpa [Instr.toCore] using this
  | .memorySize hm =>
    obtain ⟨l, hl⟩ := mems_zero hA hm
    have := single_plain (.memory (.memorySize hl)) (R [V1.ValType.i32])
    simpa [Instr.toCore] using this
  | .memoryGrow hm =>
    obtain ⟨l, hl⟩ := mems_zero hA hm
    have := single_plain (.memory (.memoryGrow hl)) (R [V1.ValType.i32])
    simpa [Instr.toCore] using this
  | .memoryFill hm =>
    obtain ⟨l, hl⟩ := mems_zero hA hm
    have := single_plain (.memory (.memoryFill hl)) (by simp [ResultOk])
    simpa [Instr.toCore] using this
  | .memoryCopy hm =>
    obtain ⟨l, hl⟩ := mems_zero hA hm
    have := single_plain (.memory (.memoryCopy hl hl)) (by simp [ResultOk])
    simpa [Instr.toCore, AddrType.min] using this
  | .intConst t bits => exact single_plain (.numeric (.intConst t bits)) (R _)
  | .floatConst t bits => exact single_plain (.numeric (.floatConst t bits)) (R _)
  | .intUnOp t op valid =>
    have hv : op.toCore.valid t = true := by
      cases op <;> simp_all [IntUnOp.toCore, Wasm.IntUnOp.valid, IntUnOpValid,
        packSize_toCore_width]
    exact single_plain (.numeric (.intUnOp hv)) (R _)
  | .intBinOp t op => exact single_plain (.numeric (.intBinOp t op)) (R _)
  | .intTestOp t op =>
    have := single_plain (.numeric (.intTestOp (C := D) t op)) (R [V1.ValType.i32])
    simpa [Instr.toCore] using this
  | .intRelOp t op =>
    have := single_plain (.numeric (.intRelOp (C := D) t op)) (R [V1.ValType.i32])
    simpa [Instr.toCore] using this
  | .floatUnOp t op => exact single_plain (.numeric (.floatUnOp t op)) (R _)
  | .floatBinOp t op => exact single_plain (.numeric (.floatBinOp t op)) (R _)
  | .floatRelOp t op =>
    have := single_plain (.numeric (.floatRelOp (C := D) t op)) (R [V1.ValType.i32])
    simpa [Instr.toCore] using this
  | .convert op => exact single_plain (.numeric (.convert op)) (R _)

/-- Sequence transport into any agreeing Core context. -/
theorem ExprType.toCore' {C : Silmaril.Wasm.Validation.Context} {D : Wasm.Validation.Context} (hA : Agrees C D)
    {es : Expr} {a b : ResultType} (h : ExprType C es a b) :
    Wasm.Validation.InstrsOk D (Expr.toCore es) (.plain (a.map valToC) (b.map valToC)) := by
  match h with
  | .nil ts =>
    have := InstrsOk.frame (C := D) (ts := ts.map valToC) InstrsOk.nil
      (resultOk_map _ ts)
    simpa [Expr.toCore] using this
  | .cons hi his =>
    have := InstrsOk.append (xs₁ := []) (xs₂ := []) (Silmaril.Wasm.Validation.InstrType.toCore' hA hi) (by simp)
      (by rw [initLocals_nil]; exact ExprType.toCore' hA his)
    simpa [Expr.toCore] using this

end

/-- Single-instruction transport. -/
theorem Silmaril.Wasm.Validation.InstrType.toCore {C : Silmaril.Wasm.Validation.Context} {i : Instr} {a b : ResultType} (h : Silmaril.Wasm.Validation.InstrType C i a b) :
    Wasm.Validation.InstrsOk C.toCore [i.toCore] (.plain (a.map valToC) (b.map valToC)) :=
  Silmaril.Wasm.Validation.InstrType.toCore' (Agrees.refl C) h

/-- Sequence transport. -/
theorem ExprType.toCore {C : Silmaril.Wasm.Validation.Context} {es : Expr} {a b : ResultType} (h : ExprType C es a b) :
    Wasm.Validation.InstrsOk C.toCore (Expr.toCore es) (.plain (a.map valToC) (b.map valToC)) :=
  ExprType.toCore' (Agrees.refl C) h

/-! ## Module validation -/

theorem tyOk_ofList_num (Δ : TypeCtx) : (ts : List NumType) → TyOk Δ (Silmaril.Wasm.Validation.Ty.ofList (ts.map Silmaril.Wasm.Validation.Ty.num))
  | [] => .nil
  | t :: ts => .cons (.num t) (tyOk_ofList_num Δ ts)

theorem liftComp_func_toCore (t : FuncType) :
    liftComp (.func t.toCore) =
      .func (Silmaril.Wasm.Validation.Ty.ofList (t.params.map Silmaril.Wasm.Validation.Ty.num)) (Silmaril.Wasm.Validation.Ty.ofList (t.results.map Silmaril.Wasm.Validation.Ty.num)) := by
  simp [liftComp, V1.FuncType.toCore, V1.liftResult_toCore]

theorem tyOk_toDefType (Δ : TypeCtx) (t : FuncType) : TyOk Δ t.toDefType := by
  have h : t.toDefType = .defn (.group (.cons (.sub true .nil
      (.func (Silmaril.Wasm.Validation.Ty.ofList (t.params.map Silmaril.Wasm.Validation.Ty.num)) (Silmaril.Wasm.Validation.Ty.ofList (t.results.map Silmaril.Wasm.Validation.Ty.num)))) .nil)) 0 := by
    simp [V1.FuncType.toDefType, liftRec, V1.FuncType.toCoreRec, liftSub,
      liftComp_func_toCore]
  rw [h]
  exact .defn (.cons (.noSuper (.func (tyOk_ofList_num _ _) (tyOk_ofList_num _ _))) .nil)
    (by simp [Silmaril.Wasm.Validation.Ty.length])

theorem expand_toDefType (t : FuncType) :
    Expand t.toDefType (.func (Silmaril.Wasm.Validation.Ty.ofList (t.params.map Silmaril.Wasm.Validation.Ty.num)) (Silmaril.Wasm.Validation.Ty.ofList (t.results.map Silmaril.Wasm.Validation.Ty.num))) :=
  Expand.iff.mpr (V1.FuncType.toDefType_expand t)

theorem rollGroup_toCoreRec (C : Wasm.Validation.Context) (t : FuncType) :
    C.rollGroup t.toCoreRec = [t.toDefType] := by
  simp [Wasm.Validation.Context.rollGroup, V1.FuncType.rolldt_toCoreRec,
    Silmaril.Wasm.Validation.Ty.substAll_closed (V1.FuncType.toDefType_closed t)]

theorem closeComp_func_toCore (C : Wasm.Validation.Context) (t : FuncType) :
    C.closeComp (.func t.toCore) =
      .func (Silmaril.Wasm.Validation.Ty.ofList (t.params.map Silmaril.Wasm.Validation.Ty.num)) (Silmaril.Wasm.Validation.Ty.ofList (t.results.map Silmaril.Wasm.Validation.Ty.num)) := by
  simp [Wasm.Validation.Context.closeComp, liftComp_func_toCore, Silmaril.Wasm.Validation.Ty.substAll, Silmaril.Wasm.Validation.Ty.subst,
    V1.subst_ofList_num]

theorem typesOk_map : (ts : List FuncType) → (C : Wasm.Validation.Context) →
    TypesOk C (ts.map V1.FuncType.toCoreRec) (ts.map V1.FuncType.toDefType)
  | [], _ => .nil
  | t :: ts, C => by
    have hok : RecTypeOkAt { C with types := C.types ++ C.rollGroup t.toCoreRec }
        t.toCoreRec.types C.types.length := by
      refine .cons (.noSuper ?_) .nil
      rw [closeComp_func_toCore]
      exact .func (tyOk_ofList_num _ _) (tyOk_ofList_num _ _)
    have h := TypesOk.cons hok (typesOk_map ts _)
    rw [rollGroup_toCoreRec] at h
    simpa using h

@[simp] theorem closeVal_num (C : Wasm.Validation.Context) (t : NumType) :
    C.closeVal (.num t) = .num t := rfl

@[simp] theorem closeRef_funcref (C : Wasm.Validation.Context) :
    C.closeRef V1.funcref = Silmaril.Wasm.Validation.Ty.funcref := rfl

@[simp] theorem closeHeap_func (C : Wasm.Validation.Context) :
    C.closeHeap (.abstract .func) = .abs .func := rfl

theorem closeTableType_toCore (C : Wasm.Validation.Context) (t : TableType) :
    C.closeTableType t.toCore = tableToC t := rfl

theorem closeGlobalType_toCore (C : Wasm.Validation.Context) (g : GlobalType) :
    C.closeGlobalType g.toCore = globalToC g := rfl

theorem limits_valid_toCore {l : Limits} {b : Nat} (_hb : b ≤ 2 ^ 32) (h : LimitsValid b l) :
    l.toCore.Valid (min b (2 ^ 32 - 1)) := by
  obtain ⟨hmin, hmax⟩ := h
  have h1 := l.min.isLt
  unfold Limits.Valid
  refine ⟨by simp [V1.Limits.toCore, V1.widen32]; omega, ?_⟩
  rcases hm : l.max with _ | mx
  · simp [V1.Limits.toCore, hm]
  · have := hmax mx (by simp [hm])
    have h2 := mx.isLt
    simp [V1.Limits.toCore, hm, V1.widen32]
    omega

theorem tableTypeOk_toCore (Δ : TypeCtx) {t : TableType} (h : TableTypeValid t) :
    TableTypeOk Δ (tableToC t) := by
  refine ⟨?_, .ref (.abs _)⟩
  have := limits_valid_toCore (le_refl _) h
  simpa [tableToC, AddrType.width, AddrType.intType, IntType.width] using this

theorem memTypeOk_toCore {t : MemoryType} (h : MemoryTypeValid t) : MemTypeOk t.toCore := by
  have := limits_valid_toCore (Nat.pow_le_pow_right (by omega) (by omega)) h
  simpa [MemTypeOk, Wasm.MemoryType.Valid, V1.MemoryType.toCore, AddrType.width,
    AddrType.intType, IntType.width] using this

/-- The Core closed extern type of a Lime1 import. -/
def importC (types : List FuncType) : ImportDesc → CExternType
  | .func i => .func (((types[i.toNat]?).map V1.FuncType.toDefType).getD default)
  | .table tt => .table (tableToC tt)
  | .memory mt => .mem mt.toCore
  | .global gt => .global (globalToC gt)

theorem importOk_toCore (types : List FuncType) (i : Import) (hv : ImportValid types i) :
    ImportOk { types := types.map V1.FuncType.toDefType } i.toCore (importC types i.desc) := by
  obtain ⟨et, het, hval⟩ := hv
  rcases i with ⟨mn, n, d⟩
  cases d with
  | func x =>
    simp only [importType?, Option.map_eq_some_iff] at het
    obtain ⟨ft, hft, rfl⟩ := het
    refine ⟨?_, ?_⟩
    · simp [V1.Import.toCore, V1.ImportDesc.toCore, Wasm.Validation.Context.closeExtern?,
        Wasm.Validation.Context.type?, hft, importC]
    · simp only [importC, hft, Option.map_some, Option.getD_some]
      exact .func (tyOk_toDefType _ _) (expand_toDefType ft)
  | table tt =>
    simp only [importType?, Option.some.injEq] at het
    subst het
    exact ⟨by simp [V1.Import.toCore, V1.ImportDesc.toCore,
      Wasm.Validation.Context.closeExtern?, importC, closeTableType_toCore],
      .table (tableTypeOk_toCore _ hval)⟩
  | memory mt =>
    simp only [importType?, Option.some.injEq] at het
    subst het
    exact ⟨by simp [V1.Import.toCore, V1.ImportDesc.toCore,
      Wasm.Validation.Context.closeExtern?, importC], .mem (memTypeOk_toCore hval)⟩
  | global gt =>
    exact ⟨by simp [V1.Import.toCore, V1.ImportDesc.toCore,
      Wasm.Validation.Context.closeExtern?, importC, closeGlobalType_toCore],
      .global (.num _)⟩

section ImportLists

variable (types : List FuncType)

theorem xt_funcs : (imps : List Import) → (∀ i ∈ imps, ImportValid types i) →
    CExternType.funcs (imps.map fun i => importC types i.desc) =
      (imps.filterMap fun i => match i.desc with
        | .func idx => types[idx.toNat]?
        | _ => none).map V1.FuncType.toDefType
  | [], _ => rfl
  | ⟨mn, n, d⟩ :: imps, hv => by
    have ih := xt_funcs imps (fun i hi => hv i (by simp [hi]))
    simp only [importC] at ih
    cases d with
    | func x =>
      obtain ⟨et, het, -⟩ := hv ⟨mn, n, .func x⟩ (by simp)
      simp only [importType?, Option.map_eq_some_iff] at het
      obtain ⟨ft, hft, -⟩ := het
      simp [importC, CExternType.funcs, ih, hft]
    | _ => simp [importC, CExternType.funcs, ih]

theorem xt_tables : (imps : List Import) →
    CExternType.tables (imps.map fun i => importC types i.desc) =
      (imps.filterMap fun i => match i.desc with
        | .table tt => some tt
        | _ => none).map tableToC
  | [] => rfl
  | ⟨mn, n, d⟩ :: imps => by
    have ih := xt_tables imps
    simp only [importC] at ih
    cases d <;> simp [importC, CExternType.tables, ih]

theorem xt_mems : (imps : List Import) →
    CExternType.mems (imps.map fun i => importC types i.desc) =
      (imps.filterMap fun i => match i.desc with
        | .memory mt => some mt
        | _ => none).map V1.MemoryType.toCore
  | [] => rfl
  | ⟨mn, n, d⟩ :: imps => by
    have ih := xt_mems imps
    simp only [importC] at ih
    cases d <;> simp [importC, CExternType.mems, ih]

theorem xt_globals : (imps : List Import) →
    CExternType.globals (imps.map fun i => importC types i.desc) =
      (imps.filterMap fun i => match i.desc with
        | .global gt => some gt
        | _ => none).map globalToC
  | [] => rfl
  | ⟨mn, n, d⟩ :: imps => by
    have ih := xt_globals imps
    simp only [importC] at ih
    cases d <;> simp [importC, CExternType.globals, ih]

theorem xt_tags : (imps : List Import) →
    CExternType.tags (imps.map fun i => importC types i.desc) = []
  | [] => rfl
  | ⟨mn, n, d⟩ :: imps => by
    have ih := xt_tags imps
    simp only [importC] at ih
    cases d <;> simp [importC, CExternType.tags, ih]

end ImportLists

theorem forall₂_map_of {α β γ : Type _} {R : β → γ → Prop} (f : α → β) (g : α → γ) :
    (l : List α) → (∀ a ∈ l, R (f a) (g a)) → List.Forall₂ R (l.map f) (l.map g)
  | [], _ => .nil
  | a :: l, h => .cons (h a (by simp)) (forall₂_map_of f g l (fun b hb => h b (by simp [hb])))

theorem forall₂_filterMap_of {α β γ δ : Type _} {R : γ → δ → Prop} (f : α → γ)
    (g : α → Option β) (k : β → δ) :
    (l : List α) → (∀ a ∈ l, ∃ b, g a = some b ∧ R (f a) (k b)) →
      List.Forall₂ R (l.map f) ((l.filterMap g).map k)
  | [], _ => .nil
  | a :: l, h => by
    obtain ⟨b, hb, hr⟩ := h a (by simp)
    simp only [List.map_cons, List.filterMap_cons, hb]
    exact .cons hr (forall₂_filterMap_of f g k l (fun c hc => h c (by simp [hc])))

theorem forall₂_exists_of {α β : Type _} {R : α → β → Prop} :
    (l : List α) → (∀ a ∈ l, ∃ b, R a b) → ∃ l', List.Forall₂ R l l'
  | [], _ => ⟨[], .nil⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a (by simp)
    obtain ⟨l', hl'⟩ := forall₂_exists_of l (fun c hc => h c (by simp [hc]))
    exact ⟨b :: l', .cons hb hl'⟩

theorem filterMap_eq_map_of {α β : Type _} (g : α → Option β) :
    (l : List α) → (∀ a ∈ l, ∃ b, g a = some b) →
      (l.filterMap g).map some = l.map g
  | [], _ => rfl
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a (by simp)
    simp [hb, filterMap_eq_map_of g l (fun c hc => h c (by simp [hc]))]

theorem mem_refs_of_elem {m : Module} {e : Elem} (he : e ∈ m.elems) {f : FuncIdx}
    (hf : f ∈ e.init) : f.toNat ∈ funcIdxNonFuncs m.toCore := by
  unfold funcIdxNonFuncs
  apply List.mem_append_left
  apply List.mem_append_right
  rw [List.mem_flatMap]
  refine ⟨e.toCore, by simp only [Module.toCore]; exact List.mem_map_of_mem he, ?_⟩
  apply List.mem_append_left
  rw [List.mem_flatMap]
  refine ⟨funcRef f, by simp only [Elem.toCore]; exact List.mem_map_of_mem hf, ?_⟩
  simp [funcRef, Expr.freeFuncs, Instr.freeFuncs]

/-- Constant expressions transport. -/
theorem constExpr_toCore {C : Silmaril.Wasm.Validation.Context} {D : Wasm.Validation.Context} (hA : Agrees C D)
    {body : Expr} {t : ValType} (h : ConstExprType C body t) :
    ExprOkConst D (Expr.toCore body) (.num t) := by
  refine ⟨?_, ?_⟩
  · have := ExprType.toCore' hA h.typed
    simpa [ExprOk] using this
  · intro i hi
    rw [Expr.toCore_eq_map, List.mem_map] at hi
    obtain ⟨i₀, hi₀, rfl⟩ := hi
    cases h.constant i₀ hi₀ with
    | intConst t b => exact .intConst t b
    | floatConst t b => exact .floatConst t b
    | globalGet x hx => exact .globalGet (prefix_map_getElem? hA.globals hx)
    | add t => exact .binop (Or.inl rfl)
    | sub t => exact .binop (Or.inr (Or.inl rfl))
    | mul t => exact .binop (Or.inr (Or.inr rfl))

theorem refNull_ok (C : Wasm.Validation.Context) :
    ExprOkConst C [.refNull (.abstract .func)] (.refv Silmaril.Wasm.Validation.Ty.funcref) := by
  refine ⟨?_, ?_⟩
  · have := single_plain (C := C) (.reference (.refNull (ht := .abstract .func) (.abs _)))
      (by intro t ht; simp at ht; subst ht; exact .refv (.ref (.abs _)))
    simpa [ExprOk, Silmaril.Wasm.Validation.Ty.refT, Silmaril.Wasm.Validation.Ty.funcref] using this
  · intro i hi
    simp at hi; subst hi; exact .refNull _

theorem refFunc_ok (C : Wasm.Validation.Context) {x : FuncIdx} {ft : FuncType}
    (hf : C.funcs[x.toNat]? = some ft.toDefType) (hr : x.toNat ∈ C.refs) :
    ExprOkConst C [.refFunc x] (.refv Silmaril.Wasm.Validation.Ty.funcref) := by
  refine ⟨?_, ?_⟩
  · have h1 := single_plain (C := C) (.reference (.refFunc hf hr))
      (by intro t ht; simp at ht; subst ht
          exact .refv (.ref (.use (.dt (tyOk_toDefType _ _)))))
    refine InstrsOk.sub h1 ⟨.nil, ?_, by simp⟩ ⟨by simp [ResultOk], ?_, by simp⟩
    · exact .cons (.refv (.refNull (.defFunc (expand_toDefType ft)))) .nil
    · intro t ht; simp at ht; subst ht; exact .refv (.ref (.abs _))
  · intro i hi
    simp at hi; subst hi; exact .refFunc _

/-- A valid Lime1 module maps to a Core module whose import types are `importC`. -/
theorem Silmaril.Wasm.Validation.ModuleValid.toCore_ok {m : Module} (h : Silmaril.Wasm.Validation.ModuleValid m) :
    ∃ xtE, Wasm.Validation.ModuleOk m.toCore
      ⟨m.imports.map fun i => importC m.types i.desc, xtE⟩ := by
  -- Core index spaces
  let dts := m.types.map V1.FuncType.toDefType
  let xtI := m.imports.map fun i => importC m.types i.desc
  let fdts := (m.funcs.filterMap fun f => m.types[f.type.toNat]?).map V1.FuncType.toDefType
  let gts := m.globals.map fun g => globalToC g.type
  let tts := m.tables.map tableToC
  let rts := m.elems.map fun _ => Silmaril.Wasm.Validation.Ty.funcref
  let C' : Wasm.Validation.Context :=
    { types := dts, globals := CExternType.globals xtI,
      funcs := CExternType.funcs xtI ++ fdts, refs := funcIdxNonFuncs m.toCore }
  let C : Wasm.Validation.Context :=
    { C' with
      tags := CExternType.tags xtI ++ [], globals := C'.globals ++ gts,
      mems := CExternType.mems xtI ++ m.toCore.memories,
      tables := CExternType.tables xtI ++ tts,
      datas := m.toCore.data.map fun _ => (), elems := rts }
  have hfuncs_eq : (moduleContext m).funcs.map V1.FuncType.toDefType = C.funcs := by
    simp only [C, C', moduleContext, List.map_append, fdts]
    rw [xt_funcs m.types m.imports h.imports]
    rfl
  have hA : Agrees (moduleContext m) C := by
    refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · exact List.prefix_refl _
    · rw [hfuncs_eq]
    · simp only [C, moduleContext, List.map_append, tts]
      rw [xt_tables m.types m.imports]
      exact List.prefix_refl _
    · simp only [C, moduleContext, List.map_append, Module.toCore]
      rw [xt_mems m.types m.imports]
      exact List.prefix_refl _
    · simp only [C, C', moduleContext, List.map_append, gts, List.map_map]
      rw [xt_globals m.types m.imports]
      simp only [importedGlobals]
      exact List.prefix_refl _
  have hAinit : ∀ D : Wasm.Validation.Context,
      (importedGlobals m).map globalToC <+: D.globals → D.locals = [] → D.labels = [] →
      D.return_ = none → Agrees (initializerContext m) D := by
    intro D hg hl hlab hr
    exact ⟨by simp [initializerContext], by simp [initializerContext],
      by simp [initializerContext], by simp [initializerContext], hg,
      by simp [initializerContext, hl], by simp [initializerContext, hlab],
      by simp [initializerContext, hr]⟩
  have hglobals : ∀ (gs : List Global) (D : Wasm.Validation.Context),
      (∀ g ∈ gs, GlobalValid (initializerContext m) g) →
      (importedGlobals m).map globalToC <+: D.globals → D.locals = [] → D.labels = [] →
      D.return_ = none →
      GlobalsOk D (gs.map Global.toCore) (gs.map fun g => globalToC g.type) := by
    intro gs
    induction gs with
    | nil => intro D _ _ _ _ _; exact .nil
    | cons g gs ih =>
      intro D hv hg hl hlab hr
      refine .cons ⟨(closeGlobalType_toCore _ _).symm, .num _, ?_⟩
        (ih _ (fun g' hg' => hv g' (by simp [hg'])) (hg.trans (List.prefix_append _ _))
          hl hlab hr)
      exact constExpr_toCore (hAinit D hg hl hlab hr) (hv g (by simp))
  have hexports : ∀ e ∈ m.toCore.exports, ∃ xt, ExportOk C e xt := by
    intro e he
    simp only [Module.toCore, List.mem_map] at he
    obtain ⟨e₀, he₀, rfl⟩ := he
    obtain ⟨et, het⟩ := h.exports e₀ he₀
    rcases e₀ with ⟨nm, idx⟩
    cases idx with
    | func i =>
      simp only [exportType?, Option.map_eq_some_iff] at het
      obtain ⟨ft, hft, -⟩ := het
      exact ⟨.func ft.toDefType, .func (prefix_map_getElem? hA.funcs hft)⟩
    | table i =>
      simp only [exportType?, Option.map_eq_some_iff] at het
      obtain ⟨tt, htt, -⟩ := het
      exact ⟨.table (tableToC tt), .table (prefix_map_getElem? hA.tables htt)⟩
    | memory i =>
      simp only [exportType?, Option.map_eq_some_iff] at het
      obtain ⟨mt, hmt, -⟩ := het
      exact ⟨.mem mt.toCore, .mem (prefix_map_getElem? hA.mems hmt)⟩
    | global i =>
      simp only [exportType?, Option.map_eq_some_iff] at het
      obtain ⟨gt, hgt, -⟩ := het
      exact ⟨.global (globalToC gt), .global (prefix_map_getElem? hA.globals hgt)⟩
  obtain ⟨xtE, hxtE⟩ := forall₂_exists_of _ hexports
  have himports : List.Forall₂ (ImportOk { types := dts }) m.toCore.imports xtI :=
    forall₂_map_of _ _ m.imports (fun i hi => importOk_toCore m.types i (h.imports i hi))
  have hglobals' : GlobalsOk C' m.toCore.globals gts := by
    refine hglobals m.globals C' h.globals ?_ rfl rfl rfl
    show _ <+: CExternType.globals xtI
    rw [xt_globals]
    exact List.prefix_refl _
  have hmems : ∀ mt ∈ m.toCore.memories, MemOk mt := by
    intro mt hmt
    simp only [Module.toCore, List.mem_map] at hmt
    obtain ⟨mt₀, hmt₀, rfl⟩ := hmt
    exact memTypeOk_toCore (h.memories mt₀ hmt₀)
  have htables : List.Forall₂ (TableOk C') m.toCore.tables tts :=
    forall₂_map_of tableToCore tableToC m.tables
      (fun t ht => ⟨rfl, tableTypeOk_toCore _ (h.tables t ht), refNull_ok C'⟩)
  have hfuncs : List.Forall₂ (FuncOk C) m.toCore.funcs fdts := by
    refine forall₂_filterMap_of Func.toCore _ V1.FuncType.toDefType m.funcs ?_
    intro f hf
    obtain ⟨ft, hft, -, hbody⟩ := h.functions f hf
    refine ⟨ft, hft, ?_⟩
    have hd : C.type? (Func.toCore f).type = some ft.toDefType := by
      simp only [Wasm.Validation.Context.type?, C, C', dts, Func.toCore, List.getElem?_map]
      rw [show m.types[f.type.toNat]? = some ft from hft]; rfl
    have hAf : Agrees (functionContext (moduleContext m) ft f.locals)
        (C.funcBody (ft.params.map Silmaril.Wasm.Validation.Ty.num) (ft.results.map Silmaril.Wasm.Validation.Ty.num)
          (f.locals.map fun t => ⟨.set, .num t⟩)) :=
      ⟨hA.types, hA.funcs, hA.tables, hA.mems, hA.globals,
        by simp [functionContext, Wasm.Validation.Context.funcBody, Function.comp_def],
        by simp [functionContext, Wasm.Validation.Context.funcBody],
        by simp [functionContext, Wasm.Validation.Context.funcBody]⟩
    refine FuncOk.mk (lts := f.locals.map fun t => ⟨.set, .num t⟩) hd (expand_toDefType ft) ?_ ?_
    · exact forall₂_map_of _ _ f.locals (fun t _ => LocalOk.set (.num t) trivial)
    · simpa [ExprOk, Silmaril.Wasm.Validation.Ty.toList_ofList, Func.toCore] using ExprType.toCore' hAf hbody
  have hdata : ∀ d ∈ m.toCore.data, DataOk C d := by
    intro d hd
    simp only [Module.toCore, List.mem_map] at hd
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    obtain ⟨⟨mt, hmt⟩, hoff⟩ := h.data d₀ hd₀
    exact DataModeOk.active (prefix_map_getElem? hA.mems hmt) (constExpr_toCore hA hoff)
  have helems : List.Forall₂ (ElemOk C) m.toCore.elems rts := by
    refine forall₂_map_of Elem.toCore (fun _ => Silmaril.Wasm.Validation.Ty.funcref) m.elems ?_
    intro e he
    obtain ⟨⟨tt, htt⟩, hoff, hfs⟩ := h.elements e he
    refine ⟨rfl, .ref (.abs _), ?_, ?_⟩
    · intro ex hex
      simp only [Elem.toCore, List.mem_map] at hex
      obtain ⟨f, hf, rfl⟩ := hex
      obtain ⟨ft, hft⟩ := hfs f hf
      exact refFunc_ok C (prefix_map_getElem? hA.funcs hft) (mem_refs_of_elem he hf)
    · exact ElemModeOk.active (prefix_map_getElem? hA.tables htt)
        (Sub.refl _ (k := .ref) trivial _) (constExpr_toCore hA hoff)
  have hstart : ∀ x, m.toCore.start = some x → StartOk C x := by
    intro x hx
    have := h.start x hx
    exact ⟨_, prefix_map_getElem? hA.funcs this, by simpa using expand_toDefType ⟨[], []⟩⟩
  have hdisjoint : (m.toCore.exports.map Wasm.Export.name).Nodup := by
    simpa [Module.toCore, V1.Export.toCore, Function.comp_def] using h.uniqueExports
  exact ⟨xtE, ModuleOk.mk (jts := []) (typesOk_map m.types {}) himports rfl rfl .nil
    hglobals' hmems htables hfuncs hdata helems hstart hxtE hdisjoint⟩

/-- **Milestone.** Every valid Lime1 module maps to a valid Core 3.0 module. -/
theorem Silmaril.Wasm.Validation.ModuleValid.toCore {m : Module} (h : Silmaril.Wasm.Validation.ModuleValid m) :
    Wasm.Validation.ModuleValid m.toCore :=
  let ⟨_, hok⟩ := Silmaril.Wasm.Validation.ModuleValid.toCore_ok h
  ⟨_, hok⟩

end Silmaril.Wasm.Lime1.Validation

namespace Silmaril.Wasm.V1.Validation

/-- **Milestone.** Every valid V1 module maps to a valid Core 3.0 module
(through Lime1: `ModuleValid.toLime` and `Module.toLime_toCore`). -/
theorem Silmaril.Wasm.Validation.ModuleValid.toCore {m : Module} (h : Silmaril.Wasm.Validation.ModuleValid m) :
    Wasm.Validation.ModuleValid m.toCore := by
  have := Lime1.Validation.ModuleValid.toCore (Silmaril.Wasm.Validation.ModuleValid.toLime h)
  simpa using this

end Silmaril.Wasm.V1.Validation
