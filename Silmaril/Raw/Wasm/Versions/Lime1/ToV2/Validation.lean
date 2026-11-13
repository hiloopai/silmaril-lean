module

public import Silmaril.Raw.Wasm.Versions.Lime1.ToV2.Modules
public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Validation
public import Silmaril.Raw.Wasm.Versions.Lime1.Features
public import Silmaril.Wasm.V2.Validation
public import Silmaril.Raw.Wasm.Versions.V2.Validation.Inversion

/-!
# Lime1 validation in WebAssembly 2.0

The validation half of the subset theorem `Lime1 ⊆ 2.0`. The *syntax* injection
`Silmaril/Wasm/Lime1/ToV2/Modules.lean` is total; validation preservation is
**not**, and this file is where that is made precise.

## Why the module theorem is conditional

Lime1 has seven features. Six of them — multivalue, sign extension,
nontrapping float-to-int, bulk-memory-opt, call-indirect-overlong and mutable
globals — are Wasm 2.0 features. The seventh, **extended constant
expressions**, is not. `Instr_const` (`6-typing:539-557` of
`specification/wasm-2.0/6-typing.spectec` at WebAssembly/spec revision
`608711107b7f1edb13efd57b7d79b49477462d36`) has exactly five rules — `CONST`,
`VCONST`, `REF.NULL`, `REF.FUNC` and `GLOBAL.GET` of an immutable global — and
nothing else is a 2.0 constant instruction. `i32.add` in a global initializer
was added by the extended-const proposal, which landed in 3.0, and Lime1's
`ConstantInstr` (`Silmaril/Wasm/Lime1/Validation/Modules.lean`) has the three
extra rules `add`, `sub`, `mul`.

So:

* `InstrType.toV2` and `ExprType.toV2` are **unconditional**: every Lime1
  *instruction* typing derivation maps to a 2.0 one. Lime1's instruction-level
  `frame` rule has no 2.0 instruction-level counterpart (2.0, like the spec,
  frames *sequences*, `Instrs_ok/frame`, `6-typing:175`), so a single Lime1
  instruction is transported to `InstrsOk … [i.toV2]`.
* `ConstantInstr.toV2` and `ConstExprType.toV2` carry the hypothesis
  `¬ isExtendedConstOp`, pointwise.
* `ModuleValid.toV2` carries `Module.NoExtendedConst` **and a second side
  condition**, `Module.SegmentOffsetsImported`; see below.
* `exists_valid_not_toV2_valid` is the counterexample that shows the
  extended-const side condition cannot be dropped: an explicit Lime1 module,
  valid in Lime1, whose 2.0 image is not valid. It is proved, with no `sorry`.
* `exists_valid_noExtendedConst_not_toV2_valid` is the counterexample for the
  second side condition, also proved.
* The Wasm 1.0 route discharges `NoExtendedConst` outright: a **valid** 1.0
  module has no `intBinOp` in any constant expression, because
  `V1.Validation.ConstantInstr` (`Silmaril/Wasm/V1/Validation/Modules.lean`)
  has only the three rules `intConst`, `floatConst`, `globalGet`.

**Correction to the unit's brief, 1.** The brief asked for
`theorem V1.Module.toLime_noExtendedConst (m : V1.Module) : m.toLime.NoExtendedConst`
with no hypothesis. That statement is **false**: `NoExtendedConst` is a
*syntactic* predicate, and `V1.Module` syntax happily admits
`(global i32 (i32.const 1) (i32.const 2) (i32.add))` — it is merely *invalid*.
`V1.Validation.ModuleValid.noExtendedConst` below is the minimal true
statement: it takes `V1.Validation.ModuleValid m` as a hypothesis, which is
exactly what the 1.0 route already has in hand.

**Correction to the unit's brief, 2.** Extended-const is not the only
obstruction. Wasm 2.0 validates element and data segments in `C'`
(`6-typing:691-692`), whose `GLOBALS` are the **imported** globals alone
(`6-typing:703`); Wasm 1.0 (`specification/wasm-1.0/6-typing.spectec:450-451`, `:459`)
and Wasm 3.0 (`wasm-3.0/2.4-validation.modules.spectec:157-158`, `:163`)
validate them in the full context `C`, and Lime1 follows 1.0. So a Lime1-valid
module whose data offset reads a *defined* immutable global is not 2.0-valid,
with no extended-const anywhere. `Module.SegmentOffsetsImported` is the second
side condition, and it does **not** follow from 1.0 validity either, so
`V1.Validation.ModuleValid.toV2` carries it too. See the report.

## Contexts

Lime1's `Context` has no `ELEMS`, `DATAS` or `REFS` component, because no Lime1
instruction mentions one: Lime1 has no `table.init`, `elem.drop`,
`memory.init`, `data.drop` or `ref.func`. `Context.toV2` therefore leaves those
three fields empty, and the instruction-level theorems are stated against an
arbitrary 2.0 context `D` satisfying `AgreesV2 C D`, which constrains only the
six fields Lime1 uses. The module-level proof instantiates `D` at the `C` and
`C'` that `V2.Validation.ModuleOk` prescribes, whose `ELEMS`, `DATAS` and
`REFS` are non-trivial.

`AgreesV2` asks for a *prefix* in the five index spaces and equality in
`LOCALS`, `LABELS` and `RETURN`, exactly as `Agrees` does for the Core 3.0
injection in `Silmaril/Wasm/Lime1/ToCore/Validation.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.Lime1.Validation

/-! ## Value and result types -/

/-- A Lime1 value type as a 2.0 validation value type. Lime1's value types are
the 2.0 number types, and none of them is `BOT`. -/
def valToV2 (t : ValType) : V2.Validation.CValType := .val (ValType.toV2 t)

/-- A Lime1 result type as a 2.0 validation result type, bottom of the stack
first on both sides. -/
def resToV2 (ts : ResultType) : V2.Validation.CResultType := ts.map valToV2

@[simp] theorem resToV2_nil : resToV2 [] = [] := rfl

@[simp] theorem resToV2_cons (t : ValType) (ts : ResultType) :
    resToV2 (t :: ts) = valToV2 t :: resToV2 ts := rfl

@[simp] theorem resToV2_append (a b : ResultType) :
    resToV2 (a ++ b) = resToV2 a ++ resToV2 b := List.map_append ..

@[simp] theorem liftResult_map_toV2 (ts : ResultType) :
    V2.Validation.liftResult (ts.map ValType.toV2) = resToV2 ts := by
  simp [V2.Validation.liftResult, resToV2, valToV2, List.map_map, Function.comp_def]

theorem resToV2_eq_map (ts : ResultType) :
    resToV2 ts = ts.map (V2.Validation.CValType.val ∘ ValType.toV2) := rfl

theorem resToV2_injective : Function.Injective resToV2 := by
  intro a b h
  exact List.map_injective_iff.2
    (fun x y hxy => ValType.toV2_injective (by cases hxy; rfl)) h

/-! ## Contexts -/

/-- The canonical 2.0 validation context of a Lime1 one. `ELEMS`, `DATAS` and
`REFS` are empty: no Lime1 instruction reads them. -/
def Context.toV2 (C : Context) : V2.Validation.Context where
  types := C.types.map FuncType.toV2
  funcs := C.funcs.map FuncType.toV2
  globals := C.globals.map GlobalType.toV2
  tables := C.tables.map TableType.toV2
  mems := C.memories.map MemoryType.toV2
  locals := C.locals.map ValType.toV2
  labels := C.labels.map resToV2
  return_ := C.returnType.map resToV2

/-- A 2.0 context agrees with the image of a Lime1 one: its five index spaces
extend the images, and `LOCALS`, `LABELS` and `RETURN` are exactly the images.
`ELEMS`, `DATAS` and `REFS` are unconstrained. -/
structure AgreesV2 (C : Context) (D : V2.Validation.Context) : Prop where
  /-- `C.TYPES` injects as a prefix. -/
  types : C.types.map FuncType.toV2 <+: D.types
  /-- `C.FUNCS` injects as a prefix. -/
  funcs : C.funcs.map FuncType.toV2 <+: D.funcs
  /-- `C.TABLES` injects as a prefix. -/
  tables : C.tables.map TableType.toV2 <+: D.tables
  /-- `C.MEMS` injects as a prefix. -/
  mems : C.memories.map MemoryType.toV2 <+: D.mems
  /-- `C.GLOBALS` injects as a prefix. -/
  globals : C.globals.map GlobalType.toV2 <+: D.globals
  /-- `C.LOCALS` is reproduced exactly. -/
  locals : D.locals = C.locals.map ValType.toV2
  /-- `C.LABELS` is reproduced exactly. -/
  labels : D.labels = C.labels.map resToV2
  /-- `C.RETURN` is reproduced exactly. -/
  return_ : D.return_ = C.returnType.map resToV2

namespace AgreesV2

variable {C : Context} {D : V2.Validation.Context}

theorem refl (C : Context) : AgreesV2 C C.toV2 :=
  ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _,
    List.prefix_refl _, rfl, rfl, rfl⟩

theorem withLabel (hA : AgreesV2 C D) (ts : ResultType) :
    AgreesV2 (C.withLabel ts) (D.withLabel (resToV2 ts)) :=
  ⟨hA.types, hA.funcs, hA.tables, hA.mems, hA.globals, hA.locals,
    by simp [Context.withLabel, V2.Validation.Context.withLabel, hA.labels], hA.return_⟩

theorem type? (hA : AgreesV2 C D) {x : TypeIdx} {ft : FuncType}
    (h : C.types[x.toNat]? = some ft) : D.types[x.toNat]? = some (FuncType.toV2 ft) :=
  prefix_map_getElem? hA.types h

theorem func? (hA : AgreesV2 C D) {x : FuncIdx} {ft : FuncType}
    (h : C.funcs[x.toNat]? = some ft) : D.funcs[x.toNat]? = some (FuncType.toV2 ft) :=
  prefix_map_getElem? hA.funcs h

theorem global? (hA : AgreesV2 C D) {x : GlobalIdx} {gt : GlobalType}
    (h : C.globals[x.toNat]? = some gt) : D.globals[x.toNat]? = some (GlobalType.toV2 gt) :=
  prefix_map_getElem? hA.globals h

theorem table? (hA : AgreesV2 C D) {x : TableIdx} {tt : TableType}
    (h : C.tables[x.toNat]? = some tt) : D.tables[x.toNat]? = some (TableType.toV2 tt) :=
  prefix_map_getElem? hA.tables h

theorem mem? (hA : AgreesV2 C D) {x : MemIdx} {mt : MemoryType}
    (h : C.memories[x.toNat]? = some mt) : D.mems[x.toNat]? = some (MemoryType.toV2 mt) :=
  prefix_map_getElem? hA.mems h

theorem local? (hA : AgreesV2 C D) {x : LocalIdx} {t : ValType}
    (h : C.locals[x.toNat]? = some t) : D.locals[x.toNat]? = some (ValType.toV2 t) := by
  rw [hA.locals, List.getElem?_map, h]; rfl

theorem label? (hA : AgreesV2 C D) {l : LabelIdx} {ts : ResultType}
    (h : C.labels[l.toNat]? = some ts) : D.labels[l.toNat]? = some (resToV2 ts) := by
  rw [hA.labels, List.getElem?_map, h]; rfl

theorem return? (hA : AgreesV2 C D) {ts : ResultType} (h : C.returnType = some ts) :
    D.return_ = some (resToV2 ts) := by rw [hA.return_, h]; rfl

/-- 2.0 names memory `0` explicitly in the typing premises where Lime1 only
requires the memory index space to be non-empty. -/
theorem mem_zero (hA : AgreesV2 C D) (h : C.memories ≠ []) :
    ∃ mt : V2.MemoryType, D.mems[0]? = some mt := by
  cases hm : C.memories with
  | nil => exact absurd hm h
  | cons mt ms => exact ⟨MemoryType.toV2 mt, prefix_map_getElem? hA.mems (by rw [hm]; rfl)⟩

/-- Likewise for the implicit table `0` of `call_indirect`; the image table is
always a `FUNCREF` table. -/
theorem table_zero (hA : AgreesV2 C D) (h : C.tables ≠ []) :
    ∃ tt : V2.TableType, D.tables[0]? = some tt ∧ tt.element = .funcref := by
  cases ht : C.tables with
  | nil => exact absurd ht h
  | cons tt ts =>
      exact ⟨TableType.toV2 tt, prefix_map_getElem? hA.tables (by rw [ht]; rfl), rfl⟩

end AgreesV2

/-! ## Immediates -/

@[simp] theorem PackSize.toV2_width (n : PackSize) : (PackSize.toV2 n).width = n.width := by
  cases n <;> rfl

theorem intUnOp_valid_toV2 {t : IntType} {op : IntUnOp} (h : IntUnOpValid t op) :
    Wasm.IntUnOp.valid t op.toV2 = true := by
  cases op with
  | extend n =>
      simp only [IntUnOp.toV2, Wasm.IntUnOp.valid, decide_eq_true_eq, PackSize.toV2_width]
      exact h
  | _ => rfl

/-- `Blocktype_ok` (`6-typing:203-210`) for the image of a Lime1 block
signature; both rules, `Blocktype_ok/valtype` and `Blocktype_ok/typeidx`. -/
theorem blockTypeOk_toV2 {C : Context} {D : V2.Validation.Context} (hA : AgreesV2 C D)
    {bt : BlockType} {ft : FuncType} (h : blockType? C bt = some ft) :
    V2.Validation.BlockTypeOk D (BlockType.toV2 bt)
      ⟨resToV2 ft.params, resToV2 ft.results⟩ := by
  cases bt with
  | empty =>
      simp only [blockType?, Option.some.injEq] at h
      subst h
      exact .result none
  | value t =>
      simp only [blockType?, Option.some.injEq] at h
      subst h
      exact .result (some (ValType.toV2 t))
  | typeIdx x =>
      have hx := hA.type? h
      have := V2.Validation.BlockTypeOk.typeIdx (C := D) (x := x) hx
      rw [← liftResult_map_toV2 ft.params, ← liftResult_map_toV2 ft.results]
      exact this

/-! ## Instruction typing

`InstrType.toV2` and `ExprType.toV2` are **unconditional**: extended-const is a
restriction on `Instr_const`, not on `Instr_ok`, so `i32.add` types in 2.0
exactly as it does in Lime1.

Lime1 frames single *instructions* (`InstrType.frame`); 2.0, like the official
spec, frames *sequences* (`Instrs_ok/frame`, `6-typing:175`). The conclusion is
therefore an `InstrsOk` on the singleton sequence. -/

/-- The generalised form, with the 2.0 context universally quantified so that
the `block`/`loop`/`if` cases may extend it. -/
theorem InstrType.toV2Gen {C : Context} {i : Instr} {a b : ResultType}
    (h : InstrType C i a b) : ∀ D : V2.Validation.Context, AgreesV2 C D →
      V2.Validation.InstrsOk D [Instr.toV2 i] ⟨resToV2 a, resToV2 b⟩ := by
  induction h using InstrType.rec (motive_2 := fun C es a b _ =>
      ∀ D : V2.Validation.Context, AgreesV2 C D →
        V2.Validation.InstrsOk D (Expr.toV2 es) ⟨resToV2 a, resToV2 b⟩) with
  | @frame C i a b pre h ih =>
      intro D hA
      rw [resToV2_append, resToV2_append]
      exact .frame (ih D hA)
  | @nop C => intro D _; exact .instr .nop
  | @unreachable C a b => intro D _; exact .instr .unreachable
  | @drop C t => intro D _; exact .instr .drop
  | @select C t => intro D _; exact .instr (.selectImpl (.refl _) (Or.inl ⟨t, rfl⟩))
  | @block C bt ft body type h ih =>
      intro D hA
      exact .instr (.block (blockTypeOk_toV2 hA type) (ih _ (hA.withLabel _)))
  | @loop C bt ft body type h ih =>
      intro D hA
      exact .instr (.loop (blockTypeOk_toV2 hA type) (ih _ (hA.withLabel _)))
  | @if_ C bt ft left right type hl hr ihl ihr =>
      intro D hA
      rw [resToV2_append]
      exact .instr (.if_ (blockTypeOk_toV2 hA type)
        (ihl _ (hA.withLabel _)) (ihr _ (hA.withLabel _)))
  | @br C l ts h pre out =>
      intro D hA
      rw [resToV2_append]
      exact .instr (.br (hA.label? h))
  | @brIf C l ts h =>
      intro D hA
      rw [resToV2_append]
      exact .instr (.brIf (hA.label? h))
  | @brTable C ls l' ts hd hs pre out =>
      intro D hA
      simp only [resToV2_append]
      exact .instr (.brTable
        (fun l hl => ⟨resToV2 ts, hA.label? (hs l hl), V2.Validation.CResultType.sub_refl _⟩)
        ⟨resToV2 ts, hA.label? hd, V2.Validation.CResultType.sub_refl _⟩)
  | @return_ C ts h pre out =>
      intro D hA
      rw [resToV2_append]
      exact .instr (.return_ (hA.return? h))
  | @call C x ft h =>
      intro D hA
      rw [← liftResult_map_toV2 ft.params, ← liftResult_map_toV2 ft.results]
      exact .instr (.call (hA.func? h))
  | @callIndirect C y ft h table =>
      intro D hA
      obtain ⟨tt, htt, hrt⟩ := hA.table_zero table
      rw [resToV2_append, ← liftResult_map_toV2 ft.params, ← liftResult_map_toV2 ft.results]
      exact .instr (.callIndirect htt hrt (hA.type? h))
  | @localGet C x t h => intro D hA; exact .instr (.localGet (hA.local? h))
  | @localSet C x t h => intro D hA; exact .instr (.localSet (hA.local? h))
  | @localTee C x t h => intro D hA; exact .instr (.localTee (hA.local? h))
  | @globalGet C x gt h => intro D hA; exact .instr (.globalGet (hA.global? h))
  | @globalSet C x t h => intro D hA; exact .instr (.globalSet (hA.global? h) rfl)
  | @intLoad C t p arg memory access =>
      intro D hA
      obtain ⟨mt, hm⟩ := hA.mem_zero memory
      cases p with
      | none => exact .instr (.intLoadVal hm access)
      | some ps =>
          obtain ⟨n, s⟩ := ps
          have hacc : n.width < t.width ∧ Aligned arg n.width := access
          refine .instr (.intLoadPack hm ?_ ?_)
          · rw [PackSize.toV2_width]; exact hacc.1
          · rw [PackSize.toV2_width]; exact hacc.2
  | @floatLoad C t arg memory aligned =>
      intro D hA
      obtain ⟨mt, hm⟩ := hA.mem_zero memory
      exact .instr (.floatLoadVal hm aligned)
  | @intStore C t p arg memory access =>
      intro D hA
      obtain ⟨mt, hm⟩ := hA.mem_zero memory
      cases p with
      | none => exact .instr (.intStoreVal hm access)
      | some n =>
          have hacc : n.width < t.width ∧ Aligned arg n.width := access
          refine .instr (.intStorePack hm ?_ ?_)
          · rw [PackSize.toV2_width]; exact hacc.1
          · rw [PackSize.toV2_width]; exact hacc.2
  | @floatStore C t arg memory aligned =>
      intro D hA
      obtain ⟨mt, hm⟩ := hA.mem_zero memory
      exact .instr (.floatStoreVal hm aligned)
  | @memorySize C memory =>
      intro D hA
      obtain ⟨mt, hm⟩ := hA.mem_zero memory
      exact .instr (.memorySize hm)
  | @memoryGrow C memory =>
      intro D hA
      obtain ⟨mt, hm⟩ := hA.mem_zero memory
      exact .instr (.memoryGrow hm)
  | @memoryFill C memory =>
      intro D hA
      obtain ⟨mt, hm⟩ := hA.mem_zero memory
      exact .instr (.memoryFill hm)
  | @memoryCopy C memory =>
      intro D hA
      obtain ⟨mt, hm⟩ := hA.mem_zero memory
      exact .instr (.memoryCopy hm)
  | @intConst C t bits => intro D _; exact .instr .intConst
  | @floatConst C t bits => intro D _; exact .instr .floatConst
  | @intUnOp C t op valid => intro D _; exact .instr (.intUnOp (intUnOp_valid_toV2 valid))
  | @intBinOp C t op => intro D _; exact .instr .intBinOp
  | @intTestOp C t op => intro D _; exact .instr .intTestOp
  | @intRelOp C t op => intro D _; exact .instr .intRelOp
  | @floatUnOp C t op => intro D _; exact .instr .floatUnOp
  | @floatBinOp C t op => intro D _; exact .instr .floatBinOp
  | @floatRelOp C t op => intro D _; exact .instr .floatRelOp
  | @convert C op =>
      intro D _
      refine .instr ?_
      cases op with
      | wrap => exact .cvtOpConvert (by decide) (by simp [V2.CvtOp.toShared])
      | extend s => exact .cvtOpConvert (by decide) (by simp [V2.CvtOp.toShared])
      | trunc f i s => exact .cvtOpConvert (by simp) (by simp [V2.CvtOp.toShared])
      | truncSat f i s => exact .cvtOpConvert (by simp) (by simp [V2.CvtOp.toShared])
      | convert i f s => exact .cvtOpConvert (by simp) (by simp [V2.CvtOp.toShared])
      | demote => exact .cvtOpConvert (by decide) (by simp [V2.CvtOp.toShared])
      | promote => exact .cvtOpConvert (by decide) (by simp [V2.CvtOp.toShared])
      | reinterpretInt f =>
          cases f <;> exact .cvtOpConvert (by decide) (by decide)
      | reinterpretFloat i =>
          cases i <;> exact .cvtOpConvert (by decide) (by decide)
  | @nil C ts =>
      exact V2.Validation.InstrsOk.nil_iff.mpr (V2.Validation.CResultType.sub_refl _)
  | @cons C i is a b c hi his ihi ihis =>
      rename_i D hA
      exact V2.Validation.InstrsOk.seq (ihi D hA) (ihis D hA)

/-- **Unconditional.** Every Lime1 instruction typing derivation is a 2.0 one. -/
theorem InstrType.toV2 {C : Context} {D : V2.Validation.Context} (hA : AgreesV2 C D)
    {i : Instr} {a b : ResultType} (h : InstrType C i a b) :
    V2.Validation.InstrsOk D [Instr.toV2 i] ⟨resToV2 a, resToV2 b⟩ := h.toV2Gen D hA

/-- **Unconditional.** Every Lime1 instruction-sequence typing derivation is a
2.0 one. -/
theorem ExprType.toV2 {C : Context} {D : V2.Validation.Context} (hA : AgreesV2 C D)
    {es : Expr} {a b : ResultType} (h : ExprType C es a b) :
    V2.Validation.InstrsOk D (Expr.toV2 es) ⟨resToV2 a, resToV2 b⟩ := by
  induction es generalizing a with
  | nil =>
      cases h
      exact V2.Validation.InstrsOk.nil_iff.mpr (V2.Validation.CResultType.sub_refl _)
  | cons i es ih =>
      cases h with
      | cons hi his => exact V2.Validation.InstrsOk.seq (InstrType.toV2 hA hi) (ih his)

/-! ## Constant expressions

This is where `Lime1 ⊆ 2.0` stops being unconditional. 2.0's `Instr_const`
(`6-typing:539-557`) has exactly five rules — `CONST`, `VCONST`, `REF.NULL`,
`REF.FUNC` and `GLOBAL.GET` of an immutable global. Lime1's `ConstantInstr`
has three more: `add`, `sub` and `mul` on an integer type, the extended-const
feature. `Silmaril.Wasm.Lime1.Instr.isExtendedConstOp` recognises exactly those
six instructions. -/

/-- No constant expression in the module — no global initializer, no
element-segment offset, no data-segment offset — uses extended-const
arithmetic. This is the side condition under which Lime1 validation is
preserved by `Module.toV2`.

The predicate is stated with `Silmaril.Wasm.Lime1.Instr.isExtendedConstOp`,
which is `true` on exactly `intBinOp t ADD`, `intBinOp t SUB` and
`intBinOp t MUL`. -/
def Module.NoExtendedConst (m : Module) : Prop :=
  (∀ g ∈ m.globals, ∀ i ∈ g.init, Instr.isExtendedConstOp i = false) ∧
    (∀ e ∈ m.elems, ∀ i ∈ e.offset, Instr.isExtendedConstOp i = false) ∧
    (∀ d ∈ m.data, ∀ i ∈ d.offset, Instr.isExtendedConstOp i = false)

instance (m : Module) : Decidable (Module.NoExtendedConst m) := by
  unfold Module.NoExtendedConst; infer_instance

/-- The only context component a 2.0 *constant* expression reads is `GLOBALS`,
and it reads it only at the indices its `global.get`s name. This is the exact
agreement `ConstExprType.toV2` needs, and it is weaker than `AgreesV2`: it lets
a Lime1 derivation taken in the full module context be replayed in `C'`, whose
`GLOBALS` are the imported globals alone. -/
def GlobalsAgree (C : Context) (D : V2.Validation.Context) (es : Expr) : Prop :=
  ∀ x : GlobalIdx, Instr.globalGet x ∈ es → ∀ gt : GlobalType,
    C.globals[x.toNat]? = some gt → D.globals[x.toNat]? = some (GlobalType.toV2 gt)

theorem AgreesV2.globalsAgree {C : Context} {D : V2.Validation.Context}
    (hA : AgreesV2 C D) (es : Expr) : GlobalsAgree C D es :=
  fun _ _ _ hgt => hA.global? hgt

/-- **Conditional.** A Lime1 constant instruction that is not extended-const
arithmetic is a 2.0 constant instruction. -/
theorem ConstantInstr.toV2 {C : Context} {D : V2.Validation.Context} {i : Instr}
    (h : ConstantInstr C i) (hc : Instr.isExtendedConstOp i = false)
    (hg : GlobalsAgree C D [i]) : V2.Validation.InstrConst D (Instr.toV2 i) := by
  cases h with
  | intConst t c => exact .intConst t c
  | floatConst t c => exact .floatConst t c
  | globalGet x hx => exact .globalGet (hg x (by simp) _ hx) rfl
  | add t => simp [Instr.isExtendedConstOp] at hc
  | sub t => simp [Instr.isExtendedConstOp] at hc
  | mul t => simp [Instr.isExtendedConstOp] at hc

/-- The sequence form of `ConstantInstr.toV2`. -/
theorem ConstantExpr.toV2 {C : Context} {D : V2.Validation.Context} {es : Expr}
    (h : ConstantExpr C es) (hc : ∀ i ∈ es, Instr.isExtendedConstOp i = false)
    (hg : GlobalsAgree C D es) : V2.Validation.ExprConst D (Expr.toV2 es) := by
  intro j hj
  rw [Expr.toV2_eq_map, List.mem_map] at hj
  obtain ⟨i, hi, rfl⟩ := hj
  refine ConstantInstr.toV2 (h i hi) (hc i hi) ?_
  intro x hx gt hgt
  have hxi : Instr.globalGet x = i := List.mem_singleton.1 hx
  subst hxi
  exact hg x hi gt hgt

/-- Typing transport for a *constant* instruction. Unlike `InstrType.toV2` it
needs no agreement outside `GLOBALS`, because a constant instruction reads
nothing else; that is what makes the element- and data-segment offsets of a
Lime1 module replayable in 2.0's `C'`.

**Unconditional in extended-const.** Like `InstrType.toV2Gen`, this takes no
`isExtendedConstOp` hypothesis: extended-const restricts `Instr_const`
(`6-typing:539-557`), not `Instr_ok` (`Instr_ok/binop`, `6-typing:270`, is
premise-free), so `i32.add` types in 2.0 exactly as it does in Lime1. The
`ConstantInstr C i` hypothesis is still needed, and only to rule out the
non-constant instructions; the extended-const side condition belongs to
`ConstantInstr.toV2`, the *constness* half, not to the typing half. -/
theorem InstrType.toV2Const {C : Context} {i : Instr} {a b : ResultType}
    (h : InstrType C i a b) : ∀ D : V2.Validation.Context,
      ConstantInstr C i → GlobalsAgree C D [i] →
      V2.Validation.InstrsOk D [Instr.toV2 i] ⟨resToV2 a, resToV2 b⟩ := by
  induction h using InstrType.rec (motive_2 := fun _ _ _ _ _ => True) with
  | @frame C i a b pre h ih =>
      intro D hcon hg
      rw [resToV2_append, resToV2_append]
      exact .frame (ih D hcon hg)
  | @intConst C t bits => intro D _ _; exact .instr .intConst
  | @floatConst C t bits => intro D _ _; exact .instr .floatConst
  | @globalGet C x gt hx =>
      intro D _ hg
      exact .instr (.globalGet (hg x (by simp) gt hx))
  | @intBinOp C t op => intro D _ _; exact .instr .intBinOp
  | @nil C ts => trivial
  | @cons C i is a b c hi his ihi ihis => trivial
  | _ => intro D hcon _; cases hcon

/-- The sequence form of `InstrType.toV2Const`, and like it unconditional in
extended-const. -/
theorem ExprType.toV2Const {C : Context} {D : V2.Validation.Context} {es : Expr}
    {a b : ResultType} (h : ExprType C es a b) (hcon : ConstantExpr C es)
    (hg : GlobalsAgree C D es) :
    V2.Validation.InstrsOk D (Expr.toV2 es) ⟨resToV2 a, resToV2 b⟩ := by
  induction es generalizing a with
  | nil =>
      cases h
      exact V2.Validation.InstrsOk.nil_iff.mpr (V2.Validation.CResultType.sub_refl _)
  | cons i es ih =>
      cases h with
      | cons hi his =>
          refine V2.Validation.InstrsOk.seq
            (InstrType.toV2Const hi D (hcon i (by simp)) ?_)
            (ih his (fun j hj => hcon j (by simp [hj]))
              (fun x hx gt hgt => hg x (by simp [hx]) gt hgt))
          intro x hx gt hgt
          have hxi : Instr.globalGet x = i := List.mem_singleton.1 hx
          subst hxi
          exact hg x (by simp) gt hgt

/-- **Conditional.** `Expr_ok_const` (`6-typing:564`) for the image of a Lime1
constant expression that uses no extended-const arithmetic. -/
theorem ConstExprType.toV2 {C : Context} {D : V2.Validation.Context} {es : Expr}
    {t : ValType} (h : ConstExprType C es t)
    (hc : ∀ i ∈ es, Instr.isExtendedConstOp i = false) (hg : GlobalsAgree C D es) :
    V2.Validation.ExprOkConst D (Expr.toV2 es) (ValType.toV2 t) :=
  ⟨ExprType.toV2Const h.typed h.constant hg, ConstantExpr.toV2 h.constant hc hg⟩

/-! ## The counterexample

The side condition is not an artefact of the proof. `(i32.const 1)
(i32.const 2) (i32.add)` is a Lime1 constant expression and is not a 2.0 one,
so the module below is `Lime1.Validation.ModuleValid` and its 2.0 image is not
`V2.Validation.ModuleValid`. -/

/-- The extended-const global initializer `(i32.const 1) (i32.const 2)
(i32.add)`. -/
def extendedConstInit : Expr :=
  [.intConst .i32 1, .intConst .i32 2, .intBinOp .i32 .add]

/-- A Lime1 module whose only content is one immutable `i32` global with an
extended-const initializer. -/
def extendedConstModule : Module where
  globals := [⟨⟨.const, .i32⟩, extendedConstInit⟩]

theorem extendedConstInit_type (C : Context) : ExprType C extendedConstInit [] [.i32] :=
  .cons (.intConst .i32 1)
    (.cons (.frame [V1.ValType.i32] (.intConst .i32 2))
      (.cons (.intBinOp .i32 .add) (.nil _)))

theorem extendedConstInit_constant (C : Context) : ConstantExpr C extendedConstInit := by
  intro i hi
  simp only [extendedConstInit, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact .intConst _ _
  · exact .intConst _ _
  · exact .add _

/-- The counterexample module is valid in Lime1. -/
theorem extendedConstModule_valid : ModuleValid extendedConstModule where
  types := by simp [extendedConstModule]
  imports := by simp [extendedConstModule]
  functions := by simp [extendedConstModule]
  tables := by simp [extendedConstModule]
  memories := by simp [extendedConstModule]
  globals := by
    intro g hg
    simp only [extendedConstModule, List.mem_singleton] at hg
    subst hg
    exact ⟨extendedConstInit_type _, extendedConstInit_constant _⟩
  elements := by simp [extendedConstModule]
  data := by simp [extendedConstModule]
  start := by simp [StartValid, extendedConstModule]
  exports := by simp [extendedConstModule]
  uniqueExports := by simp [extendedConstModule]
  singleTable := by simp [moduleContext, extendedConstModule]
  singleMemory := by simp [moduleContext, extendedConstModule]

/-- …and it does not satisfy the side condition. -/
theorem extendedConstModule_not_noExtendedConst :
    ¬ Module.NoExtendedConst extendedConstModule := by
  rintro ⟨hg, -, -⟩
  have := hg ⟨⟨.const, .i32⟩, extendedConstInit⟩ (by simp [extendedConstModule])
    (.intBinOp .i32 .add) (by simp [extendedConstInit])
  simp [Instr.isExtendedConstOp] at this

/-- The sharp statement: the 2.0 image of the initializer is not a 2.0
constant expression, in *any* context and at *any* type. -/
theorem not_exprOkConst_toV2_extendedConstInit (D : V2.Validation.Context) (t : V2.ValType) :
    ¬ V2.Validation.ExprOkConst D (Expr.toV2 extendedConstInit) t := by
  rintro ⟨-, hconst⟩
  have hmem : V2.Instr.intBinOp .i32 .add ∈ Expr.toV2 extendedConstInit := by
    simp [extendedConstInit, Expr.toV2_eq_map, Instr.toV2]
  cases hconst _ hmem

/-- **The counterexample.** There is a Lime1 module that validates in Lime1 and
whose 2.0 image does not validate in 2.0. Hence `ModuleValid.toV2` *must* carry
a side condition. -/
theorem exists_valid_not_toV2_valid :
    ∃ m : Module, ModuleValid m ∧ ¬ V2.Validation.ModuleValid (Module.toV2 m) := by
  refine ⟨extendedConstModule, extendedConstModule_valid, ?_⟩
  rintro ⟨ixt, xt, hok⟩
  obtain ⟨-, -, hglobals, -, -, -, -, -, -, -, -, -, -, -⟩ := hok
  have hg : (Module.toV2 extendedConstModule).globals =
      [Global.toV2 ⟨⟨.const, .i32⟩, extendedConstInit⟩] := rfl
  rw [hg] at hglobals
  cases hglobals with
  | cons hgo _ =>
      exact not_exprOkConst_toV2_extendedConstInit _ _ hgo.2.2

/-! ## Module validation

### A second gap: segment offsets

Wasm 2.0 validates element and data segments in `C'` (`6-typing:691-692`),
whose `GLOBALS` component is `igt*`, the **imported** globals alone
(`6-typing:703`). Wasm 1.0 validates them in the full context `C`
(`specification/wasm-1.0/6-typing.spectec:450-451`, `:459`), and so does Wasm 3.0
(`wasm-3.0/2.4-validation.modules.spectec:157-158`, `:163`). Lime1 follows 1.0:
`ModuleValid.elements` and `.data` use `moduleContext m`
(`Silmaril/Wasm/Lime1/Validation/Modules.lean`), whose `globals` are the
imported ones *followed by the defined ones*.

So a Lime1 module whose data-segment offset is `global.get` of a **defined**
immutable global is Lime1-valid and is not 2.0-valid. That is a second, entirely
separate obstruction to validation preservation, and it is *not* about
extended-const. `Module.SegmentOffsetsImported` is the side condition that
closes it; `ModuleValid.toV2` therefore takes **two** hypotheses, not the one
the unit brief anticipated. See the report. -/

/-- Every `global.get` in an element- or data-segment offset names an
*imported* global. Required because 2.0 checks segment offsets in `C'`; see the
section documentation. -/
def Module.SegmentOffsetsImported (m : Module) : Prop :=
  (∀ e ∈ m.elems, ∀ x : GlobalIdx, Instr.globalGet x ∈ e.offset →
      x.toNat < (importedGlobals m).length) ∧
    (∀ d ∈ m.data, ∀ x : GlobalIdx, Instr.globalGet x ∈ d.offset →
      x.toNat < (importedGlobals m).length)

theorem globalsAgree_init {m : Module} {D : V2.Validation.Context}
    (hD : D.globals = (importedGlobals m).map GlobalType.toV2) (es : Expr) :
    GlobalsAgree (initializerContext m) D es := by
  intro x _ gt hgt
  have hgt' : (importedGlobals m)[x.toNat]? = some gt := hgt
  rw [hD, List.getElem?_map, hgt']
  rfl

theorem globalsAgree_offset {m : Module} {D : V2.Validation.Context} {es : Expr}
    (hD : D.globals = (importedGlobals m).map GlobalType.toV2)
    (hlt : ∀ x : GlobalIdx, Instr.globalGet x ∈ es →
      x.toNat < (importedGlobals m).length) :
    GlobalsAgree (moduleContext m) D es := by
  intro x hx gt hgt
  have hgt' : (importedGlobals m ++ m.globals.map Global.type)[x.toNat]? = some gt := hgt
  rw [List.getElem?_append_left (hlt x hx)] at hgt'
  rw [hD, List.getElem?_map, hgt']
  rfl

/-! ### Types and imports -/

theorem limitsOk_toV2 {l : Limits} {b k : Nat} (h : LimitsValid b l)
    (hmin : l.min.val ≤ k) (hb : ∀ m : Fin (2 ^ 32), m.val ≤ b → m.val ≤ k) :
    V2.Limits.Ok k (Limits.toV2 l) := by
  refine ⟨hmin, ?_⟩
  show match l.max with | none => True | some mx => l.min.val ≤ mx.val ∧ mx.val ≤ k
  cases hm : l.max with
  | none => trivial
  | some mx =>
      obtain ⟨hle, hmm⟩ := h.2 mx (by rw [hm]; rfl)
      exact ⟨hmm, hb mx hle⟩

/-- `Tabletype_ok` (`6-typing:38`) bounds a table by `2^32-1`, Lime1's
`TableTypeValid` by `2^32`; the gap is immaterial because both bounds are
`u32`s, so every bound is already at most `2^32-1`. -/
theorem tableTypeOk_toV2 {tt : TableType} (h : TableTypeValid tt) :
    V2.TableType.Ok (TableType.toV2 tt) :=
  limitsOk_toV2 h (by have := tt.limits.min.isLt; omega)
    (fun mx _ => by have := mx.isLt; omega)

theorem memTypeOk_toV2 {mt : MemoryType} (h : MemoryTypeValid mt) :
    V2.MemoryType.Ok (MemoryType.toV2 mt) := limitsOk_toV2 h h.1 (fun _ hm => hm)

/-- The 2.0 external type of a Lime1 import descriptor. -/
def importV2 (types : List FuncType) : ImportDesc → V2.ExternType
  | .func i => .func (((types[i.toNat]?).map FuncType.toV2).getD ⟨[], []⟩)
  | .table tt => .table (TableType.toV2 tt)
  | .memory mt => .memory (MemoryType.toV2 mt)
  | .global gt => .global (GlobalType.toV2 gt)

theorem importOk_toV2 (types : List FuncType) (i : Import) (hv : ImportValid types i) :
    V2.Validation.ImportOk { types := types.map FuncType.toV2 } (Import.toV2 i)
      (importV2 types i.desc) := by
  obtain ⟨et, het, hval⟩ := hv
  rcases i with ⟨mn, n, d⟩
  cases d with
  | func x =>
      simp only [importType?, Option.map_eq_some_iff] at het
      obtain ⟨ft, hft, rfl⟩ := het
      exact ⟨by simp [Import.toV2, ImportDesc.toV2, V2.Module.importType?, importV2,
        List.getElem?_map, hft], trivial⟩
  | table tt =>
      simp only [importType?, Option.some.injEq] at het
      subst het
      exact ⟨rfl, tableTypeOk_toV2 hval⟩
  | memory mt =>
      simp only [importType?, Option.some.injEq] at het
      subst het
      exact ⟨rfl, memTypeOk_toV2 hval⟩
  | global gt => exact ⟨rfl, trivial⟩

section ImportLists

variable (types : List FuncType)

theorem xtV2_funcs : (imps : List Import) → (∀ i ∈ imps, ImportValid types i) →
    V2.ExternType.funcs (imps.map fun i => importV2 types i.desc) =
      (imps.filterMap fun i => match i.desc with
        | .func idx => types[idx.toNat]?
        | _ => none).map FuncType.toV2
  | [], _ => rfl
  | ⟨mn, n, d⟩ :: imps, hv => by
      have ih := xtV2_funcs imps (fun i hi => hv i (by simp [hi]))
      simp only [importV2] at ih
      cases d with
      | func x =>
          obtain ⟨et, het, -⟩ := hv ⟨mn, n, .func x⟩ (by simp)
          simp only [importType?, Option.map_eq_some_iff] at het
          obtain ⟨ft, hft, -⟩ := het
          simpa [importV2, V2.ExternType.funcs, hft] using ih
      | _ => simpa [importV2, V2.ExternType.funcs] using ih

theorem xtV2_tables : (imps : List Import) →
    V2.ExternType.tables (imps.map fun i => importV2 types i.desc) =
      (imps.filterMap fun i => match i.desc with
        | .table tt => some tt
        | _ => none).map TableType.toV2
  | [] => rfl
  | ⟨mn, n, d⟩ :: imps => by
      have ih := xtV2_tables imps
      simp only [importV2] at ih
      cases d <;> simpa [importV2, V2.ExternType.tables] using ih

theorem xtV2_mems : (imps : List Import) →
    V2.ExternType.mems (imps.map fun i => importV2 types i.desc) =
      (imps.filterMap fun i => match i.desc with
        | .memory mt => some mt
        | _ => none).map MemoryType.toV2
  | [] => rfl
  | ⟨mn, n, d⟩ :: imps => by
      have ih := xtV2_mems imps
      simp only [importV2] at ih
      cases d <;> simpa [importV2, V2.ExternType.mems] using ih

theorem xtV2_globals : (imps : List Import) →
    V2.ExternType.globals (imps.map fun i => importV2 types i.desc) =
      (imps.filterMap fun i => match i.desc with
        | .global gt => some gt
        | _ => none).map GlobalType.toV2
  | [] => rfl
  | ⟨mn, n, d⟩ :: imps => by
      have ih := xtV2_globals imps
      simp only [importV2] at ih
      cases d <;> simpa [importV2, V2.ExternType.globals] using ih

end ImportLists

/-- Every function index named by an element segment is in `C.REFS`, as
`Instr_ok/ref.func` (`6-typing:294`) plus decided deviation 6 requires. -/
theorem mem_refsV2_of_elem {m : Module} {e : Elem} (he : e ∈ m.elems) {f : FuncIdx}
    (hf : f ∈ e.init) : f ∈ V2.Validation.funcIdxNonFuncs (Module.toV2 m) := by
  unfold V2.Validation.funcIdxNonFuncs
  apply List.mem_append_left
  apply List.mem_append_right
  rw [List.mem_flatMap]
  refine ⟨Elem.toV2 e, by simp only [Module.toV2]; exact List.mem_map_of_mem he, ?_⟩
  apply List.mem_append_left
  rw [List.mem_flatMap]
  refine ⟨funcRefV2 f, by simp only [Elem.toV2]; exact List.mem_map_of_mem hf, ?_⟩
  simp [funcRefV2, V2.Validation.Expr.freeFuncs, V2.Validation.Instr.freeFuncs]

/-! ### `Module_ok` -/

/-- **The module theorem, with both side conditions.** A valid Lime1 module
whose constant expressions use no extended-const arithmetic and whose segment
offsets read only imported globals is a valid Wasm 2.0 module, with the import
types `importV2` computes. -/
theorem ModuleValid.toV2_ok {m : Module} (h : ModuleValid m)
    (hc : Module.NoExtendedConst m) (hs : Module.SegmentOffsetsImported m) :
    ∃ xtE, V2.Validation.ModuleOk (Module.toV2 m)
      (m.imports.map fun i => importV2 m.types i.desc) xtE := by
  let ixt : List V2.ExternType := m.imports.map fun i => importV2 m.types i.desc
  let ft' : List V2.FuncType := m.types.map FuncType.toV2
  let fts : List V2.FuncType :=
    (m.funcs.filterMap fun f => m.types[f.type.toNat]?).map FuncType.toV2
  let gts : List V2.GlobalType := m.globals.map fun g => GlobalType.toV2 g.type
  let tts : List V2.TableType := m.tables.map TableType.toV2
  let mts : List V2.MemoryType := m.memories.map MemoryType.toV2
  let rts : List V2.RefType := m.elems.map fun _ => V2.RefType.funcref
  let C' : V2.Validation.Context :=
    { types := ft', funcs := V2.ExternType.funcs ixt ++ fts,
      globals := V2.ExternType.globals ixt,
      tables := V2.ExternType.tables ixt ++ tts,
      mems := V2.ExternType.mems ixt ++ mts,
      refs := V2.Validation.funcIdxNonFuncs (Module.toV2 m) }
  let C : V2.Validation.Context :=
    { types := ft', funcs := V2.ExternType.funcs ixt ++ fts,
      globals := V2.ExternType.globals ixt ++ gts,
      tables := V2.ExternType.tables ixt ++ tts,
      mems := V2.ExternType.mems ixt ++ mts,
      elems := rts, datas := (Module.toV2 m).data.map fun _ => (),
      refs := V2.Validation.funcIdxNonFuncs (Module.toV2 m) }
  -- the index-space identifications
  have hgx : V2.ExternType.globals ixt = (importedGlobals m).map GlobalType.toV2 :=
    xtV2_globals m.types m.imports
  have hpty : m.types.map FuncType.toV2 <+: ft' := List.prefix_refl _
  have hpf : (moduleContext m).funcs.map FuncType.toV2 <+: V2.ExternType.funcs ixt ++ fts := by
    show ((m.imports.filterMap fun i => match i.desc with
        | .func idx => m.types[idx.toNat]?
        | _ => none) ++
      m.funcs.filterMap fun f => m.types[f.type.toNat]?).map FuncType.toV2 <+: _
    rw [List.map_append, xtV2_funcs m.types m.imports h.imports]
    exact List.prefix_refl _
  have hpt : (moduleContext m).tables.map TableType.toV2 <+:
      V2.ExternType.tables ixt ++ tts := by
    show ((m.imports.filterMap fun i => match i.desc with
        | .table tt => some tt
        | _ => none) ++ m.tables).map TableType.toV2 <+: _
    rw [List.map_append, xtV2_tables m.types m.imports]
    exact List.prefix_refl _
  have hpm : (moduleContext m).memories.map MemoryType.toV2 <+:
      V2.ExternType.mems ixt ++ mts := by
    show ((m.imports.filterMap fun i => match i.desc with
        | .memory mt => some mt
        | _ => none) ++ m.memories).map MemoryType.toV2 <+: _
    rw [List.map_append, xtV2_mems m.types m.imports]
    exact List.prefix_refl _
  have hpg : (moduleContext m).globals.map GlobalType.toV2 <+:
      V2.ExternType.globals ixt ++ gts := by
    show (importedGlobals m ++ m.globals.map Global.type).map GlobalType.toV2 <+: _
    rw [List.map_append, hgx, List.map_map]
    exact List.prefix_refl _
  have hA : AgreesV2 (moduleContext m) C := ⟨hpty, hpf, hpt, hpm, hpg, rfl, rfl, rfl⟩
  -- premises
  have htypes : List.Forall₂ V2.Validation.TypeOk (Module.toV2 m).types ft' :=
    forall₂_map_of FuncType.toV2 FuncType.toV2 m.types fun _ _ => ⟨rfl, trivial⟩
  have himports : List.Forall₂ (V2.Validation.ImportOk { types := ft' })
      (Module.toV2 m).imports ixt :=
    forall₂_map_of Import.toV2 (fun i => importV2 m.types i.desc) m.imports
      fun i hi => importOk_toV2 m.types i (h.imports i hi)
  have hglobals : List.Forall₂ (V2.Validation.GlobalOk C') (Module.toV2 m).globals gts :=
    forall₂_map_of Global.toV2 (fun g => GlobalType.toV2 g.type) m.globals fun g hg =>
      ⟨rfl, trivial,
        ConstExprType.toV2 (h.globals g hg) (hc.1 g hg) (globalsAgree_init hgx _)⟩
  have htables : List.Forall₂ V2.Validation.TableOk (Module.toV2 m).tables tts :=
    forall₂_map_of TableType.toV2 TableType.toV2 m.tables fun t ht =>
      ⟨rfl, tableTypeOk_toV2 (h.tables t ht)⟩
  have hmems : List.Forall₂ V2.Validation.MemOk (Module.toV2 m).memories mts :=
    forall₂_map_of MemoryType.toV2 MemoryType.toV2 m.memories fun t ht =>
      ⟨rfl, memTypeOk_toV2 (h.memories t ht)⟩
  have helems : List.Forall₂ (V2.Validation.ElemOk C') (Module.toV2 m).elems rts := by
    refine forall₂_map_of Elem.toV2 (fun _ => V2.RefType.funcref) m.elems fun e he => ?_
    obtain ⟨⟨tt, htt⟩, hoff, hfs⟩ := h.elements e he
    refine ⟨rfl, ?_, ?_⟩
    · intro ex hex
      simp only [Elem.toV2, List.mem_map] at hex
      obtain ⟨f, hf, rfl⟩ := hex
      obtain ⟨ft, hft⟩ := hfs f hf
      refine ⟨V2.Validation.InstrsOk.instr (.refFunc
        (prefix_map_getElem? hpf hft) (mem_refsV2_of_elem he hf)), ?_⟩
      intro i hi
      simp only [funcRefV2, List.mem_singleton] at hi
      subst hi
      exact .refFunc f
    · exact .active (prefix_map_getElem? hpt htt) rfl
        (ConstExprType.toV2 hoff (hc.2.1 e he) (globalsAgree_offset hgx (hs.1 e he)))
  have hdatas : ∀ d ∈ (Module.toV2 m).data, V2.Validation.DataOk C' d := by
    intro d hd
    simp only [Module.toV2, List.mem_map] at hd
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    obtain ⟨⟨mt, hmt⟩, hoff⟩ := h.data d₀ hd₀
    have hzero : d₀.memory.toNat = 0 := by
      have hlt := (List.getElem?_eq_some_iff.1 hmt).1
      have := h.singleMemory
      omega
    have hmem : C'.mems[0]? = some (MemoryType.toV2 mt) := by
      have hlk := prefix_map_getElem? hpm hmt
      rwa [hzero] at hlk
    exact .active hzero hmem
      (ConstExprType.toV2 hoff (hc.2.2 d₀ hd₀) (globalsAgree_offset hgx (hs.2 d₀ hd₀)))
  have hfuncs : List.Forall₂ (V2.Validation.FuncOk C) (Module.toV2 m).funcs fts := by
    refine forall₂_filterMap_of Func.toV2 (fun f => m.types[f.type.toNat]?) FuncType.toV2
      m.funcs fun f hf => ?_
    obtain ⟨ft, hft, -, hbody⟩ := h.functions f hf
    refine ⟨ft, hft, V2.Validation.FuncOk.mk ?_ ?_⟩
    · show C.types[f.type.toNat]? = some (FuncType.toV2 ft)
      simp only [C, ft', List.getElem?_map]
      rw [show m.types[f.type.toNat]? = some ft from hft]
      rfl
    · have hAf : AgreesV2 (functionContext (moduleContext m) ft f.locals)
          (C.withFuncFrame ((FuncType.toV2 ft).params ++ f.locals.map ValType.toV2)
            (V2.Validation.liftResult (FuncType.toV2 ft).results)
            (V2.Validation.liftResult (FuncType.toV2 ft).results)) :=
        ⟨hpty, hpf, hpt, hpm, hpg,
          by simp [functionContext, V2.Validation.Context.withFuncFrame, C, FuncType.toV2],
          by simp [functionContext, V2.Validation.Context.withFuncFrame, C, FuncType.toV2,
            resToV2_eq_map],
          by simp [functionContext, V2.Validation.Context.withFuncFrame, C, FuncType.toV2,
            resToV2_eq_map]⟩
      have := ExprType.toV2 hAf hbody
      rw [← liftResult_map_toV2 ft.results] at this
      exact this
  have hstart : ∀ x, (Module.toV2 m).start = some x → V2.Validation.StartOk C x := by
    intro x hx
    exact prefix_map_getElem? hpf (h.start x hx)
  have hexports : ∀ e ∈ (Module.toV2 m).exports, ∃ xt, V2.Validation.ExportOk C e xt := by
    intro e he
    simp only [Module.toV2, List.mem_map] at he
    obtain ⟨e₀, he₀, rfl⟩ := he
    obtain ⟨et, het⟩ := h.exports e₀ he₀
    rcases e₀ with ⟨nm, idx⟩
    cases idx with
    | func i =>
        simp only [exportType?, Option.map_eq_some_iff] at het
        obtain ⟨ft, hft, -⟩ := het
        exact ⟨.func (FuncType.toV2 ft), .func (prefix_map_getElem? hpf hft)⟩
    | table i =>
        simp only [exportType?, Option.map_eq_some_iff] at het
        obtain ⟨tt, htt, -⟩ := het
        exact ⟨.table (TableType.toV2 tt), .table (prefix_map_getElem? hpt htt)⟩
    | memory i =>
        simp only [exportType?, Option.map_eq_some_iff] at het
        obtain ⟨mt, hmt, -⟩ := het
        exact ⟨.memory (MemoryType.toV2 mt), .memory (prefix_map_getElem? hpm hmt)⟩
    | global i =>
        simp only [exportType?, Option.map_eq_some_iff] at het
        obtain ⟨gt, hgt, -⟩ := het
        exact ⟨.global (GlobalType.toV2 gt), .global (prefix_map_getElem? hpg hgt)⟩
  obtain ⟨xtE, hxtE⟩ := forall₂_exists_of _ hexports
  have hmems_le : C.mems.length ≤ 1 := by
    have hlen := h.singleMemory
    simp only [moduleContext, List.length_append] at hlen
    show (V2.ExternType.mems ixt ++ mts).length ≤ 1
    rw [xtV2_mems m.types m.imports]
    simp only [List.length_append, List.length_map, mts]
    exact hlen
  have hnames : ((Module.toV2 m).exports.map V2.Export.name).Nodup := by
    simpa [Module.toV2, Export.toV2, Function.comp_def] using h.uniqueExports
  exact ⟨xtE, V2.Validation.ModuleOk.mk htypes himports hglobals htables hmems helems
    hdatas hfuncs hstart hxtE hmems_le hnames rfl rfl⟩

/-- **Milestone, conditional.** Every valid Lime1 module with no extended-const
arithmetic and with imported-only segment offsets is a valid Wasm 2.0 module. -/
theorem ModuleValid.toV2 {m : Module} (h : ModuleValid m)
    (hc : Module.NoExtendedConst m) (hs : Module.SegmentOffsetsImported m) :
    V2.Validation.ModuleValid (Module.toV2 m) :=
  let ⟨_, hok⟩ := ModuleValid.toV2_ok h hc hs
  ⟨_, _, hok⟩

/-! ### The second counterexample: a segment offset reading a defined global -/

/-- A data-segment offset that reads the module's own (defined, immutable)
global. -/
def definedGlobalOffsetData : Data :=
  ⟨⟨⟨0, Nat.two_pow_pos 32⟩⟩, [.globalGet ⟨⟨0, Nat.two_pow_pos 32⟩⟩], ByteArray.empty⟩

/-- A Lime1 module with one memory, one defined immutable `i32` global and one
data segment whose offset reads that global. Lime1 (like Wasm 1.0) validates
segment offsets in the full module context, so this is valid; Wasm 2.0
validates them in `C'`, whose `GLOBALS` are empty here, so it is not. -/
def definedGlobalOffsetModule : Module where
  memories := [⟨⟨⟨0, Nat.two_pow_pos 32⟩, none⟩⟩]
  globals := [⟨⟨.const, .i32⟩, [.intConst .i32 8]⟩]
  data := [definedGlobalOffsetData]

theorem definedGlobalOffsetModule_valid : ModuleValid definedGlobalOffsetModule where
  types := by simp [definedGlobalOffsetModule]
  imports := by simp [definedGlobalOffsetModule]
  functions := by simp [definedGlobalOffsetModule]
  tables := by simp [definedGlobalOffsetModule]
  memories := by
    intro mt hmt
    simp only [definedGlobalOffsetModule, List.mem_singleton] at hmt
    subst hmt
    exact ⟨Nat.zero_le _, by simp⟩
  globals := by
    intro g hg
    simp only [definedGlobalOffsetModule, List.mem_singleton] at hg
    subst hg
    exact ⟨.cons (.intConst .i32 8) (.nil _), by
      intro i hi
      simp only [Global.init, List.mem_singleton] at hi
      subst hi
      exact .intConst _ _⟩
  elements := by simp [definedGlobalOffsetModule]
  data := by
    intro d hd
    simp only [definedGlobalOffsetModule, List.mem_singleton] at hd
    subst hd
    refine ⟨⟨_, rfl⟩, ⟨.cons (.globalGet _ rfl) (.nil _), ?_⟩⟩
    intro i hi
    simp only [Data.offset, definedGlobalOffsetData, List.mem_singleton] at hi
    subst hi
    exact .globalGet _ rfl
  start := by simp [StartValid, definedGlobalOffsetModule]
  exports := by simp [definedGlobalOffsetModule]
  uniqueExports := by simp [definedGlobalOffsetModule]
  singleTable := by simp [moduleContext, definedGlobalOffsetModule]
  singleMemory := by simp [moduleContext, definedGlobalOffsetModule]

theorem definedGlobalOffsetModule_not_segmentOffsetsImported :
    ¬ Module.SegmentOffsetsImported definedGlobalOffsetModule := by
  rintro ⟨-, hd⟩
  have := hd definedGlobalOffsetData (by simp [definedGlobalOffsetModule])
    ⟨⟨0, Nat.two_pow_pos 32⟩⟩ (by simp [definedGlobalOffsetData])
  simp [importedGlobals, definedGlobalOffsetModule, Idx.toNat] at this

/-- **The second counterexample.** Even with no extended-const arithmetic
anywhere, a Lime1-valid module can fail 2.0 validation, because 2.0 checks
segment offsets in `C'`. -/
theorem exists_valid_noExtendedConst_not_toV2_valid :
    ∃ m : Module, ModuleValid m ∧ Module.NoExtendedConst m ∧
      ¬ V2.Validation.ModuleValid (Module.toV2 m) := by
  refine ⟨definedGlobalOffsetModule, definedGlobalOffsetModule_valid, ?_, ?_⟩
  · refine ⟨?_, by simp [definedGlobalOffsetModule], ?_⟩
    · intro g hg i hi
      simp only [definedGlobalOffsetModule, List.mem_singleton] at hg
      subst hg
      simp only [List.mem_singleton] at hi
      subst hi
      rfl
    · intro d hd i hi
      simp only [definedGlobalOffsetModule, List.mem_singleton] at hd
      subst hd
      simp only [definedGlobalOffsetData, List.mem_singleton] at hi
      subst hi
      rfl
  · rintro ⟨ixt, xt, hok⟩
    obtain ⟨-, himports, -, -, -, -, hdatas, -, -, -, -, -, -, rfl⟩ := hok
    have hixt : ixt = [] := by
      have hlen := himports.length_eq
      simp only [Module.toV2, definedGlobalOffsetModule, List.map_nil,
        List.length_nil] at hlen
      exact List.eq_nil_of_length_eq_zero hlen.symm
    subst hixt
    have hd := hdatas (Data.toV2 definedGlobalOffsetData) (by
      show Data.toV2 definedGlobalOffsetData ∈ [Data.toV2 definedGlobalOffsetData]
      simp)
    cases hd with
    | active hx hmem hoff =>
        refine V2.Validation.InstrsOk.singleton_elim hoff.typed (fun it' hit' => ?_)
        obtain ⟨gt, hgt, -⟩ := V2.Validation.InstrOk.globalGet_inv hit'
        simp [V2.ExternType.globals] at hgt

/-! ## The commuting triangle at the validation level

`Module.toV2_toCore` (`Silmaril/Wasm/Lime1/ToV2/Modules.lean`) says the 2.0
route to Core 3.0 computes the direct Lime1 → Core 3.0 injection. At the
validation level that means the two preservation results are about the *same*
Core module: the composite `Lime1 → 2.0 → 3.0` and the direct
`Lime1.Validation.ModuleValid.toCore` agree.

This is what makes the conjunction below a *triangle* rather than three
unrelated facts: `V2.Validation.ModuleValid.toCore`
(`Silmaril/Wasm/V2/ToCore/Validation.lean`) has signature
`V2.Module.toCore m = some c → V2.Validation.ModuleValid m →
Wasm.Validation.ModuleValid c`, so conjunct 3 is *derivable* from conjuncts 1
and 2 — the composite route arrives at `Wasm.Validation.ModuleValid m.toCore`,
and the direct `ModuleValid.toCore` proves the same statement. -/

/-- The three statements the triangle relates, for one valid Lime1 module.
Conjunct 3 is proved by the direct route, `Lime1.Validation.ModuleValid.toCore`;
`V2.Validation.ModuleValid.toCore` applied to conjuncts 1 and 2 is the composite
route to the same conclusion. -/
theorem ModuleValid.toV2_toCore {m : Module} (h : ModuleValid m)
    (hc : Module.NoExtendedConst m) (hs : Module.SegmentOffsetsImported m) :
    V2.Validation.ModuleValid (Module.toV2 m) ∧
      V2.Module.toCore (Module.toV2 m) = some m.toCore ∧
      Wasm.Validation.ModuleValid m.toCore :=
  ⟨ModuleValid.toV2 h hc hs, Module.toV2_toCore m, ModuleValid.toCore h⟩

end Silmaril.Wasm.Lime1.Validation

namespace Silmaril.Wasm.V1.Validation

/-! ## Wasm 1.0 into Wasm 2.0

The 1.0 route discharges `NoExtendedConst` outright: `V1.Validation.ConstantInstr`
(`Silmaril/Wasm/V1/Validation/Modules.lean`) has only `intConst`, `floatConst`
and `globalGet`, so no constant expression of a **valid** 1.0 module contains an
`intBinOp`.

It does **not** discharge `SegmentOffsetsImported`: Wasm 1.0 validates segment
offsets in the full context, exactly as Lime1 does, so a valid 1.0 module may
read a defined global in a data offset. That hypothesis therefore survives into
the 1.0 statement. -/

/-- A 1.0 constant instruction is never extended-const arithmetic: the three
rules of `V1.Validation.ConstantInstr` are `CONST`, `CONST` and `GLOBAL.GET`. -/
theorem ConstantInstr.not_extendedConst {C : Context} {i : Instr}
    (h : ConstantInstr C i) : Lime1.Instr.isExtendedConstOp i.toLime = false := by
  cases h <;> rfl

theorem ConstantExpr.not_extendedConst {C : Context} {es : Expr} (h : ConstantExpr C es) :
    ∀ i ∈ Expr.toLime es, Lime1.Instr.isExtendedConstOp i = false := by
  intro i hi
  rw [Expr.toLime_eq_map, List.mem_map] at hi
  obtain ⟨j, hj, rfl⟩ := hi
  exact (h j hj).not_extendedConst

/-- **The promised discharge.** Note the `ModuleValid` hypothesis: the
unqualified statement `∀ m : V1.Module, m.toLime.NoExtendedConst` is false,
because `NoExtendedConst` is syntactic and 1.0 *syntax* admits
`(global i32 (i32.const 1) (i32.const 2) (i32.add))`. See the report. -/
theorem ModuleValid.noExtendedConst {m : Module} (h : ModuleValid m) :
    Lime1.Validation.Module.NoExtendedConst m.toLime := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [Module.toLime, List.mem_map] at hg
    obtain ⟨g₀, hg₀, rfl⟩ := hg
    exact (h.globals g₀ hg₀).constant.not_extendedConst
  · intro e he
    simp only [Module.toLime, List.mem_map] at he
    obtain ⟨e₀, he₀, rfl⟩ := he
    exact (h.elements e₀ he₀).offset.constant.not_extendedConst
  · intro d hd
    simp only [Module.toLime, List.mem_map] at hd
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    exact (h.data d₀ hd₀).offset.constant.not_extendedConst

/-- **Milestone.** Every valid Wasm 1.0 module whose segment offsets read only
imported globals is a valid Wasm 2.0 module. No extended-const hypothesis is
needed. -/
theorem ModuleValid.toV2 {m : Module} (h : ModuleValid m)
    (hs : Lime1.Validation.Module.SegmentOffsetsImported m.toLime) :
    V2.Validation.ModuleValid m.toV2 := by
  have hv := Lime1.Validation.ModuleValid.toV2 (ModuleValid.toLime h) h.noExtendedConst hs
  rwa [Module.toLime_toV2] at hv

/-- The 1.0 commuting triangle at the validation level. -/
theorem ModuleValid.toV2_toCore {m : Module} (h : ModuleValid m)
    (hs : Lime1.Validation.Module.SegmentOffsetsImported m.toLime) :
    V2.Validation.ModuleValid m.toV2 ∧
      V2.Module.toCore m.toV2 = some m.toCore ∧
      Wasm.Validation.ModuleValid m.toCore :=
  ⟨ModuleValid.toV2 h hs, Module.toV2_toCore m, ModuleValid.toCore h⟩

end Silmaril.Wasm.V1.Validation
