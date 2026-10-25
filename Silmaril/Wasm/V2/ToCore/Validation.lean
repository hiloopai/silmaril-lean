module

public import Silmaril.Wasm.V2.Validation
public import Silmaril.Wasm.V2.ToCore
public import Silmaril.Wasm.Validation.Modules
public import Silmaril.Wasm.Validation.Instructions.Properties

/-!
# Wasm 2.0 validation is a subset of Core 3.0 validation

The validation half of the `2.0 ⊆ 3.0` subset theorem. `Silmaril/Wasm/V2/ToCore/*`
injects the *syntax*; this file transports every *judgment*:

```
Context.toCore            : V2.Validation.Context → Wasm.Validation.Context
InstrOk.toCore            single instructions          (6-typing:142)
InstrsOk.toCore           instruction sequences        (6-typing:143)
ExprOk.toCore             expressions                  (6-typing:144)
ExprOkConst.toCore'       constant expressions         (6-typing:541)
ModuleOk.toCore           whole modules                (6-typing:682)
ModuleValid.toCore        / ModuleValid.toCore_ok
ModuleValid.toCoreBinary  binary-faithful element types (binary-faithful embedding)
```

**Every statement is conditioned on `Module.toCore m = some c`.** `Instr.toCore`
is partial, for the single reason documented in
`Silmaril/Wasm/V2/ToCore/Instructions.lean`: 2.0's `CVTOP numtype_1 numtype_2
cvtop` is untyped, so `Instr_ok/cvtop-convert` (`6-typing:285`) types
combinations such as `CVTOP F64 I32 WRAP` for which `3-numerics` defines no
`$cvtop__` and Core 3.0's indexed `ConvertOp` has no constructor. There is
therefore no total map `V2.Module → Wasm.Module` to state the theorem over.

## What the translation does

* a 2.0 `functype` becomes its singleton final recursive group's defined type,
  `FuncType.toDefType`, so type indices do not shift;
* 2.0 has no local-initialisation tracking — its `instrtype` is just
  `resulttype -> resulttype` — and `Func_ok` (`6-typing:592`) gives every local
  a `valtype`, never `BOT`; every 2.0 value type is defaultable, so each Core
  local type is `⟨SET, _⟩` and every Core `instrtype` in the image has empty
  `inits`. The two Core rules that *do* produce `inits` (`local.set`,
  `local.tee`) are immediately followed by `Instrs_ok/sub`, which discards them
  (`singleInits`);
* `ref.func` needs `Instrs_ok/sub` as well: Core assigns it the *non-nullable*
  `(ref $ft)` where 2.0 assigns `funcref` (`singleSub`);
* `C.REFS` maps across directly, and `funcIdxNonFuncs_toCore` proves the two
  sets are **literally the same list** on the image. 2.0 SpecTec has no `REFS`
  field (`6-typing:681` reads `;; TODO: refs`) and
  `Silmaril/Wasm/V2/Validation/Modules.lean` implements the W3C 2.0 reading,
  which is Core 3.0's `funcIdxNonFuncs` minus the table-initialiser
  contribution; on the image that contribution is empty, because
  `TableType.toCoreTable` gives every table the initialiser `[REF.NULL ht]`
  (`coreTables_freeFuncs_nil`). The hypotheses of `funcIdxNonFuncs_toCore` —
  that the globals' initialisers and the element segments' initialisers and
  offsets are constant — hold in every valid module, by `Global_ok` and
  `Elem_ok`;
* export-name disjointness is `;; -- TODO: disjoint export names`
  (`6-typing:699`) in SpecTec 2.0; `ModuleOk.hnames` requires it and Core
  requires it, so it transports verbatim.

## Constant expressions see a smaller context

Core 3.0's `Module_ok` checks global initialisers in a `C'` with **no** tables,
memories, element or data segments, while 2.0's `C'` carries tables and
memories (`6-typing:703`). The difference is immaterial — a 2.0 constant
expression is `t.const`, `v128.const`, `ref.null`, `ref.func` or `global.get`
(`6-typing:539`), none of which reads a table or a memory — but `Agrees`
compares *all* index spaces, so it is made explicit: `Context.constPart` is the
fragment a constant expression can see and `ExprOkConst.restrict` moves a 2.0
derivation into it.

## The converse is false

Two checked counterexamples, in namespace `Converse`:

* `converse_fails_globals` — `sharedGlobalModule` has two defined immutable
  `i32` globals, the second initialised by `global.get 0`. Core 3.0's
  `Globals_ok` is sequential, so each initialiser sees the globals before it
  (`coreSharedGlobal_valid`); 2.0's `Module_ok` checks *every* initialiser in
  `C'`, whose `GLOBALS` component is `igt*`, the **imported** globals only
  (`6-typing:703,706`), so `Instr_const/global.get` (`6-typing:555`) has nothing to
  look up (`sharedGlobalModule_invalid`).
* `converse_fails_memories` — `twoMemModule` has two memories. Core 3.0 has
  the multi-memory proposal; 2.0 bounds the memory *index space* by `1`
  (`6-typing:698`; see the `ModuleOk.hmems_le` deviation, memory-count deviation).

Both Core-3.0 halves were cross-checked against the oracle (`node`,
V8 / Node v22.14.0): `x_v2_defglobalinit.wasm` and
`x_v2_twomem.wasm` both pass `WebAssembly.validate` and
`new WebAssembly.Module`, because modern V8 ships both features. As the
`val/inversion` unit already noted, the oracle cannot be used to confirm a
2.0-only *negative*; those halves are proved from `Module_ok` directly.

No deviation from the pinned SpecTec source is taken in this file.
-/

@[expose] public section

namespace Silmaril.Wasm.V2.Validation

open Silmaril.Wasm.Validation (Ty TyOk Sub ResultOk ResultSub Expand TypeCtx
  InstrTypeOk InstrTypeSub Defaultable LocalType Init
  CRefType CHeapType CGlobalType CTableType CExternType CModuleType DefType
  liftVal liftRef liftHeap liftRec liftComp liftSub
  TypesOk GlobalsOk LocalOk MemTypeOk TableTypeOk GlobalTypeOk ExternTypeOk
  RecTypeOkAt)

/-! ## Value types -/

/-- The Core 3.0 semantic value type of a 2.0 validation value type: `BOT` is
Core's `BOT`, everything else goes through `ValType.toC`. -/
def valToC : CValType → Silmaril.Wasm.Validation.CValType
  | .val t => t.toC
  | .bot => .botv

/-- `valToC` pointwise on result types. -/
abbrev resultToC (ts : CResultType) : List Silmaril.Wasm.Validation.CValType :=
  ts.map valToC

@[simp] theorem valToC_val (t : ValType) : valToC (.val t) = t.toC := rfl

@[simp] theorem valToC_bot : valToC .bot = .botv := rfl

@[simp] theorem resultToC_liftResult (ts : ResultType) :
    resultToC (liftResult ts) = ts.map ValType.toC := by
  simp [liftResult, List.map_map, Function.comp_def]

@[simp] theorem map_valToC_comp (ts : ResultType) :
    ts.map (valToC ∘ CValType.val) = ts.map ValType.toC := by
  simp [Function.comp_def]

/-! The simp normal form for a value type in the image is `Ty.num`/`Ty.vec`/
`Ty.refv (.ref true (.abs _))`; the Core abbreviations `Ty.i32`, `Ty.v128`,
`Ty.funcref` and `Ty.refT` and the 2.0 abbreviations `ValType.i32`,
`ValType.v128`, `ValType.funcref` all unfold to it. -/

@[simp] theorem valType_i32_eq : ValType.i32 = ValType.num (.int .i32) := rfl

@[simp] theorem valType_v128_eq : ValType.v128 = ValType.vec .v128 := rfl

@[simp] theorem valType_funcref_eq : ValType.funcref = ValType.ref .funcref := rfl

@[simp] theorem valType_externref_eq : ValType.externref = ValType.ref .externref := rfl

theorem ty_i32_eq : Ty.i32 = Ty.num (.int .i32) := rfl

theorem ty_v128_eq : Ty.v128 = Ty.vec .v128 := rfl

theorem ty_funcref_eq : Ty.funcref = Ty.ref true (.abs .func) := rfl

theorem ty_refT_eq (n : Bool) (h : CHeapType) : Ty.refT n h = Ty.refv (.ref n h) := rfl

attribute [local simp] ty_i32_eq ty_v128_eq ty_funcref_eq ty_refT_eq

@[simp] theorem toC_num (t : NumType) : (ValType.num t).toC = .num t := rfl

@[simp] theorem toC_vec (t : VecType) : (ValType.vec t).toC = .vec t := rfl

@[simp] theorem toC_ref_func : (ValType.ref .funcref).toC = .refv (.ref true (.abs .func)) := rfl

@[simp] theorem toC_ref_extern :
    (ValType.ref .externref).toC = .refv (.ref true (.abs .extern)) := rfl

@[simp] theorem refToC_func : RefType.funcref.toC = .ref true (.abs .func) := rfl

@[simp] theorem refToC_extern : RefType.externref.toC = .ref true (.abs .extern) := rfl

/-- Every 2.0 value type is well formed in every Core 3.0 type context. -/
theorem tyOk_toC (Δ : TypeCtx) (t : ValType) : TyOk Δ t.toC := by
  cases t with
  | num t => exact .num t
  | vec t => exact .vec t
  | ref r => cases r <;> exact .refv (.ref (.abs _))

/-- Every validation value type in the 2.0 image is well formed. -/
theorem tyOk_valToC (Δ : TypeCtx) (t : CValType) : TyOk Δ (valToC t) := by
  cases t with
  | val t => exact tyOk_toC Δ t
  | bot => exact .botv

/-- Result types in the 2.0 image are well formed. -/
theorem resultOk_toC (Δ : TypeCtx) (ts : CResultType) : ResultOk Δ (resultToC ts) := by
  intro t ht
  simp only [List.mem_map] at ht
  obtain ⟨a, _, rfl⟩ := ht
  exact tyOk_valToC Δ a

/-- 2.0 instruction types in the image are well formed. -/
theorem instrTypeOk_toC (D : Silmaril.Wasm.Validation.Context) (a b : CResultType) :
    InstrTypeOk D (.plain (resultToC a) (resultToC b)) :=
  ⟨resultOk_toC _ a, resultOk_toC _ b, by simp⟩

/-- `Valtype_sub` (`6-typing:74-78`) transports: 2.0's only non-reflexive rule
is `BOT <: t`, which is Core's `Valtype_sub/bot`. -/
theorem sub_valToC {Δ : TypeCtx} {a b : CValType} (h : CValType.Sub a b) :
    Sub Δ (valToC a) (valToC b) := by
  cases h with
  | refl t => exact Silmaril.Wasm.Validation.Sub.refl Δ (k := .val) trivial _
  | bot t => exact .botv

/-- `Resulttype_sub` (`6-typing:80-82`) transports pointwise. -/
theorem resultSub_toC {Δ : TypeCtx} {a b : CResultType} (h : CResultType.Sub a b) :
    ResultSub Δ (resultToC a) (resultToC b) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (sub_valToC hab) ih

/-! ## External types -/

/-- A 2.0 global type as a closed Core 3.0 global type. -/
def globalToC (g : GlobalType) : CGlobalType := ⟨g.mutability, g.value.toC⟩

/-- A 2.0 table type as a closed Core 3.0 table type: address type `I32`. -/
def tableToC (t : TableType) : CTableType := ⟨.i32, t.limits.toCore, t.element.toC⟩

@[simp] theorem externToCore_func (t : FuncType) :
    ExternType.toCore (.func t) = .func t.toDefType := rfl

@[simp] theorem externToCore_global (t : GlobalType) :
    ExternType.toCore (.global t) = .global (globalToC t) := rfl

@[simp] theorem externToCore_table (t : TableType) :
    ExternType.toCore (.table t) = .table (tableToC t) := rfl

@[simp] theorem externToCore_memory (t : MemoryType) :
    ExternType.toCore (.memory t) = .mem t.toCore := rfl

/-! ## Contexts -/

/-- The Core 3.0 context of a 2.0 validation context (`6-typing:5-9`).

2.0 function types become their singleton-group defined types, 2.0 locals are
all initialised (`Func_ok` gives them `valtype`s, and every 2.0 value type is
defaultable), and `REFS` maps across. The Core `TAGS` and `RECS` fields stay
empty: 2.0 has neither exceptions nor recursive types. -/
def Context.toCore (C : Context) : Silmaril.Wasm.Validation.Context where
  types := C.types.map FuncType.toDefType
  funcs := C.funcs.map FuncType.toDefType
  globals := C.globals.map globalToC
  tables := C.tables.map tableToC
  mems := C.mems.map MemoryType.toCore
  elems := C.elems.map RefType.toC
  datas := C.datas
  locals := C.locals.map fun t => ⟨.set, t.toC⟩
  labels := C.labels.map resultToC
  return_ := C.return_.map resultToC
  refs := C.refs.map Idx.toNat

/-! ## Index-space agreement -/

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

/-- A Core 3.0 context agrees with (the image of) a 2.0 context: its index
spaces extend the images, every 2.0 `REFS` entry is a Core `REFS` entry, and
locals, labels and return type are exactly the images.

Index spaces are allowed to *grow* because `Module_ok` checks the various
sections against different contexts (`C` and `C'`, `6-typing:701-707`) whose
index spaces are prefixes of one another, and because Core's `Globals_ok` is
sequential while 2.0's `Global_ok` is not. -/
structure Agrees (C : Context) (D : Silmaril.Wasm.Validation.Context) : Prop where
  /-- `C.TYPES` is a prefix of `D.TYPES`. -/
  types : C.types.map FuncType.toDefType <+: D.types
  /-- `C.FUNCS` is a prefix of `D.FUNCS`. -/
  funcs : C.funcs.map FuncType.toDefType <+: D.funcs
  /-- `C.GLOBALS` is a prefix of `D.GLOBALS`. -/
  globals : C.globals.map globalToC <+: D.globals
  /-- `C.TABLES` is a prefix of `D.TABLES`. -/
  tables : C.tables.map tableToC <+: D.tables
  /-- `C.MEMS` is a prefix of `D.MEMS`. -/
  mems : C.mems.map MemoryType.toCore <+: D.mems
  /-- `C.ELEMS` is a prefix of `D.ELEMS`. -/
  elems : C.elems.map RefType.toC <+: D.elems
  /-- `D.DATAS` is at least as long as `C.DATAS` (`datatype = OK` carries no
  information, so only the length matters). -/
  datas : C.datas.length ≤ D.datas.length
  /-- Locals agree on the nose, all initialised. -/
  locals : D.locals = C.locals.map fun t => ⟨.set, t.toC⟩
  /-- Labels agree on the nose. -/
  labels : D.labels = C.labels.map resultToC
  /-- The return type agrees on the nose. -/
  return_ : D.return_ = C.return_.map resultToC
  /-- Every declared function reference survives. -/
  refs : ∀ x ∈ C.refs, x.toNat ∈ D.refs

theorem Agrees.refl (C : Context) : Agrees C C.toCore where
  types := List.prefix_refl _
  funcs := List.prefix_refl _
  globals := List.prefix_refl _
  tables := List.prefix_refl _
  mems := List.prefix_refl _
  elems := List.prefix_refl _
  datas := le_refl _
  locals := rfl
  labels := rfl
  return_ := rfl
  refs := fun _ hx => List.mem_map_of_mem hx

theorem Agrees.withLabel {C : Context} {D : Silmaril.Wasm.Validation.Context}
    (h : Agrees C D) (ts : CResultType) :
    Agrees (C.withLabel ts) (D.withLabel (resultToC ts)) :=
  { h with
    labels := by
      simp [Context.withLabel, Silmaril.Wasm.Validation.Context.withLabel, h.labels] }

/-- A `datatype = OK` lookup survives into any longer `DATAS`. -/
theorem Agrees.data_getElem? {C : Context} {D : Silmaril.Wasm.Validation.Context}
    (h : Agrees C D) {x : Nat} (hx : C.datas[x]? = some ()) : D.datas[x]? = some () := by
  have hlt : x < C.datas.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hx
    cases hx
  have : x < D.datas.length := lt_of_lt_of_le hlt h.datas
  rw [List.getElem?_eq_getElem this]

/-! ## Closing 2.0 types

2.0 types contain no type indices, so closing them against a Core type section
is the identity. -/

/-- `$clos_valtype(C, t)` on the 2.0 image. -/
@[simp] theorem closeVal_toCore (D : Silmaril.Wasm.Validation.Context) (t : ValType) :
    D.closeVal t.toCore = t.toC :=
  Ty.substAll_closed (by simp [Ty.Closed]) _

/-- `$clos_heaptype(C, ht)` on the 2.0 image. -/
@[simp] theorem closeHeap_toCoreHeap (D : Silmaril.Wasm.Validation.Context) (t : RefType) :
    D.closeHeap t.toCoreHeap = .abs (match t with | .funcref => .func | .externref => .extern) := by
  cases t <;> exact Ty.substAll_closed (by rfl) _

/-- `$clos_reftype(C, rt)` on the 2.0 image. -/
@[simp] theorem closeRef_toCore (D : Silmaril.Wasm.Validation.Context) (t : RefType) :
    D.closeRef t.toCore = t.toC := by
  cases t <;> exact Ty.substAll_closed (by rfl) _

/-- `$clos_globaltype(C, gt)` on the 2.0 image. -/
@[simp] theorem closeGlobalType_toCore (D : Silmaril.Wasm.Validation.Context) (g : GlobalType) :
    D.closeGlobalType g.toCore = globalToC g := by
  simp [Silmaril.Wasm.Validation.Context.closeGlobalType, GlobalType.toCore, globalToC]

/-- `$clos_tabletype(C, tt)` on the 2.0 image. -/
@[simp] theorem closeTableType_toCore (D : Silmaril.Wasm.Validation.Context) (t : TableType) :
    D.closeTableType t.toCore = tableToC t := by
  simp [Silmaril.Wasm.Validation.Context.closeTableType, TableType.toCore, tableToC]

/-- A 2.0 reference type is a well-formed Core 3.0 reference type. -/
theorem tyOk_toC_ref (Δ : TypeCtx) (t : RefType) : TyOk Δ t.toC := by
  cases t <;> exact .ref (.abs _)

/-- `Expand` for the defined type of a 2.0 function type. -/
theorem expand_toDefType (t : FuncType) :
    Expand t.toDefType
      (.func (Ty.ofList (t.params.map ValType.toC)) (Ty.ofList (t.results.map ValType.toC))) :=
  Expand.iff.mpr (FuncType.toDefType_expand t)

/-- Every 2.0 value type is Core-defaultable: `funcref` and `externref` are
nullable, and numeric and vector types always are. -/
theorem defaultable_toC (t : ValType) : Defaultable t.toC := by
  cases t with
  | num t => exact trivial
  | vec t => exact trivial
  | ref r => cases r <;> exact rfl

/-! ## Single-instruction packaging -/

/-- A Core rule for the image of a single 2.0 instruction. -/
theorem single {D : Silmaril.Wasm.Validation.Context} {c c' : Wasm.Instr}
    {it : Silmaril.Wasm.Validation.InstrType}
    (hc : (some c' : Option Wasm.Instr) = some c)
    (h : Silmaril.Wasm.Validation.InstrOk D c' it) :
    Silmaril.Wasm.Validation.InstrsOk D [c] it := by
  cases hc; exact .instr h

/-- A Core rule whose `inits` must be discarded, for `local.set`/`local.tee`:
2.0's `instrtype` has no `inits` component. -/
theorem singleInits {D : Silmaril.Wasm.Validation.Context} {c c' : Wasm.Instr}
    {a b : List Silmaril.Wasm.Validation.CValType} {xs : List Nat}
    (hc : (some c' : Option Wasm.Instr) = some c)
    (h : Silmaril.Wasm.Validation.InstrOk D c' ⟨a, xs, b⟩)
    (hok : InstrTypeOk D (.plain a b)) :
    Silmaril.Wasm.Validation.InstrsOk D [c] (.plain a b) := by
  cases hc
  exact .sub (.instr h) ⟨ResultSub.refl _ _, ResultSub.refl _ _, by simp⟩ hok

/-- A Core rule followed by `Instrs_ok/sub`, for `ref.func`, whose Core type is
the *non-nullable* `(ref $ft)` where 2.0 assigns `funcref`. -/
theorem singleSub {D : Silmaril.Wasm.Validation.Context} {c c' : Wasm.Instr}
    {a b a' b' : List Silmaril.Wasm.Validation.CValType}
    (hc : (some c' : Option Wasm.Instr) = some c)
    (h : Silmaril.Wasm.Validation.InstrOk D c' (.plain a b))
    (hp : ResultSub D.toTypeCtx a' a) (hr : ResultSub D.toTypeCtx b b')
    (hok : InstrTypeOk D (.plain a' b')) :
    Silmaril.Wasm.Validation.InstrsOk D [c] (.plain a' b') := by
  cases hc
  exact .sub (.instr h) ⟨hp, hr, by simp⟩ hok

/-! ## Immediates -/

/-- 2.0's `memarg` has no offset bound (`6-typing:468`); the Core 3.0 premise
`memarg.OFFSET < 2^|at|` holds automatically because a 2.0 offset is a `u32`
and a 2.0 memory has address type `I32`. -/
theorem memArgOk_toCore {arg : MemArg} {N : Nat} (h : MemArgOk arg N) :
    Silmaril.Wasm.Validation.MemArgOk arg.toCore .i32 N :=
  ⟨h, arg.offset.isLt⟩

/-- `VecLoadOp.accessWidth` agrees across the injection. -/
@[simp] theorem accessWidth_toCoreOpt (op : Option VecLoadOp) :
    (VecLoadOp.toCoreOpt op).accessWidth = VecLoadOp.accessWidth op := by
  cases op with
  | none => rfl
  | some op => cases op <;> rfl

/-- `Instr_ok/vload-pack` (`6-typing:502`) bounds the alignment by
`$(M/8 * N)`, which is `8` for each of `SHAPE 8 X 8`, `SHAPE 16 X 4` and
`SHAPE 32 X 2`; that is `64/8`, the Core 3.0 bound. -/
theorem memArgOk_packShape {arg : MemArg} {o : VecLoadOp} {m n : Nat}
    (hop : VecLoadOp.packShape o = some (m, n)) (ha : MemArgOkPack arg m n) :
    MemArgOk arg (VecLoadOp.accessWidth (some o)) := by
  cases o with
  | shape8x8 _ | shape16x4 _ | shape32x2 _ =>
    simp only [VecLoadOp.packShape, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨h₁, h₂⟩ := hop
    subst h₁; subst h₂
    simpa [VecLoadOp.accessWidth, MemArgOk, MemArgOkPack] using ha
  | splat _ | zero32 | zero64 => exact absurd hop (by simp [VecLoadOp.packShape])

/-- `Instr_ok/vload-zero` (`6-typing:512`) bounds the alignment by `n/8` with
`n` the width of `ZERO n`, which is the Core 3.0 bound. -/
theorem memArgOk_zeroWidth {arg : MemArg} {o : VecLoadOp} {n : Nat}
    (hop : VecLoadOp.zeroWidth o = some n) (ha : MemArgOk arg n) :
    MemArgOk arg (VecLoadOp.accessWidth (some o)) := by
  cases o with
  | zero32 | zero64 =>
    simp only [VecLoadOp.zeroWidth, Option.some.injEq] at hop
    subst hop
    simpa [VecLoadOp.accessWidth] using ha
  | shape8x8 _ | shape16x4 _ | shape32x2 _ | splat _ =>
    exact absurd hop (by simp [VecLoadOp.zeroWidth])

/-- `CVTOP target source op` denotes a Core 3.0 operator with exactly those
source and target types. -/
theorem cvtOp_toCore_types {t₁ t₂ : NumType} {op : CvtOp} {c : Wasm.ConvertOp}
    (h : CvtOp.toCore t₁ t₂ op = some c) : c.source = t₂ ∧ c.target = t₁ := by
  have hof := CvtOp.ofCore_toCore t₁ t₂ op c h
  have hgen : ∀ d : Wasm.ConvertOp,
      (CvtOp.ofCore d).1 = d.target ∧ (CvtOp.ofCore d).2.1 = d.source := by
    intro d
    cases d with
    | reinterpretInt t => cases t <;> exact ⟨rfl, rfl⟩
    | reinterpretFloat t => cases t <;> exact ⟨rfl, rfl⟩
    | _ => exact ⟨rfl, rfl⟩
  obtain ⟨h1, h2⟩ := hgen c
  rw [hof] at h1 h2
  exact ⟨h2.symm, h1.symm⟩

/-! ## Block types -/

/-- `Blocktype_ok` (`6-typing:203`) transports. -/
theorem blockType_toCore {C : Context} {D : Silmaril.Wasm.Validation.Context}
    (hA : Agrees C D) {bt : BlockType} {t₁ t₂ : CResultType} (h : BlockTypeOk C bt ⟨t₁, t₂⟩) :
    Silmaril.Wasm.Validation.BlockTypeOk D bt.toCore (resultToC t₁) (resultToC t₂) := by
  cases h with
  | result t =>
    cases t with
    | none => exact .empty
    | some v =>
      have := Silmaril.Wasm.Validation.BlockTypeOk.value (C := D) (t := v.toCore)
        (by rw [closeVal_toCore]; exact tyOk_toC _ v)
      simpa [BlockType.toCore] using this
  | typeIdx hx =>
    have hd : D.type? _ = some (FuncType.toDefType _) := prefix_map_getElem? hA.types hx
    have := Silmaril.Wasm.Validation.BlockTypeOk.typeIdx hd (expand_toDefType _)
    simpa [BlockType.toCore] using this

/-! ## Sequences -/

/-- `Expr.toCore` splits over concatenation. -/
theorem Expr.toCore_append {is₁ is₂ : Expr} {cs : Wasm.Expr}
    (h : Expr.toCore (is₁ ++ is₂) = some cs) :
    ∃ cs₁ cs₂, Expr.toCore is₁ = some cs₁ ∧ Expr.toCore is₂ = some cs₂ ∧ cs = cs₁ ++ cs₂ := by
  induction is₁ generalizing cs with
  | nil => exact ⟨[], cs, rfl, h, rfl⟩
  | cons i is ih =>
    simp only [List.cons_append, Expr.toCore, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨c, hc, cs', hcs', rfl⟩ := h
    obtain ⟨cs₁, cs₂, h₁, h₂, rfl⟩ := ih hcs'
    exact ⟨c :: cs₁, cs₂, by simp [Expr.toCore, hc, h₁], h₂, rfl⟩

/-- `$with_locals` does not touch the type fields. -/
theorem withLocals_toTypeCtx : (D : Silmaril.Wasm.Validation.Context) → (xs : List Nat) →
    (lts : List LocalType) → (D.withLocals xs lts).toTypeCtx = D.toTypeCtx
  | D, x :: xs, _ :: lts => by
    rw [Silmaril.Wasm.Validation.Context.withLocals, withLocals_toTypeCtx]; rfl
  | _, [], _ => by simp [Silmaril.Wasm.Validation.Context.withLocals]
  | _, _ :: _, [] => by simp [Silmaril.Wasm.Validation.Context.withLocals]

@[simp] theorem initLocals_nil (D : Silmaril.Wasm.Validation.Context) : D.initLocals [] = D := by
  simp [Silmaril.Wasm.Validation.Context.initLocals,
    Silmaril.Wasm.Validation.Context.withLocals]

/-! ## Lookups -/

theorem addrI32_valType : AddrType.i32.valType = Ty.num (.int .i32) := rfl

theorem addrMin_i32 : AddrType.min .i32 .i32 = AddrType.i32 := rfl

theorem idx_zero_toNat {k : IndexKind} : (⟨0⟩ : Idx k).toNat = 0 := rfl

attribute [local simp] addrI32_valType addrMin_i32 idx_zero_toNat

theorem funcs_get {C : Context} {D : Silmaril.Wasm.Validation.Context} (hA : Agrees C D)
    {x : Nat} {ft : FuncType} (hx : C.funcs[x]? = some ft) :
    D.funcs[x]? = some ft.toDefType := prefix_map_getElem? hA.funcs hx

theorem tables_get {C : Context} {D : Silmaril.Wasm.Validation.Context} (hA : Agrees C D)
    {x : Nat} {tt : TableType} (hx : C.tables[x]? = some tt) :
    D.tables[x]? = some (tableToC tt) := prefix_map_getElem? hA.tables hx

theorem globals_get {C : Context} {D : Silmaril.Wasm.Validation.Context} (hA : Agrees C D)
    {x : Nat} {gt : GlobalType} (hx : C.globals[x]? = some gt) :
    D.globals[x]? = some (globalToC gt) := prefix_map_getElem? hA.globals hx

theorem elems_get {C : Context} {D : Silmaril.Wasm.Validation.Context} (hA : Agrees C D)
    {x : Nat} {rt : RefType} (hx : C.elems[x]? = some rt) :
    D.elems[x]? = some rt.toC := prefix_map_getElem? hA.elems hx

theorem mems_zero {C : Context} {D : Silmaril.Wasm.Validation.Context} (hA : Agrees C D)
    {mt : MemoryType} (hm : C.mems[0]? = some mt) :
    D.mems[(⟨0⟩ : MemIdx).toNat]? = some mt.toCore :=
  prefix_map_getElem? hA.mems hm

theorem labels_get {C : Context} {D : Silmaril.Wasm.Validation.Context} (hA : Agrees C D)
    {x : Nat} {ts : CResultType} (hx : C.labels[x]? = some ts) :
    D.labels[x]? = some (resultToC ts) := by rw [hA.labels]; simp [hx]

/-- `NumOrVec` transports. -/
theorem isNumOrVec_toC {t : ValType} (h : NumOrVec t) : Ty.IsNumOrVec t.toC := by
  rcases h with ⟨nt, rfl⟩ | ⟨vt, rfl⟩ <;> exact trivial

/-! ## Instruction transport -/

mutual

/-- Single-instruction transport into any agreeing Core 3.0 context: every rule
of `Instr_ok` (`6-typing:182-532`).

A 2.0 instruction is transported to the Core *sequence* `[i.toCore]`, because
`ref.func` needs `Instrs_ok/sub` to go from Core's non-nullable `(ref $ft)` to
2.0's `funcref`, and `local.set`/`local.tee` need it to discard Core's `inits`
component. -/
theorem InstrOk.toCore' {C : Context} {D : Silmaril.Wasm.Validation.Context} (hA : Agrees C D)
    {i : Instr} {it : InstrType} (h : InstrOk C i it) :
    ∀ c : Wasm.Instr, Instr.toCore i = some c →
      Silmaril.Wasm.Validation.InstrsOk D [c]
        (.plain (resultToC it.params) (resultToC it.results)) := by
  match h with
  | .nop => exact fun _ hc => single hc (.parametric .nop)
  | @InstrOk.unreachable _ t₁ t₂ =>
    exact fun _ hc => single hc (.parametric (.unreachable (instrTypeOk_toC D t₁ t₂)))
  | @InstrOk.drop _ t =>
    exact fun _ hc => single hc (.parametric (.drop (tyOk_valToC _ t)))
  | @InstrOk.selectExpl _ t =>
    intro c hc
    have := single hc (.parametric (Silmaril.Wasm.Validation.ParametricInstrOk.selectExpl
      (C := D) (t := t.toCore) (by rw [closeVal_toCore]; exact tyOk_toC _ t)))
    simpa using this
  | @InstrOk.selectImpl _ t t' hsub hnv =>
    intro c hc
    exact single hc (.parametric (Silmaril.Wasm.Validation.ParametricInstrOk.selectImpl
      (C := D) (t := valToC t) (t' := t'.toC) (tyOk_valToC _ t) (sub_valToC hsub)
      (isNumOrVec_toC hnv)))
  | .block hbt hbody =>
    intro c hc
    simp only [Instr.toCore, Option.map_eq_some_iff] at hc
    obtain ⟨cb, hcb, rfl⟩ := hc
    exact .instr (.block (blockType_toCore hA hbt)
      (InstrsOk.toCore' (hA.withLabel _) hbody _ hcb))
  | .loop hbt hbody =>
    intro c hc
    simp only [Instr.toCore, Option.map_eq_some_iff] at hc
    obtain ⟨cb, hcb, rfl⟩ := hc
    exact .instr (.loop (blockType_toCore hA hbt)
      (InstrsOk.toCore' (hA.withLabel _) hbody _ hcb))
  | .if_ hbt hthen helse =>
    intro c hc
    simp only [Instr.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨cl, hcl, cr, hcr, rfl⟩ := hc
    have := Silmaril.Wasm.Validation.InstrsOk.instr
      (Silmaril.Wasm.Validation.InstrOk.if_ (blockType_toCore hA hbt)
        (InstrsOk.toCore' (hA.withLabel _) hthen _ hcl)
        (InstrsOk.toCore' (hA.withLabel _) helse _ hcr))
    simpa using this
  | @InstrOk.br _ l ts t₁ t₂ hl =>
    intro c hc
    have := single hc (.br (labels_get hA hl) (instrTypeOk_toC D t₁ t₂))
    simpa using this
  | .brIf hl =>
    intro c hc
    have := single hc (.brIf (labels_get hA hl))
    simpa using this
  | @InstrOk.brTable _ ls l' ts t₁ t₂ hls hl' =>
    intro c hc
    have hok : InstrTypeOk D (.plain (resultToC (t₁ ++ ts ++ [.val .i32])) (resultToC t₂)) :=
      instrTypeOk_toC D _ _
    have := single hc (Silmaril.Wasm.Validation.InstrOk.brTable (C := D) (ls := ls) (l' := l')
      (ts := resultToC ts)
      (fun l hl => by
        obtain ⟨lt, hlt, hsub⟩ := hls l hl
        exact ⟨resultToC lt, labels_get hA hlt, resultSub_toC hsub⟩)
      (by
        obtain ⟨lt, hlt, hsub⟩ := hl'
        exact ⟨resultToC lt, labels_get hA hlt, resultSub_toC hsub⟩)
      (by simpa using hok))
    simpa using this
  | .call hx =>
    intro c hc
    have := single hc (.call (funcs_get hA hx) (expand_toDefType _))
    simpa [InstrType.lift] using this
  | @InstrOk.callIndirect _ x y tt ft hx hrt hy =>
    intro c hc
    have hs : Sub D.toTypeCtx (RefType.toC tt.element) Ty.funcref := by
      rw [hrt]; exact Silmaril.Wasm.Validation.Sub.refl _ (k := .ref) trivial _
    have := single hc (Silmaril.Wasm.Validation.InstrOk.callIndirect (C := D)
      (a := .i32) (tables_get hA hx) hs
      (prefix_map_getElem? hA.types hy) (expand_toDefType _))
    simpa using this
  | @InstrOk.return_ _ ts t₁ t₂ hr =>
    intro c hc
    have hr' : D.return_ = some (resultToC ts) := by rw [hA.return_, hr]; rfl
    have := single hc (.return_ hr' (instrTypeOk_toC D t₁ t₂))
    simpa using this
  | .intConst => exact fun _ hc => single hc (.numeric (.intConst _ _))
  | .floatConst => exact fun _ hc => single hc (.numeric (.floatConst _ _))
  | .intUnOp hop => exact fun _ hc => single hc (.numeric (.intUnOp hop))
  | .floatUnOp => exact fun _ hc => single hc (.numeric (.floatUnOp _ _))
  | .intBinOp => exact fun _ hc => single hc (.numeric (.intBinOp _ _))
  | .floatBinOp => exact fun _ hc => single hc (.numeric (.floatBinOp _ _))
  | .intTestOp => exact fun _ hc => single hc (.numeric (.intTestOp _ _))
  | .intRelOp => exact fun _ hc => single hc (.numeric (.intRelOp _ _))
  | .floatRelOp => exact fun _ hc => single hc (.numeric (.floatRelOp _ _))
  | .cvtOpReinterpret _ _ =>
    intro c hc
    simp only [Instr.toCore, Option.map_eq_some_iff] at hc
    obtain ⟨op, hop, rfl⟩ := hc
    obtain ⟨hs, ht⟩ := cvtOp_toCore_types hop
    have := Silmaril.Wasm.Validation.InstrsOk.instr
      (Silmaril.Wasm.Validation.InstrOk.numeric
        (Silmaril.Wasm.Validation.NumericInstrOk.convert (C := D) op))
    rw [hs, ht] at this
    exact this
  | .cvtOpConvert _ _ =>
    intro c hc
    simp only [Instr.toCore, Option.map_eq_some_iff] at hc
    obtain ⟨op, hop, rfl⟩ := hc
    obtain ⟨hs, ht⟩ := cvtOp_toCore_types hop
    have := Silmaril.Wasm.Validation.InstrsOk.instr
      (Silmaril.Wasm.Validation.InstrOk.numeric
        (Silmaril.Wasm.Validation.NumericInstrOk.convert (C := D) op))
    rw [hs, ht] at this
    exact this
  | @InstrOk.refNull _ rt =>
    intro c hc
    have := single hc (.reference (Silmaril.Wasm.Validation.RefInstrOk.refNull
      (C := D) (ht := rt.toCoreHeap) (by rw [closeHeap_toCoreHeap]; exact .abs _)))
    cases rt <;> simpa using this
  | @InstrOk.refFunc _ x ft hx hrefs =>
    intro c hc
    refine singleSub hc (.reference (Silmaril.Wasm.Validation.RefInstrOk.refFunc
      (funcs_get hA hx) (hA.refs x hrefs))) ?_ ?_ (instrTypeOk_toC D [] [.val .funcref])
    · exact .nil
    · exact .cons (.refv (.refNull (.defFunc (expand_toDefType ft)))) .nil
  | @InstrOk.refIsNull _ rt =>
    intro c hc
    have := single hc (.reference (Silmaril.Wasm.Validation.RefInstrOk.refIsNull
      (C := D) (ht := .abs (match rt with | .funcref => .func | .externref => .extern))
      (.abs _)))
    cases rt <;> simpa using this
  | .vecConst => exact fun _ hc => single hc (.vector (.vecConst _))
  | .vvUnOp => exact fun _ hc => single hc (.vector (.vecUnOp _))
  | .vvBinOp => exact fun _ hc => single hc (.vector (.vecBinOp _))
  | .vvTernOp => exact fun _ hc => single hc (.vector (.vecTernOp _))
  | .vvTestOp => exact fun _ hc => single hc (.vector (.vecTestOp _))
  | .vecIntUnOp hop => exact fun _ hc => single hc (.vector (.vecIntUnOp hop))
  | .vecFloatUnOp => exact fun _ hc => single hc (.vector (.vecFloatUnOp _ _))
  | .vecIntBinOp hop =>
    exact fun _ hc => single hc (.vector (.vecIntBinOp (by simpa using hop)))
  | .vecFloatBinOp => exact fun _ hc => single hc (.vector (.vecFloatBinOp _ _))
  | .vecAllTrue => exact fun _ hc => single hc (.vector (.vecAllTrue _))
  | .vecIntRelOp hop => exact fun _ hc => single hc (.vector (.vecIntRelOp hop))
  | .vecFloatRelOp => exact fun _ hc => single hc (.vector (.vecFloatRelOp _ _))
  | .vecShiftOp => exact fun _ hc => single hc (.vector (.vecShiftOp _ _))
  | .vecBitmask => exact fun _ hc => single hc (.vector (.vecBitmask _))
  | .vecSwizzle => exact fun _ hc => single hc (.vector (.vecSwizzle _))
  | .vecShuffle hlen hlanes =>
    exact fun _ hc => single hc (.vector (.vecShuffle hlen hlanes))
  | .vecSplat => exact fun _ hc => single hc (.vector (.vecSplat _))
  | .vecExtractLane hsx hi => exact fun _ hc => single hc (.vector (.vecExtractLane hi hsx))
  | .vecReplaceLane hi => exact fun _ hc => single hc (.vector (.vecReplaceLane hi))
  | @InstrOk.vecExtUnOp _ sh₁ sh₂ op hop =>
    refine fun _ hc => single hc (.vector (.vecExtUnOp (sh₁ := sh₂) (sh₂ := sh₁) ?_))
    simp only [VecExtUnOp.valid2, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hop
    simp only [Silmaril.Wasm.VecExtUnOp.valid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨hop.1.1, hop.2⟩
  | .vecExtBinOp hop =>
    exact fun _ hc => single hc (.vector (.vecExtBinOp (by simpa using hop)))
  | .vecNarrow hwidth hmax =>
    exact fun _ hc => single hc (.vector (.vecNarrow ⟨hwidth, hmax⟩))
  | .vecCvtOp hop =>
    exact fun _ hc => single hc (.vector (.vecConvert (by simpa using hop)))
  | .localGet hx =>
    intro c hc
    exact single hc (.variable (.localGet (by rw [hA.locals]; simp [hx])))
  | @InstrOk.localSet _ x t hx =>
    intro c hc
    exact singleInits hc (.variable (Silmaril.Wasm.Validation.VariableInstrOk.localSet
      (i := .set) (t := t.toC) (by rw [hA.locals]; simp [hx])))
      (instrTypeOk_toC D [.val t] [])
  | @InstrOk.localTee _ x t hx =>
    intro c hc
    exact singleInits hc (.variable (Silmaril.Wasm.Validation.VariableInstrOk.localTee
      (i := .set) (t := t.toC) (by rw [hA.locals]; simp [hx])))
      (instrTypeOk_toC D [.val t] [.val t])
  | .globalGet hx => exact fun _ hc => single hc (.variable (.globalGet (globals_get hA hx)))
  | @InstrOk.globalSet _ x gt hx hmut =>
    intro c hc
    have hg : D.globals[x.toNat]? = some ⟨Mutability.var, gt.value.toC⟩ := by
      rw [← hmut]; exact globals_get hA hx
    exact single hc (.variable (Silmaril.Wasm.Validation.VariableInstrOk.globalSet hg))
  | .tableGet hx => exact fun _ hc => single hc (.table (.tableGet (tables_get hA hx)))
  | .tableSet hx => exact fun _ hc => single hc (.table (.tableSet (tables_get hA hx)))
  | .tableSize hx => exact fun _ hc => single hc (.table (.tableSize (tables_get hA hx)))
  | .tableGrow hx => exact fun _ hc => single hc (.table (.tableGrow (tables_get hA hx)))
  | .tableFill hx => exact fun _ hc => single hc (.table (.tableFill (tables_get hA hx)))
  | @InstrOk.tableCopy _ x₁ x₂ tt₁ tt₂ hx₁ hx₂ hrt =>
    intro c hc
    have hs : Sub D.toTypeCtx (RefType.toC tt₂.element) (RefType.toC tt₁.element) := by
      rw [hrt]; exact Silmaril.Wasm.Validation.Sub.refl _ (k := .ref) trivial _
    have := single hc (.table (Silmaril.Wasm.Validation.TableInstrOk.tableCopy
      (tables_get hA hx₁) (tables_get hA hx₂) hs))
    simpa using this
  | @InstrOk.tableInit _ x₁ x₂ tt rt hx₁ hx₂ hrt =>
    intro c hc
    have hs : Sub D.toTypeCtx (RefType.toC rt) (RefType.toC tt.element) := by
      rw [hrt]; exact Silmaril.Wasm.Validation.Sub.refl _ (k := .ref) trivial _
    have := single hc (.table (Silmaril.Wasm.Validation.TableInstrOk.tableInit
      (tables_get hA hx₁) (elems_get hA hx₂) hs))
    simpa using this
  | .elemDrop hx => exact fun _ hc => single hc (.table (.elemDrop (elems_get hA hx)))
  | .memorySize hm =>
    intro c hc
    have := single hc (.memory (.memorySize (mems_zero hA hm)))
    simpa using this
  | .memoryGrow hm =>
    intro c hc
    have := single hc (.memory (.memoryGrow (mems_zero hA hm)))
    simpa using this
  | .memoryFill hm =>
    intro c hc
    have := single hc (.memory (.memoryFill (mems_zero hA hm)))
    simpa using this
  | .memoryCopy hm =>
    intro c hc
    have := single hc (.memory (.memoryCopy (mems_zero hA hm) (mems_zero hA hm)))
    simpa using this
  | .memoryInit hm hx =>
    intro c hc
    have := single hc (.memory (.memoryInit (mems_zero hA hm) (hA.data_getElem? hx)))
    simpa using this
  | .dataDrop hx =>
    exact fun _ hc => single hc (.memory (.dataDrop (hA.data_getElem? hx)))
  | .intLoadVal hm ha =>
    intro c hc
    have := single hc (.memory (.intLoad (mems_zero hA hm) (memArgOk_toCore ha)))
    simpa using this
  | .floatLoadVal hm ha =>
    intro c hc
    have := single hc (.memory (.floatLoad (mems_zero hA hm) (memArgOk_toCore ha)))
    simpa using this
  | .intLoadPack hm hsz ha =>
    intro c hc
    have := single hc (.memory (.intLoadPack (mems_zero hA hm) hsz (memArgOk_toCore ha)))
    simpa using this
  | .intStoreVal hm ha =>
    intro c hc
    have := single hc (.memory (.intStore (mems_zero hA hm) (memArgOk_toCore ha)))
    simpa using this
  | .floatStoreVal hm ha =>
    intro c hc
    have := single hc (.memory (.floatStore (mems_zero hA hm) (memArgOk_toCore ha)))
    simpa using this
  | .intStorePack hm hsz ha =>
    intro c hc
    have := single hc (.memory (.intStorePack (mems_zero hA hm) hsz (memArgOk_toCore ha)))
    simpa using this
  | .vloadVal hm ha =>
    intro c hc
    have := single hc (.memory (Silmaril.Wasm.Validation.MemoryInstrOk.vecLoad
      (op := VecLoadOp.toCoreOpt none) (mems_zero hA hm)
      (by simpa using memArgOk_toCore (N := VecLoadOp.accessWidth none) ha)))
    simpa using this
  | .vloadPack hm hop ha =>
    intro c hc
    have := single hc (.memory (Silmaril.Wasm.Validation.MemoryInstrOk.vecLoad
      (op := VecLoadOp.toCoreOpt (some _)) (mems_zero hA hm)
      (by simpa using memArgOk_toCore (memArgOk_packShape hop ha))))
    simpa using this
  | .vloadSplat hm ha =>
    intro c hc
    have := single hc (.memory (Silmaril.Wasm.Validation.MemoryInstrOk.vecLoad
      (op := VecLoadOp.toCoreOpt (some (.splat _))) (mems_zero hA hm)
      (by simpa [VecLoadOp.accessWidth] using memArgOk_toCore ha)))
    simpa using this
  | .vloadZero hm hop ha =>
    intro c hc
    have := single hc (.memory (Silmaril.Wasm.Validation.MemoryInstrOk.vecLoad
      (op := VecLoadOp.toCoreOpt (some _)) (mems_zero hA hm)
      (by simpa using memArgOk_toCore (memArgOk_zeroWidth hop ha))))
    simpa using this
  | .vloadLane hm ha hi =>
    intro c hc
    have := single hc (.memory (.vecLoadLane (mems_zero hA hm) (memArgOk_toCore ha) hi))
    simpa using this
  | .vstore hm ha =>
    intro c hc
    have := single hc (.memory (.vecStore (mems_zero hA hm) (memArgOk_toCore ha)))
    simpa using this
  | .vstoreLane hm ha hi =>
    intro c hc
    have := single hc (.memory (.vecStoreLane (mems_zero hA hm) (memArgOk_toCore ha) hi))
    simpa using this

/-- Sequence transport: the five rules of `Instrs_ok` (`6-typing:155-177`). -/
theorem InstrsOk.toCore' {C : Context} {D : Silmaril.Wasm.Validation.Context} (hA : Agrees C D)
    {is : List Instr} {it : InstrType} (h : InstrsOk C is it) :
    ∀ cs : Wasm.Expr, Expr.toCore is = some cs →
      Silmaril.Wasm.Validation.InstrsOk D cs
        (.plain (resultToC it.params) (resultToC it.results)) := by
  match h with
  | .empty =>
    intro cs hcs
    simp only [Expr.toCore, Option.some.injEq] at hcs
    subst hcs
    exact .nil
  | .instr hi =>
    intro cs hcs
    simp only [Expr.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hcs
    obtain ⟨c, hc, cs', hcs', rfl⟩ := hcs
    simp only [Option.some.injEq] at hcs'
    subst hcs'
    exact InstrOk.toCore' hA hi c hc
  | .seq h₁ h₂ =>
    intro cs hcs
    obtain ⟨cs₁, cs₂, h₁', h₂', rfl⟩ := Expr.toCore_append hcs
    have := Silmaril.Wasm.Validation.InstrsOk.seq (xs₁ := []) (xs₂ := [])
      (InstrsOk.toCore' hA h₁ _ h₁') (by simp)
      (by rw [initLocals_nil]; exact InstrsOk.toCore' hA h₂ _ h₂')
    simpa using this
  | .sub h' hs =>
    intro cs hcs
    exact .sub (InstrsOk.toCore' hA h' _ hcs)
      ⟨resultSub_toC hs.1, resultSub_toC hs.2, by simp⟩ (instrTypeOk_toC D _ _)
  | @InstrsOk.frame _ is ts t₁ t₂ h' =>
    intro cs hcs
    have := Silmaril.Wasm.Validation.InstrsOk.frame (ts := resultToC ts)
      (InstrsOk.toCore' hA h' _ hcs) (resultOk_toC D.toTypeCtx ts)
    simpa using this

end

/-! ## Transport, closed form -/

/-- Single-instruction transport (`6-typing:142`). -/
theorem InstrOk.toCore {C : Context} {i : Instr} {it : InstrType} {c : Wasm.Instr}
    (h : InstrOk C i it) (hc : Instr.toCore i = some c) :
    Silmaril.Wasm.Validation.InstrsOk C.toCore [c]
      (.plain (resultToC it.params) (resultToC it.results)) :=
  InstrOk.toCore' (Agrees.refl C) h c hc

/-- Sequence transport (`6-typing:143`). -/
theorem InstrsOk.toCore {C : Context} {is : List Instr} {it : InstrType} {cs : Wasm.Expr}
    (h : InstrsOk C is it) (hc : Expr.toCore is = some cs) :
    Silmaril.Wasm.Validation.InstrsOk C.toCore cs
      (.plain (resultToC it.params) (resultToC it.results)) :=
  InstrsOk.toCore' (Agrees.refl C) h cs hc

/-- `Expr_ok` transport (`6-typing:144`). -/
theorem ExprOk.toCore' {C : Context} {D : Silmaril.Wasm.Validation.Context} (hA : Agrees C D)
    {e : Expr} {ts : CResultType} {cs : Wasm.Expr} (h : ExprOk C e ts)
    (hc : Expr.toCore e = some cs) :
    Silmaril.Wasm.Validation.ExprOk D cs (resultToC ts) :=
  InstrsOk.toCore' hA h cs hc

/-- `Expr_ok` transport into the canonical context. -/
theorem ExprOk.toCore {C : Context} {e : Expr} {ts : CResultType} {cs : Wasm.Expr}
    (h : ExprOk C e ts) (hc : Expr.toCore e = some cs) :
    Silmaril.Wasm.Validation.ExprOk C.toCore cs (resultToC ts) :=
  ExprOk.toCore' (Agrees.refl C) h hc

/-! ## Constant expressions

`Instr_const`, `Expr_const`, `Expr_ok_const` (`6-typing:535-567`). 2.0 has no
extended constant expressions, so every 2.0 constant instruction is one of
Core 3.0's. -/

/-- `Instr_const` (`6-typing:539`) transports. -/
theorem InstrConst.toCore' {C : Context} {D : Silmaril.Wasm.Validation.Context}
    (hA : Agrees C D) {i : Instr} {c : Wasm.Instr}
    (h : InstrConst C i) (hc : Instr.toCore i = some c) :
    Silmaril.Wasm.Validation.InstrConst D c := by
  cases h with
  | intConst t b =>
    simp only [Instr.toCore, Option.some.injEq] at hc; subst hc; exact .intConst t b
  | floatConst t b =>
    simp only [Instr.toCore, Option.some.injEq] at hc; subst hc; exact .floatConst t b
  | vecConst b =>
    simp only [Instr.toCore, Option.some.injEq] at hc; subst hc; exact .vecConst b
  | refNull rt =>
    simp only [Instr.toCore, Option.some.injEq] at hc; subst hc; exact .refNull _
  | refFunc x =>
    simp only [Instr.toCore, Option.some.injEq] at hc; subst hc; exact .refFunc x
  | @globalGet x gt hx hmut =>
    simp only [Instr.toCore, Option.some.injEq] at hc; subst hc
    have hg : D.globals[x.toNat]? = some ⟨Mutability.const, gt.value.toC⟩ := by
      rw [← hmut]; exact globals_get hA hx
    exact .globalGet hg

/-- `Expr_const` (`6-typing:540`) transports. -/
theorem ExprConst.toCore' {C : Context} {D : Silmaril.Wasm.Validation.Context}
    (hA : Agrees C D) {e : Expr} {cs : Wasm.Expr}
    (h : ExprConst C e) (hc : Expr.toCore e = some cs) :
    Silmaril.Wasm.Validation.ExprConst D cs := by
  induction e generalizing cs with
  | nil =>
    simp only [Expr.toCore, Option.some.injEq] at hc
    subst hc
    intro i hi; exact absurd hi (by simp)
  | cons i is ih =>
    simp only [Expr.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨c, hc1, cs', hc2, rfl⟩ := hc
    intro j hj
    rcases List.mem_cons.1 hj with rfl | hj
    · exact InstrConst.toCore' hA (h i (by simp)) hc1
    · exact ih (fun k hk => h k (by simp [hk])) hc2 j hj

/-- `Expr_ok_const` (`6-typing:541`) transports. -/
theorem ExprOkConst.toCore' {C : Context} {D : Silmaril.Wasm.Validation.Context}
    (hA : Agrees C D) {e : Expr} {t : ValType} {cs : Wasm.Expr}
    (h : ExprOkConst C e t) (hc : Expr.toCore e = some cs) :
    Silmaril.Wasm.Validation.ExprOkConst D cs t.toC := by
  refine ⟨?_, ExprConst.toCore' hA h.const hc⟩
  have := ExprOk.toCore' hA h.typed hc
  simpa using this

/-! ## Free function indices

Every expression that contributes to `funcIdxNonFuncs` in a *valid* module is a
constant expression, and 2.0 constant expressions contain no blocks, so the
transport needs no recursion through instruction bodies. -/

@[simp] theorem coreExpr_freeFuncs_cons (c : Wasm.Instr) (cs : Wasm.Expr) :
    Silmaril.Wasm.Validation.Expr.freeFuncs (c :: cs) =
      Silmaril.Wasm.Validation.Instr.freeFuncs c ++
        Silmaril.Wasm.Validation.Expr.freeFuncs cs := by
  simp [Silmaril.Wasm.Validation.Expr.freeFuncs]

@[simp] theorem expr_freeFuncs_cons (i : Instr) (is : Expr) :
    Expr.freeFuncs (i :: is) = Instr.freeFuncs i ++ Expr.freeFuncs is := by
  simp [Expr.freeFuncs]

/-- `$free_instr(instr).FUNCS` transports on constant instructions. -/
theorem Instr.freeFuncs_toCore_const {C : Context} {i : Instr} {c : Wasm.Instr}
    (hi : InstrConst C i) (hc : Instr.toCore i = some c) :
    Silmaril.Wasm.Validation.Instr.freeFuncs c = (Instr.freeFuncs i).map Idx.toNat := by
  cases hi <;>
    (simp only [Instr.toCore, Option.some.injEq] at hc; subst hc;
     simp [Instr.freeFuncs, Silmaril.Wasm.Validation.Instr.freeFuncs])

/-- `$free_expr(expr).FUNCS` transports on constant expressions. -/
theorem Expr.freeFuncs_toCore_const {C : Context} {e : Expr} {cs : Wasm.Expr}
    (h : ExprConst C e) (hc : Expr.toCore e = some cs) :
    Silmaril.Wasm.Validation.Expr.freeFuncs cs = (Expr.freeFuncs e).map Idx.toNat := by
  induction e generalizing cs with
  | nil =>
    simp only [Expr.toCore, Option.some.injEq] at hc
    subst hc
    rfl
  | cons i is ih =>
    simp only [Expr.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨c, hc1, cs', hc2, rfl⟩ := hc
    have h1 := Instr.freeFuncs_toCore_const (h i (by simp)) hc1
    have h2 := ih (fun k hk => h k (by simp [hk])) hc2
    rw [coreExpr_freeFuncs_cons, expr_freeFuncs_cons, h1, h2, List.map_append]

/-! ## Types, limits and external types -/

theorem tyOk_ofList_toC (Δ : TypeCtx) :
    (ts : List ValType) → TyOk Δ (Ty.ofList (ts.map ValType.toC))
  | [] => .nil
  | t :: ts => .cons (tyOk_toC Δ t) (tyOk_ofList_toC Δ ts)

theorem liftComp_func_toCore (t : FuncType) :
    liftComp (.func t.toCore) =
      .func (Ty.ofList (t.params.map ValType.toC)) (Ty.ofList (t.results.map ValType.toC)) := by
  simp [liftComp, FuncType.toCore, Silmaril.Wasm.V2.liftResult_toCore]

theorem tyOk_toDefType (Δ : TypeCtx) (t : FuncType) : TyOk Δ t.toDefType := by
  have h : t.toDefType = .defn (.group (.cons (.sub true .nil
      (.func (Ty.ofList (t.params.map ValType.toC))
        (Ty.ofList (t.results.map ValType.toC)))) .nil)) 0 := by
    simp [FuncType.toDefType, liftRec, FuncType.toCoreRec, liftSub, liftComp_func_toCore]
  rw [h]
  exact .defn (.cons (.noSuper (.func (tyOk_ofList_toC _ _) (tyOk_ofList_toC _ _))) .nil)
    (by simp [Ty.length])

theorem rollGroup_toCoreRec (D : Silmaril.Wasm.Validation.Context) (t : FuncType) :
    D.rollGroup t.toCoreRec = [t.toDefType] := by
  simp [Silmaril.Wasm.Validation.Context.rollGroup, FuncType.rolldt_toCoreRec,
    Ty.substAll_closed (FuncType.toDefType_closed t)]

theorem closeComp_func_toCore (D : Silmaril.Wasm.Validation.Context) (t : FuncType) :
    D.closeComp (.func t.toCore) =
      .func (Ty.ofList (t.params.map ValType.toC)) (Ty.ofList (t.results.map ValType.toC)) := by
  simp [Silmaril.Wasm.Validation.Context.closeComp, liftComp_func_toCore, Ty.substAll,
    Ty.subst, subst_ofList_toC]

theorem typesOk_map : (ts : List FuncType) → (D : Silmaril.Wasm.Validation.Context) →
    TypesOk D (ts.map FuncType.toCoreRec) (ts.map FuncType.toDefType)
  | [], _ => .nil
  | t :: ts, D => by
    have hok : RecTypeOkAt { D with types := D.types ++ D.rollGroup t.toCoreRec }
        t.toCoreRec.types D.types.length := by
      refine .cons (.noSuper ?_) .nil
      rw [closeComp_func_toCore]
      exact .func (tyOk_ofList_toC _ _) (tyOk_ofList_toC _ _)
    have h := TypesOk.cons hok (typesOk_map ts _)
    rw [rollGroup_toCoreRec] at h
    simpa using h

/-- `Limits_ok` (`6-typing:27`) transports at the same bound. -/
theorem limits_toCore_valid {l : Limits} {k : Nat} (h : Limits.Ok k l) :
    Silmaril.Wasm.Limits.Valid k l.toCore := by
  obtain ⟨hmin, hmax⟩ := h
  refine ⟨hmin, ?_⟩
  rcases hm : l.max with _ | mx
  · simp [Limits.toCore, hm]
  · rw [hm] at hmax
    simpa [Limits.toCore, hm, widen32] using hmax

/-- `Tabletype_ok` (`6-typing:38`) transports: both bounds are `2^32 - 1`. -/
theorem tableTypeOk_toC (Δ : TypeCtx) {t : TableType} (h : TableType.Ok t) :
    TableTypeOk Δ (tableToC t) :=
  ⟨by simpa [tableToC, AddrType.width, AddrType.intType, IntType.width] using
      limits_toCore_valid h,
    tyOk_toC_ref Δ t.element⟩

/-- `Memtype_ok` (`6-typing:42`) transports: `2^16` pages on both sides. -/
theorem memTypeOk_toCore {t : MemoryType} (h : MemoryType.Ok t) : MemTypeOk t.toCore := by
  simpa [MemTypeOk, Silmaril.Wasm.MemoryType.Valid, MemoryType.toCore, AddrType.width,
    AddrType.intType, IntType.width] using limits_toCore_valid h

/-- `Externtype_ok` (`6-typing:47`) transports. -/
theorem externTypeOk_toCore (Δ : TypeCtx) {xt : ExternType} (h : ExternType.Ok xt) :
    ExternTypeOk Δ xt.toCore := by
  cases xt with
  | func t => exact .func (tyOk_toDefType _ t) (expand_toDefType t)
  | global t => exact .global (tyOk_toC _ t.value)
  | table t => exact .table (tableTypeOk_toC _ h)
  | memory t => exact .mem (memTypeOk_toCore h)

/-! ## Imports -/

/-- `Import_ok` (`6-typing:651`) transports. -/
theorem ImportOk.toCore {types : List FuncType} {i : Import} {xt : ExternType}
    (h : ImportOk { types := types } i xt) :
    Silmaril.Wasm.Validation.ImportOk { types := types.map FuncType.toDefType }
      i.toCore xt.toCore := by
  obtain ⟨het, hok⟩ := h
  refine ⟨?_, externTypeOk_toCore _ hok⟩
  rcases i with ⟨mn, n, d⟩
  cases d with
  | func x =>
    simp only [Module.importType?, Option.map_eq_some_iff] at het
    obtain ⟨ft, hft, rfl⟩ := het
    simp [Import.toCore, ImportDesc.toCore, Silmaril.Wasm.Validation.Context.closeExtern?,
      Silmaril.Wasm.Validation.Context.type?, hft, ExternType.toCore]
  | table t =>
    simp only [Module.importType?, Option.some.injEq] at het
    subst het
    simp [Import.toCore, ImportDesc.toCore, Silmaril.Wasm.Validation.Context.closeExtern?,
      ExternType.toCore, tableToC]
  | memory t =>
    simp only [Module.importType?, Option.some.injEq] at het
    subst het
    simp [Import.toCore, ImportDesc.toCore, Silmaril.Wasm.Validation.Context.closeExtern?,
      ExternType.toCore]
  | global t =>
    simp only [Module.importType?, Option.some.injEq] at het
    subst het
    simp [Import.toCore, ImportDesc.toCore, Silmaril.Wasm.Validation.Context.closeExtern?,
      ExternType.toCore, globalToC]

/-! ## External-type projections -/

theorem cext_funcs : (xs : List ExternType) →
    CExternType.funcs (xs.map ExternType.toCore) = (ExternType.funcs xs).map FuncType.toDefType
  | [] => rfl
  | x :: xs => by cases x <;> simp [CExternType.funcs, ExternType.funcs, cext_funcs xs]

theorem cext_globals : (xs : List ExternType) →
    CExternType.globals (xs.map ExternType.toCore) = (ExternType.globals xs).map globalToC
  | [] => rfl
  | x :: xs => by cases x <;> simp [CExternType.globals, ExternType.globals, cext_globals xs]

theorem cext_tables : (xs : List ExternType) →
    CExternType.tables (xs.map ExternType.toCore) = (ExternType.tables xs).map tableToC
  | [] => rfl
  | x :: xs => by cases x <;> simp [CExternType.tables, ExternType.tables, cext_tables xs]

theorem cext_mems : (xs : List ExternType) →
    CExternType.mems (xs.map ExternType.toCore) = (ExternType.mems xs).map MemoryType.toCore
  | [] => rfl
  | x :: xs => by cases x <;> simp [CExternType.mems, ExternType.mems, cext_mems xs]

theorem cext_tags : (xs : List ExternType) →
    CExternType.tags (xs.map ExternType.toCore) = []
  | [] => rfl
  | x :: xs => by cases x <;> simp [CExternType.tags, cext_tags xs]

/-! ## List combinators -/

theorem forall₂_mapM {α β γ δ : Type _} {f : α → Option β} {R : α → γ → Prop}
    {S : β → δ → Prop} (F : γ → δ)
    (hRS : ∀ a cγ b, R a cγ → f a = some b → S b (F cγ)) :
    ∀ {l : List α} {l' : List β} {cs : List γ}, l.mapM f = some l' →
      List.Forall₂ R l cs → List.Forall₂ S l' (cs.map F) := by
  intro l
  induction l with
  | nil =>
    intro l' cs h hR
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    cases hR
    exact .nil
  | cons a l ih =>
    intro l' cs h hR
    cases hR with
    | cons hab hs =>
      rename_i cγ cs'
      simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind,
        Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨b, hb, bs, hbs, rfl⟩ := h
      exact .cons (hRS a cγ b hab hb) (ih hbs hs)

theorem forall₂_map_of {α β γ : Type _} {R : β → γ → Prop} (f : α → β) (g : α → γ) :
    (l : List α) → (∀ a ∈ l, R (f a) (g a)) → List.Forall₂ R (l.map f) (l.map g)
  | [], _ => .nil
  | a :: l, h => .cons (h a (by simp)) (forall₂_map_of f g l (fun b hb => h b (by simp [hb])))

theorem forall₂_map_map {α β γ δ : Type _} (F : α → β) (G : γ → δ) {R : α → γ → Prop}
    {S : β → δ → Prop} (hRS : ∀ a cγ, R a cγ → S (F a) (G cγ)) :
    ∀ {l : List α} {cs : List γ}, List.Forall₂ R l cs →
      List.Forall₂ S (l.map F) (cs.map G) := by
  intro l
  induction l with
  | nil => intro cs h; cases h; exact .nil
  | cons a l ih => intro cs h; cases h with | cons hab hs => exact .cons (hRS _ _ hab) (ih hs)

theorem mem_of_mapM {α β : Type _} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ b ∈ l', ∃ a ∈ l, f a = some b := by
  intro l
  induction l with
  | nil =>
    intro l' h b hb
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact absurd hb (by simp)
  | cons a l ih =>
    intro l' h b hb
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨b₀, hb₀, bs, hbs, rfl⟩ := h
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨a, by simp, hb₀⟩
    · obtain ⟨a', ha', hfa'⟩ := ih hbs b hb
      exact ⟨a', by simp [ha'], hfa'⟩

theorem mapM_flatMap_toNat {α β : Type _} {f : α → Option β}
    (g : α → List FuncIdx) (g' : β → List Nat) :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' →
      (∀ a ∈ l, ∀ b, f a = some b → g' b = (g a).map Idx.toNat) →
      l'.flatMap g' = (l.flatMap g).map Idx.toNat := by
  intro l
  induction l with
  | nil =>
    intro l' h _
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | cons a l ih =>
    intro l' h hfg
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    simp [hfg a (by simp) b hb, ih hbs (fun x hx => hfg x (by simp [hx])), List.map_append]

theorem map_flatMap_toNat {α β : Type _} (F : α → β) (g : α → List FuncIdx)
    (g' : β → List Nat) (hfg : ∀ a, g' (F a) = (g a).map Idx.toNat) :
    ∀ l : List α, (l.map F).flatMap g' = (l.flatMap g).map Idx.toNat
  | [] => rfl
  | a :: l => by simp [hfg a, map_flatMap_toNat F g g' hfg l, List.map_append]

theorem forall₂_of_mapM {α β : Type _} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' →
      List.Forall₂ (fun a b => f a = some b) l l' := by
  intro l
  induction l with
  | nil =>
    intro l' h
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact .nil
  | cons a l ih =>
    intro l' h
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    exact .cons hb (ih hbs)

theorem forall₂_imp_mem {α β : Type _} {R S : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' →
      (∀ a ∈ l, ∀ b, R a b → S a b) → List.Forall₂ S l l'
  | [], [], .nil, _ => .nil
  | a :: l, b :: l', .cons hab hs, h =>
    .cons (h a (by simp) b hab) (forall₂_imp_mem hs (fun x hx => h x (by simp [hx])))

theorem flatMap_congr_toNat {α β : Type _} {g : α → List FuncIdx} {g' : β → List Nat} :
    ∀ {l : List α} {l' : List β},
      List.Forall₂ (fun a b => g' b = (g a).map Idx.toNat) l l' →
      l'.flatMap g' = (l.flatMap g).map Idx.toNat
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons hab hs => by
    simp [hab, flatMap_congr_toNat hs, List.map_append]

/-! ## `Module_ok`'s auxiliary lists -/

theorem typeOk_list_eq : ∀ {ts fts : List FuncType}, List.Forall₂ TypeOk ts fts → fts = ts
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by rw [h.1, typeOk_list_eq hs]

theorem memOk_list_eq : ∀ {ms mts : List MemoryType}, List.Forall₂ MemOk ms mts → mts = ms
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by rw [h.1, memOk_list_eq hs]

theorem memOk_list_valid : ∀ {ms mts : List MemoryType}, List.Forall₂ MemOk ms mts →
    ∀ mt ∈ ms, MemoryType.Ok mt
  | [], [], .nil => by simp
  | _ :: _, _ :: _, .cons h hs => by
    intro mt hmt
    rcases List.mem_cons.1 hmt with rfl | hmt
    · exact h.2
    · exact memOk_list_valid hs mt hmt

theorem tableOk_list_eq : ∀ {ts tts : List TableType}, List.Forall₂ TableOk ts tts → tts = ts
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by rw [h.1, tableOk_list_eq hs]

theorem globalOk_list_eq {C : Context} : ∀ {gs : List Global} {gts : List GlobalType},
    List.Forall₂ (GlobalOk C) gs gts → gts = gs.map Declaration.Global.type
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by rw [h.1, globalOk_list_eq hs]; rfl

theorem elemOk_list_eq {C : Context} : ∀ {es : List Elem} {rts : List RefType},
    List.Forall₂ (ElemOk C) es rts → rts = es.map Elem.type
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by rw [h.1, elemOk_list_eq hs]; rfl

/-! ## Segment modes -/

/-- `Datamode_ok` (`6-typing:582`) transports. -/
theorem DataModeOk.toCore' {C : Context} {D : Silmaril.Wasm.Validation.Context}
    (hA : Agrees C D) {dm : DataMode} {cdm : Wasm.DataMode}
    (h : DataModeOk C dm) (hc : DataMode.toCore dm = some cdm) :
    Silmaril.Wasm.Validation.DataModeOk D cdm := by
  cases h with
  | passive =>
    simp only [DataMode.toCore, Option.some.injEq] at hc; subst hc; exact .passive
  | @active x off mt hx hmem hoff =>
    simp only [DataMode.toCore, Option.map_eq_some_iff] at hc
    obtain ⟨coff, hcoff, rfl⟩ := hc
    refine Silmaril.Wasm.Validation.DataModeOk.active (a := .i32)
      (l := mt.limits.toCore) ?_ ?_
    · rw [hx]; exact mems_zero hA hmem
    · simpa using ExprOkConst.toCore' hA hoff hcoff

/-- `Elemmode_ok` (`6-typing:581`) transports. -/
theorem ElemModeOk.toCore' {C : Context} {D : Silmaril.Wasm.Validation.Context}
    (hA : Agrees C D) {em : ElemMode} {cem : Wasm.ElemMode} {rt : RefType}
    (h : ElemModeOk C em rt) (hc : ElemMode.toCore em = some cem) :
    Silmaril.Wasm.Validation.ElemModeOk D cem rt.toC := by
  cases h with
  | passive => simp only [ElemMode.toCore, Option.some.injEq] at hc; subst hc; exact .passive
  | declare =>
    simp only [ElemMode.toCore, Option.some.injEq] at hc; subst hc; exact .declarative
  | @active x off rt tt hx hrt hoff =>
    simp only [ElemMode.toCore, Option.map_eq_some_iff] at hc
    obtain ⟨coff, hcoff, rfl⟩ := hc
    refine Silmaril.Wasm.Validation.ElemModeOk.active (a := .i32) (tables_get hA hx) ?_ ?_
    · rw [← hrt]; exact Silmaril.Wasm.Validation.Sub.refl _ (k := .ref) trivial _
    · simpa using ExprOkConst.toCore' hA hoff hcoff

/-- The implicit null initializer that `$alloctable` supplies in 2.0
(`9-module:58`) is a Core 3.0 constant expression of the table's own element
type. -/
theorem refNull_ok (D : Silmaril.Wasm.Validation.Context) (rt : RefType) :
    Silmaril.Wasm.Validation.ExprOkConst D [.refNull rt.toCoreHeap] (.refv rt.toC) := by
  refine ⟨?_, ?_⟩
  · have := Silmaril.Wasm.Validation.InstrsOk.instr
      (Silmaril.Wasm.Validation.InstrOk.reference
        (Silmaril.Wasm.Validation.RefInstrOk.refNull (C := D) (ht := rt.toCoreHeap)
          (by rw [closeHeap_toCoreHeap]; exact .abs _)))
    cases rt <;> simpa [Silmaril.Wasm.Validation.ExprOk] using this
  · intro i hi
    simp only [List.mem_singleton] at hi
    subst hi
    exact .refNull _

/-! ## Context growth -/

theorem Agrees.extendGlobals {C : Context} {D : Silmaril.Wasm.Validation.Context}
    (h : Agrees C D) (g : CGlobalType) :
    Agrees C { D with globals := D.globals ++ [g] } :=
  { h with globals := h.globals.trans (List.prefix_append _ _) }

theorem Agrees.funcBody {C : Context} {D : Silmaril.Wasm.Validation.Context} (h : Agrees C D)
    (hl : C.locals = []) (hlab : C.labels = []) (ft : FuncType) (locs : List ValType) :
    Agrees (C.withFuncFrame (ft.params ++ locs) (liftResult ft.results) (liftResult ft.results))
      (D.funcBody (ft.params.map ValType.toC) (ft.results.map ValType.toC)
        (locs.map fun t => ⟨.set, t.toC⟩)) :=
  { h with
    locals := by
      simp [Context.withFuncFrame, Silmaril.Wasm.Validation.Context.funcBody, hl,
        List.map_map, Function.comp_def]
    labels := by
      simp [Context.withFuncFrame, Silmaril.Wasm.Validation.Context.funcBody, hlab]
    return_ := by
      simp [Context.withFuncFrame, Silmaril.Wasm.Validation.Context.funcBody] }

/-! ## `C.REFS`

Decided deviation 6: 2.0 SpecTec has no `REFS` field (`6-typing:681`,
`;; TODO: refs`). `Silmaril/Wasm/V2/Validation/Modules.lean` implements the
W3C 2.0 reading, `funcIdxNonFuncs`, which omits Core 3.0's table-initialiser
contribution because a 2.0 `table` carries no expression. On the image the two
agree *exactly*: `TableType.toCoreTable` gives every table the initialiser
`[REF.NULL ht]`, whose free function indices are none. -/

theorem coreTables_freeFuncs_nil (ts : List TableType) :
    (ts.map TableType.toCoreTable).flatMap
        (fun t => Silmaril.Wasm.Validation.Expr.freeFuncs t.init) = [] := by
  simp [TableType.toCoreTable, Silmaril.Wasm.Validation.Expr.freeFuncs,
    Silmaril.Wasm.Validation.Instr.freeFuncs]

theorem coreExport_index_freeFuncs (e : Export) :
    (match (Export.toCore e).index with
      | .func x => [x.toNat]
      | _ => []) =
    (match e.index with
      | .func x => [x]
      | .global _ | .table _ | .memory _ => []).map Idx.toNat := by
  cases e with
  | mk name idx => cases idx <;> rfl

/-- **The `REFS` check.** On the image of `Module.toCore`, the 2.0 and Core 3.0
free-function-index sets are literally the same list. The hypotheses hold in
every valid module: `Global_ok` and `Elem_ok` make all of these expressions
constant, and a 2.0 constant expression contains no blocks. -/
theorem funcIdxNonFuncs_toCore {C : Context} {m : Module} {c : Wasm.Module}
    (hc : Module.toCore m = some c)
    (hg : ∀ g ∈ m.globals, ExprConst C g.init)
    (hei : ∀ e ∈ m.elems, ∀ ex ∈ e.init, ExprConst C ex)
    (heo : ∀ e ∈ m.elems, ∀ x off, e.mode = .active x off → ExprConst C off) :
    Silmaril.Wasm.Validation.funcIdxNonFuncs c = (funcIdxNonFuncs m).map Idx.toNat := by
  simp only [Module.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
  obtain ⟨cg, hcg, cf, hcf, ce, hce, cd, hcd, rfl⟩ := hc
  have hglob := mapM_flatMap_toNat (f := Global.toCore)
    (fun g => Expr.freeFuncs g.init)
    (fun g => Silmaril.Wasm.Validation.Expr.freeFuncs g.init) hcg
    (by
      intro a ha b hb
      simp only [Global.toCore, Option.map_eq_some_iff] at hb
      obtain ⟨init, hinit, rfl⟩ := hb
      exact Expr.freeFuncs_toCore_const (hg a ha) hinit)
  simp only [Silmaril.Wasm.Validation.funcIdxNonFuncs, funcIdxNonFuncs]
  rw [coreTables_freeFuncs_nil, hglob, List.append_nil, List.map_append, List.map_append]
  refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) rfl ?_) ?_
  · -- element segments
    refine flatMap_congr_toNat (forall₂_imp_mem (forall₂_of_mapM hce) ?_)
    intro a ha b hb
    simp only [Elem.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hb
    obtain ⟨cinit, hcinit, cmode, hcmode, rfl⟩ := hb
    have h1 : cinit.flatMap Silmaril.Wasm.Validation.Expr.freeFuncs =
        (a.init.flatMap Expr.freeFuncs).map Idx.toNat :=
      mapM_flatMap_toNat Expr.freeFuncs Silmaril.Wasm.Validation.Expr.freeFuncs hcinit
        (fun ex hex cs hcs => Expr.freeFuncs_toCore_const (hei a ha ex hex) hcs)
    cases hm : a.mode with
    | passive =>
      rw [hm] at hcmode
      simp only [ElemMode.toCore, Option.some.injEq] at hcmode
      subst hcmode
      simp [h1]
    | declare =>
      rw [hm] at hcmode
      simp only [ElemMode.toCore, Option.some.injEq] at hcmode
      subst hcmode
      simp [h1]
    | active x off =>
      rw [hm] at hcmode
      simp only [ElemMode.toCore, Option.map_eq_some_iff] at hcmode
      obtain ⟨coff, hcoff, rfl⟩ := hcmode
      have h2 := Expr.freeFuncs_toCore_const (heo a ha x off hm) hcoff
      simp [h1, h2, List.map_append]
  · -- exports
    exact map_flatMap_toNat Export.toCore _ _ coreExport_index_freeFuncs _

/-! ## Constant expressions see only part of the context

Core 3.0's `Module_ok` checks global initialisers in a context with **no**
tables, memories, element or data segments (`C'`), while 2.0's `Module_ok`
checks them in a `C'` that carries tables and memories (`6-typing:703`). The
difference is immaterial — a 2.0 constant expression is `t.const`, `v128.const`,
`ref.null`, `ref.func` or `global.get` (`6-typing:539`), none of which reads a
table or a memory — but it has to be made explicit, because `Agrees` compares
*all* index spaces. `Context.constPart` is the fragment a constant expression
can see, and `ExprOkConst.restrict` moves a 2.0 derivation into it. -/

/-- The fragment of a 2.0 context visible to a constant expression. -/
def Context.constPart (C : Context) : Context :=
  { types := C.types, funcs := C.funcs, globals := C.globals, refs := C.refs }

@[simp] theorem constPart_types (C : Context) : C.constPart.types = C.types := rfl
@[simp] theorem constPart_funcs (C : Context) : C.constPart.funcs = C.funcs := rfl
@[simp] theorem constPart_globals (C : Context) : C.constPart.globals = C.globals := rfl
@[simp] theorem constPart_tables (C : Context) : C.constPart.tables = [] := rfl
@[simp] theorem constPart_mems (C : Context) : C.constPart.mems = [] := rfl
@[simp] theorem constPart_elems (C : Context) : C.constPart.elems = [] := rfl
@[simp] theorem constPart_datas (C : Context) : C.constPart.datas = [] := rfl
@[simp] theorem constPart_locals (C : Context) : C.constPart.locals = [] := rfl
@[simp] theorem constPart_labels (C : Context) : C.constPart.labels = [] := rfl
@[simp] theorem constPart_return (C : Context) : C.constPart.return_ = none := rfl
@[simp] theorem constPart_refs (C : Context) : C.constPart.refs = C.refs := rfl

theorem InstrConst.restrict {C : Context} {i : Instr} (h : InstrConst C i) :
    InstrConst C.constPart i := by
  cases h with
  | intConst t b => exact .intConst t b
  | floatConst t b => exact .floatConst t b
  | vecConst b => exact .vecConst b
  | refNull rt => exact .refNull rt
  | refFunc x => exact .refFunc x
  | globalGet hx hmut => exact .globalGet hx hmut

theorem InstrOk.restrict {C : Context} {i : Instr} {it : InstrType}
    (h : InstrOk C i it) (hc : InstrConst C i) : InstrOk C.constPart i it := by
  cases hc with
  | intConst t b => cases h; exact .intConst
  | floatConst t b => cases h; exact .floatConst
  | vecConst b => cases h; exact .vecConst
  | refNull rt => cases h; exact .refNull
  | refFunc x => cases h with | refFunc hx hr => exact .refFunc hx hr
  | globalGet hx hmut => cases h with | globalGet hx' => exact .globalGet hx'

theorem InstrsOk.restrict {C : Context} {is : List Instr} {it : InstrType}
    (h : InstrsOk C is it) : ExprConst C is → InstrsOk C.constPart is it := by
  match h with
  | .empty => exact fun _ => .empty
  | .instr hi => exact fun hc => .instr (InstrOk.restrict hi (hc _ (by simp)))
  | .seq h₁ h₂ =>
    exact fun hc => .seq (InstrsOk.restrict h₁ (fun i hi => hc i (by simp [hi])))
      (InstrsOk.restrict h₂ (fun i hi => hc i (by simp [hi])))
  | .sub h' hs => exact fun hc => .sub (InstrsOk.restrict h' hc) hs
  | .frame h' => exact fun hc => .frame (InstrsOk.restrict h' hc)

theorem ExprOkConst.restrict {C : Context} {e : Expr} {t : ValType}
    (h : ExprOkConst C e t) : ExprOkConst C.constPart e t :=
  ⟨InstrsOk.restrict h.typed h.const, fun i hi => (h.const i hi).restrict⟩

/-! ## Sequential globals -/

/-- Core 3.0's `Globals_ok` is sequential (each initialiser sees the globals
before it) where 2.0's `Module_ok` checks every initialiser in the same `C'`.
The 2.0 derivations therefore transport into the growing Core contexts. -/
theorem globalsOk_toCore {C : Context} :
    ∀ {gs : List Global} {gts : List GlobalType} {cgs : List Wasm.Global}
      {D : Silmaril.Wasm.Validation.Context},
      List.Forall₂ (GlobalOk C) gs gts → gs.mapM Global.toCore = some cgs →
      Agrees C.constPart D → GlobalsOk D cgs (gts.map globalToC) := by
  intro gs
  induction gs with
  | nil =>
    intro gts cgs D h1 h2 _
    cases h1
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h2
    subst h2
    exact .nil
  | cons g gs ih =>
    intro gts cgs D h1 h2 hA
    cases h1 with
    | cons hg hgs =>
      simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind,
        Option.bind_eq_some_iff, Option.some.injEq] at h2
      obtain ⟨cg, hcg, cgs', hcgs', rfl⟩ := h2
      refine .cons ?_ (ih hgs hcgs' (hA.extendGlobals _))
      obtain ⟨hgt, -, hinit⟩ := hg
      simp only [Global.toCore, Option.map_eq_some_iff] at hcg
      obtain ⟨cinit, hcinit, rfl⟩ := hcg
      subst hgt
      exact ⟨(closeGlobalType_toCore D g.type).symm, tyOk_toC _ _,
        ExprOkConst.toCore' hA hinit.restrict hcinit⟩

/-! ## `Module_ok`'s per-item premises -/

theorem globalOk_mem {C : Context} : ∀ {gs : List Global} {gts : List GlobalType},
    List.Forall₂ (GlobalOk C) gs gts → ∀ g ∈ gs, GlobalOk C g g.type
  | [], [], .nil => by simp
  | a :: l, _ :: _, .cons hab hs => by
    intro g hgm
    rcases List.mem_cons.1 hgm with rfl | hgm
    · exact hab.1 ▸ hab
    · exact globalOk_mem hs g hgm

theorem elemOk_mem {C : Context} : ∀ {es : List Elem} {rts : List RefType},
    List.Forall₂ (ElemOk C) es rts → ∀ e ∈ es, ElemOk C e e.type
  | [], [], .nil => by simp
  | a :: l, _ :: _, .cons hab hs => by
    intro e hem
    rcases List.mem_cons.1 hem with rfl | hem
    · exact hab.1 ▸ hab
    · exact elemOk_mem hs e hem

/-! ## Module transport -/

/-- **`Module_ok` transports** (`6-typing:682`): a valid 2.0 module maps to a
valid Core 3.0 module, with the import and export types the images of the 2.0
ones. -/
theorem ModuleOk.toCore {m : Module} {c : Wasm.Module} {ixt xt : List ExternType}
    (hc : Module.toCore m = some c) (h : ModuleOk m ixt xt) :
    Silmaril.Wasm.Validation.ModuleOk c
      ⟨ixt.map ExternType.toCore, xt.map ExternType.toCore⟩ := by
  cases h with
  | @mk ft' ft gt tt mt rt C C' htypes himports hglobals htables hmems helems
      hdatas hfuncs hstart hexports hmems_le hnames hC hC' =>
  subst hC
  subst hC'
  obtain rfl := typeOk_list_eq htypes
  obtain rfl := memOk_list_eq hmems
  obtain rfl := tableOk_list_eq htables
  obtain rfl := globalOk_list_eq hglobals
  obtain rfl := elemOk_list_eq helems
  -- the Core module's sections
  have hc0 := hc
  simp only [Module.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
  obtain ⟨cg, hcg, cf, hcf, ce, hce, cd, hcd, hceq⟩ := hc
  have hcty : c.types = m.types.map FuncType.toCoreRec := by rw [← hceq]
  have hctags : c.tags = [] := by rw [← hceq]
  have hcimp : c.imports = m.imports.map Import.toCore := by rw [← hceq]
  have hcglob : c.globals = cg := by rw [← hceq]
  have hcmem : c.memories = m.memories.map MemoryType.toCore := by rw [← hceq]
  have hctab : c.tables = m.tables.map TableType.toCoreTable := by rw [← hceq]
  have hcfun : c.funcs = cf := by rw [← hceq]
  have hcdat : c.data = cd := by rw [← hceq]
  have hcele : c.elems = ce := by rw [← hceq]
  have hcsta : c.start = m.start := by rw [← hceq]
  have hcexp : c.exports = m.exports.map Export.toCore := by rw [← hceq]
  -- `C.REFS` agrees on the image
  have hrefs := funcIdxNonFuncs_toCore hc0
    (fun g hgm => (globalOk_mem hglobals g hgm).2.2.const)
    (fun e hem ex hex => ((elemOk_mem helems e hem).2.1 ex hex).const)
    (fun e hem x off hmode => by
      have hmo := (elemOk_mem helems e hem).2.2
      rw [hmode] at hmo
      cases hmo with | active _ _ hoff => exact hoff.const)
  have hrefmem : ∀ x ∈ funcIdxNonFuncs m,
      x.toNat ∈ Silmaril.Wasm.Validation.funcIdxNonFuncs c := by
    intro x hx
    rw [hrefs]
    exact List.mem_map_of_mem hx
  have hdlen : cd.length = m.data.length := (forall₂_of_mapM hcd).length_eq.symm
  -- the two Core contexts
  have hA : Agrees
      { types := m.types,
        funcs := ExternType.funcs ixt ++ ft,
        globals := ExternType.globals ixt ++ m.globals.map Declaration.Global.type,
        tables := ExternType.tables ixt ++ m.tables,
        mems := ExternType.mems ixt ++ m.memories,
        elems := m.elems.map Elem.type,
        datas := m.data.map fun _ => (),
        refs := funcIdxNonFuncs m }
      { types := m.types.map FuncType.toDefType,
        globals := Silmaril.Wasm.Validation.CExternType.globals (ixt.map ExternType.toCore)
          ++ (m.globals.map Declaration.Global.type).map globalToC,
        funcs := Silmaril.Wasm.Validation.CExternType.funcs (ixt.map ExternType.toCore)
          ++ ft.map FuncType.toDefType,
        tags := Silmaril.Wasm.Validation.CExternType.tags (ixt.map ExternType.toCore) ++ [],
        mems := Silmaril.Wasm.Validation.CExternType.mems (ixt.map ExternType.toCore)
          ++ c.memories,
        tables := Silmaril.Wasm.Validation.CExternType.tables (ixt.map ExternType.toCore)
          ++ m.tables.map tableToC,
        datas := c.data.map fun _ => (),
        elems := (m.elems.map Elem.type).map RefType.toC,
        refs := Silmaril.Wasm.Validation.funcIdxNonFuncs c } :=
    { types := List.prefix_refl _
      funcs := by rw [cext_funcs, ← List.map_append]
      globals := by rw [cext_globals, ← List.map_append]
      tables := by rw [cext_tables, ← List.map_append]
      mems := by rw [cext_mems, hcmem, ← List.map_append]
      elems := List.prefix_refl _
      datas := by simp [hcdat, hdlen]
      locals := rfl
      labels := rfl
      return_ := rfl
      refs := hrefmem }
  have hA' : Agrees
      ({ types := m.types,
         funcs := ExternType.funcs ixt ++ ft,
         globals := ExternType.globals ixt,
         tables := ExternType.tables ixt ++ m.tables,
         mems := ExternType.mems ixt ++ m.memories,
         refs := funcIdxNonFuncs m } : Context).constPart
      { types := m.types.map FuncType.toDefType,
        globals := Silmaril.Wasm.Validation.CExternType.globals (ixt.map ExternType.toCore),
        funcs := Silmaril.Wasm.Validation.CExternType.funcs (ixt.map ExternType.toCore)
          ++ ft.map FuncType.toDefType,
        refs := Silmaril.Wasm.Validation.funcIdxNonFuncs c } :=
    { types := List.prefix_refl _
      funcs := by rw [cext_funcs, ← List.map_append]; exact List.prefix_refl _
      globals := by rw [cext_globals]; exact List.prefix_refl _
      tables := by simp
      mems := by simp
      elems := by simp
      datas := by simp
      locals := rfl
      labels := rfl
      return_ := rfl
      refs := hrefmem }
  have hAe : Agrees
      { types := m.types,
        funcs := ExternType.funcs ixt ++ ft,
        globals := ExternType.globals ixt,
        tables := ExternType.tables ixt ++ m.tables,
        mems := ExternType.mems ixt ++ m.memories,
        refs := funcIdxNonFuncs m }
      { types := m.types.map FuncType.toDefType,
        globals := Silmaril.Wasm.Validation.CExternType.globals (ixt.map ExternType.toCore)
          ++ (m.globals.map Declaration.Global.type).map globalToC,
        funcs := Silmaril.Wasm.Validation.CExternType.funcs (ixt.map ExternType.toCore)
          ++ ft.map FuncType.toDefType,
        tags := Silmaril.Wasm.Validation.CExternType.tags (ixt.map ExternType.toCore) ++ [],
        mems := Silmaril.Wasm.Validation.CExternType.mems (ixt.map ExternType.toCore)
          ++ c.memories,
        tables := Silmaril.Wasm.Validation.CExternType.tables (ixt.map ExternType.toCore)
          ++ m.tables.map tableToC,
        datas := c.data.map fun _ => (),
        elems := (m.elems.map Elem.type).map RefType.toC,
        refs := Silmaril.Wasm.Validation.funcIdxNonFuncs c } :=
    { types := List.prefix_refl _
      funcs := by rw [cext_funcs, ← List.map_append]
      globals := by rw [cext_globals]; exact List.prefix_append _ _
      tables := by rw [cext_tables, ← List.map_append]
      mems := by rw [cext_mems, hcmem, ← List.map_append]
      elems := by simp
      datas := by simp
      locals := rfl
      labels := rfl
      return_ := rfl
      refs := hrefmem }
  refine Silmaril.Wasm.Validation.ModuleOk.mk
    (dts := m.types.map FuncType.toDefType)
    (xtI := ixt.map ExternType.toCore)
    (jts := [])
    (gts := (m.globals.map Declaration.Global.type).map globalToC)
    (tts := m.tables.map tableToC)
    (fdts := ft.map FuncType.toDefType)
    (rts := (m.elems.map Elem.type).map RefType.toC)
    (xtE := xt.map ExternType.toCore)
    (hcty ▸ typesOk_map m.types {})
    (hcimp ▸ forall₂_map_map Import.toCore ExternType.toCore
      (fun i x hi => ImportOk.toCore hi) himports)
    rfl rfl (hctags ▸ List.Forall₂.nil)
    (globalsOk_toCore hglobals (hcglob ▸ hcg) hA')
    ?hmems ?htables ?hfuncs ?hdata ?helems ?hstart ?hexports ?hdisjoint
  case hmems =>
    intro mt hmt
    rw [hcmem] at hmt
    simp only [List.mem_map] at hmt
    obtain ⟨mt₀, hmt₀, rfl⟩ := hmt
    exact memTypeOk_toCore (memOk_list_valid hmems mt₀ hmt₀)
  case htables =>
    rw [hctab]
    refine forall₂_map_map TableType.toCoreTable tableToC ?_ htables
    intro t t' ht
    refine ⟨?_, ?_, ?_⟩
    · rw [ht.1]; exact (closeTableType_toCore _ t).symm
    · rw [ht.1]; exact tableTypeOk_toC _ ht.2
    · rw [ht.1]; exact refNull_ok _ t.element
  case hfuncs =>
    refine hcfun ▸ forall₂_mapM FuncType.toDefType ?_ hcf hfuncs
    intro f fty cf' hf hcf'
    cases hf with
    | mk hx hbody =>
      simp only [Func.toCore, Option.map_eq_some_iff] at hcf'
      obtain ⟨cbody, hcbody, rfl⟩ := hcf'
      refine Silmaril.Wasm.Validation.FuncOk.mk
        (lts := f.locals.map fun t => (⟨.set, t.toC⟩ : LocalType))
        (prefix_map_getElem? hA.types hx) (expand_toDefType fty) ?_ ?_
      · refine forall₂_map_of ValType.toCore
          (fun t => (⟨.set, t.toC⟩ : LocalType)) f.locals ?_
        intro t _
        exact (closeVal_toCore _ t) ▸ Silmaril.Wasm.Validation.LocalOk.set
          (by rw [closeVal_toCore]; exact tyOk_toC _ t)
          (by rw [closeVal_toCore]; exact defaultable_toC t)
      · have := ExprOk.toCore' (Agrees.funcBody hA rfl rfl fty f.locals) hbody hcbody
        simpa [Silmaril.Wasm.Validation.ExprOk, Ty.toList_ofList] using this
  case hdata =>
    intro d hd
    rw [hcdat] at hd
    obtain ⟨d₀, hd₀, hd₀c⟩ := mem_of_mapM hcd d hd
    simp only [Data.toCore, Option.map_eq_some_iff] at hd₀c
    obtain ⟨cmode, hcmode, rfl⟩ := hd₀c
    exact DataModeOk.toCore' hAe (hdatas d₀ hd₀) hcmode
  case helems =>
    refine hcele ▸ forall₂_mapM RefType.toC ?_ hce helems
    intro e rt' ce' he hce'
    obtain ⟨rfl, hinit, hmode⟩ := he
    simp only [Elem.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hce'
    obtain ⟨cinit, hcinit, cmode, hcmode, rfl⟩ := hce'
    refine ⟨(closeRef_toCore _ _).symm, tyOk_toC_ref _ _, ?_, ElemModeOk.toCore' hAe hmode hcmode⟩
    intro ex hex
    obtain ⟨ex₀, hex₀, hexc⟩ := mem_of_mapM hcinit ex hex
    exact ExprOkConst.toCore' hAe (hinit ex₀ hex₀) hexc
  case hstart =>
    intro x hx
    rw [hcsta] at hx
    refine ⟨_, prefix_map_getElem? hA.funcs (hstart x hx), ?_⟩
    simpa using expand_toDefType ⟨[], []⟩
  case hexports =>
    refine hcexp ▸ forall₂_map_map Export.toCore ExternType.toCore ?_ hexports
    rintro ⟨nm, idx⟩ x he
    cases he with
    | func hx => exact .func (funcs_get hA hx)
    | global hx => exact .global (globals_get hA hx)
    | table hx => exact .table (tables_get hA hx)
    | memory hx => exact .mem (prefix_map_getElem? hA.mems hx)
  case hdisjoint =>
    rw [hcexp]
    simpa [Export.toCore, Function.comp_def] using hnames

/-- **Milestone.** Every valid 2.0 module maps to a valid Core 3.0 module, with
the import and export types the images of the 2.0 ones. -/
theorem ModuleValid.toCore_ok {m : Module} {c : Wasm.Module}
    (hc : Module.toCore m = some c) (h : ModuleValid m) :
    ∃ ixt xt : List ExternType, ModuleOk m ixt xt ∧
      Silmaril.Wasm.Validation.ModuleOk c
        ⟨ixt.map ExternType.toCore, xt.map ExternType.toCore⟩ :=
  let ⟨ixt, xt, hok⟩ := h
  ⟨ixt, xt, hok, ModuleOk.toCore hc hok⟩

/-- **Milestone.** Every valid 2.0 module maps to a valid Core 3.0 module. -/
theorem ModuleValid.toCore {m : Module} {c : Wasm.Module}
    (hc : Module.toCore m = some c) (h : ModuleValid m) :
    Silmaril.Wasm.Validation.ModuleValid c :=
  let ⟨_, _, _, hok⟩ := ModuleValid.toCore_ok hc h
  ⟨_, hok⟩

/-- **binary-faithful embedding.** The binary-faithful image of a valid 2.0 module is valid
too, with the *same* Core 3.0 module type; the bridge is
`V2.Module.toCoreBinary_ok`. -/
theorem ModuleValid.toCoreBinary {m : Module} {c cb : Wasm.Module}
    (hc : Module.toCore m = some c) (hb : Module.toCoreBinary m = some cb)
    (h : ModuleValid m) : Silmaril.Wasm.Validation.ModuleValid cb :=
  Module.toCoreBinary_valid hc hb (ModuleValid.toCore hc h)

/-! ## The converse is false

Two checked counterexamples. Both are 2.0 *syntax* whose Core 3.0 image is
valid, and which 2.0 validation rejects. -/

namespace Converse

/-- A 2.0 index literal. -/
abbrev idx0 {k : IndexKind} : Idx k := ⟨⟨0, Nat.two_pow_pos 32⟩⟩

/-! ### `global.get` of an earlier *defined* immutable global

Core 3.0's `Globals_ok` is sequential: each initialiser sees the globals defined
before it. 2.0's `Module_ok` checks *every* global initialiser in `C'`, whose
`GLOBALS` component is `igt*`, the **imported** globals only
(`6-typing:703,706`).
So this module is Core-valid and 2.0-invalid. -/
def sharedGlobalModule : Module where
  globals :=
    [⟨⟨.const, .num (.int .i32)⟩, [.intConst .i32 0]⟩,
     ⟨⟨.const, .num (.int .i32)⟩, [.globalGet idx0]⟩]

/-- The Core 3.0 image of `sharedGlobalModule`. -/
def coreSharedGlobal : Wasm.Module where
  globals :=
    [⟨⟨.const, .num (.int .i32)⟩, [.intConst .i32 0]⟩,
     ⟨⟨.const, .num (.int .i32)⟩, [.globalGet idx0]⟩]

theorem toCore_sharedGlobalModule :
    Module.toCore sharedGlobalModule = some coreSharedGlobal := rfl

/-- The image **is** valid in Core 3.0. -/
theorem coreSharedGlobal_valid :
    Silmaril.Wasm.Validation.ModuleValid coreSharedGlobal := by
  refine ⟨⟨[], []⟩, Silmaril.Wasm.Validation.ModuleOk.mk
    (dts := []) (xtI := []) (jts := []) (fdts := [])
    (gts := [⟨.const, .num (.int .i32)⟩, ⟨.const, .num (.int .i32)⟩])
    (tts := []) (rts := []) (xtE := [])
    .nil .nil rfl rfl .nil ?_ (by simp [coreSharedGlobal]) .nil .nil
    (by simp [coreSharedGlobal]) .nil (by simp [coreSharedGlobal]) .nil
    (by simp [coreSharedGlobal])⟩
  refine Silmaril.Wasm.Validation.GlobalsOk.cons ⟨rfl, .num _, ?_, ?_⟩
    (Silmaril.Wasm.Validation.GlobalsOk.cons ⟨rfl, .num _, ?_, ?_⟩ .nil)
  · exact .instr (.numeric (.intConst _ _))
  · intro i hi
    obtain rfl : i = Wasm.Instr.intConst .i32 0 := by simpa using hi
    exact .intConst _ _
  · exact .instr (.variable (Silmaril.Wasm.Validation.VariableInstrOk.globalGet
      (x := idx0) (m := .const) (t := .num (.int .i32))
      (by simp [Idx.toNat, Silmaril.Wasm.Validation.CExternType.globals])))
  · intro i hi
    obtain rfl : i = Wasm.Instr.globalGet idx0 := by simpa using hi
    exact Silmaril.Wasm.Validation.InstrConst.globalGet
      (x := idx0) (t := .num (.int .i32))
      (by simp [Idx.toNat, Silmaril.Wasm.Validation.CExternType.globals])

/-- But it is **not** valid in Wasm 2.0: `Instr_const/global.get`
(`6-typing:555`) looks the global up in `C'`, which has only the imported
globals. -/
theorem sharedGlobalModule_invalid : ¬ ModuleValid sharedGlobalModule := by
  rintro ⟨ixt, xt, h⟩
  cases h with
  | @mk ft' ft gt tt mt rt C C' htypes himports hglobals htables hmems helems hdatas
      hfuncs hstart hexports hmems_le hnames hC hC' =>
    subst hC'
    cases himports
    cases hglobals with
    | cons _ hrest =>
      cases hrest with
      | cons h1 _ =>
        have hconst := h1.2.2.const (.globalGet idx0) (by simp)
        cases hconst with
        | globalGet hx _ => simp [ExternType.globals, Idx.toNat] at hx

/-- **The converse fails.** -/
theorem converse_fails_globals :
    ∃ (m : Module) (c : Wasm.Module), Module.toCore m = some c ∧
      Silmaril.Wasm.Validation.ModuleValid c ∧ ¬ ModuleValid m :=
  ⟨sharedGlobalModule, coreSharedGlobal, toCore_sharedGlobalModule,
    coreSharedGlobal_valid, sharedGlobalModule_invalid⟩

/-! ### Two memories

Core 3.0 has the multi-memory proposal; 2.0 bounds the memory index space by
`1` (`6-typing:698`, and see the `ModuleOk.hmems_le` deviation memory-count deviation). -/

/-- Two empty 2.0 memories. -/
def twoMemModule : Module where
  memories := [⟨⟨⟨0, Nat.two_pow_pos 32⟩, none⟩⟩, ⟨⟨⟨0, Nat.two_pow_pos 32⟩, none⟩⟩]

/-- The Core 3.0 image of `twoMemModule`. -/
def coreTwoMem : Wasm.Module where
  memories :=
    [⟨.i32, ⟨⟨0, Nat.two_pow_pos 64⟩, none⟩⟩, ⟨.i32, ⟨⟨0, Nat.two_pow_pos 64⟩, none⟩⟩]

theorem toCore_twoMemModule : Module.toCore twoMemModule = some coreTwoMem := rfl

/-- The image **is** valid in Core 3.0. -/
theorem coreTwoMem_valid : Silmaril.Wasm.Validation.ModuleValid coreTwoMem := by
  refine ⟨⟨[], []⟩, Silmaril.Wasm.Validation.ModuleOk.mk
    (dts := []) (xtI := []) (jts := []) (fdts := []) (gts := [])
    (tts := []) (rts := []) (xtE := [])
    .nil .nil rfl rfl .nil .nil ?_ .nil .nil
    (by simp [coreTwoMem]) .nil (by simp [coreTwoMem]) .nil (by simp [coreTwoMem])⟩
  intro mt hmt
  simp only [coreTwoMem, List.mem_cons, List.not_mem_nil, or_false] at hmt
  rcases hmt with rfl | rfl <;>
    exact ⟨by simp, trivial⟩

/-- But it is **not** valid in Wasm 2.0. -/
theorem twoMemModule_invalid : ¬ ModuleValid twoMemModule := by
  rintro ⟨ixt, xt, h⟩
  cases h with
  | @mk ft' ft gt tt mt rt C C' htypes himports hglobals htables hmems helems hdatas
      hfuncs hstart hexports hmems_le hnames hC hC' =>
    subst hC
    cases himports
    obtain rfl := memOk_list_eq hmems
    simp [ExternType.mems, twoMemModule] at hmems_le

/-- **The converse fails**, a second time. -/
theorem converse_fails_memories :
    ∃ (m : Module) (c : Wasm.Module), Module.toCore m = some c ∧
      Silmaril.Wasm.Validation.ModuleValid c ∧ ¬ ModuleValid m :=
  ⟨twoMemModule, coreTwoMem, toCore_twoMemModule, coreTwoMem_valid, twoMemModule_invalid⟩

end Converse

end Silmaril.Wasm.V2.Validation
