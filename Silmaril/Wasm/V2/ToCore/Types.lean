module

public import Silmaril.Wasm.V2.Modules
public import Silmaril.Wasm.Modules
public import Silmaril.Wasm.Validation.Subtyping.Properties

/-!
# Wasm 2.0 types and immediates as Core 3.0 syntax

This file opens the `2.0 ⊆ 3.0` subset theorem. For every sort of the Wasm 2.0
type and immediate syntax (`Silmaril.Wasm.V2.Types`, `…Ops`, `…Instructions`,
`…Modules`) it gives a *source-level* injection `toCore` into the corresponding
Core 3.0 sort (`Silmaril.Wasm.Types`, `…Ops`, `…Instructions`, `…Modules`),
together with a partial retraction `ofCore?` that accepts exactly the 2.0 image,
a `@[simp]` retraction lemma, and injectivity derived from it. No typing or
execution correspondence is asserted here; those are separate files.

Line references `1-syntax:NN` point into
`specification/wasm-2.0/1-syntax.spectec` at WebAssembly/spec revision
`608711107b7f1edb13efd57b7d79b49477462d36` (hash-pinned in
`specs/wasm/core-2.0.json`), and were re-checked against the pinned file with
`cat -n`; they are therefore a few lines later than the (slightly shifted)
citations in `Silmaril/Wasm/V2/Types.lean`.

## How 2.0 syntax lands in 3.0

* `reftype` (`1-syntax:135`) is a two-element enumeration. Core 3.0 `RefType` is
  `nullable × heaptype`, so `FUNCREF ↦ (REF NULL FUNC)` and
  `EXTERNREF ↦ (REF NULL EXTERN)`. The image consists of exactly those two
  nullable abstract reference types, which `RefType.ofCore?` recognises.
* `limits` (`1-syntax:164`) has `u32` bounds; Core 3.0 widened them to `u64` for
  memory64. `widen32`/`narrow32?` are the corresponding embedding/retraction.
  They are the V2 copies of `V1.widen32`/`V1.narrow32?`: the 2.0 layer is an
  independent formalization and deliberately does not import the 1.0 layer.
* `tabletype`/`memtype` (`1-syntax:171`, `1-syntax:173`) gain a 3.0 `addrtype`
  field, always `I32` in the image.
* `memarg` (`1-syntax:383`) gains a 64-bit offset in 3.0; the memory index of
  3.0's `memarg` is *not* part of this file (it belongs to the instruction
  injection, where it is always `0`).
* `cvtop` (`1-syntax:305`) is untyped in 2.0 — the source and target number
  types sit on the `CVTOP` instruction — whereas Core 3.0's `ConvertOp` fixes
  them in the operator. The injection is therefore the partial, type-indexed
  `CvtOp.toCore`, which is literally `V2.CvtOp.toShared`; its retraction
  `CvtOp.ofCore` recovers the triple `(target, source, op)` and is total,
  because every Core 3.0 `ConvertOp` already exists in 2.0.
* The vector operator families of 2.0 (`1-syntax:340`, `350`, `376`, `367`,
  `390`) are the Core 3.0 ones minus the relaxed-SIMD alternatives, so each
  `toCore` is the inclusion `toShared` of `Silmaril.Wasm.V2.Ops` and each
  `ofCore?` rejects exactly the relaxed operators. `VecLoadOp` additionally
  gains 3.0's `full` alternative, which is 2.0's absent `vloadop?`
  (`VecLoadOp.toCoreOpt`).

## `externtype` versus `importdesc`

`1-syntax:179` writes `externtype ::= FUNC functype | GLOBAL globaltype |
TABLE tabletype | MEM memtype`: the function case carries a whole `functype`.
Core 3.0's *source* `ExternType.func` instead carries a `TypeIdx`, because 3.0
function types are defined types living in the type section. There is no
type-section-free map `V2.ExternType → Wasm.ExternType`. We therefore split the
job in two, and both halves are total:

* **Syntactic.** `ImportDesc.toCore : V2.ImportDesc → Wasm.ExternType`. The 2.0
  import descriptor already carries a `TypeIdx` (the decided deviation
  documented in `Silmaril/Wasm/V2/Modules.lean`, matching `A-binary:139`'s
  `;; TODO: typeidx`, the W3C 2.0 text and the reference interpreter), so this
  map needs no type section and is the one `Import.toCore` uses. This is the
  injection a module-level `Module.toCore` will use.
* **Semantic.** `ExternType.toCore : V2.ExternType → CExternType`, into Core
  3.0's *closed* external types of `Silmaril.Wasm.Validation.DefTypes`, whose
  `func` case carries a `DefType`. The resolved 2.0 `functype` maps to its
  defined type `FuncType.toDefType`, so no type index is needed. This is the
  injection the import/export matching of the subset theorem needs, since
  `Module_ok` in Core 3.0 produces `CExternType`s.

## Defined types

The second half of the file mirrors `Silmaril/Wasm/V1/ToCore/DefTypes.lean`.
Each 2.0 `functype` becomes one final, parent-free, singleton recursive group
(`FuncType.toCoreRec`), so a 2.0 type section of length `n` becomes a 3.0 type
section of `n` recursive groups and *type indices do not shift*. Its defined
type `FuncType.toDefType` is closed, expands to the 2.0 signature, and on this
image Core 3.0 defined-type subtyping is equality
(`FuncType.toDefType_sub_iff`) — which is what `call_indirect` needs.
-/

@[expose] public section

namespace Silmaril.Wasm.V2

open Silmaril.Wasm.Validation

/-! ## Generic plumbing -/

/-- Mapping the trivially-succeeding partial function over a list succeeds. -/
@[simp] theorem mapM_some {α : Type*} (xs : List α) : xs.mapM some = some xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.mapM_cons, ih]; rfl

/-- A map with a left inverse among partial functions is injective. -/
theorem injective_of_ofCore? {α β : Type*} {f : α → β} {g : β → Option α}
    (h : ∀ a, g (f a) = some a) : Function.Injective f := by
  intro a b hab
  have ha := h a
  rw [hab, h b] at ha
  exact (Option.some.inj ha).symm

/-- The `u32` bounds of 2.0 (`1-syntax:164`) inside the `u64` bounds of Core 3.0.
Deliberately a V2 copy of `V1.widen32`: the 2.0 layer does not import the 1.0
layer. -/
def widen32 (n : Fin (2 ^ 32)) : Fin (2 ^ 64) :=
  ⟨n.val, Nat.lt_of_lt_of_le n.isLt (by decide)⟩

/-- The retraction of `widen32`; see `1-syntax:164`. -/
def narrow32? (n : Fin (2 ^ 64)) : Option (Fin (2 ^ 32)) :=
  if h : n.val < 2 ^ 32 then some ⟨n.val, h⟩ else none

@[simp] theorem narrow32?_widen32 (n : Fin (2 ^ 32)) :
    narrow32? (widen32 n) = some n := by simp [narrow32?, widen32]

theorem widen32_injective : Function.Injective widen32 :=
  injective_of_ofCore? narrow32?_widen32

/-! ## Value types -/

/-- `reftype ::= FUNCREF | EXTERNREF` (`1-syntax:135`) as the two nullable
abstract reference types of Core 3.0. -/
def RefType.toCore : RefType → Wasm.RefType
  | .funcref => ⟨true, .abstract .func⟩
  | .externref => ⟨true, .abstract .extern⟩

/-- The retraction of `RefType.toCore` (`1-syntax:135`). -/
def RefType.ofCore? : Wasm.RefType → Option RefType
  | ⟨true, .abstract .func⟩ => some .funcref
  | ⟨true, .abstract .extern⟩ => some .externref
  | _ => none

@[simp] theorem RefType.ofCore?_toCore (t : RefType) : ofCore? t.toCore = some t := by
  cases t <;> rfl

theorem RefType.toCore_injective : Function.Injective RefType.toCore :=
  injective_of_ofCore? RefType.ofCore?_toCore

/-- `valtype ::= numtype | vectype | reftype` (`1-syntax:138`, without `BOT`). -/
def ValType.toCore : ValType → Wasm.ValType
  | .num t => .num t
  | .vec t => .vec t
  | .ref t => .ref t.toCore

/-- The retraction of `ValType.toCore` (`1-syntax:138`). -/
def ValType.ofCore? : Wasm.ValType → Option ValType
  | .num t => some (.num t)
  | .vec t => some (.vec t)
  | .ref t => (RefType.ofCore? t).map ValType.ref

@[simp] theorem ValType.ofCore?_toCore (t : ValType) : ofCore? t.toCore = some t := by
  cases t <;> simp [toCore, ofCore?]

theorem ValType.toCore_injective : Function.Injective ValType.toCore :=
  injective_of_ofCore? ValType.ofCore?_toCore

/-- `resulttype ::= list(valtype)` (`1-syntax:146`). -/
def ResultType.toCore (ts : ResultType) : Wasm.ResultType := ts.map ValType.toCore

/-- The retraction of `ResultType.toCore` (`1-syntax:146`). -/
def ResultType.ofCore? (ts : Wasm.ResultType) : Option ResultType := ts.mapM ValType.ofCore?

@[simp] theorem ResultType.ofCore?_toCore (ts : ResultType) :
    ResultType.ofCore? (ResultType.toCore ts) = some ts := by
  simp [toCore, ofCore?, List.mapM_map, Function.comp_def]

theorem ResultType.toCore_injective : Function.Injective ResultType.toCore :=
  injective_of_ofCore? ResultType.ofCore?_toCore

/-! ## External types -/

/-- `limits ::= `[u32 .. u32?]` (`1-syntax:164`), widened into the `u64` limits
of Core 3.0. -/
def Limits.toCore (l : Limits) : Wasm.Limits :=
  ⟨widen32 l.min, l.max.map widen32⟩

/-- The retraction of `Limits.toCore` (`1-syntax:164`). -/
def Limits.ofCore? (l : Wasm.Limits) : Option Limits := do
  let min ← narrow32? l.min
  let max ← match l.max with
    | none => some none
    | some n => (narrow32? n).map some
  return ⟨min, max⟩

@[simp] theorem Limits.ofCore?_toCore (l : Limits) : ofCore? l.toCore = some l := by
  rcases l with ⟨min, max⟩
  cases max <;> simp [toCore, ofCore?]

theorem Limits.toCore_injective : Function.Injective Limits.toCore :=
  injective_of_ofCore? Limits.ofCore?_toCore

/-- `functype ::= resulttype -> resulttype` (`1-syntax:169`). -/
def FuncType.toCore (t : FuncType) : Wasm.FuncType :=
  ⟨ResultType.toCore t.params, ResultType.toCore t.results⟩

/-- The retraction of `FuncType.toCore` (`1-syntax:169`). -/
def FuncType.ofCore? (t : Wasm.FuncType) : Option FuncType := do
  return ⟨← ResultType.ofCore? t.params, ← ResultType.ofCore? t.results⟩

@[simp] theorem FuncType.ofCore?_toCore (t : FuncType) : ofCore? t.toCore = some t := by
  cases t
  simp [toCore, ofCore?]

theorem FuncType.toCore_injective : Function.Injective FuncType.toCore :=
  injective_of_ofCore? FuncType.ofCore?_toCore

/-- Each 2.0 function type (`1-syntax:169`) occupies one final, parent-free,
singleton recursive group, so a 2.0 type section maps to a 3.0 type section of
the same length and type indices do not shift. -/
def FuncType.toCoreRec (t : FuncType) : Wasm.RecType :=
  ⟨[⟨true, [], .func t.toCore⟩]⟩

/-- The retraction of `FuncType.toCoreRec`. -/
def FuncType.ofCoreRec? : Wasm.RecType → Option FuncType
  | ⟨[⟨true, [], .func t⟩]⟩ => ofCore? t
  | _ => none

@[simp] theorem FuncType.ofCoreRec?_toCoreRec (t : FuncType) :
    ofCoreRec? t.toCoreRec = some t := by simp [toCoreRec, ofCoreRec?]

theorem FuncType.toCoreRec_injective : Function.Injective FuncType.toCoreRec :=
  injective_of_ofCore? FuncType.ofCoreRec?_toCoreRec

/-- `tabletype ::= limits reftype` (`1-syntax:171`). Core 3.0 tables carry an
`addrtype`, which is `I32` for every 2.0 table. -/
def TableType.toCore (t : TableType) : Wasm.TableType :=
  ⟨.i32, t.limits.toCore, t.element.toCore⟩

/-- The retraction of `TableType.toCore` (`1-syntax:171`). -/
def TableType.ofCore? (t : Wasm.TableType) : Option TableType := do
  if t.address = .i32 then
    return ⟨← Limits.ofCore? t.limits, ← RefType.ofCore? t.element⟩
  else none

@[simp] theorem TableType.ofCore?_toCore (t : TableType) : ofCore? t.toCore = some t := by
  cases t
  simp [toCore, ofCore?]

theorem TableType.toCore_injective : Function.Injective TableType.toCore :=
  injective_of_ofCore? TableType.ofCore?_toCore

/-- `memtype ::= limits PAGE` (`1-syntax:173`); the `PAGE` marker carries no
information and the Core 3.0 `addrtype` is `I32`. -/
def MemoryType.toCore (t : MemoryType) : Wasm.MemoryType := ⟨.i32, t.limits.toCore⟩

/-- The retraction of `MemoryType.toCore` (`1-syntax:173`). -/
def MemoryType.ofCore? (t : Wasm.MemoryType) : Option MemoryType := do
  if t.address = .i32 then return ⟨← Limits.ofCore? t.limits⟩ else none

@[simp] theorem MemoryType.ofCore?_toCore (t : MemoryType) : ofCore? t.toCore = some t := by
  cases t
  simp [toCore, ofCore?]

theorem MemoryType.toCore_injective : Function.Injective MemoryType.toCore :=
  injective_of_ofCore? MemoryType.ofCore?_toCore

/-- `globaltype ::= mut valtype` (`1-syntax:167`). -/
def GlobalType.toCore (t : GlobalType) : Wasm.GlobalType := ⟨t.mutability, t.value.toCore⟩

/-- The retraction of `GlobalType.toCore` (`1-syntax:167`). -/
def GlobalType.ofCore? (t : Wasm.GlobalType) : Option GlobalType := do
  return ⟨t.mutability, ← ValType.ofCore? t.value⟩

@[simp] theorem GlobalType.ofCore?_toCore (t : GlobalType) : ofCore? t.toCore = some t := by
  cases t
  simp [toCore, ofCore?]

theorem GlobalType.toCore_injective : Function.Injective GlobalType.toCore :=
  injective_of_ofCore? GlobalType.ofCore?_toCore

/-! ## Imports and exports -/

/-- The 2.0 import descriptor of `Silmaril.Wasm.V2.Modules` as a Core 3.0 source
`externtype`. The function case already carries a `typeidx`, so this needs no
type section; see the module documentation. -/
def ImportDesc.toCore : ImportDesc → Wasm.ExternType
  | .func t => .func t
  | .table t => .table t.toCore
  | .memory t => .memory t.toCore
  | .global t => .global t.toCore

/-- The retraction of `ImportDesc.toCore`; Core 3.0 tag imports are outside the
2.0 image. -/
def ImportDesc.ofCore? : Wasm.ExternType → Option ImportDesc
  | .func t => some (.func t)
  | .table t => (TableType.ofCore? t).map ImportDesc.table
  | .memory t => (MemoryType.ofCore? t).map ImportDesc.memory
  | .global t => (GlobalType.ofCore? t).map ImportDesc.global
  | .tag _ => none

@[simp] theorem ImportDesc.ofCore?_toCore (d : ImportDesc) : ofCore? d.toCore = some d := by
  cases d <;> simp [toCore, ofCore?]

theorem ImportDesc.toCore_injective : Function.Injective ImportDesc.toCore :=
  injective_of_ofCore? ImportDesc.ofCore?_toCore

/-- `import ::= IMPORT name name externtype` (`1-syntax:564`). -/
def Import.toCore (i : Import) : Wasm.Import := ⟨i.moduleName, i.name, i.desc.toCore⟩

/-- The retraction of `Import.toCore` (`1-syntax:564`). -/
def Import.ofCore? (i : Wasm.Import) : Option Import := do
  return ⟨i.moduleName, i.name, ← ImportDesc.ofCore? i.type⟩

@[simp] theorem Import.ofCore?_toCore (i : Import) : ofCore? i.toCore = some i := by
  cases i
  simp [toCore, ofCore?]

theorem Import.toCore_injective : Function.Injective Import.toCore :=
  injective_of_ofCore? Import.ofCore?_toCore

/-- `externidx ::= FUNC funcidx | GLOBAL globalidx | TABLE tableidx | MEM memidx`
(`1-syntax:560`). -/
def ExternIdx.toCore : ExternIdx → Wasm.ExternIdx
  | .func i => .func i
  | .table i => .table i
  | .memory i => .memory i
  | .global i => .global i

/-- The retraction of `ExternIdx.toCore` (`1-syntax:560`); Core 3.0 tag indices
are outside the 2.0 image. -/
def ExternIdx.ofCore? : Wasm.ExternIdx → Option ExternIdx
  | .func i => some (.func i)
  | .table i => some (.table i)
  | .memory i => some (.memory i)
  | .global i => some (.global i)
  | .tag _ => none

@[simp] theorem ExternIdx.ofCore?_toCore (i : ExternIdx) : ofCore? i.toCore = some i := by
  cases i <;> rfl

theorem ExternIdx.toCore_injective : Function.Injective ExternIdx.toCore :=
  injective_of_ofCore? ExternIdx.ofCore?_toCore

/-- `export ::= EXPORT name externidx` (`1-syntax:562`). -/
def Export.toCore (e : Export) : Wasm.Export := ⟨e.name, e.index.toCore⟩

/-- The retraction of `Export.toCore` (`1-syntax:562`). -/
def Export.ofCore? (e : Wasm.Export) : Option Export := do
  return ⟨e.name, ← ExternIdx.ofCore? e.index⟩

@[simp] theorem Export.ofCore?_toCore (e : Export) : ofCore? e.toCore = some e := by
  cases e
  simp [toCore, ofCore?]

theorem Export.toCore_injective : Function.Injective Export.toCore :=
  injective_of_ofCore? Export.ofCore?_toCore

/-! ## Instruction immediates -/

/-- `blocktype ::= _RESULT valtype? | _IDX typeidx` (`1-syntax:400`). -/
def BlockType.toCore : BlockType → Wasm.BlockType
  | .result none => .empty
  | .result (some t) => .value t.toCore
  | .typeIdx i => .typeIdx i

/-- The retraction of `BlockType.toCore` (`1-syntax:400`). -/
def BlockType.ofCore? : Wasm.BlockType → Option BlockType
  | .empty => some (.result none)
  | .value t => (ValType.ofCore? t).map fun v => .result (some v)
  | .typeIdx i => some (.typeIdx i)

@[simp] theorem BlockType.ofCore?_toCore (t : BlockType) : ofCore? t.toCore = some t := by
  cases t with
  | result t => cases t <;> simp [toCore, ofCore?]
  | typeIdx i => rfl

theorem BlockType.toCore_injective : Function.Injective BlockType.toCore :=
  injective_of_ofCore? BlockType.ofCore?_toCore

/-- `memarg ::= {ALIGN u32, OFFSET u32}` (`1-syntax:383`); Core 3.0 offsets are
`u64`. The Core 3.0 memory index is not part of `memarg` here: it lives on the
instruction and is always `0` in the 2.0 image. -/
def MemArg.toCore (a : MemArg) : Wasm.MemArg := ⟨a.align, widen32 a.offset⟩

/-- The retraction of `MemArg.toCore` (`1-syntax:383`). -/
def MemArg.ofCore? (a : Wasm.MemArg) : Option MemArg := do
  return ⟨a.align, ← narrow32? a.offset⟩

@[simp] theorem MemArg.ofCore?_toCore (a : MemArg) : ofCore? a.toCore = some a := by
  cases a
  simp [toCore, ofCore?]

theorem MemArg.toCore_injective : Function.Injective MemArg.toCore :=
  injective_of_ofCore? MemArg.ofCore?_toCore

/-! ## Scalar conversions

`cvtop` (`1-syntax:305`) is untyped: `CVTOP numtype_1 numtype_2 cvtop` carries
the target and source. Core 3.0's `ConvertOp` fixes them inside the operator,
so the injection is partial in exactly the way `V2.CvtOp.toShared` already is
(`3-numerics:310-320`): combinations with no `$cvtop__` equation have no Core
3.0 operator either. -/

/-- The Core 3.0 conversion operator denoted by `CVTOP target source op`
(`1-syntax:305`). -/
def CvtOp.toCore (target source : NumType) (op : CvtOp) : Option Wasm.ConvertOp :=
  op.toShared target source

/-- The retraction of `CvtOp.toCore`: Core 3.0's `ConvertOp` determines the
target type, the source type and the 2.0 operator, and every Core 3.0
`ConvertOp` is in the 2.0 image, so this is total. -/
def CvtOp.ofCore : Wasm.ConvertOp → NumType × NumType × CvtOp
  | .wrap => (.int .i32, .int .i64, .wrap)
  | .extend s => (.int .i64, .int .i32, .extend s)
  | .trunc f i s => (.int i, .float f, .trunc s)
  | .truncSat f i s => (.int i, .float f, .truncSat s)
  | .convert i f s => (.float f, .int i, .convert s)
  | .demote => (.float .f32, .float .f64, .demote)
  | .promote => (.float .f64, .float .f32, .promote)
  | .reinterpretInt .f32 => (.int .i32, .float .f32, .reinterpret)
  | .reinterpretInt .f64 => (.int .i64, .float .f64, .reinterpret)
  | .reinterpretFloat .i32 => (.float .f32, .int .i32, .reinterpret)
  | .reinterpretFloat .i64 => (.float .f64, .int .i64, .reinterpret)

/-- `CvtOp.ofCore` inverts `CvtOp.toCore` wherever the latter is defined. -/
theorem CvtOp.map_ofCore_toCore (target source : NumType) (op : CvtOp) :
    (CvtOp.toCore target source op).map CvtOp.ofCore =
      (CvtOp.toCore target source op).map (fun _ => (target, source, op)) := by
  cases target <;> cases source <;> rename_i t s <;> cases t <;> cases s <;> cases op <;> rfl

/-- The retraction property of `CvtOp.ofCore`. -/
theorem CvtOp.ofCore_toCore (target source : NumType) (op : CvtOp) (c : Wasm.ConvertOp)
    (h : CvtOp.toCore target source op = some c) :
    CvtOp.ofCore c = (target, source, op) := by
  have hm := CvtOp.map_ofCore_toCore target source op
  rw [h] at hm
  simpa using hm

/-- `CVTOP` immediates are determined by the Core 3.0 operator they denote. -/
theorem CvtOp.toCore_injective {target₁ source₁ target₂ source₂ : NumType} {op₁ op₂ : CvtOp}
    {c : Wasm.ConvertOp} (h₁ : CvtOp.toCore target₁ source₁ op₁ = some c)
    (h₂ : CvtOp.toCore target₂ source₂ op₂ = some c) :
    (target₁, source₁, op₁) = (target₂, source₂, op₂) := by
  rw [← CvtOp.ofCore_toCore _ _ _ _ h₁, ← CvtOp.ofCore_toCore _ _ _ _ h₂]

/-! ## Vector operators

Each 2.0 vector operator family is the Core 3.0 family minus the relaxed-SIMD
alternatives, so `toCore` is the inclusion already written as `toShared` in
`Silmaril.Wasm.V2.Ops`, and `ofCore?` rejects exactly the relaxed operators. -/

/-- `vbinop_(Jnn X M)` (`1-syntax:340`). -/
def VecIntBinOp.toCore (op : VecIntBinOp) : Wasm.VecIntBinOp := op.toShared

/-- The retraction of `VecIntBinOp.toCore` (`1-syntax:340`); `RELAXED_Q15MULR_S`
is not a 2.0 operator. -/
def VecIntBinOp.ofCore? : Wasm.VecIntBinOp → Option VecIntBinOp
  | .add => some .add
  | .sub => some .sub
  | .mul => some .mul
  | .addSat s => some (.addSat s)
  | .subSat s => some (.subSat s)
  | .avgrU => some .avgrU
  | .q15mulrSatS => some .q15mulrSatS
  | .min s => some (.min s)
  | .max s => some (.max s)
  | .relaxedQ15mulrS => none

@[simp] theorem VecIntBinOp.ofCore?_toCore (op : VecIntBinOp) : ofCore? op.toCore = some op := by
  cases op <;> rfl

theorem VecIntBinOp.toCore_injective : Function.Injective VecIntBinOp.toCore :=
  injective_of_ofCore? VecIntBinOp.ofCore?_toCore

/-- The 2.0 shape side conditions of `1-syntax:340-349` agree with the Core 3.0
ones on the image. -/
@[simp] theorem VecIntBinOp.valid_toCore (s : IntShape) (op : VecIntBinOp) :
    op.toCore.valid s = op.valid s := by
  cases s <;> cases op <;> rfl

/-- `vbinop_(Fnn X M)` (`1-syntax:350`). -/
def VecFloatBinOp.toCore (op : VecFloatBinOp) : Wasm.VecFloatBinOp := op.toShared

/-- The retraction of `VecFloatBinOp.toCore` (`1-syntax:350`); `RELAXED_MIN` and
`RELAXED_MAX` are not 2.0 operators. -/
def VecFloatBinOp.ofCore? : Wasm.VecFloatBinOp → Option VecFloatBinOp
  | .add => some .add
  | .sub => some .sub
  | .mul => some .mul
  | .div => some .div
  | .min => some .min
  | .max => some .max
  | .pmin => some .pmin
  | .pmax => some .pmax
  | .relaxedMin | .relaxedMax => none

@[simp] theorem VecFloatBinOp.ofCore?_toCore (op : VecFloatBinOp) :
    ofCore? op.toCore = some op := by cases op <;> rfl

theorem VecFloatBinOp.toCore_injective : Function.Injective VecFloatBinOp.toCore :=
  injective_of_ofCore? VecFloatBinOp.ofCore?_toCore

/-- `vextbinop_(Jnn X M) = EXTMUL half sx | DOT S` (`1-syntax:376`). -/
def VecExtBinOp.toCore (op : VecExtBinOp) : Wasm.VecExtBinOp := op.toShared

/-- The retraction of `VecExtBinOp.toCore` (`1-syntax:376`); `RELAXED_DOT` is
not a 2.0 operator. -/
def VecExtBinOp.ofCore? : Wasm.VecExtBinOp → Option VecExtBinOp
  | .extmul h s => some (.extmul h s)
  | .dotS => some .dotS
  | .relaxedDotS => none

@[simp] theorem VecExtBinOp.ofCore?_toCore (op : VecExtBinOp) : ofCore? op.toCore = some op := by
  cases op <;> rfl

theorem VecExtBinOp.toCore_injective : Function.Injective VecExtBinOp.toCore :=
  injective_of_ofCore? VecExtBinOp.ofCore?_toCore

/-- The 2.0 side conditions of `1-syntax:376-378` agree with the Core 3.0 ones
on the image. `VecExtBinOp.valid` takes the result shape first in the 2.0 layer
and the operand shape first in Core 3.0. -/
@[simp] theorem VecExtBinOp.valid_toCore (target source : IntShape) (op : VecExtBinOp) :
    op.toCore.valid source target = op.valid target source := by
  cases target <;> cases source <;> cases op <;> rfl

/-- `vcvtop` (`1-syntax:367`). -/
def VecCvtOp.toCore (op : VecCvtOp) : Wasm.VecConvertOp := op.toShared

/-- The retraction of `VecCvtOp.toCore` (`1-syntax:367`); `RELAXED_TRUNC` is not
a 2.0 operator. -/
def VecCvtOp.ofCore? : Wasm.VecConvertOp → Option VecCvtOp
  | .extend h s => some (.extend h s)
  | .truncSat s z => some (.truncSat s z)
  | .convert h s => some (.convert h s)
  | .demoteZero => some .demoteZero
  | .promoteLow => some .promoteLow
  | .relaxedTrunc _ _ => none

@[simp] theorem VecCvtOp.ofCore?_toCore (op : VecCvtOp) : ofCore? op.toCore = some op := by
  cases op <;> rfl

theorem VecCvtOp.toCore_injective : Function.Injective VecCvtOp.toCore :=
  injective_of_ofCore? VecCvtOp.ofCore?_toCore

/-- `VecCvtOp.valid` of the 2.0 layer is by definition the Core 3.0 condition on
the image; see `Silmaril/Wasm/V2/Ops.lean` and the deviation recorded in
`Silmaril/Wasm/V2/Instructions.lean`. -/
@[simp] theorem VecCvtOp.valid_toCore (target source : Shape) (op : VecCvtOp) :
    op.toCore.valid source target = op.valid target source := rfl

/-- `vloadop ::= SHAPE n X n _ sx | SPLAT n | ZERO n` (`1-syntax:390`). -/
def VecLoadOp.toCore (op : VecLoadOp) : Wasm.VecLoadOp := op.toShared

/-- `vloadop?` of `VLOAD vectype vloadop? memarg` (`1-syntax:510`): an absent
2.0 load shape is Core 3.0's `full`. -/
def VecLoadOp.toCoreOpt : Option VecLoadOp → Wasm.VecLoadOp
  | none => .full
  | some op => op.toCore

/-- The retraction of `VecLoadOp.toCore` (`1-syntax:390`); Core 3.0's `full` is
2.0's absent load shape, not a `vloadop`. -/
def VecLoadOp.ofCore? : Wasm.VecLoadOp → Option VecLoadOp
  | .extend8x8 s => some (.shape8x8 s)
  | .extend16x4 s => some (.shape16x4 s)
  | .extend32x2 s => some (.shape32x2 s)
  | .splat sz => some (.splat sz)
  | .zero32 => some .zero32
  | .zero64 => some .zero64
  | .full => none

/-- The retraction of `VecLoadOp.toCoreOpt`; total, since every Core 3.0 vector
load shape occurs in 2.0. -/
def VecLoadOp.ofCoreOpt : Wasm.VecLoadOp → Option VecLoadOp := VecLoadOp.ofCore?

@[simp] theorem VecLoadOp.ofCore?_toCore (op : VecLoadOp) : ofCore? op.toCore = some op := by
  cases op <;> rfl

@[simp] theorem VecLoadOp.ofCoreOpt_toCoreOpt (op : Option VecLoadOp) :
    ofCoreOpt (toCoreOpt op) = op := by
  cases op with
  | none => rfl
  | some op => exact ofCore?_toCore op

theorem VecLoadOp.toCore_injective : Function.Injective VecLoadOp.toCore :=
  injective_of_ofCore? VecLoadOp.ofCore?_toCore

theorem VecLoadOp.toCoreOpt_injective : Function.Injective VecLoadOp.toCoreOpt :=
  Function.LeftInverse.injective VecLoadOp.ofCoreOpt_toCoreOpt

/-! ## Semantic value types

`Silmaril.Wasm.Validation` works with `Ty`-valued *semantic* types, obtained from
the Core 3.0 source syntax by `liftVal`/`liftRec`. Composing with `toCore` gives
the 2.0 image directly. -/

/-- The Core 3.0 semantic value type of a 2.0 reference type (`1-syntax:135`). -/
def RefType.toC (t : RefType) : CRefType := liftRef t.toCore

/-- The Core 3.0 semantic value type of a 2.0 value type (`1-syntax:138`). -/
def ValType.toC (t : ValType) : CValType := liftVal t.toCore

@[simp] theorem liftRef_toCore (t : RefType) : liftRef t.toCore = t.toC := rfl

@[simp] theorem liftVal_toCore (t : ValType) : liftVal t.toCore = t.toC := rfl

/-- The retraction of `RefType.toC`. -/
def RefType.ofC? : CRefType → Option RefType
  | .ref true (.abs .func) => some .funcref
  | .ref true (.abs .extern) => some .externref
  | _ => none

@[simp] theorem RefType.ofC?_toC (t : RefType) : ofC? t.toC = some t := by cases t <;> rfl

theorem RefType.toC_injective : Function.Injective RefType.toC :=
  injective_of_ofCore? RefType.ofC?_toC

/-- The retraction of `ValType.toC`. -/
def ValType.ofC? : CValType → Option ValType
  | .num t => some (.num t)
  | .vec t => some (.vec t)
  | .refv r => (RefType.ofC? r).map ValType.ref
  | _ => none

@[simp] theorem ValType.ofC?_toC (t : ValType) : ofC? t.toC = some t := by
  cases t <;> simp [toC, ofC?, toCore, liftVal]

theorem ValType.toC_injective : Function.Injective ValType.toC :=
  injective_of_ofCore? ValType.ofC?_toC

/-- 2.0 value types contain no type indices, so substitution leaves them fixed. -/
@[simp] theorem ValType.subst_toC (σ : Subst) (t : ValType) : t.toC.subst σ = t.toC := by
  cases t with
  | num t => rfl
  | vec t => rfl
  | ref r => cases r <;> rfl

/-- 2.0 value types contain no type indices. -/
@[simp] theorem ValType.freeIdx_toC (t : ValType) : t.toC.freeIdx = [] := by
  cases t with
  | num t => rfl
  | vec t => rfl
  | ref r => cases r <;> rfl

theorem subst_ofList_toC (σ : Subst) (ts : List ValType) :
    (Ty.ofList (ts.map ValType.toC)).subst σ = Ty.ofList (ts.map ValType.toC) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [Ty.subst, ih]

theorem freeIdx_ofList_toC (ts : List ValType) :
    (Ty.ofList (ts.map ValType.toC)).freeIdx = [] := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [Ty.freeIdx, ih]

theorem liftResult_toCore (ts : List ValType) :
    liftResult (ResultType.toCore ts) = Ty.ofList (ts.map ValType.toC) := by
  simp [liftResult, ResultType.toCore, Function.comp_def]

theorem ofList_map_toC_injective :
    Function.Injective (fun ts : List ValType => Ty.ofList (ts.map ValType.toC)) := by
  intro a b h
  have h' := congrArg Ty.toList h
  simp only [Ty.toList_ofList] at h'
  exact List.map_injective_iff.mpr ValType.toC_injective h'

/-! ## Defined types

Modelled on `Silmaril/Wasm/V1/ToCore/DefTypes.lean`. -/

/-- The Core 3.0 defined type of a 2.0 function type (`1-syntax:169`):
projection `0` of its singleton recursive group. -/
def FuncType.toDefType (t : FuncType) : DefType := .defn (liftRec t.toCoreRec) 0

/-- The expansion of a 2.0 function type's defined type is its signature. -/
theorem FuncType.toDefType_expand (t : FuncType) :
    t.toDefType.expand? =
      some (.func (Ty.ofList (t.params.map ValType.toC))
        (Ty.ofList (t.results.map ValType.toC))) := by
  simp [toDefType, DefType.expand?, unrolldt, unrollrt, liftRec, toCoreRec, liftSub, liftComp,
    FuncType.toCore, liftResult_toCore, Ty.subst, subst_ofList_toC, Ty.subs, Ty.body, Ty.length]

/-- A 2.0 function type's defined type mentions no type index. -/
theorem FuncType.toDefType_closed (t : FuncType) : t.toDefType.Closed := by
  simp [toDefType, Ty.Closed, Ty.freeIdx, liftRec, toCoreRec, liftSub, liftComp,
    FuncType.toCore, liftResult_toCore, freeIdx_ofList_toC]

/-- Rolling the 2.0 group at any index gives exactly its defined type, so type
indices never shift. -/
theorem FuncType.rolldt_toCoreRec (x : Nat) (t : FuncType) :
    rolldt x (liftRec t.toCoreRec) = [t.toDefType] := by
  simp [rolldt, rollrt, toDefType, liftRec, toCoreRec, liftSub, liftComp, FuncType.toCore,
    liftResult_toCore, Ty.subst, subst_ofList_toC, Ty.subs, Ty.length]

/-- A 2.0 function type's defined type unrolls to a final, parent-free sub type. -/
theorem FuncType.toDefType_unroll (t : FuncType) :
    unrolldt t.toDefType =
      some (.sub true .nil
        (.func (Ty.ofList (t.params.map ValType.toC))
          (Ty.ofList (t.results.map ValType.toC)))) := by
  simp [toDefType, unrolldt, unrollrt, liftRec, toCoreRec, liftSub, liftComp,
    FuncType.toCore, liftResult_toCore, Ty.subst, subst_ofList_toC, Ty.subs, Ty.length]

/-- The retraction of `FuncType.toDefType`, read off the expansion. -/
def FuncType.ofDefType? (d : DefType) : Option FuncType :=
  match d.expand? with
  | some (.func ps rs) => do
      return ⟨← ps.toList.mapM ValType.ofC?, ← rs.toList.mapM ValType.ofC?⟩
  | _ => none

@[simp] theorem FuncType.ofDefType?_toDefType (t : FuncType) :
    ofDefType? t.toDefType = some t := by
  rcases t with ⟨ps, rs⟩
  simp [ofDefType?, toDefType_expand, List.mapM_map, Function.comp_def]

/-- The Core 3.0 defined type determines the 2.0 function type. -/
theorem FuncType.toDefType_injective : Function.Injective FuncType.toDefType :=
  injective_of_ofCore? FuncType.ofDefType?_toDefType

/-- On the 2.0 image, Core 3.0 defined-type subtyping is equality: 2.0 has no
subtyping between concrete types, and this is what the `call_indirect`
simulation needs. -/
theorem FuncType.toDefType_sub_iff (Δ : TypeCtx) (t₁ t₂ : FuncType) :
    Sub Δ t₁.toDefType t₂.toDefType ↔ t₁ = t₂ := by
  rw [Sub.def_iff_of_noSupers (by
    intro fin sups ct h
    rw [toDefType_unroll] at h
    simp only [Option.some.injEq, Ty.sub.injEq] at h
    exact h.2.1.symm)]
  simp only [Ty.clos, Ty.substAll_closed (toDefType_closed _)]
  exact toDefType_injective.eq_iff

/-! ## Semantic external types

`externtype` (`1-syntax:179`) carries a whole `functype` in its function case,
which Core 3.0's *source* `ExternType` cannot express without a type index. The
*closed* external types of `Silmaril.Wasm.Validation.DefTypes` can: their
function case carries a `DefType`. See the module documentation. -/

/-- `externtype ::= FUNC functype | GLOBAL globaltype | TABLE tabletype |
MEM memtype` (`1-syntax:179`) as a Core 3.0 closed external type. -/
def ExternType.toCore : ExternType → CExternType
  | .func t => .func t.toDefType
  | .global t => .global ⟨t.mutability, t.value.toC⟩
  | .table t => .table ⟨.i32, t.limits.toCore, t.element.toC⟩
  | .memory t => .mem t.toCore

/-- The retraction of `ExternType.toCore` (`1-syntax:179`); Core 3.0 tag types
are outside the 2.0 image. -/
def ExternType.ofCore? : CExternType → Option ExternType
  | .func d => (FuncType.ofDefType? d).map ExternType.func
  | .global g => (ValType.ofC? g.type).map fun v => .global ⟨g.mutability, v⟩
  | .table t =>
      if t.address = .i32 then do
        return .table ⟨← Limits.ofCore? t.limits, ← RefType.ofC? t.element⟩
      else none
  | .mem m => (MemoryType.ofCore? m).map ExternType.memory
  | .tag _ => none

@[simp] theorem ExternType.ofCore?_toCore (t : ExternType) : ofCore? t.toCore = some t := by
  cases t <;> simp [toCore, ofCore?]

theorem ExternType.toCore_injective : Function.Injective ExternType.toCore :=
  injective_of_ofCore? ExternType.ofCore?_toCore

end Silmaril.Wasm.V2
