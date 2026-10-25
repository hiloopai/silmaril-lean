module

public import Silmaril.Wasm.V1.Modules
public import Silmaril.Wasm.Modules

/-!
# Type and immediate injections into Core 3

These maps preserve the source representation. Their partial inverses accept
only the canonical image, rather than identifying distinct modern encodings.
No typing or execution correspondence is asserted by a source injection.
-/

@[expose] public section

namespace Silmaril.Wasm.V1

@[simp] theorem mapM_some {α : Type*} (xs : List α) : xs.mapM some = some xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.mapM_cons, ih]; rfl

def widen32 (n : Fin (2 ^ 32)) : Fin (2 ^ 64) :=
  ⟨n.val, Nat.lt_of_lt_of_le n.isLt (by decide)⟩

def narrow32? (n : Fin (2 ^ 64)) : Option (Fin (2 ^ 32)) :=
  if h : n.val < 2 ^ 32 then some ⟨n.val, h⟩ else none

@[simp] theorem narrow32?_widen32 (n : Fin (2 ^ 32)) :
    narrow32? (widen32 n) = some n := by simp [narrow32?, widen32]

def ValType.toCore : ValType → Wasm.ValType := Wasm.ValType.num

def ValType.ofCore? : Wasm.ValType → Option ValType
  | .num t => some t
  | _ => none

@[simp] theorem ValType.ofCore?_toCore (t : ValType) : ofCore? (toCore t) = some t := rfl

def BlockType.toCore : BlockType → Wasm.BlockType
  | none => .empty
  | some t => .value (ValType.toCore t)

def BlockType.ofCore? : Wasm.BlockType → Option BlockType
  | .empty => some none
  | .value t => (ValType.ofCore? t).map some
  | .typeIdx _ => none

@[simp] theorem BlockType.ofCore?_toCore (t : BlockType) : ofCore? (toCore t) = some t := by
  cases t <;> rfl

def Limits.toCore (l : Limits) : Wasm.Limits :=
  ⟨widen32 l.min, l.max.map widen32⟩

def Limits.ofCore? (l : Wasm.Limits) : Option Limits := do
  let min ← narrow32? l.min
  let max ← match l.max with
    | none => some none
    | some n => (narrow32? n).map some
  return ⟨min, max⟩

@[simp] theorem Limits.ofCore?_toCore (l : Limits) : ofCore? l.toCore = some l := by
  rcases l with ⟨min, max⟩
  cases max <;> simp [toCore, ofCore?]

def FuncType.toCore (t : FuncType) : Wasm.FuncType :=
  ⟨t.params.map ValType.toCore, t.results.map ValType.toCore⟩

def FuncType.ofCore? (t : Wasm.FuncType) : Option FuncType := do
  return ⟨← t.params.mapM ValType.ofCore?, ← t.results.mapM ValType.ofCore?⟩

@[simp] theorem FuncType.ofCore?_toCore (t : FuncType) : ofCore? t.toCore = some t := by
  cases t
  simp [toCore, ofCore?, List.mapM_map, Function.comp_def]

/-- Each original function type occupies one final, parent-free recursive group. -/
def FuncType.toCoreRec (t : FuncType) : Wasm.RecType :=
  ⟨[⟨true, [], .func t.toCore⟩]⟩

def FuncType.ofCoreRec? : Wasm.RecType → Option FuncType
  | ⟨[⟨true, [], .func t⟩]⟩ => ofCore? t
  | _ => none

@[simp] theorem FuncType.ofCoreRec?_toCoreRec (t : FuncType) :
    ofCoreRec? t.toCoreRec = some t := by simp [toCoreRec, ofCoreRec?]

def funcref : RefType := ⟨true, .abstract .func⟩

def TableType.toCore (t : TableType) : Wasm.TableType :=
  ⟨.i32, t.limits.toCore, funcref⟩

def TableType.ofCore? (t : Wasm.TableType) : Option TableType := do
  if t.address = .i32 ∧ t.element = funcref then
    return ⟨← Limits.ofCore? t.limits⟩
  else none

@[simp] theorem TableType.ofCore?_toCore (t : TableType) : ofCore? t.toCore = some t := by
  cases t
  simp [toCore, ofCore?]

def MemoryType.toCore (t : MemoryType) : Wasm.MemoryType := ⟨.i32, t.limits.toCore⟩

def MemoryType.ofCore? (t : Wasm.MemoryType) : Option MemoryType := do
  if t.address = .i32 then return ⟨← Limits.ofCore? t.limits⟩ else none

@[simp] theorem MemoryType.ofCore?_toCore (t : MemoryType) : ofCore? t.toCore = some t := by
  cases t
  simp [toCore, ofCore?]

def GlobalType.toCore (t : GlobalType) : Wasm.GlobalType := ⟨t.mutability, t.value.toCore⟩

def GlobalType.ofCore? (t : Wasm.GlobalType) : Option GlobalType := do
  return ⟨t.mutability, ← ValType.ofCore? t.value⟩

@[simp] theorem GlobalType.ofCore?_toCore (t : GlobalType) : ofCore? t.toCore = some t := by
  cases t
  simp [toCore, ofCore?]

def IntUnOp.toCore : IntUnOp → Wasm.IntUnOp
  | .clz => .clz
  | .ctz => .ctz
  | .popcnt => .popcnt

def IntUnOp.ofCore? : Wasm.IntUnOp → Option IntUnOp
  | .clz => some .clz
  | .ctz => some .ctz
  | .popcnt => some .popcnt
  | .extend _ => none

@[simp] theorem IntUnOp.ofCore?_toCore (op : IntUnOp) : ofCore? op.toCore = some op := by
  cases op <;> rfl

def ConvertOp.toCore : ConvertOp → Wasm.ConvertOp
  | .wrap => .wrap
  | .extend s => .extend s
  | .trunc f i s => .trunc f i s
  | .convert i f s => .convert i f s
  | .demote => .demote
  | .promote => .promote
  | .reinterpretInt f => .reinterpretInt f
  | .reinterpretFloat i => .reinterpretFloat i

def ConvertOp.ofCore? : Wasm.ConvertOp → Option ConvertOp
  | .wrap => some .wrap
  | .extend s => some (.extend s)
  | .trunc f i s => some (.trunc f i s)
  | .convert i f s => some (.convert i f s)
  | .demote => some .demote
  | .promote => some .promote
  | .reinterpretInt f => some (.reinterpretInt f)
  | .reinterpretFloat i => some (.reinterpretFloat i)
  | .truncSat _ _ _ => none

@[simp] theorem ConvertOp.ofCore?_toCore (op : ConvertOp) : ofCore? op.toCore = some op := by
  cases op <;> rfl

def PackSize.toCore : PackSize → Wasm.PackSize
  | .i8 => .i8
  | .i16 => .i16
  | .i32 => .i32

def PackSize.ofCore? : Wasm.PackSize → Option PackSize
  | .i8 => some .i8
  | .i16 => some .i16
  | .i32 => some .i32
  | .i64 => none

@[simp] theorem PackSize.ofCore?_toCore (size : PackSize) : ofCore? size.toCore = some size := by
  cases size <;> rfl

def MemArg.toCore (a : MemArg) : Wasm.MemArg := ⟨a.align, widen32 a.offset⟩

def MemArg.ofCore? (a : Wasm.MemArg) : Option MemArg := do
  return ⟨a.align, ← narrow32? a.offset⟩

@[simp] theorem MemArg.ofCore?_toCore (a : MemArg) : ofCore? a.toCore = some a := by
  cases a
  simp [toCore, ofCore?]

def ImportDesc.toCore : ImportDesc → Wasm.ExternType
  | .func t => .func t
  | .table t => .table t.toCore
  | .memory t => .memory t.toCore
  | .global t => .global t.toCore

def ImportDesc.ofCore? : Wasm.ExternType → Option ImportDesc
  | .func t => some (.func t)
  | .table t => (TableType.ofCore? t).map .table
  | .memory t => (MemoryType.ofCore? t).map .memory
  | .global t => (GlobalType.ofCore? t).map .global
  | .tag _ => none

@[simp] theorem ImportDesc.ofCore?_toCore (d : ImportDesc) : ofCore? d.toCore = some d := by
  cases d <;> simp [toCore, ofCore?]

def Import.toCore (i : Import) : Wasm.Import := ⟨i.moduleName, i.name, i.desc.toCore⟩

def Import.ofCore? (i : Wasm.Import) : Option Import := do
  return ⟨i.moduleName, i.name, ← ImportDesc.ofCore? i.type⟩

@[simp] theorem Import.ofCore?_toCore (i : Import) : ofCore? i.toCore = some i := by
  cases i
  simp [toCore, ofCore?]

def ExternIdx.toCore : ExternIdx → Wasm.ExternIdx
  | .func i => .func i
  | .table i => .table i
  | .memory i => .memory i
  | .global i => .global i

def ExternIdx.ofCore? : Wasm.ExternIdx → Option ExternIdx
  | .func i => some (.func i)
  | .table i => some (.table i)
  | .memory i => some (.memory i)
  | .global i => some (.global i)
  | .tag _ => none

@[simp] theorem ExternIdx.ofCore?_toCore (i : ExternIdx) : ofCore? i.toCore = some i := by
  cases i <;> rfl

def Export.toCore (e : Export) : Wasm.Export := ⟨e.name, e.index.toCore⟩

def Export.ofCore? (e : Wasm.Export) : Option Export := do
  return ⟨e.name, ← ExternIdx.ofCore? e.index⟩

@[simp] theorem Export.ofCore?_toCore (e : Export) : ofCore? e.toCore = some e := by
  cases e
  simp [toCore, ofCore?]

end Silmaril.Wasm.V1
