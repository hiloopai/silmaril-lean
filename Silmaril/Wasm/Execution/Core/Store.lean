module

public import Silmaril.Wasm.Execution.Core.Runtime

@[expose] public section

/-! # State access, update, growth and type instantiation (§4.0, §4.2)

Transcribes the state accessors (`$type`, `$tag`, `$global`, `$mem`, `$table`,
`$func`, `$data`, `$elem`, `$local`), updaters (`$with_*`, `$add_*`), growth
(`$growtable`, `$growmem`, memory64/table64 aware), field packing
(`$packfield_`, `$unpackfield_`) and type instantiation (`$inst_*`).

Accessors are `Option`-valued: an out-of-range index makes the rule's premise
false, so the machine is *stuck* (not trapped) on invalid indices, as in the V1
and Lime1 machines. Soundness (`Soundness.lean`) shows valid configurations never
reach that situation.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation

variable {H : Type}

/-! ## Accessors (relative to the current frame) -/

/-- `$type(z, x)`. -/
def Frame.type? (f : Frame) (x : TypeIdx) : Option DefType := f.module.types[x.toNat]?

/-- `$local(z, x)`. -/
def Frame.local? (f : Frame) (x : LocalIdx) : Option (Option Val) := f.locals[x.toNat]?

/-- `$with_local(z, x, v)`. -/
def Frame.setLocal (f : Frame) (x : LocalIdx) (v : Val) : Frame :=
  { f with locals := f.locals.set x.toNat (some v) }

def Store.funcAt? (s : Store H) (a : Nat) : Option (FuncInst H) := s.funcs[a]?

/-- `$func(z, x)` with its address. -/
def Store.func? (s : Store H) (f : Frame) (x : FuncIdx) : Option (Nat × FuncInst H) := do
  let a ← f.module.funcs[x.toNat]?
  return (a, ← s.funcs[a]?)

/-- `$tag(z, x)` with its address. -/
def Store.tag? (s : Store H) (f : Frame) (x : TagIdx) : Option (Nat × TagInst) := do
  let a ← f.module.tags[x.toNat]?
  return (a, ← s.tags[a]?)

/-- `$global(z, x)` with its address. -/
def Store.global? (s : Store H) (f : Frame) (x : GlobalIdx) : Option (Nat × GlobalInst) := do
  let a ← f.module.globals[x.toNat]?
  return (a, ← s.globals[a]?)

/-- `$mem(z, x)` with its address. -/
def Store.mem? (s : Store H) (f : Frame) (x : MemIdx) : Option (Nat × MemInst) := do
  let a ← f.module.mems[x.toNat]?
  return (a, ← s.mems[a]?)

/-- `$table(z, x)` with its address. -/
def Store.table? (s : Store H) (f : Frame) (x : TableIdx) : Option (Nat × TableInst) := do
  let a ← f.module.tables[x.toNat]?
  return (a, ← s.tables[a]?)

/-- `$data(z, x)` with its address. -/
def Store.data? (s : Store H) (f : Frame) (x : DataIdx) : Option (Nat × DataInst) := do
  let a ← f.module.datas[x.toNat]?
  return (a, ← s.datas[a]?)

/-- `$elem(z, x)` with its address. -/
def Store.elem? (s : Store H) (f : Frame) (x : ElemIdx) : Option (Nat × ElemInst) := do
  let a ← f.module.elems[x.toNat]?
  return (a, ← s.elems[a]?)

/-! ## Updates -/

def Store.setGlobal (s : Store H) (a : Nat) (v : Val) : Store H :=
  { s with globals := s.globals.modify a fun g => { g with value := v } }

def Store.setTable (s : Store H) (a : Nat) (ti : TableInst) : Store H :=
  { s with tables := s.tables.set a ti }

def Store.setMem (s : Store H) (a : Nat) (mi : MemInst) : Store H :=
  { s with mems := s.mems.set a mi }

def Store.setElem (s : Store H) (a : Nat) (refs : List Ref) : Store H :=
  { s with elems := s.elems.modify a fun e => { e with refs := refs } }

def Store.setData (s : Store H) (a : Nat) (bytes : ByteArray) : Store H :=
  { s with datas := s.datas.modify a fun _ => ⟨bytes⟩ }

/-- `$with_struct(z, a, i, fv)`. -/
def Store.setStructField (s : Store H) (a i : Nat) (fv : FieldVal) : Store H :=
  { s with structs := s.structs.modify a fun si => { si with fields := si.fields.set i fv } }

/-- `$with_array(z, a, i, fv)`. -/
def Store.setArrayField (s : Store H) (a i : Nat) (fv : FieldVal) : Store H :=
  { s with arrays := s.arrays.modify a fun ai => { ai with fields := ai.fields.set i fv } }

def Store.addStruct (s : Store H) (si : StructInst) : Store H := { s with structs := s.structs ++ [si] }
def Store.addArray (s : Store H) (ai : ArrayInst) : Store H := { s with arrays := s.arrays ++ [ai] }
def Store.addExn (s : Store H) (e : ExnInst) : Store H := { s with exns := s.exns ++ [e] }

/-! ## Growth (`$growtable`, `$growmem`) -/

/-- `$growtable(ti, n, r)`: the new minimum is the new size; it must stay within the
maximum (if any) and `2^|at| - 1`. -/
def TableInst.grow? (ti : TableInst) (n : Nat) (r : Ref) : Option TableInst :=
  let i' := ti.refs.length + n
  if i' ≤ 2 ^ ti.type.address.width - 1 ∧ (∀ j, ti.type.limits.max = some j → i' ≤ j.val) then
    some ⟨{ ti.type with limits := { ti.type.limits with min := Fin.ofNat _ i' } },
      ti.refs ++ List.replicate n r⟩
  else none

/-- `$growmem(mi, n)` in pages of 64 KiB, bounded by `2^(|at| - 16)`. -/
def MemInst.grow? (mi : MemInst) (n : Nat) : Option MemInst :=
  let i' := mi.bytes.size / Memory.pageSize + n
  if i' ≤ 2 ^ (mi.type.address.width - 16) ∧ (∀ j, mi.type.limits.max = some j → i' ≤ j.val) then
    some ⟨{ mi.type with limits := { mi.type.limits with min := Fin.ofNat _ i' } },
      mi.bytes ++ ByteArray.mk (Array.replicate (n * Memory.pageSize) 0)⟩
  else none

/-- The size of a memory in pages. -/
def MemInst.pages (mi : MemInst) : Nat := mi.bytes.size / Memory.pageSize

/-! ## Packed fields -/

/-- `$packfield_(zt, v)` on its domain `packable zt v`. Outside that domain (a packed
storage type given a non-`i32` value) the spec function is undefined; the total
function returns `.val v` there, but every reduction rule that packs carries the
premise `packable zt v`, so the machine is stuck exactly where the spec is. -/
def packField : CStorageType → Val → FieldVal
  | .pack p, .num ⟨.int .i32, b⟩ => .pack p (b.setWidth p.width)
  | _, v => .val v

/-- The domain of `$packfield_(zt, val)` (spec/4.0-execution.configurations.spectec:180-182):
any value for an unpacked storage type, an `i32` for a packed one. -/
def packable : CStorageType → Val → Bool
  | .pack _, .num ⟨.int .i32, _⟩ => true
  | .pack _, _ => false
  | .val _, _ => true

/-- `$unpackfield_(zt, sx?, fv)` on its domain `unpackable zt sx? fv`. The storage type
only restricts the domain, so it is not an argument; the reduction rules that unpack
carry the premise `unpackable zt sx? fv`. -/
def unpackField : Option Signedness → FieldVal → Val
  | _, .val v => v
  | some .signed, .pack _ b => .i32 (b.signExtend 32)
  | _, .pack _ b => .i32 (b.setWidth 32)

/-- The domain of `$unpackfield_(zt, sx?, fv)` (spec/4.0-execution.configurations.spectec:184-185):
`(valtype, eps, val)` or `(packtype, sx, PACK packtype i)` with matching packed types. -/
def unpackable : CStorageType → Option Signedness → FieldVal → Bool
  | .val _, none, .val _ => true
  | .pack p, some _, .pack p' _ => decide (p = p')
  | _, _, _ => false

/-! ## Type instantiation (§4.2 `$inst_*`) -/

def ModuleInst.instVal (m : ModuleInst) (t : ValType) : CValType :=
  (liftVal t).substAll (m.types.map .dt)

def ModuleInst.instRef (m : ModuleInst) (r : RefType) : CRefType :=
  (liftRef r).substAll (m.types.map .dt)

def ModuleInst.instHeap (m : ModuleInst) (h : HeapType) : CHeapType :=
  (liftHeap h).substAll (m.types.map .dt)

/-- `$blocktype_(z, bt)`. -/
def ModuleInst.blockType? (m : ModuleInst) : BlockType → Option (List CValType × List CValType)
  | .empty => some ([], [])
  | .value t => some ([], [m.instVal t])
  | .typeIdx x => m.types[x.toNat]? >>= DefType.funcType?

end Silmaril.Wasm.Execution.Core
