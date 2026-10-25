module

public import Silmaril.Wasm.Validation.TypeOk

@[expose] public section

/-! # Typing family: references, i31, structures, arrays, extern (§2.3)

Spec rules (all 27 present):
* references: `Instr_ok/ref.null`, `ref.func`, `ref.i31`, `ref.is_null`,
  `ref.as_non_null`, `ref.eq`, `ref.test`, `ref.cast`;
* scalar references: `Instr_ok/i31.get`;
* structures: `Instr_ok/struct.new`, `struct.new_default`, `struct.get`,
  `struct.set`;
* arrays: `Instr_ok/array.new`, `array.new_default`, `array.new_fixed`,
  `array.new_elem`, `array.new_data`, `array.get`, `array.set`, `array.len`,
  `array.fill`, `array.copy`, `array.init_elem`, `array.init_data`;
* external references: `Instr_ok/extern.convert_any`, `any.convert_extern`.

`REF NULL? (_IDX x)` is closed to `refT _ (defHeap d)` with `C.type? x = some d`.
-/

namespace Silmaril.Wasm.Validation

/-- The unpacked operand type of a field type. -/
def fieldUnpack : CFieldType → CValType
  | .field _ z => z.unpack

inductive RefInstrOk (C : Context) : Instr → InstrType → Prop where
  /-- `Instr_ok/ref.null`. -/
  | refNull {ht : HeapType} (h : TyOk C.toTypeCtx (C.closeHeap ht)) :
      RefInstrOk C (.refNull ht) (.plain [] [.refT true (C.closeHeap ht)])
  /-- `Instr_ok/ref.func`: the function must be declared in `C.REFS`. -/
  | refFunc {x : FuncIdx} {d : DefType} (h : C.funcs[x.toNat]? = some d)
      (hr : x.toNat ∈ C.refs) :
      RefInstrOk C (.refFunc x) (.plain [] [.refT false (.defHeap d)])
  /-- `Instr_ok/ref.i31`. -/
  | refI31 : RefInstrOk C .refI31 (.plain [.i32] [.refT false (.abs .i31)])
  /-- `Instr_ok/ref.is_null`. -/
  | refIsNull {ht : CHeapType} (h : TyOk C.toTypeCtx ht) :
      RefInstrOk C .refIsNull (.plain [.refT true ht] [.i32])
  /-- `Instr_ok/ref.as_non_null`. -/
  | refAsNonNull {ht : CHeapType} (h : TyOk C.toTypeCtx ht) :
      RefInstrOk C .refAsNonNull (.plain [.refT true ht] [.refT false ht])
  /-- `Instr_ok/ref.eq`. -/
  | refEq : RefInstrOk C .refEq (.plain [.refT true (.abs .eq), .refT true (.abs .eq)] [.i32])
  /-- `Instr_ok/ref.test`. -/
  | refTest {rt : RefType} {rt' : CRefType} (h : TyOk C.toTypeCtx (C.closeRef rt))
      (h' : TyOk C.toTypeCtx rt') (hs : Sub C.toTypeCtx (C.closeRef rt) rt') :
      RefInstrOk C (.refTest rt) (.plain [.refv rt'] [.i32])
  /-- `Instr_ok/ref.cast`. -/
  | refCast {rt : RefType} {rt' : CRefType} (h : TyOk C.toTypeCtx (C.closeRef rt))
      (h' : TyOk C.toTypeCtx rt') (hs : Sub C.toTypeCtx (C.closeRef rt) rt') :
      RefInstrOk C (.refCast rt) (.plain [.refv rt'] [.refv (C.closeRef rt)])
  /-- `Instr_ok/i31.get`. -/
  | i31Get (sx : Signedness) :
      RefInstrOk C (.i31Get sx) (.plain [.refT true (.abs .i31)] [.i32])
  /-- `Instr_ok/struct.new`. -/
  | structNew {x : TypeIdx} {d : DefType} {fs : Ty (.list .field)}
      (hd : C.type? x = some d) (he : Expand d (.struct fs)) :
      RefInstrOk C (.structNew x) (.plain (fs.toList.map fieldUnpack) [.refT false (.defHeap d)])
  /-- `Instr_ok/struct.new_default`. -/
  | structNewDefault {x : TypeIdx} {d : DefType} {fs : Ty (.list .field)}
      (hd : C.type? x = some d) (he : Expand d (.struct fs))
      (hdef : ∀ f ∈ fs.toList, Defaultable (fieldUnpack f)) :
      RefInstrOk C (.structNewDefault x) (.plain [] [.refT false (.defHeap d)])
  /-- `Instr_ok/struct.get`: a sign extension is given exactly for packed fields. -/
  | structGet {sx : Option Signedness} {x : TypeIdx} {i : FieldIdx} {d : DefType}
      {fs : Ty (.list .field)} {m : Mutability} {z : CStorageType}
      (hd : C.type? x = some d) (he : Expand d (.struct fs))
      (hi : fs.toList[i.toNat]? = some (.field m z)) (hsx : sx.isSome = z.isPacked) :
      RefInstrOk C (.structGet sx x i) (.plain [.refT true (.defHeap d)] [z.unpack])
  /-- `Instr_ok/struct.set`: only mutable fields. -/
  | structSet {x : TypeIdx} {i : FieldIdx} {d : DefType} {fs : Ty (.list .field)}
      {z : CStorageType}
      (hd : C.type? x = some d) (he : Expand d (.struct fs))
      (hi : fs.toList[i.toNat]? = some (.field .var z)) :
      RefInstrOk C (.structSet x i) (.plain [.refT true (.defHeap d), z.unpack] [])
  /-- `Instr_ok/array.new`. -/
  | arrayNew {x : TypeIdx} {d : DefType} {m : Mutability} {z : CStorageType}
      (hd : C.type? x = some d) (he : Expand d (.array (.field m z))) :
      RefInstrOk C (.arrayNew x) (.plain [z.unpack, .i32] [.refT false (.defHeap d)])
  /-- `Instr_ok/array.new_default`. -/
  | arrayNewDefault {x : TypeIdx} {d : DefType} {m : Mutability} {z : CStorageType}
      (hd : C.type? x = some d) (he : Expand d (.array (.field m z)))
      (hdef : Defaultable z.unpack) :
      RefInstrOk C (.arrayNewDefault x) (.plain [.i32] [.refT false (.defHeap d)])
  /-- `Instr_ok/array.new_fixed`. -/
  | arrayNewFixed {x : TypeIdx} {n : Fin (2 ^ 32)} {d : DefType} {m : Mutability}
      {z : CStorageType}
      (hd : C.type? x = some d) (he : Expand d (.array (.field m z))) :
      RefInstrOk C (.arrayNewFixed x n)
        (.plain (List.replicate n.val z.unpack) [.refT false (.defHeap d)])
  /-- `Instr_ok/array.new_elem`: the element type is a reference type. -/
  | arrayNewElem {x : TypeIdx} {y : ElemIdx} {d : DefType} {m : Mutability}
      {rt rt' : CRefType}
      (hd : C.type? x = some d) (he : Expand d (.array (.field m (.val (.refv rt)))))
      (hy : C.elems[y.toNat]? = some rt') (hs : Sub C.toTypeCtx rt' rt) :
      RefInstrOk C (.arrayNewElem x y) (.plain [.i32, .i32] [.refT false (.defHeap d)])
  /-- `Instr_ok/array.new_data`: numeric or vector element storage. -/
  | arrayNewData {x : TypeIdx} {y : DataIdx} {d : DefType} {m : Mutability}
      {z : CStorageType}
      (hd : C.type? x = some d) (he : Expand d (.array (.field m z)))
      (hnv : z.unpack.IsNumOrVec) (hy : C.datas[y.toNat]? = some ()) :
      RefInstrOk C (.arrayNewData x y) (.plain [.i32, .i32] [.refT false (.defHeap d)])
  /-- `Instr_ok/array.get`. -/
  | arrayGet {sx : Option Signedness} {x : TypeIdx} {d : DefType} {m : Mutability}
      {z : CStorageType}
      (hd : C.type? x = some d) (he : Expand d (.array (.field m z)))
      (hsx : sx.isSome = z.isPacked) :
      RefInstrOk C (.arrayGet sx x) (.plain [.refT true (.defHeap d), .i32] [z.unpack])
  /-- `Instr_ok/array.set`. -/
  | arraySet {x : TypeIdx} {d : DefType} {z : CStorageType}
      (hd : C.type? x = some d) (he : Expand d (.array (.field .var z))) :
      RefInstrOk C (.arraySet x) (.plain [.refT true (.defHeap d), .i32, z.unpack] [])
  /-- `Instr_ok/array.len`. -/
  | arrayLen : RefInstrOk C .arrayLen (.plain [.refT true (.abs .array)] [.i32])
  /-- `Instr_ok/array.fill`. -/
  | arrayFill {x : TypeIdx} {d : DefType} {z : CStorageType}
      (hd : C.type? x = some d) (he : Expand d (.array (.field .var z))) :
      RefInstrOk C (.arrayFill x)
        (.plain [.refT true (.defHeap d), .i32, z.unpack, .i32] [])
  /-- `Instr_ok/array.copy`. -/
  | arrayCopy {x₁ x₂ : TypeIdx} {d₁ d₂ : DefType} {m₂ : Mutability} {z₁ z₂ : CStorageType}
      (hd₁ : C.type? x₁ = some d₁) (he₁ : Expand d₁ (.array (.field .var z₁)))
      (hd₂ : C.type? x₂ = some d₂) (he₂ : Expand d₂ (.array (.field m₂ z₂)))
      (hs : Sub C.toTypeCtx z₂ z₁) :
      RefInstrOk C (.arrayCopy x₁ x₂)
        (.plain [.refT true (.defHeap d₁), .i32, .refT true (.defHeap d₂), .i32, .i32] [])
  /-- `Instr_ok/array.init_elem`. -/
  | arrayInitElem {x : TypeIdx} {y : ElemIdx} {d : DefType} {z : CStorageType} {rt : CRefType}
      (hd : C.type? x = some d) (he : Expand d (.array (.field .var z)))
      (hy : C.elems[y.toNat]? = some rt) (hs : Sub C.toTypeCtx (.val (.refv rt)) z) :
      RefInstrOk C (.arrayInitElem x y)
        (.plain [.refT true (.defHeap d), .i32, .i32, .i32] [])
  /-- `Instr_ok/array.init_data`. -/
  | arrayInitData {x : TypeIdx} {y : DataIdx} {d : DefType} {z : CStorageType}
      (hd : C.type? x = some d) (he : Expand d (.array (.field .var z)))
      (hnv : z.unpack.IsNumOrVec) (hy : C.datas[y.toNat]? = some ()) :
      RefInstrOk C (.arrayInitData x y)
        (.plain [.refT true (.defHeap d), .i32, .i32, .i32] [])
  /-- `Instr_ok/extern.convert_any`. -/
  | externConvertAny (n : Bool) :
      RefInstrOk C .externConvertAny (.plain [.refT n (.abs .any)] [.refT n (.abs .extern)])
  /-- `Instr_ok/any.convert_extern`. -/
  | anyConvertExtern (n : Bool) :
      RefInstrOk C .anyConvertExtern (.plain [.refT n (.abs .extern)] [.refT n (.abs .any)])

end Silmaril.Wasm.Validation
