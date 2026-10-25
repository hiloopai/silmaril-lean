module

public import Silmaril.Wasm.Execution.Core.Values

@[expose] public section

/-! # Reduction family: structures and arrays (GC)

Spec rules (all 42 present):
* structures: `Step/struct.new`, `Step_read/struct.new_default`,
  `struct.get-null/struct`, `Step/struct.set-null/struct`;
* arrays: `Step_pure/array.new`, `Step_read/array.new_default`,
  `Step/array.new_fixed`, `array.new_elem-oob/alloc`, `array.new_data-oob/num`,
  `array.get-null/oob/array`, `Step/array.set-null/oob/array`,
  `array.len-null/array`, `array.fill-null/oob/zero/succ`,
  `array.copy-null1/null2/oob1/oob2/zero/le/gt`,
  `array.init_elem-null/oob1/oob2/zero/succ`,
  `array.init_data-null/oob1/oob2/zero/num`.

The heap only grows (`Store.addStruct`/`addArray`); addresses are list positions.

Partial spec functions. `$packfield_`/`$unpackfield_` are total here (`packField`,
`unpackField`), so every rule that uses them carries the premise `packable` /
`unpackable` (their spec domain) together with the `Expand` premise that supplies `zt`;
`$zsize` has no reference clause, so the rules that use it carry
`0 < storageSize zt`; `$with_struct`/`$with_array` are partial updates, so the rules
that use them bound the address and field index. Where the spec is undefined, the
machine is stuck.

`$sx(zt)` (spec/3.1-numerics.scalar.spectec:61-63) has no clause for reference storage
types; `storageSx` returns eps for them (deviation in Silmaril.Wasm.Execution.Core.Instantiation), so
`array.copy-le/gt` step on reference arrays.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation

/-- The storage type of a field type. -/
def fieldStorage : CFieldType → CStorageType
  | .field _ z => z

/-- `$zsize(zt)` in bits. The spec function has no reference clause; the total function
returns `0` there, and every rule that uses it carries `0 < storageSize zt`. -/
def storageSize : CStorageType → Nat
  | .val (.num t) => t.width
  | .val (.vec _) => 128
  | .pack p => p.width
  | _ => 0

/-- `$sx(zt)`: packed fields are copied with a signed read; every other storage type
gives eps. The spec's `$sx` has no reftype clause (a spec gap: `array.copy` on a
reference array would be stuck); see the deviations in Silmaril.Wasm.Execution.Core.Instantiation. -/
def storageSx : CStorageType → Option Signedness
  | .pack _ => some .signed
  | _ => none

/-- `$const($cunpack(zt), $cunpacknum_(zt, c))` for bytes `$zbytes_(zt, c)` at `off`. -/
def readField? (zt : CStorageType) (bytes : ByteArray) (off : Nat) : Option Val :=
  match zt with
  | .pack p => (Memory.load bytes off (p.width / 8)).map fun c => .i32 (c.setWidth 32)
  | .val (.num t) => (Memory.load bytes off (t.width / 8)).map fun c => .num ⟨t, c.setWidth _⟩
  | .val (.vec _) => (Memory.load bytes off 16).map fun c => .vec c
  | _ => none

/-- `$zsize` is defined (nonzero) wherever a field can be read from bytes. -/
theorem storageSize_pos_of_readField {zt : CStorageType} {bytes : ByteArray} {off : Nat}
    {v : Val} (h : readField? zt bytes off = some v) : 0 < storageSize zt := by
  unfold readField? at h
  split at h
  · rename_i p; cases p <;> decide
  · rename_i t
    rcases t with it | ft
    · cases it <;> decide
    · cases ft <;> decide
  · simp [storageSize]
  · cases h

variable {H : Type}

/-- `REF.ARRAY_ADDR a`. -/
abbrev arrRef (a : Nat) : Admin := .ref (.array a)

inductive AggregateStep : Config H → Config H → Prop where
  /-- `Step/struct.new`. -/
  | structNew {s : Store H} {f : Frame} {x : TypeIdx} {d : DefType} {fs : Ty (.list .field)}
      {vs : List Val} (hd : f.type? x = some d) (he : Expand d (.struct fs))
      (hn : vs.length = fs.length)
      (hp : ∀ p ∈ fs.toList.zip vs, packable (fieldStorage p.1) p.2) :
      AggregateStep ⟨s, f, vals vs ++ [.plain (.structNew x)]⟩
        ⟨s.addStruct ⟨d, (fs.toList.zip vs).map fun (ft, v) => packField (fieldStorage ft) v⟩, f,
          [.ref (.struct s.structs.length)]⟩
  /-- `Step_read/struct.new_default`. -/
  | structNewDefault {s : Store H} {f : Frame} {x : TypeIdx} {d : DefType} {fs : Ty (.list .field)}
      {vs : List Val} (hd : f.type? x = some d) (he : Expand d (.struct fs))
      (hdef : fs.toList.mapM (fun ft => defaultVal? (fieldStorage ft).unpack) = some vs) :
      AggregateStep ⟨s, f, [.plain (.structNewDefault x)]⟩
        ⟨s, f, vals vs ++ [.plain (.structNew x)]⟩
  /-- `Step_read/struct.get-null`. -/
  | structGetNull {s : Store H} {f : Frame} {sx : Option Signedness} {x : TypeIdx} {i : FieldIdx} :
      AggregateStep ⟨s, f, [.ref .null, .plain (.structGet sx x i)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_read/struct.get-struct`. -/
  | structGetStruct {s : Store H} {f : Frame} {sx : Option Signedness} {x : TypeIdx} {i : FieldIdx}
      {a : Nat} {si : StructInst} {fv : FieldVal} {d : DefType} {fs : Ty (.list .field)}
      {ft : CFieldType}
      (hs : s.structs[a]? = some si) (hf : si.fields[i.toNat]? = some fv)
      (hd : f.type? x = some d) (he : Expand d (.struct fs)) (hi : fs.toList[i.toNat]? = some ft)
      (hu : unpackable (fieldStorage ft) sx fv) :
      AggregateStep ⟨s, f, [.ref (.struct a), .plain (.structGet sx x i)]⟩
        ⟨s, f, [(unpackField sx fv).toAdmin]⟩
  /-- `Step/struct.set-null`. -/
  | structSetNull {s : Store H} {f : Frame} {x : TypeIdx} {i : FieldIdx} {v : Val} :
      AggregateStep ⟨s, f, [.ref .null, v.toAdmin, .plain (.structSet x i)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step/struct.set-struct`. -/
  | structSetStruct {s : Store H} {f : Frame} {x : TypeIdx} {i : FieldIdx} {v : Val} {a : Nat}
      {d : DefType} {fs : Ty (.list .field)} {ft : CFieldType} {si : StructInst}
      (hd : f.type? x = some d) (he : Expand d (.struct fs)) (hi : fs.toList[i.toNat]? = some ft)
      (hs : s.structs[a]? = some si) (hf : i.toNat < si.fields.length)
      (hp : packable (fieldStorage ft) v) :
      AggregateStep ⟨s, f, [.ref (.struct a), v.toAdmin, .plain (.structSet x i)]⟩
        ⟨s.setStructField a i.toNat (packField (fieldStorage ft) v), f, []⟩
  /-- `Step_pure/array.new`. -/
  | arrayNew {s : Store H} {f : Frame} {x : TypeIdx} (v : Val) (n : BitVec 32) :
      AggregateStep ⟨s, f, [v.toAdmin, constI32 n, .plain (.arrayNew x)]⟩
        ⟨s, f, vals (List.replicate n.toNat v) ++ [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]⟩
  /-- `Step_read/array.new_default`. -/
  | arrayNewDefault {s : Store H} {f : Frame} {x : TypeIdx} {n : BitVec 32} {d : DefType}
      {ft : CFieldType} {v : Val} (hd : f.type? x = some d) (he : Expand d (.array ft))
      (hv : defaultVal? (fieldStorage ft).unpack = some v) :
      AggregateStep ⟨s, f, [constI32 n, .plain (.arrayNewDefault x)]⟩
        ⟨s, f, vals (List.replicate n.toNat v) ++ [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]⟩
  /-- `Step/array.new_fixed`. -/
  | arrayNewFixed {s : Store H} {f : Frame} {x : TypeIdx} {n : Fin (2 ^ 32)} {d : DefType}
      {ft : CFieldType} {vs : List Val} (hd : f.type? x = some d) (he : Expand d (.array ft))
      (hn : vs.length = n.val) (hp : ∀ v ∈ vs, packable (fieldStorage ft) v) :
      AggregateStep ⟨s, f, vals vs ++ [.plain (.arrayNewFixed x n)]⟩
        ⟨s.addArray ⟨d, vs.map (packField (fieldStorage ft))⟩, f, [arrRef s.arrays.length]⟩
  /-- `Step_read/array.new_elem-oob`. -/
  | arrayNewElemOob {s : Store H} {f : Frame} {x : TypeIdx} {y : ElemIdx} {i n : BitVec 32}
      {ea : Nat} {ei : ElemInst} (he : s.elem? f y = some (ea, ei))
      (h : ei.refs.length < i.toNat + n.toNat) :
      AggregateStep ⟨s, f, [constI32 i, constI32 n, .plain (.arrayNewElem x y)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_read/array.new_elem-alloc`. -/
  | arrayNewElemAlloc {s : Store H} {f : Frame} {x : TypeIdx} {y : ElemIdx} {i n : BitVec 32}
      {ea : Nat} {ei : ElemInst} (he : s.elem? f y = some (ea, ei))
      (h : i.toNat + n.toNat ≤ ei.refs.length) :
      AggregateStep ⟨s, f, [constI32 i, constI32 n, .plain (.arrayNewElem x y)]⟩
        ⟨s, f, ((ei.refs.drop i.toNat).take n.toNat).map .ref ++
          [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]⟩
  /-- `Step_read/array.new_data-oob`. -/
  | arrayNewDataOob {s : Store H} {f : Frame} {x : TypeIdx} {y : DataIdx} {i n : BitVec 32}
      {d : DefType} {ft : CFieldType} {da : Nat} {di : DataInst}
      (hd : f.type? x = some d) (he : Expand d (.array ft)) (hdat : s.data? f y = some (da, di))
      (hz : 0 < storageSize (fieldStorage ft))
      (h : di.bytes.size < i.toNat + n.toNat * storageSize (fieldStorage ft) / 8) :
      AggregateStep ⟨s, f, [constI32 i, constI32 n, .plain (.arrayNewData x y)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_read/array.new_data-num`. -/
  | arrayNewDataNum {s : Store H} {f : Frame} {x : TypeIdx} {y : DataIdx} {i n : BitVec 32}
      {d : DefType} {ft : CFieldType} {da : Nat} {di : DataInst} {vs : List Val}
      (hd : f.type? x = some d) (he : Expand d (.array ft)) (hdat : s.data? f y = some (da, di))
      (hz : 0 < storageSize (fieldStorage ft))
      (hb : i.toNat + n.toNat * storageSize (fieldStorage ft) / 8 ≤ di.bytes.size)
      (hvs : (List.range n.toNat).mapM (fun k =>
        readField? (fieldStorage ft) di.bytes (i.toNat + k * (storageSize (fieldStorage ft) / 8))) = some vs) :
      AggregateStep ⟨s, f, [constI32 i, constI32 n, .plain (.arrayNewData x y)]⟩
        ⟨s, f, vals vs ++ [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]⟩
  /-- `Step_read/array.get-null`. -/
  | arrayGetNull {s : Store H} {f : Frame} {sx : Option Signedness} {x : TypeIdx} {i : BitVec 32} :
      AggregateStep ⟨s, f, [.ref .null, constI32 i, .plain (.arrayGet sx x)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_read/array.get-oob`. -/
  | arrayGetOob {s : Store H} {f : Frame} {sx : Option Signedness} {x : TypeIdx} {i : BitVec 32}
      {a : Nat} {ai : ArrayInst} (ha : s.arrays[a]? = some ai) (h : ai.fields.length ≤ i.toNat) :
      AggregateStep ⟨s, f, [arrRef a, constI32 i, .plain (.arrayGet sx x)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_read/array.get-array`. -/
  | arrayGetArray {s : Store H} {f : Frame} {sx : Option Signedness} {x : TypeIdx} {i : BitVec 32}
      {a : Nat} {ai : ArrayInst} {fv : FieldVal} {d : DefType} {ft : CFieldType}
      (ha : s.arrays[a]? = some ai) (h : ai.fields[i.toNat]? = some fv)
      (hd : f.type? x = some d) (he : Expand d (.array ft))
      (hu : unpackable (fieldStorage ft) sx fv) :
      AggregateStep ⟨s, f, [arrRef a, constI32 i, .plain (.arrayGet sx x)]⟩
        ⟨s, f, [(unpackField sx fv).toAdmin]⟩
  /-- `Step/array.set-null`. -/
  | arraySetNull {s : Store H} {f : Frame} {x : TypeIdx} {i : BitVec 32} {v : Val} :
      AggregateStep ⟨s, f, [.ref .null, constI32 i, v.toAdmin, .plain (.arraySet x)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step/array.set-oob`. -/
  | arraySetOob {s : Store H} {f : Frame} {x : TypeIdx} {i : BitVec 32} {v : Val} {a : Nat}
      {ai : ArrayInst} (ha : s.arrays[a]? = some ai) (h : ai.fields.length ≤ i.toNat) :
      AggregateStep ⟨s, f, [arrRef a, constI32 i, v.toAdmin, .plain (.arraySet x)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step/array.set-array`. -/
  | arraySetArray {s : Store H} {f : Frame} {x : TypeIdx} {i : BitVec 32} {v : Val} {a : Nat}
      {ai : ArrayInst} {d : DefType} {ft : CFieldType} (ha : s.arrays[a]? = some ai)
      (h : i.toNat < ai.fields.length) (hd : f.type? x = some d) (he : Expand d (.array ft))
      (hp : packable (fieldStorage ft) v) :
      AggregateStep ⟨s, f, [arrRef a, constI32 i, v.toAdmin, .plain (.arraySet x)]⟩
        ⟨s.setArrayField a i.toNat (packField (fieldStorage ft) v), f, []⟩
  /-- `Step_read/array.len-null`. -/
  | arrayLenNull {s : Store H} {f : Frame} :
      AggregateStep ⟨s, f, [.ref .null, .plain .arrayLen]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_read/array.len-array`. -/
  | arrayLenArray {s : Store H} {f : Frame} {a : Nat} {ai : ArrayInst} (ha : s.arrays[a]? = some ai) :
      AggregateStep ⟨s, f, [arrRef a, .plain .arrayLen]⟩
        ⟨s, f, [constI32 (BitVec.ofNat 32 ai.fields.length)]⟩
  /-- `Step_read/array.fill-null`. -/
  | arrayFillNull {s : Store H} {f : Frame} {x : TypeIdx} {i n : BitVec 32} {v : Val} :
      AggregateStep ⟨s, f, [.ref .null, constI32 i, v.toAdmin, constI32 n, .plain (.arrayFill x)]⟩
        ⟨s, f, [.trap]⟩
  /-- `Step_read/array.fill-oob`. -/
  | arrayFillOob {s : Store H} {f : Frame} {x : TypeIdx} {i n : BitVec 32} {v : Val} {a : Nat}
      {ai : ArrayInst} (ha : s.arrays[a]? = some ai) (h : ai.fields.length < i.toNat + n.toNat) :
      AggregateStep ⟨s, f, [arrRef a, constI32 i, v.toAdmin, constI32 n, .plain (.arrayFill x)]⟩
        ⟨s, f, [.trap]⟩
  /-- `Step_read/array.fill-zero`. -/
  | arrayFillZero {s : Store H} {f : Frame} {x : TypeIdx} {i : BitVec 32} {v : Val} {a : Nat}
      {ai : ArrayInst} (ha : s.arrays[a]? = some ai) (h : i.toNat ≤ ai.fields.length) :
      AggregateStep ⟨s, f, [arrRef a, constI32 i, v.toAdmin, constI32 0, .plain (.arrayFill x)]⟩
        ⟨s, f, []⟩
  /-- `Step_read/array.fill-succ`. -/
  | arrayFillSucc {s : Store H} {f : Frame} {x : TypeIdx} {i n : BitVec 32} {v : Val} {a : Nat}
      {ai : ArrayInst} (ha : s.arrays[a]? = some ai) (h : i.toNat + n.toNat ≤ ai.fields.length)
      (hn : n ≠ 0) :
      AggregateStep ⟨s, f, [arrRef a, constI32 i, v.toAdmin, constI32 n, .plain (.arrayFill x)]⟩
        ⟨s, f, [arrRef a, constI32 i, v.toAdmin, .plain (.arraySet x),
          arrRef a, constI32 (i + 1), v.toAdmin, constI32 (n - 1), .plain (.arrayFill x)]⟩
  /-- `Step_read/array.copy-null1`. -/
  | arrayCopyNull₁ {s : Store H} {f : Frame} {x₁ x₂ : TypeIdx} {i₁ i₂ n : BitVec 32} {r : Ref} :
      AggregateStep ⟨s, f, [.ref .null, constI32 i₁, .ref r, constI32 i₂, constI32 n,
        .plain (.arrayCopy x₁ x₂)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_read/array.copy-null2`. -/
  | arrayCopyNull₂ {s : Store H} {f : Frame} {x₁ x₂ : TypeIdx} {i₁ i₂ n : BitVec 32} {r : Ref} :
      AggregateStep ⟨s, f, [.ref r, constI32 i₁, .ref .null, constI32 i₂, constI32 n,
        .plain (.arrayCopy x₁ x₂)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_read/array.copy-oob1`. -/
  | arrayCopyOob₁ {s : Store H} {f : Frame} {x₁ x₂ : TypeIdx} {i₁ i₂ n : BitVec 32} {a₁ a₂ : Nat}
      {ai₁ : ArrayInst} (ha : s.arrays[a₁]? = some ai₁) (h : ai₁.fields.length < i₁.toNat + n.toNat) :
      AggregateStep ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 n,
        .plain (.arrayCopy x₁ x₂)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_read/array.copy-oob2`. -/
  | arrayCopyOob₂ {s : Store H} {f : Frame} {x₁ x₂ : TypeIdx} {i₁ i₂ n : BitVec 32} {a₁ a₂ : Nat}
      {ai₂ : ArrayInst} (ha : s.arrays[a₂]? = some ai₂) (h : ai₂.fields.length < i₂.toNat + n.toNat) :
      AggregateStep ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 n,
        .plain (.arrayCopy x₁ x₂)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_read/array.copy-zero`. -/
  | arrayCopyZero {s : Store H} {f : Frame} {x₁ x₂ : TypeIdx} {i₁ i₂ : BitVec 32} {a₁ a₂ : Nat}
      {ai₁ ai₂ : ArrayInst} (ha₁ : s.arrays[a₁]? = some ai₁) (ha₂ : s.arrays[a₂]? = some ai₂)
      (h : i₁.toNat ≤ ai₁.fields.length ∧ i₂.toNat ≤ ai₂.fields.length) :
      AggregateStep ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 0,
        .plain (.arrayCopy x₁ x₂)]⟩ ⟨s, f, []⟩
  /-- `Step_read/array.copy-le`. -/
  | arrayCopyLe {s : Store H} {f : Frame} {x₁ x₂ : TypeIdx} {i₁ i₂ n : BitVec 32} {a₁ a₂ : Nat}
      {ai₁ ai₂ : ArrayInst} {d₂ : DefType} {ft₂ : CFieldType}
      (ha₁ : s.arrays[a₁]? = some ai₁) (ha₂ : s.arrays[a₂]? = some ai₂)
      (h : i₁.toNat + n.toNat ≤ ai₁.fields.length ∧ i₂.toNat + n.toNat ≤ ai₂.fields.length)
      (hn : n ≠ 0) (hd : f.type? x₂ = some d₂) (he : Expand d₂ (.array ft₂))
      (hle : i₁.toNat ≤ i₂.toNat) :
      AggregateStep ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 n,
        .plain (.arrayCopy x₁ x₂)]⟩
        ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂,
          .plain (.arrayGet (storageSx (fieldStorage ft₂)) x₂), .plain (.arraySet x₁),
          arrRef a₁, constI32 (i₁ + 1), arrRef a₂, constI32 (i₂ + 1), constI32 (n - 1),
          .plain (.arrayCopy x₁ x₂)]⟩
  /-- `Step_read/array.copy-gt`. -/
  | arrayCopyGt {s : Store H} {f : Frame} {x₁ x₂ : TypeIdx} {i₁ i₂ n : BitVec 32} {a₁ a₂ : Nat}
      {ai₁ ai₂ : ArrayInst} {d₂ : DefType} {ft₂ : CFieldType}
      (ha₁ : s.arrays[a₁]? = some ai₁) (ha₂ : s.arrays[a₂]? = some ai₂)
      (h : i₁.toNat + n.toNat ≤ ai₁.fields.length ∧ i₂.toNat + n.toNat ≤ ai₂.fields.length)
      (hn : n ≠ 0) (hd : f.type? x₂ = some d₂) (he : Expand d₂ (.array ft₂))
      (hgt : i₂.toNat < i₁.toNat) :
      AggregateStep ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 n,
        .plain (.arrayCopy x₁ x₂)]⟩
        ⟨s, f, [arrRef a₁, constI32 (i₁ + n - 1), arrRef a₂, constI32 (i₂ + n - 1),
          .plain (.arrayGet (storageSx (fieldStorage ft₂)) x₂), .plain (.arraySet x₁),
          arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 (n - 1),
          .plain (.arrayCopy x₁ x₂)]⟩
  /-- `Step_read/array.init_elem-null`. -/
  | arrayInitElemNull {s : Store H} {f : Frame} {x : TypeIdx} {y : ElemIdx} {i j n : BitVec 32} :
      AggregateStep ⟨s, f, [.ref .null, constI32 i, constI32 j, constI32 n,
        .plain (.arrayInitElem x y)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_read/array.init_elem-oob1`. -/
  | arrayInitElemOob₁ {s : Store H} {f : Frame} {x : TypeIdx} {y : ElemIdx} {i j n : BitVec 32}
      {a : Nat} {ai : ArrayInst} (ha : s.arrays[a]? = some ai)
      (h : ai.fields.length < i.toNat + n.toNat) :
      AggregateStep ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
        .plain (.arrayInitElem x y)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_read/array.init_elem-oob2`. -/
  | arrayInitElemOob₂ {s : Store H} {f : Frame} {x : TypeIdx} {y : ElemIdx} {i j n : BitVec 32}
      {a ea : Nat} {ei : ElemInst} (he : s.elem? f y = some (ea, ei))
      (h : ei.refs.length < j.toNat + n.toNat) :
      AggregateStep ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
        .plain (.arrayInitElem x y)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_read/array.init_elem-zero`. -/
  | arrayInitElemZero {s : Store H} {f : Frame} {x : TypeIdx} {y : ElemIdx} {i j : BitVec 32}
      {a ea : Nat} {ai : ArrayInst} {ei : ElemInst} (ha : s.arrays[a]? = some ai)
      (he : s.elem? f y = some (ea, ei))
      (h : i.toNat ≤ ai.fields.length ∧ j.toNat ≤ ei.refs.length) :
      AggregateStep ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 0,
        .plain (.arrayInitElem x y)]⟩ ⟨s, f, []⟩
  /-- `Step_read/array.init_elem-succ`. -/
  | arrayInitElemSucc {s : Store H} {f : Frame} {x : TypeIdx} {y : ElemIdx} {i j n : BitVec 32}
      {a ea : Nat} {ai : ArrayInst} {ei : ElemInst} {r : Ref} (ha : s.arrays[a]? = some ai)
      (he : s.elem? f y = some (ea, ei))
      (h : i.toNat + n.toNat ≤ ai.fields.length ∧ j.toNat + n.toNat ≤ ei.refs.length)
      (hn : n ≠ 0) (hr : ei.refs[j.toNat]? = some r) :
      AggregateStep ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
        .plain (.arrayInitElem x y)]⟩
        ⟨s, f, [arrRef a, constI32 i, .ref r, .plain (.arraySet x),
          arrRef a, constI32 (i + 1), constI32 (j + 1), constI32 (n - 1),
          .plain (.arrayInitElem x y)]⟩
  /-- `Step_read/array.init_data-null`. -/
  | arrayInitDataNull {s : Store H} {f : Frame} {x : TypeIdx} {y : DataIdx} {i j n : BitVec 32} :
      AggregateStep ⟨s, f, [.ref .null, constI32 i, constI32 j, constI32 n,
        .plain (.arrayInitData x y)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_read/array.init_data-oob1`. -/
  | arrayInitDataOob₁ {s : Store H} {f : Frame} {x : TypeIdx} {y : DataIdx} {i j n : BitVec 32}
      {a : Nat} {ai : ArrayInst} (ha : s.arrays[a]? = some ai)
      (h : ai.fields.length < i.toNat + n.toNat) :
      AggregateStep ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
        .plain (.arrayInitData x y)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_read/array.init_data-oob2`. -/
  | arrayInitDataOob₂ {s : Store H} {f : Frame} {x : TypeIdx} {y : DataIdx} {i j n : BitVec 32}
      {a da : Nat} {d : DefType} {ft : CFieldType} {di : DataInst}
      (hd : f.type? x = some d) (he : Expand d (.array ft)) (hdat : s.data? f y = some (da, di))
      (hz : 0 < storageSize (fieldStorage ft))
      (h : di.bytes.size < j.toNat + n.toNat * storageSize (fieldStorage ft) / 8) :
      AggregateStep ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
        .plain (.arrayInitData x y)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_read/array.init_data-zero`. -/
  | arrayInitDataZero {s : Store H} {f : Frame} {x : TypeIdx} {y : DataIdx} {i j : BitVec 32}
      {a da : Nat} {ai : ArrayInst} {di : DataInst} (ha : s.arrays[a]? = some ai)
      (hdat : s.data? f y = some (da, di))
      (h : i.toNat ≤ ai.fields.length ∧ j.toNat ≤ di.bytes.size) :
      AggregateStep ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 0,
        .plain (.arrayInitData x y)]⟩ ⟨s, f, []⟩
  /-- `Step_read/array.init_data-num`. -/
  | arrayInitDataNum {s : Store H} {f : Frame} {x : TypeIdx} {y : DataIdx} {i j n : BitVec 32}
      {a da : Nat} {ai : ArrayInst} {d : DefType} {ft : CFieldType} {di : DataInst} {v : Val}
      (ha : s.arrays[a]? = some ai) (hd : f.type? x = some d) (he : Expand d (.array ft))
      (hdat : s.data? f y = some (da, di))
      (h : i.toNat + n.toNat ≤ ai.fields.length ∧
        j.toNat + n.toNat * storageSize (fieldStorage ft) / 8 ≤ di.bytes.size)
      (hn : n ≠ 0) (hv : readField? (fieldStorage ft) di.bytes j.toNat = some v) :
      AggregateStep ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
        .plain (.arrayInitData x y)]⟩
        ⟨s, f, [arrRef a, constI32 i, v.toAdmin, .plain (.arraySet x),
          arrRef a, constI32 (i + 1), constI32 (j + BitVec.ofNat 32 (storageSize (fieldStorage ft) / 8)),
          constI32 (n - 1), .plain (.arrayInitData x y)]⟩

end Silmaril.Wasm.Execution.Core
