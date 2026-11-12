module

public import Silmaril.Proofs.Wasm.Logic.Instr.Vector

/-!
# Instruction rules: GC structures and arrays

Rules for the aggregate instructions of Core 3.0 not already in
`Silmaril.Proofs.Wasm.Logic.Hoare.Instr` (`struct.new`, `struct.get`, `struct.set`
are there, for `HWP`), in both readings (`Wp m`) and every profile:
`struct.new_default`, `array.new`, `array.new_default`, `array.new_fixed`,
`array.new_elem`, `array.new_data`, `array.get`, `array.set`, `array.len`, and
`array.fill`, `array.copy`, `array.init_elem`, `array.init_data` one step at a
time, each with its null and out-of-bounds traps.

A Silmaril addition; the step rules are silmaril-lean's
`Silmaril/Wasm/Execution/Core/Step/Aggregate.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Hoare

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded.Det (Head famOf)
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}
variable {m : Corr} {s : Store H} {f : Frame} {us : List Val} {rest : List Admin} {Q : Post H}
variable {x : TypeIdx} {d : DefType} {ft : CFieldType} {a : Nat} {ai : ArrayInst} {v : Val}

/-- `famOf` of a concrete instruction. -/
local macro "fam_ok" : term => `(by simp [famOf])

/-! ## Allocation -/

/-- **`struct.new_default`**: the default field values, then `struct.new`. -/
theorem Wp.structNewDefault {fs : Ty (.list .field)} {vs : List Val} (hd : f.type? x = some d)
    (he : Expand d (.struct fs))
    (hdef : fs.toList.mapM (fun ft => defaultVal? (fieldStorage ft).unpack) = some vs)
    (h : Wp m P host s f (vals (us ++ vs) ++ .plain (.structNew x) :: rest) Q) :
    Wp m P host s f (vals us ++ .plain (.structNewDefault x) :: rest) Q := by
  simpa using Wp.det (us := us) (args := []) (rest := rest) fam_ok (by trivial)
    (.aggregate (.structNewDefault hd he hdef)) (by simpa using h)

/-- **`array.new`**: `n` copies of the operand, then `array.new_fixed`. -/
theorem Wp.arrayNew {n : BitVec 32}
    (h : Wp m P host s f (vals (us ++ List.replicate n.toNat v) ++
      .plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩) :: rest) Q) :
    Wp m P host s f (vals (us ++ [v, .i32 n]) ++ .plain (.arrayNew x) :: rest) Q :=
  Wp.det fam_ok (by trivial) (.aggregate (.arrayNew (x := x) v n)) (by simpa using h)

/-- **`array.new_default`**: `n` default values, then `array.new_fixed`. -/
theorem Wp.arrayNewDefault {n : BitVec 32} (hd : f.type? x = some d) (he : Expand d (.array ft))
    (hv : defaultVal? (fieldStorage ft).unpack = some v)
    (h : Wp m P host s f (vals (us ++ List.replicate n.toNat v) ++
      .plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩) :: rest) Q) :
    Wp m P host s f (vals (us ++ [.i32 n]) ++ .plain (.arrayNewDefault x) :: rest) Q :=
  Wp.det fam_ok (by trivial) (.aggregate (.arrayNewDefault (n := n) hd he hv)) (by simpa using h)

/-- **`array.new_fixed`**: a fresh array at the end of the array heap. -/
theorem Wp.arrayNewFixed {n : Fin (2 ^ 32)} {vs : List Val} (hd : f.type? x = some d)
    (he : Expand d (.array ft)) (hn : vs.length = n.val)
    (hp : ∀ v ∈ vs, packable (fieldStorage ft) v)
    (h : Wp m P host (s.addArray ⟨d, vs.map (packField (fieldStorage ft))⟩) f
      (vals (us ++ [.ref (.array s.arrays.length)]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ vs) ++ .plain (.arrayNewFixed x n) :: rest) Q :=
  Wp.detVals (res := [.ref (.array s.arrays.length)]) fam_ok (by trivial)
    (.aggregate (.arrayNewFixed hd he hn hp)) h

variable {i n : BitVec 32}

/-- **`array.new_elem`** out of bounds: traps. -/
theorem Wp.arrayNewElem_oob {y : ElemIdx} {ea : Nat} {ei : ElemInst}
    (he : s.elem? f y = some (ea, ei)) (hb : ei.refs.length < i.toNat + n.toNat)
    (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.i32 i, .i32 n]) ++ .plain (.arrayNewElem x y) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.aggregate (.arrayNewElemOob (x := x) he hb)) hq

/-- **`array.new_elem`** in bounds: the element segment's references, then
`array.new_fixed`. -/
theorem Wp.arrayNewElem {y : ElemIdx} {ea : Nat} {ei : ElemInst}
    (he : s.elem? f y = some (ea, ei)) (hb : i.toNat + n.toNat ≤ ei.refs.length)
    (h : Wp m P host s f (vals (us ++ ((ei.refs.drop i.toNat).take n.toNat).map .ref) ++
      .plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩) :: rest) Q) :
    Wp m P host s f (vals (us ++ [.i32 i, .i32 n]) ++ .plain (.arrayNewElem x y) :: rest) Q :=
  Wp.det fam_ok (by trivial) (.aggregate (.arrayNewElemAlloc (x := x) he hb))
    (by simpa [vals, Function.comp_def] using h)

/-- **`array.new_data`** out of bounds: traps. -/
theorem Wp.arrayNewData_oob {y : DataIdx} {da : Nat} {di : DataInst} (hd : f.type? x = some d)
    (he : Expand d (.array ft)) (hdat : s.data? f y = some (da, di))
    (hz : 0 < storageSize (fieldStorage ft))
    (hb : di.bytes.size < i.toNat + n.toNat * storageSize (fieldStorage ft) / 8)
    (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.i32 i, .i32 n]) ++ .plain (.arrayNewData x y) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.aggregate (.arrayNewDataOob hd he hdat hz hb)) hq

/-- **`array.new_data`** in bounds: the values read from the data segment, then
`array.new_fixed`. -/
theorem Wp.arrayNewData {y : DataIdx} {da : Nat} {di : DataInst} {vs : List Val}
    (hd : f.type? x = some d) (he : Expand d (.array ft)) (hdat : s.data? f y = some (da, di))
    (hz : 0 < storageSize (fieldStorage ft))
    (hb : i.toNat + n.toNat * storageSize (fieldStorage ft) / 8 ≤ di.bytes.size)
    (hvs : (List.range n.toNat).mapM (fun k => readField? (fieldStorage ft) di.bytes
      (i.toNat + k * (storageSize (fieldStorage ft) / 8))) = some vs)
    (h : Wp m P host s f (vals (us ++ vs) ++ .plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩) :: rest) Q) :
    Wp m P host s f (vals (us ++ [.i32 i, .i32 n]) ++ .plain (.arrayNewData x y) :: rest) Q :=
  Wp.det fam_ok (by trivial) (.aggregate (.arrayNewDataNum hd he hdat hz hb hvs)) (by simpa using h)

/-! ## Access -/

/-- **`array.get`** on a null reference traps. -/
theorem Wp.arrayGet_null {sx : Option Signedness} (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.ref .null, .i32 i]) ++ .plain (.arrayGet sx x) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.aggregate .arrayGetNull) hq

/-- **`array.get`** out of bounds traps. -/
theorem Wp.arrayGet_oob {sx : Option Signedness} (ha : s.arrays[a]? = some ai)
    (hb : ai.fields.length ≤ i.toNat) (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.ref (.array a), .i32 i]) ++ .plain (.arrayGet sx x) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.aggregate (.arrayGetOob ha hb)) hq

/-- **`array.get`** in bounds: reads (and unpacks) the element. -/
theorem Wp.arrayGet {sx : Option Signedness} {fv : FieldVal} (ha : s.arrays[a]? = some ai)
    (hi : ai.fields[i.toNat]? = some fv) (hd : f.type? x = some d) (he : Expand d (.array ft))
    (hu : unpackable (fieldStorage ft) sx fv)
    (h : Wp m P host s f (vals (us ++ [unpackField sx fv]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref (.array a), .i32 i]) ++ .plain (.arrayGet sx x) :: rest) Q :=
  Wp.detVals (res := [unpackField sx fv]) fam_ok (by trivial)
    (.aggregate (.arrayGetArray ha hi hd he hu)) h

/-- **`array.set`** on a null reference traps. -/
theorem Wp.arraySet_null (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.ref .null, .i32 i, v]) ++ .plain (.arraySet x) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.aggregate .arraySetNull) hq

/-- **`array.set`** out of bounds traps. -/
theorem Wp.arraySet_oob (ha : s.arrays[a]? = some ai) (hb : ai.fields.length ≤ i.toNat)
    (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.ref (.array a), .i32 i, v]) ++ .plain (.arraySet x) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.aggregate (.arraySetOob ha hb)) hq

/-- **`array.set`** in bounds: writes the (packed) element. -/
theorem Wp.arraySet (ha : s.arrays[a]? = some ai) (hb : i.toNat < ai.fields.length)
    (hd : f.type? x = some d) (he : Expand d (.array ft)) (hp : packable (fieldStorage ft) v)
    (h : Wp m P host (s.setArrayField a i.toNat (packField (fieldStorage ft) v)) f
      (vals us ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref (.array a), .i32 i, v]) ++ .plain (.arraySet x) :: rest) Q :=
  Wp.detVals (res := []) fam_ok (by trivial) (.aggregate (.arraySetArray ha hb hd he hp))
    (by simpa using h)

/-- **`array.len`** on a null reference traps. -/
theorem Wp.arrayLen_null (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.ref .null]) ++ .plain .arrayLen :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.aggregate .arrayLenNull) hq

/-- **`array.len`.** -/
theorem Wp.arrayLen (ha : s.arrays[a]? = some ai)
    (h : Wp m P host s f (vals (us ++ [.i32 (BitVec.ofNat 32 ai.fields.length)]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref (.array a)]) ++ .plain .arrayLen :: rest) Q :=
  Wp.detVals (res := [.i32 (BitVec.ofNat 32 ai.fields.length)]) fam_ok (by trivial)
    (.aggregate (.arrayLenArray ha)) h

/-! ## Bulk array operations, one step at a time -/

/-- **`array.fill`** on a null reference traps. -/
theorem Wp.arrayFill_null (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.ref .null, .i32 i, v, .i32 n]) ++
      .plain (.arrayFill x) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.aggregate .arrayFillNull) hq

/-- **`array.fill`** out of bounds traps. -/
theorem Wp.arrayFill_oob (ha : s.arrays[a]? = some ai) (hb : ai.fields.length < i.toNat + n.toNat)
    (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.ref (.array a), .i32 i, v, .i32 n]) ++
      .plain (.arrayFill x) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.aggregate (.arrayFillOob ha hb)) hq

/-- **`array.fill`** of zero elements. -/
theorem Wp.arrayFill_zero (ha : s.arrays[a]? = some ai) (hb : i.toNat ≤ ai.fields.length)
    (h : Wp m P host s f (vals us ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref (.array a), .i32 i, v, .i32 0]) ++
      .plain (.arrayFill x) :: rest) Q :=
  Wp.detVals (res := []) fam_ok (by trivial) (.aggregate (.arrayFillZero ha hb)) (by simpa using h)

/-- **`array.fill`** of `n ≠ 0` elements: set one, fill the rest. -/
theorem Wp.arrayFill_succ (ha : s.arrays[a]? = some ai) (hb : i.toNat + n.toNat ≤ ai.fields.length)
    (hn : n ≠ 0)
    (h : Wp m P host s f (vals (us ++ [.ref (.array a), .i32 i, v]) ++ .plain (.arraySet x) ::
      (vals [.ref (.array a), .i32 (i + 1), v, .i32 (n - 1)] ++ .plain (.arrayFill x) :: rest)) Q) :
    Wp m P host s f (vals (us ++ [.ref (.array a), .i32 i, v, .i32 n]) ++
      .plain (.arrayFill x) :: rest) Q :=
  Wp.det fam_ok (by trivial) (.aggregate (.arrayFillSucc ha hb hn)) (by simpa using h)

section Copy

variable {x₁ x₂ : TypeIdx} {i₁ i₂ : BitVec 32} {a₁ a₂ : Nat} {ai₁ ai₂ : ArrayInst} {r : Ref}

/-- **`array.copy`** with a null destination traps. -/
theorem Wp.arrayCopy_null₁ (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.ref .null, .i32 i₁, .ref r, .i32 i₂, .i32 n]) ++
      .plain (.arrayCopy x₁ x₂) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.aggregate .arrayCopyNull₁) hq

/-- **`array.copy`** with a null source traps. -/
theorem Wp.arrayCopy_null₂ (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.ref r, .i32 i₁, .ref .null, .i32 i₂, .i32 n]) ++
      .plain (.arrayCopy x₁ x₂) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.aggregate .arrayCopyNull₂) hq

/-- **`array.copy`** out of bounds in the destination traps. -/
theorem Wp.arrayCopy_oob₁ (ha : s.arrays[a₁]? = some ai₁)
    (hb : ai₁.fields.length < i₁.toNat + n.toNat) (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.ref (.array a₁), .i32 i₁, .ref (.array a₂), .i32 i₂, .i32 n]) ++
      .plain (.arrayCopy x₁ x₂) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.aggregate (.arrayCopyOob₁ ha hb)) hq

/-- **`array.copy`** out of bounds in the source traps. -/
theorem Wp.arrayCopy_oob₂ (ha : s.arrays[a₂]? = some ai₂)
    (hb : ai₂.fields.length < i₂.toNat + n.toNat) (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.ref (.array a₁), .i32 i₁, .ref (.array a₂), .i32 i₂, .i32 n]) ++
      .plain (.arrayCopy x₁ x₂) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.aggregate (.arrayCopyOob₂ ha hb)) hq

/-- **`array.copy`** of zero elements. -/
theorem Wp.arrayCopy_zero (ha₁ : s.arrays[a₁]? = some ai₁) (ha₂ : s.arrays[a₂]? = some ai₂)
    (hb : i₁.toNat ≤ ai₁.fields.length ∧ i₂.toNat ≤ ai₂.fields.length)
    (h : Wp m P host s f (vals us ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref (.array a₁), .i32 i₁, .ref (.array a₂), .i32 i₂, .i32 0]) ++
      .plain (.arrayCopy x₁ x₂) :: rest) Q :=
  Wp.detVals (res := []) fam_ok (by trivial) (.aggregate (.arrayCopyZero ha₁ ha₂ hb))
    (by simpa using h)

/-- **`array.copy`** forwards: copy the first element, then the rest. -/
theorem Wp.arrayCopy_le {d₂ : DefType} {ft₂ : CFieldType} (ha₁ : s.arrays[a₁]? = some ai₁)
    (ha₂ : s.arrays[a₂]? = some ai₂)
    (hb : i₁.toNat + n.toNat ≤ ai₁.fields.length ∧ i₂.toNat + n.toNat ≤ ai₂.fields.length)
    (hn : n ≠ 0) (hd : f.type? x₂ = some d₂) (he : Expand d₂ (.array ft₂))
    (hle : i₁.toNat ≤ i₂.toNat)
    (h : Wp m P host s f (vals (us ++ [.ref (.array a₁), .i32 i₁, .ref (.array a₂), .i32 i₂]) ++
      .plain (.arrayGet (storageSx (fieldStorage ft₂)) x₂) :: .plain (.arraySet x₁) ::
      (vals [.ref (.array a₁), .i32 (i₁ + 1), .ref (.array a₂), .i32 (i₂ + 1), .i32 (n - 1)] ++
        .plain (.arrayCopy x₁ x₂) :: rest)) Q) :
    Wp m P host s f (vals (us ++ [.ref (.array a₁), .i32 i₁, .ref (.array a₂), .i32 i₂, .i32 n]) ++
      .plain (.arrayCopy x₁ x₂) :: rest) Q :=
  Wp.det fam_ok (by trivial) (.aggregate (.arrayCopyLe ha₁ ha₂ hb hn hd he hle)) (by simpa using h)

/-- **`array.copy`** backwards: copy the last element, then the rest. -/
theorem Wp.arrayCopy_gt {d₂ : DefType} {ft₂ : CFieldType} (ha₁ : s.arrays[a₁]? = some ai₁)
    (ha₂ : s.arrays[a₂]? = some ai₂)
    (hb : i₁.toNat + n.toNat ≤ ai₁.fields.length ∧ i₂.toNat + n.toNat ≤ ai₂.fields.length)
    (hn : n ≠ 0) (hd : f.type? x₂ = some d₂) (he : Expand d₂ (.array ft₂))
    (hgt : i₂.toNat < i₁.toNat)
    (h : Wp m P host s f (vals (us ++ [.ref (.array a₁), .i32 (i₁ + n - 1), .ref (.array a₂),
        .i32 (i₂ + n - 1)]) ++
      .plain (.arrayGet (storageSx (fieldStorage ft₂)) x₂) :: .plain (.arraySet x₁) ::
      (vals [.ref (.array a₁), .i32 i₁, .ref (.array a₂), .i32 i₂, .i32 (n - 1)] ++
        .plain (.arrayCopy x₁ x₂) :: rest)) Q) :
    Wp m P host s f (vals (us ++ [.ref (.array a₁), .i32 i₁, .ref (.array a₂), .i32 i₂, .i32 n]) ++
      .plain (.arrayCopy x₁ x₂) :: rest) Q :=
  Wp.det fam_ok (by trivial) (.aggregate (.arrayCopyGt ha₁ ha₂ hb hn hd he hgt)) (by simpa using h)

end Copy

section Init

variable {j : BitVec 32}

/-- **`array.init_elem`** on a null reference traps. -/
theorem Wp.arrayInitElem_null {y : ElemIdx} (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.ref .null, .i32 i, .i32 j, .i32 n]) ++
      .plain (.arrayInitElem x y) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.aggregate .arrayInitElemNull) hq

/-- **`array.init_elem`** out of bounds in the array traps. -/
theorem Wp.arrayInitElem_oob₁ {y : ElemIdx} (ha : s.arrays[a]? = some ai)
    (hb : ai.fields.length < i.toNat + n.toNat) (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.ref (.array a), .i32 i, .i32 j, .i32 n]) ++
      .plain (.arrayInitElem x y) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.aggregate (.arrayInitElemOob₁ ha hb)) hq

/-- **`array.init_elem`** out of bounds in the segment traps. -/
theorem Wp.arrayInitElem_oob₂ {y : ElemIdx} {ea : Nat} {ei : ElemInst}
    (he : s.elem? f y = some (ea, ei)) (hb : ei.refs.length < j.toNat + n.toNat)
    (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.ref (.array a), .i32 i, .i32 j, .i32 n]) ++
      .plain (.arrayInitElem x y) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.aggregate (.arrayInitElemOob₂ he hb)) hq

/-- **`array.init_elem`** of zero elements. -/
theorem Wp.arrayInitElem_zero {y : ElemIdx} {ea : Nat} {ei : ElemInst}
    (ha : s.arrays[a]? = some ai) (he : s.elem? f y = some (ea, ei))
    (hb : i.toNat ≤ ai.fields.length ∧ j.toNat ≤ ei.refs.length)
    (h : Wp m P host s f (vals us ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref (.array a), .i32 i, .i32 j, .i32 0]) ++
      .plain (.arrayInitElem x y) :: rest) Q :=
  Wp.detVals (res := []) fam_ok (by trivial) (.aggregate (.arrayInitElemZero ha he hb))
    (by simpa using h)

/-- **`array.init_elem`** of `n ≠ 0` elements: set the first, then the rest. -/
theorem Wp.arrayInitElem_succ {y : ElemIdx} {ea : Nat} {ei : ElemInst} {r : Ref}
    (ha : s.arrays[a]? = some ai) (he : s.elem? f y = some (ea, ei))
    (hb : i.toNat + n.toNat ≤ ai.fields.length ∧ j.toNat + n.toNat ≤ ei.refs.length)
    (hn : n ≠ 0) (hr : ei.refs[j.toNat]? = some r)
    (h : Wp m P host s f (vals (us ++ [.ref (.array a), .i32 i, .ref r]) ++ .plain (.arraySet x) ::
      (vals [.ref (.array a), .i32 (i + 1), .i32 (j + 1), .i32 (n - 1)] ++
        .plain (.arrayInitElem x y) :: rest)) Q) :
    Wp m P host s f (vals (us ++ [.ref (.array a), .i32 i, .i32 j, .i32 n]) ++
      .plain (.arrayInitElem x y) :: rest) Q :=
  Wp.det fam_ok (by trivial) (.aggregate (.arrayInitElemSucc ha he hb hn hr)) (by simpa using h)

/-- **`array.init_data`** on a null reference traps. -/
theorem Wp.arrayInitData_null {y : DataIdx} (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.ref .null, .i32 i, .i32 j, .i32 n]) ++
      .plain (.arrayInitData x y) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.aggregate .arrayInitDataNull) hq

/-- **`array.init_data`** out of bounds in the array traps. -/
theorem Wp.arrayInitData_oob₁ {y : DataIdx} (ha : s.arrays[a]? = some ai)
    (hb : ai.fields.length < i.toNat + n.toNat) (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.ref (.array a), .i32 i, .i32 j, .i32 n]) ++
      .plain (.arrayInitData x y) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.aggregate (.arrayInitDataOob₁ ha hb)) hq

/-- **`array.init_data`** out of bounds in the segment traps. -/
theorem Wp.arrayInitData_oob₂ {y : DataIdx} {da : Nat} {di : DataInst} (hd : f.type? x = some d)
    (he : Expand d (.array ft)) (hdat : s.data? f y = some (da, di))
    (hz : 0 < storageSize (fieldStorage ft))
    (hb : di.bytes.size < j.toNat + n.toNat * storageSize (fieldStorage ft) / 8) (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.ref (.array a), .i32 i, .i32 j, .i32 n]) ++
      .plain (.arrayInitData x y) :: rest) Q :=
  Wp.detTrap fam_ok (by trivial) (.aggregate (.arrayInitDataOob₂ hd he hdat hz hb)) hq

/-- **`array.init_data`** of zero elements. -/
theorem Wp.arrayInitData_zero {y : DataIdx} {da : Nat} {di : DataInst}
    (ha : s.arrays[a]? = some ai) (hdat : s.data? f y = some (da, di))
    (hb : i.toNat ≤ ai.fields.length ∧ j.toNat ≤ di.bytes.size)
    (h : Wp m P host s f (vals us ++ rest) Q) :
    Wp m P host s f (vals (us ++ [.ref (.array a), .i32 i, .i32 j, .i32 0]) ++
      .plain (.arrayInitData x y) :: rest) Q :=
  Wp.detVals (res := []) fam_ok (by trivial) (.aggregate (.arrayInitDataZero ha hdat hb))
    (by simpa using h)

/-- **`array.init_data`** of `n ≠ 0` elements: set the first, then the rest. -/
theorem Wp.arrayInitData_succ {y : DataIdx} {da : Nat} {di : DataInst}
    (ha : s.arrays[a]? = some ai) (hd : f.type? x = some d) (he : Expand d (.array ft))
    (hdat : s.data? f y = some (da, di))
    (hb : i.toNat + n.toNat ≤ ai.fields.length ∧
      j.toNat + n.toNat * storageSize (fieldStorage ft) / 8 ≤ di.bytes.size)
    (hn : n ≠ 0) (hv : readField? (fieldStorage ft) di.bytes j.toNat = some v)
    (h : Wp m P host s f (vals (us ++ [.ref (.array a), .i32 i, v]) ++ .plain (.arraySet x) ::
      (vals [.ref (.array a), .i32 (i + 1),
        .i32 (j + BitVec.ofNat 32 (storageSize (fieldStorage ft) / 8)), .i32 (n - 1)] ++
        .plain (.arrayInitData x y) :: rest)) Q) :
    Wp m P host s f (vals (us ++ [.ref (.array a), .i32 i, .i32 j, .i32 n]) ++
      .plain (.arrayInitData x y) :: rest) Q :=
  Wp.det fam_ok (by trivial) (.aggregate (.arrayInitDataNum ha hd he hdat hb hn hv))
    (by simpa using h)

end Init

end Silmaril.Wasm.Logic.Hoare
