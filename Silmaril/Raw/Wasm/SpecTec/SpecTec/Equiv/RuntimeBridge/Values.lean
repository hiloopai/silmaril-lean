module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.ExecVector
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.BinaryTypes
public import Silmaril.Wasm.Execution.Core.Runtime
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# The runtime bridge, layer 0: values

`ref`, `val`, `fieldval`, `externaddr` and bytes, as `Sem.Value`s.  These are
the leaves of the bridge `Equiv/RuntimeBridge/Instances.lean` builds; nothing
here depends on any other layer.

`Equiv/Execution.lean` already has `refV`; it is restated here so that this
file stands alone and so that the decoder and its two laws sit beside it.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv.RuntimeBridge

open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core

/-! ## Layer 0 — the leaves -/

/-- A reference, as an IL `ref` value.  This is `Equiv/Execution.lean`'s
`refV`, repeated here so that the file stands alone. -/
def refToValue : Ref → Value
  | .i31 b => .case "REF.I31_NUM" (percentV (.num (.natN b.toNat)))
  | .null => .case "REF.NULL_ADDR" (.tuple [])
  | .struct a => .case "REF.STRUCT_ADDR" (.num (.natN a))
  | .array a => .case "REF.ARRAY_ADDR" (.num (.natN a))
  | .func a => .case "REF.FUNC_ADDR" (.num (.natN a))
  | .exn a => .case "REF.EXN_ADDR" (.num (.natN a))
  | .host a => .case "REF.HOST_ADDR" (.num (.natN a))
  | .extern r => .case "REF.EXTERN" (refToValue r)

/-- A runtime value, as an IL `val`: a numeric constant, a vector constant or
a reference (`1.4-runtime.spectec`). -/
def valToValue : Val → Value
  | .num ⟨t, b⟩ => .case "CONST" (.tuple [Encode.toValue t,
      percentV (.num (.natN b.toNat))])
  | .vec b => .case "VCONST" (.tuple [.case "V128" (.tuple []),
      percentV (.num (.natN b.toNat))])
  | .ref r => refToValue r

/-- A field value: a `val`, or a packed one. -/
def fieldValToValue : FieldVal → Value
  | .val v => valToValue v
  | .pack p b => .case "PACK" (.tuple [Encode.toValue p,
      percentV (.num (.natN b.toNat))])

/-- An external address. -/
def externAddrToValue : ExternAddr → Value
  | .tag a => .case "TAG" (.num (.natN a))
  | .global a => .case "GLOBAL" (.num (.natN a))
  | .mem a => .case "MEM" (.num (.natN a))
  | .table a => .case "TABLE" (.num (.natN a))
  | .func a => .case "FUNC" (.num (.natN a))

/-- A byte array, as the IL's `byte*`: each byte is `%( n )`. -/
def bytesToValue (bs : ByteArray) : Value :=
  .list (bs.data.toList.map fun b => percentV (.num (.natN b.toNat)))

/-! ### Layer 0, the laws

Each is the `Encode` pair for the function above.  They are independent of one
another and of every later layer. -/

/-! #### Decoding a numeral back into a `BitVec`

`BitVec w` injects into `Nat` by `BitVec.toNat`, and the partial inverse is
`BitVec.ofNat` *guarded by the round trip* — the shape `Sem/Bridge.lean` uses
for `UInt8` (`uint8OfNat?`) and `Char` (`charOfNat?`), and for the same reason:
the guard is literally the equation the second law asks for, so no arithmetic
about `2 ^ w` ever enters a proof.

This is also what makes `Val.num`'s dependent pair `⟨t, b : BitVec t.width⟩`
decodable at all: the width is not guessed, it is *read off the already
decoded* `t`, and only then is the numeral narrowed to it.  A `CONST` whose
numeral does not fit the declared numeric type is simply not in the image of
`valToValue`, and the decoder rejects it. -/

/-- `BitVec.ofNat`, guarded by the round trip. -/
def bitVecOfNat? (w n : Nat) : Option (BitVec w) :=
  let b := BitVec.ofNat w n
  if b.toNat = n then some b else none

/-- **The characterisation of `bitVecOfNat?`**: it accepts exactly the
numerals in the image of `BitVec.toNat`, and returns the preimage.  Both laws
of the `BitVec` half of the bridge are this one `Iff`. -/
@[simp] theorem bitVecOfNat?_eq_some {w n : Nat} {b : BitVec w} :
    bitVecOfNat? w n = some b ↔ b.toNat = n := by
  constructor
  · intro h
    simp only [bitVecOfNat?] at h
    split at h
    · rename_i hb; cases h; exact hb
    · exact absurd h (by simp)
  · rintro rfl
    simp [bitVecOfNat?]

/-- `bitVecOfNat?` inverts `BitVec.toNat`. -/
@[simp] theorem bitVecOfNat?_toNat {w : Nat} (b : BitVec w) :
    bitVecOfNat? w b.toNat = some b := bitVecOfNat?_eq_some.mpr rfl

/-- `bitVecOfNat?` is defined only on the image of `BitVec.toNat`. -/
theorem toNat_of_bitVecOfNat? {w n : Nat} {b : BitVec w}
    (h : bitVecOfNat? w n = some b) : b.toNat = n := bitVecOfNat?_eq_some.mp h

/-! #### `ref`

The decoder dispatches on the *mixop first* and on the payload only
afterwards.  That ordering is deliberate: it makes
`refOfValue (.case op w) = none` hold by `rfl` for every `op` outside the eight,
which is what lets `valOfValue` and `fieldValOfValue` below be layered on top
of this decoder by a rewrite instead of a case analysis. -/

/-- Decoding a `ref`.  Recursive, because `REF.EXTERN` is. -/
def refOfValue : Value → Option Ref
  | .case op w =>
      match op with
      | "REF.I31_NUM" =>
          match w with
          | .case "%" (.tuple [.num (.natN n)]) => (bitVecOfNat? 31 n).map Ref.i31
          | _ => none
      | "REF.NULL_ADDR" =>
          match w with
          | .tuple [] => some .null
          | _ => none
      | "REF.STRUCT_ADDR" =>
          match w with
          | .num (.natN a) => some (.struct a)
          | _ => none
      | "REF.ARRAY_ADDR" =>
          match w with
          | .num (.natN a) => some (.array a)
          | _ => none
      | "REF.FUNC_ADDR" =>
          match w with
          | .num (.natN a) => some (.func a)
          | _ => none
      | "REF.EXN_ADDR" =>
          match w with
          | .num (.natN a) => some (.exn a)
          | _ => none
      | "REF.HOST_ADDR" =>
          match w with
          | .num (.natN a) => some (.host a)
          | _ => none
      | "REF.EXTERN" => (refOfValue w).map Ref.extern
      | _ => none
  | _ => none

/-- `refOfValue` inverts `refToValue`. -/
theorem refOfValue_toValue (r : Ref) : refOfValue (refToValue r) = some r := by
  induction r with
  | i31 b => simp [refToValue, refOfValue, percentV, caseV]
  | null => rfl
  | struct a => rfl
  | array a => rfl
  | func a => rfl
  | exn a => rfl
  | host a => rfl
  | extern r ih => simp [refToValue, refOfValue, ih]

/-- `refOfValue` is defined only on the image. -/
theorem refToValue_ofValue (v : Value) (r : Ref) : refOfValue v = some r → refToValue r = v := by
  induction v using refOfValue.induct generalizing r <;> intro h <;> simp_all [refOfValue]
  · obtain ⟨b, rfl, rfl⟩ := h; simp [refToValue, percentV, caseV]
  · cases h; rfl
  · cases h; rfl
  · cases h; rfl
  · cases h; rfl
  · cases h; rfl
  · cases h; rfl
  · rename_i w ih
    obtain ⟨r', hr', rfl⟩ := h
    simp [refToValue, ih r' hr']

/-- Nothing with a `CONST` mixop is a reference — by `rfl`, since the decoder
dispatches on the mixop first. -/
@[simp] theorem refOfValue_const (w : Value) : refOfValue (.case "CONST" w) = none := rfl

/-- Nothing with a `VCONST` mixop is a reference. -/
@[simp] theorem refOfValue_vconst (w : Value) : refOfValue (.case "VCONST" w) = none := rfl

/-- Nothing with a `PACK` mixop is a reference. -/
@[simp] theorem refOfValue_pack (w : Value) : refOfValue (.case "PACK" w) = none := rfl

/-! #### `val`

`val = CONST numtype num | VCONST vectype vec | ref`, and the third alternative
is an *inclusion*, not a wrapper: `valToValue (.ref r) = refToValue r`.  So the
decoder tries `refOfValue` first and only then the two constant forms, which is
sound because `refToValue`'s eight mixops are disjoint from `CONST` and
`VCONST` — the three `refOfValue_*` lemmas above. -/

/-- Decoding a `val`. -/
def valOfValue (v : Value) : Option Val :=
  match refOfValue v with
  | some r => some (.ref r)
  | none =>
      match v with
      | .case op w =>
          match op with
          | "CONST" =>
              match w with
              | .tuple [tv, .case "%" (.tuple [.num (.natN n)])] =>
                  match (Encode.ofValue tv : Option Wasm.NumType) with
                  | some t => (bitVecOfNat? t.width n).map fun b => Val.num ⟨t, b⟩
                  | none => none
              | _ => none
          | "VCONST" =>
              match w with
              | .tuple [.case "V128" (.tuple []), .case "%" (.tuple [.num (.natN n)])] =>
                  (bitVecOfNat? 128 n).map Val.vec
              | _ => none
          | _ => none
      | _ => none

/-- `valOfValue` on a reference, by the layering. -/
theorem valOfValue_ref (r : Ref) : valOfValue (refToValue r) = some (.ref r) := by
  unfold valOfValue
  rw [refOfValue_toValue]

/-- `valOfValue` on a `CONST`, unfolded. -/
theorem valOfValue_const (tv : Value) (n : Nat) :
    valOfValue (.case "CONST" (.tuple [tv, percentV (.num (.natN n))])) =
      (match (Encode.ofValue tv : Option Wasm.NumType) with
       | some t => (bitVecOfNat? t.width n).map fun b => Val.num ⟨t, b⟩
       | none => none) := rfl

/-- `valOfValue` on a `VCONST`, unfolded. -/
theorem valOfValue_vconst (n : Nat) :
    valOfValue (.case "VCONST" (.tuple [.case "V128" (.tuple []),
        percentV (.num (.natN n))])) = (bitVecOfNat? 128 n).map Val.vec := rfl

theorem valOfValue_toValue (v : Val) : valOfValue (valToValue v) = some v := by
  match v with
  | .ref r => exact valOfValue_ref r
  | .num ⟨t, b⟩ =>
      show valOfValue (.case "CONST" (.tuple [Encode.toValue t,
        percentV (.num (.natN b.toNat))])) = _
      rw [valOfValue_const, Encode.ofValue_toValue]
      simp
  | .vec b =>
      show valOfValue (.case "VCONST" (.tuple [.case "V128" (.tuple []),
        percentV (.num (.natN b.toNat))])) = _
      rw [valOfValue_vconst]
      simp

theorem valToValue_ofValue (w : Value) (v : Val) : valOfValue w = some v → valToValue v = w := by
  intro h
  unfold valOfValue at h
  split at h
  next r hr => cases h; exact refToValue_ofValue w r hr
  next hr =>
    split at h
    next op u =>
      split at h
      next =>
        split at h
        next tv n =>
          split at h
          next t ht =>
            obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
            simp only [valToValue, percentV, caseV, toNat_of_bitVecOfNat? hb,
              Encode.toValue_ofValue tv t ht]
          next => exact absurd h (by simp)
        next => exact absurd h (by simp)
      next =>
        split at h
        next n =>
          obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
          simp only [valToValue, percentV, caseV, toNat_of_bitVecOfNat? hb]
        next => exact absurd h (by simp)
      next => exact absurd h (by simp)
    next => exact absurd h (by simp)

/-- Nothing with a `PACK` mixop is a `val`. -/
@[simp] theorem valOfValue_pack (w : Value) : valOfValue (.case "PACK" w) = none := rfl

/-! #### `fieldval`

`fieldval = val | PACK packtype iN`, with the first alternative again an
inclusion, so the decoder is layered on `valOfValue` exactly as that one is
layered on `refOfValue`. -/

/-- Decoding a `fieldval`. -/
def fieldValOfValue (v : Value) : Option FieldVal :=
  match valOfValue v with
  | some x => some (.val x)
  | none =>
      match v with
      | .case op w =>
          match op with
          | "PACK" =>
              match w with
              | .tuple [pv, .case "%" (.tuple [.num (.natN n)])] =>
                  match (Encode.ofValue pv : Option Wasm.PackType) with
                  | some p => (bitVecOfNat? p.width n).map fun b => FieldVal.pack p b
                  | none => none
              | _ => none
          | _ => none
      | _ => none

/-- `fieldValOfValue` on a `val`, by the layering. -/
theorem fieldValOfValue_val (v : Val) : fieldValOfValue (valToValue v) = some (.val v) := by
  unfold fieldValOfValue
  rw [valOfValue_toValue]

/-- `fieldValOfValue` on a `PACK`, unfolded. -/
theorem fieldValOfValue_pack (pv : Value) (n : Nat) :
    fieldValOfValue (.case "PACK" (.tuple [pv, percentV (.num (.natN n))])) =
      (match (Encode.ofValue pv : Option Wasm.PackType) with
       | some p => (bitVecOfNat? p.width n).map fun b => FieldVal.pack p b
       | none => none) := rfl

theorem fieldValOfValue_toValue (f : FieldVal) : fieldValOfValue (fieldValToValue f) = some f := by
  match f with
  | .val v => exact fieldValOfValue_val v
  | .pack p b =>
      show fieldValOfValue (.case "PACK" (.tuple [Encode.toValue p,
        percentV (.num (.natN b.toNat))])) = _
      rw [fieldValOfValue_pack, Encode.ofValue_toValue]
      simp

theorem fieldValToValue_ofValue (w : Value) (f : FieldVal) :
    fieldValOfValue w = some f → fieldValToValue f = w := by
  intro h
  unfold fieldValOfValue at h
  split at h
  next x hx => cases h; exact valToValue_ofValue w x hx
  next hx =>
    split at h
    next op u =>
      split at h
      next =>
        split at h
        next pv n =>
          split at h
          next p hp =>
            obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
            simp only [fieldValToValue, percentV, caseV, toNat_of_bitVecOfNat? hb,
              Encode.toValue_ofValue pv p hp]
          next => exact absurd h (by simp)
        next => exact absurd h (by simp)
      next => exact absurd h (by simp)
    next => exact absurd h (by simp)

/-! #### `externaddr` -/

/-- Decoding an `externaddr`. -/
def externAddrOfValue : Value → Option ExternAddr
  | .case op w =>
      match op with
      | "TAG" => match w with | .num (.natN a) => some (.tag a) | _ => none
      | "GLOBAL" => match w with | .num (.natN a) => some (.global a) | _ => none
      | "MEM" => match w with | .num (.natN a) => some (.mem a) | _ => none
      | "TABLE" => match w with | .num (.natN a) => some (.table a) | _ => none
      | "FUNC" => match w with | .num (.natN a) => some (.func a) | _ => none
      | _ => none
  | _ => none

theorem externAddrOfValue_toValue (a : ExternAddr) :
    externAddrOfValue (externAddrToValue a) = some a := by
  cases a <;> rfl

theorem externAddrToValue_ofValue (w : Value) (a : ExternAddr) :
    externAddrOfValue w = some a → externAddrToValue a = w := by
  intro h
  unfold externAddrOfValue at h
  split at h
  · split at h <;> (try split at h) <;>
      first
        | (cases h; rfl)
        | exact absurd h (by simp)
  · exact absurd h (by simp)

/-! ### Layer 0, packaged

The four pairs above are exactly the two `Encode` laws, so each one is an
instance.  Packaging them is what lets `Sem/Bridge.lean`'s `instEncodeList`,
`instEncodeOption` and `instEncodeProd` reach `ref*`, `val?`, `fieldval*` and
`externaddr*` downstream with no further work; `Instances.lean` keeps using the
`*ToValue` names, and `toValue_ref` and friends below say the two agree. -/

/-- SpecTec's `ref` (`1.4-runtime.spectec`). -/
instance instEncodeRef : Encode Ref where
  toValue := refToValue
  ofValue := refOfValue
  ofValue_toValue := refOfValue_toValue
  toValue_ofValue := refToValue_ofValue

/-- SpecTec's `val` (`1.4-runtime.spectec`). -/
instance instEncodeVal : Encode Val where
  toValue := valToValue
  ofValue := valOfValue
  ofValue_toValue := valOfValue_toValue
  toValue_ofValue := valToValue_ofValue

/-- SpecTec's `fieldval` (`1.4-runtime.spectec`). -/
instance instEncodeFieldVal : Encode FieldVal where
  toValue := fieldValToValue
  ofValue := fieldValOfValue
  ofValue_toValue := fieldValOfValue_toValue
  toValue_ofValue := fieldValToValue_ofValue

/-- SpecTec's `externaddr` (`1.4-runtime.spectec`). -/
instance instEncodeExternAddr : Encode ExternAddr where
  toValue := externAddrToValue
  ofValue := externAddrOfValue
  ofValue_toValue := externAddrOfValue_toValue
  toValue_ofValue := externAddrToValue_ofValue

/-- `bytesToValue` needed no bespoke decoder: it *is* the generic `byte*`
encoding.  `Sem/Bridge.lean`'s `instEncodeUInt8` is `%(n)` and `instEncodeList`
is elementwise, so the two agree by `rfl`, and `instEncodeList`'s two laws are
the ones for `ByteArray` as well — modulo `ByteArray.toList`, which is the only
part of the correspondence that is not an `Encode`. -/
theorem bytesToValue_eq (bs : ByteArray) : bytesToValue bs = Encode.toValue bs.data.toList :=
  rfl

@[simp] theorem toValue_ref (r : Ref) : Encode.toValue r = refToValue r := rfl
@[simp] theorem toValue_val (v : Val) : Encode.toValue v = valToValue v := rfl
@[simp] theorem toValue_fieldVal (f : FieldVal) : Encode.toValue f = fieldValToValue f := rfl
@[simp] theorem toValue_externAddr (a : ExternAddr) :
    Encode.toValue a = externAddrToValue a := rfl

end Silmaril.SpecTec.Equiv.RuntimeBridge
