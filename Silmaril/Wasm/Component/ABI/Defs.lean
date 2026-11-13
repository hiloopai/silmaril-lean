module

public import Silmaril.Wasm.Execution.Runtime

/-!
# Component value types and a flat canonical ABI

This module fixes the value layer of the component IR (`Silmaril.Wasm.Component`):

* `ValTy`: component value types — `bool`, the eight integer types `s8`…`u64`,
  `f32`, `f64`, `char`, `record` (also used for tuples) and `variant` (with
  `enum`, `option` and `result` as derived forms).
* `Val`: untyped component values, with the typing check `ValTy.check`.
* `ValTy.flat`: the flattening of a type to core value types, as in the
  canonical ABI (`flatten_type`), including the joined payload slots of
  variants (`joinType`, `joinFlat`).
* `ValTy.lower : ValTy → Val → List Flat` and
  `ValTy.lift : ValTy → List Flat → Option (Val × List Flat)` (`lower_flat`,
  `lift_flat`): lifting consumes a prefix of the flat values and returns the
  rest; `none` is a trap.

The flat values `Flat` are silmaril's runtime numeric values
(`Silmaril.Wasm.Execution.Runtime.Value`, the `FlatValue` of
`Silmaril.Wasm.Component.Engine`).

## Coverage (what is and is not modelled)

Only the *flat* (memory-free) part of the canonical ABI is modelled: there is
no linear memory, so `string`, `list`, `flags`, resources, futures/streams and
the spilling of more than `MAX_FLAT_PARAMS`/`MAX_FLAT_RESULTS` values to
memory are omitted. Floats are carried as bit patterns; the NaN
canonicalisation of the canonical ABI is not modelled. Integer lifting keeps
the low bits (as in the canonical ABI), `bool` lifts every nonzero `i32` to
`true`, `char` lifting traps on surrogates and values above `0x10FFFF`, and
variant lifting traps on an out-of-range discriminant. Variant payloads use
the canonical ABI's bit-preserving join of core types; coercions between a
case's flat types and the joined slots are `retype` (zero-extension or
truncation of the bit pattern), which is exactly the canonical ABI's
`CoerceValueIter` on bit patterns.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open Silmaril.Wasm (NumType IntType FloatType)

/-- Flat core values at the canonical-ABI boundary (`i32`/`i64`/`f32`/`f64`). -/
abbrev Flat := Silmaril.Wasm.Execution.Runtime.Value

/-- Component value types (the memory-free subset of WIT value types). -/
inductive ValTy where
  | bool
  | s8 | u8 | s16 | u16 | s32 | u32 | s64 | u64
  | f32 | f64
  | char
  /-- A record (or tuple): the field names do not matter for the ABI. -/
  | record (fields : List ValTy)
  /-- A variant: each case has an optional payload type. -/
  | variant (cases : List (Option ValTy))
  deriving Repr, Inhabited, BEq

namespace ValTy

/-- `tuple ts` is a record. -/
abbrev tuple (ts : List ValTy) : ValTy := .record ts
/-- An enumeration with `n` cases. -/
abbrev enum (n : Nat) : ValTy := .variant (List.replicate n none)
/-- `option t`: cases `none` and `some t`. -/
abbrev option (t : ValTy) : ValTy := .variant [none, some t]
/-- `result t e`: cases `ok t` and `error e`. -/
abbrev result (t e : Option ValTy) : ValTy := .variant [t, e]

end ValTy

/-- Component values. Signed integers are stored as two's-complement bit
patterns, floats as their bit patterns. -/
inductive Val where
  | bool (b : Bool)
  | s8 (x : BitVec 8) | u8 (x : BitVec 8)
  | s16 (x : BitVec 16) | u16 (x : BitVec 16)
  | s32 (x : BitVec 32) | u32 (x : BitVec 32)
  | s64 (x : BitVec 64) | u64 (x : BitVec 64)
  | f32 (bits : BitVec 32) | f64 (bits : BitVec 64)
  | char (c : Char)
  | record (fields : List Val)
  /-- Case number `case`, with its payload. -/
  | variant (case : Nat) (payload : Option Val)
  deriving Repr, Inhabited, BEq

/-! ## Decidable equality of types -/

mutual
/-- Decidable equality of value types (written by hand: the type is nested). -/
def ValTy.decEq : (a b : ValTy) → Decidable (a = b)
  | .bool, .bool => isTrue rfl
  | .s8, .s8 => isTrue rfl
  | .u8, .u8 => isTrue rfl
  | .s16, .s16 => isTrue rfl
  | .u16, .u16 => isTrue rfl
  | .s32, .s32 => isTrue rfl
  | .u32, .u32 => isTrue rfl
  | .s64, .s64 => isTrue rfl
  | .u64, .u64 => isTrue rfl
  | .f32, .f32 => isTrue rfl
  | .f64, .f64 => isTrue rfl
  | .char, .char => isTrue rfl
  | .record xs, .record ys =>
    match ValTy.decEqList xs ys with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse fun e => h (by cases e; rfl)
  | .variant xs, .variant ys =>
    match ValTy.decEqCases xs ys with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse fun e => h (by cases e; rfl)
  | .bool, .s8 | .bool, .u8 | .bool, .s16 | .bool, .u16 | .bool, .s32 | .bool, .u32
  | .bool, .s64 | .bool, .u64 | .bool, .f32 | .bool, .f64 | .bool, .char
  | .bool, .record _ | .bool, .variant _
  | .s8, .bool | .s8, .u8 | .s8, .s16 | .s8, .u16 | .s8, .s32 | .s8, .u32
  | .s8, .s64 | .s8, .u64 | .s8, .f32 | .s8, .f64 | .s8, .char
  | .s8, .record _ | .s8, .variant _
  | .u8, .bool | .u8, .s8 | .u8, .s16 | .u8, .u16 | .u8, .s32 | .u8, .u32
  | .u8, .s64 | .u8, .u64 | .u8, .f32 | .u8, .f64 | .u8, .char
  | .u8, .record _ | .u8, .variant _
  | .s16, .bool | .s16, .s8 | .s16, .u8 | .s16, .u16 | .s16, .s32 | .s16, .u32
  | .s16, .s64 | .s16, .u64 | .s16, .f32 | .s16, .f64 | .s16, .char
  | .s16, .record _ | .s16, .variant _
  | .u16, .bool | .u16, .s8 | .u16, .u8 | .u16, .s16 | .u16, .s32 | .u16, .u32
  | .u16, .s64 | .u16, .u64 | .u16, .f32 | .u16, .f64 | .u16, .char
  | .u16, .record _ | .u16, .variant _
  | .s32, .bool | .s32, .s8 | .s32, .u8 | .s32, .s16 | .s32, .u16 | .s32, .u32
  | .s32, .s64 | .s32, .u64 | .s32, .f32 | .s32, .f64 | .s32, .char
  | .s32, .record _ | .s32, .variant _
  | .u32, .bool | .u32, .s8 | .u32, .u8 | .u32, .s16 | .u32, .u16 | .u32, .s32
  | .u32, .s64 | .u32, .u64 | .u32, .f32 | .u32, .f64 | .u32, .char
  | .u32, .record _ | .u32, .variant _
  | .s64, .bool | .s64, .s8 | .s64, .u8 | .s64, .s16 | .s64, .u16 | .s64, .s32
  | .s64, .u32 | .s64, .u64 | .s64, .f32 | .s64, .f64 | .s64, .char
  | .s64, .record _ | .s64, .variant _
  | .u64, .bool | .u64, .s8 | .u64, .u8 | .u64, .s16 | .u64, .u16 | .u64, .s32
  | .u64, .u32 | .u64, .s64 | .u64, .f32 | .u64, .f64 | .u64, .char
  | .u64, .record _ | .u64, .variant _
  | .f32, .bool | .f32, .s8 | .f32, .u8 | .f32, .s16 | .f32, .u16 | .f32, .s32
  | .f32, .u32 | .f32, .s64 | .f32, .u64 | .f32, .f64 | .f32, .char
  | .f32, .record _ | .f32, .variant _
  | .f64, .bool | .f64, .s8 | .f64, .u8 | .f64, .s16 | .f64, .u16 | .f64, .s32
  | .f64, .u32 | .f64, .s64 | .f64, .u64 | .f64, .f32 | .f64, .char
  | .f64, .record _ | .f64, .variant _
  | .char, .bool | .char, .s8 | .char, .u8 | .char, .s16 | .char, .u16 | .char, .s32
  | .char, .u32 | .char, .s64 | .char, .u64 | .char, .f32 | .char, .f64
  | .char, .record _ | .char, .variant _
  | .record _, .bool | .record _, .s8 | .record _, .u8 | .record _, .s16
  | .record _, .u16 | .record _, .s32 | .record _, .u32 | .record _, .s64
  | .record _, .u64 | .record _, .f32 | .record _, .f64 | .record _, .char
  | .record _, .variant _
  | .variant _, .bool | .variant _, .s8 | .variant _, .u8 | .variant _, .s16
  | .variant _, .u16 | .variant _, .s32 | .variant _, .u32 | .variant _, .s64
  | .variant _, .u64 | .variant _, .f32 | .variant _, .f64 | .variant _, .char
  | .variant _, .record _ => isFalse ValTy.noConfusion

/-- Decidable equality of lists of value types. -/
def ValTy.decEqList : (a b : List ValTy) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun h => nomatch h)
  | _ :: _, [] => isFalse (fun h => nomatch h)
  | x :: xs, y :: ys =>
    match ValTy.decEq x y, ValTy.decEqList xs ys with
    | isTrue h, isTrue h' => isTrue (h ▸ h' ▸ rfl)
    | isFalse h, _ => isFalse fun e => h (by cases e; rfl)
    | _, isFalse h => isFalse fun e => h (by cases e; rfl)

/-- Decidable equality of variant case lists. -/
def ValTy.decEqCases : (a b : List (Option ValTy)) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun h => nomatch h)
  | _ :: _, [] => isFalse (fun h => nomatch h)
  | x :: xs, y :: ys =>
    match ValTy.decEqOpt x y, ValTy.decEqCases xs ys with
    | isTrue h, isTrue h' => isTrue (h ▸ h' ▸ rfl)
    | isFalse h, _ => isFalse fun e => h (by cases e; rfl)
    | _, isFalse h => isFalse fun e => h (by cases e; rfl)

/-- Decidable equality of optional payload types. -/
def ValTy.decEqOpt : (a b : Option ValTy) → Decidable (a = b)
  | none, none => isTrue rfl
  | none, some _ => isFalse (fun h => nomatch h)
  | some _, none => isFalse (fun h => nomatch h)
  | some x, some y =>
    match ValTy.decEq x y with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse fun e => h (by cases e; rfl)
end

instance : DecidableEq ValTy := ValTy.decEq

/-! ## Typing -/

mutual
/-- `t.check v`: the value `v` has type `t`. Variant discriminants must also
fit in an `i32`. -/
def ValTy.check : ValTy → Val → Bool
  | .bool, .bool _ => true
  | .s8, .s8 _ => true
  | .u8, .u8 _ => true
  | .s16, .s16 _ => true
  | .u16, .u16 _ => true
  | .s32, .s32 _ => true
  | .u32, .u32 _ => true
  | .s64, .s64 _ => true
  | .u64, .u64 _ => true
  | .f32, .f32 _ => true
  | .f64, .f64 _ => true
  | .char, .char _ => true
  | .record ts, .record vs => ValTy.checkList ts vs
  | .variant cs, .variant i p => decide (i < 2 ^ 32) && ValTy.checkCase cs i p
  | _, _ => false

/-- Pointwise typing of lists (with equal lengths). -/
def ValTy.checkList : List ValTy → List Val → Bool
  | [], [] => true
  | t :: ts, v :: vs => t.check v && ValTy.checkList ts vs
  | _, _ => false

/-- Typing of the payload of case `i`. -/
def ValTy.checkCase : List (Option ValTy) → Nat → Option Val → Bool
  | [], _, _ => false
  | c :: _, 0, p => ValTy.checkOpt c p
  | _ :: cs, i + 1, p => ValTy.checkCase cs i p

/-- Typing of an optional payload. -/
def ValTy.checkOpt : Option ValTy → Option Val → Bool
  | none, none => true
  | some t, some v => t.check v
  | _, _ => false
end

/-! ## Flattening -/

/-- The core type `i32`. -/
abbrev NumType.i32 : NumType := .int .i32
/-- The core type `i64`. -/
abbrev NumType.i64 : NumType := .int .i64

/-- Bit-preserving common carrier of two alternative variant payload slots
(canonical ABI `join`). -/
def joinType : NumType → NumType → NumType
  | .int .i32, .int .i32 | .int .i32, .float .f32 | .float .f32, .int .i32 => .int .i32
  | .float .f32, .float .f32 => .float .f32
  | .float .f64, .float .f64 => .float .f64
  | _, _ => .int .i64

/-- Elementwise join of two payload slot lists, padding the shorter. -/
def joinFlat : List NumType → List NumType → List NumType
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => joinType x y :: joinFlat xs ys

mutual
/-- The flattening of a value type to core types (`flatten_type`). -/
def ValTy.flat : ValTy → List NumType
  | .bool | .s8 | .u8 | .s16 | .u16 | .s32 | .u32 | .char => [.int .i32]
  | .s64 | .u64 => [.int .i64]
  | .f32 => [.float .f32]
  | .f64 => [.float .f64]
  | .record ts => ValTy.flatList ts
  | .variant cs => .int .i32 :: ValTy.flatCases cs

/-- Flattening of a list of types: concatenation. -/
def ValTy.flatList : List ValTy → List NumType
  | [] => []
  | t :: ts => t.flat ++ ValTy.flatList ts

/-- The joined payload slots of a list of variant cases. -/
def ValTy.flatCases : List (Option ValTy) → List NumType
  | [] => []
  | c :: cs => joinFlat (ValTy.flatOpt c) (ValTy.flatCases cs)

/-- Flattening of an optional payload. -/
def ValTy.flatOpt : Option ValTy → List NumType
  | none => []
  | some t => t.flat
end

/-! ## Flat-value helpers -/

/-- An `i32` value. -/
abbrev Flat.i32 (x : BitVec 32) : Flat := ⟨.int .i32, x⟩
/-- An `i64` value. -/
abbrev Flat.i64 (x : BitVec 64) : Flat := ⟨.int .i64, x⟩

/-- Reinterpret the bit pattern of a flat value at another core type, by
zero-extension or truncation. -/
def Flat.retype (t : NumType) (v : Flat) : Flat := ⟨t, v.bits.setWidth t.width⟩

/-- Fit a list of flat values into the slots `ts`, padding with zeros. -/
def Flat.fit : List NumType → List Flat → List Flat
  | [], _ => []
  | t :: ts, [] => Silmaril.Wasm.Execution.Runtime.Value.zero t :: Flat.fit ts []
  | t :: ts, v :: vs => Flat.retype t v :: Flat.fit ts vs

/-- Read back the first `ts.length` slots at the types `ts`. -/
def Flat.unfit : List NumType → List Flat → List Flat
  | t :: ts, v :: vs => Flat.retype t v :: Flat.unfit ts vs
  | _, _ => []

/-- Take a prefix of flat values of the given types. -/
def Flat.take : List NumType → List Flat → Option (List Flat × List Flat)
  | [], vs => some ([], vs)
  | _ :: _, [] => none
  | t :: ts, v :: vs =>
    if v.type = t then (Flat.take ts vs).map fun p => (v :: p.1, p.2) else none

/-! ## Lowering and lifting -/

mutual
/-- `lower_flat`: the flat representation of a value of type `t`. Values of the
wrong type lower to `[]` (adapters check types before lowering). -/
def ValTy.lower : ValTy → Val → List Flat
  | .bool, .bool b => [.i32 (if b then 1 else 0)]
  | .s8, .s8 x => [.i32 (x.signExtend 32)]
  | .u8, .u8 x => [.i32 (x.setWidth 32)]
  | .s16, .s16 x => [.i32 (x.signExtend 32)]
  | .u16, .u16 x => [.i32 (x.setWidth 32)]
  | .s32, .s32 x => [.i32 x]
  | .u32, .u32 x => [.i32 x]
  | .s64, .s64 x => [.i64 x]
  | .u64, .u64 x => [.i64 x]
  | .f32, .f32 x => [⟨.float .f32, x⟩]
  | .f64, .f64 x => [⟨.float .f64, x⟩]
  | .char, .char c => [.i32 c.val.toBitVec]
  | .record ts, .record vs => ValTy.lowerList ts vs
  | .variant cs, .variant i p =>
    .i32 (BitVec.ofNat 32 i) :: Flat.fit (ValTy.flatCases cs) (ValTy.lowerCase cs i p)
  | _, _ => []

/-- Lowering of a list of values, pointwise. -/
def ValTy.lowerList : List ValTy → List Val → List Flat
  | t :: ts, v :: vs => t.lower v ++ ValTy.lowerList ts vs
  | _, _ => []

/-- Lowering of the payload of case `i`. -/
def ValTy.lowerCase : List (Option ValTy) → Nat → Option Val → List Flat
  | [], _, _ => []
  | c :: _, 0, p => ValTy.lowerOpt c p
  | _ :: cs, i + 1, p => ValTy.lowerCase cs i p

/-- Lowering of an optional payload. -/
def ValTy.lowerOpt : Option ValTy → Option Val → List Flat
  | some t, some v => t.lower v
  | _, _ => []
end

/-- The character with code point `x`, if valid. -/
def charOfBits (x : BitVec 32) : Option Char :=
  if h : (UInt32.ofBitVec x).isValidChar then some ⟨UInt32.ofBitVec x, h⟩ else none

mutual
/-- `lift_flat`: read a value of type `t` from the front of a list of flat
values, returning it and the rest. `none` is a trap (or a core value of the
wrong core type, which validation excludes). -/
def ValTy.lift : ValTy → List Flat → Option (Val × List Flat)
  | .bool, ⟨.int .i32, x⟩ :: r => some (.bool (x != 0), r)
  | .s8, ⟨.int .i32, x⟩ :: r => some (.s8 (x.setWidth 8), r)
  | .u8, ⟨.int .i32, x⟩ :: r => some (.u8 (x.setWidth 8), r)
  | .s16, ⟨.int .i32, x⟩ :: r => some (.s16 (x.setWidth 16), r)
  | .u16, ⟨.int .i32, x⟩ :: r => some (.u16 (x.setWidth 16), r)
  | .s32, ⟨.int .i32, x⟩ :: r => some (.s32 x, r)
  | .u32, ⟨.int .i32, x⟩ :: r => some (.u32 x, r)
  | .s64, ⟨.int .i64, x⟩ :: r => some (.s64 x, r)
  | .u64, ⟨.int .i64, x⟩ :: r => some (.u64 x, r)
  | .f32, ⟨.float .f32, x⟩ :: r => some (.f32 x, r)
  | .f64, ⟨.float .f64, x⟩ :: r => some (.f64 x, r)
  | .char, ⟨.int .i32, x⟩ :: r => (charOfBits x).map fun c => (.char c, r)
  | .record ts, vs => (ValTy.liftList ts vs).map fun p => (.record p.1, p.2)
  | .variant cs, ⟨.int .i32, d⟩ :: r =>
    match Flat.take (ValTy.flatCases cs) r with
    | none => none
    | some (js, r') =>
      (ValTy.liftCase cs d.toNat js).map fun p => (.variant d.toNat p, r')
  | _, _ => none

/-- Lifting of a list of values, in order. -/
def ValTy.liftList : List ValTy → List Flat → Option (List Val × List Flat)
  | [], vs => some ([], vs)
  | t :: ts, vs =>
    match t.lift vs with
    | none => none
    | some (v, r) => (ValTy.liftList ts r).map fun p => (v :: p.1, p.2)

/-- Lifting of the payload of case `i` from the joined slots `js`; traps on an
out-of-range case. -/
def ValTy.liftCase : List (Option ValTy) → Nat → List Flat → Option (Option Val)
  | [], _, _ => none
  | c :: _, 0, js => ValTy.liftOpt c (Flat.unfit (ValTy.flatOpt c) js)
  | _ :: cs, i + 1, js => ValTy.liftCase cs i js

/-- Lifting of an optional payload that must consume all of `xs`. -/
def ValTy.liftOpt : Option ValTy → List Flat → Option (Option Val)
  | none, _ => some none
  | some t, xs =>
    match t.lift xs with
    | some (v, []) => some (some v)
    | _ => none
end

/-! ## Function arguments -/

/-- Lift a complete argument (or result) list: every flat value must be used. -/
def liftArgs (ts : List ValTy) (xs : List Flat) : Option (List Val) :=
  match ValTy.liftList ts xs with
  | some (vs, []) => some vs
  | _ => none

/-- Lower an argument (or result) list. -/
def lowerArgs (ts : List ValTy) (vs : List Val) : List Flat := ValTy.lowerList ts vs

/-- Check and lower: `none` (trap) on ill-typed values. -/
def checkLower (ts : List ValTy) (vs : List Val) : Option (List Flat) :=
  if ValTy.checkList ts vs then some (lowerArgs ts vs) else none

/-- Check component values: `none` (trap) on ill-typed values. -/
def checkVals (ts : List ValTy) (vs : List Val) : Option (List Val) :=
  if ValTy.checkList ts vs then some vs else none

/-- The canonicalisation of flat values performed by a lower-of-lift
round trip (`canon lower` of a `canon lift`): lift, then lower. -/
def canonFlat (ts : List ValTy) (xs : List Flat) : Option (List Flat) :=
  (liftArgs ts xs).map (lowerArgs ts)

/-- Check that flat values have the given core types. -/
def checkFlat (ts : List NumType) (xs : List Flat) : Option (List Flat) :=
  if xs.map (·.type) = ts then some xs else none

mutual
/-- Types whose canonical ABI representation is the identity on well-typed
flat values: 32/64-bit integers and floats, and records of such. For these the
canonicalisation `canonFlat` is a type check (`canonFlat_trivial`). -/
def ValTy.trivial : ValTy → Bool
  | .s32 | .u32 | .s64 | .u64 | .f32 | .f64 => true
  | .record ts => ValTy.trivialList ts
  | _ => false

/-- All types of the list are trivial. -/
def ValTy.trivialList : List ValTy → Bool
  | [] => true
  | t :: ts => t.trivial && ValTy.trivialList ts
end

end Silmaril.Wasm.Component
