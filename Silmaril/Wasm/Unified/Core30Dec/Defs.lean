module

public import Silmaril.Wasm.Unified.Core30.Defs

/-!
# Decoding the Core 3.0 encoding

A decoder for the encoding of Core 3.0 instructions in the unified syntax
(`Silmaril.Wasm.Unified.Core30`). It is a proof device: with it the encoding is injective, so the
meaning of an encoded program in the 3.0 opcode algebra is exactly that program, and `model30`
observes exactly silmaril's Core 3.0 behaviours (`Thms`).

* `uncode? n`: the value with code `n`, if any (classical; codes are injective).
* `uncatch?`: a handler-table entry back to a catch clause.
* `dec (k :: ps) imms hs bs`: the instruction of family `k` (the first opcode parameter) with
  operator parameters `ps`, immediates `imms`, handler table `hs` and bodies `bs`. It
  dispatches through a table of per-family decoders (`decTable`, `decAt`); `decAt_k` are the
  table lookups.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Core30

open Silmaril.Wasm Silmaril.Wasm.Unified

open Classical in
/-- The value with a given code, if any. -/
noncomputable def uncode? {α : Type} [Code α] (n : Nat) : Option α :=
  if h : ∃ a : α, code a = n then some h.choose else none

/-- A handler-table entry back to a catch clause. -/
noncomputable def uncatch? : Handler → Option Catch
  | ⟨"catch", [.nat a, .nat b]⟩ => do
    let a ← uncode? a
    let b ← uncode? b
    pure (.catch_ a b)
  | ⟨"catch_ref", [.nat a, .nat b]⟩ => do
    let a ← uncode? a
    let b ← uncode? b
    pure (.catchRef a b)
  | ⟨"catch_all", [.nat a]⟩ => do
    let a ← uncode? a
    pure (.catchAll a)
  | ⟨"catch_all_ref", [.nat a]⟩ => do
    let a ← uncode? a
    pure (.catchAllRef a)
  | _ => none

/-- A decoder of one family: operator parameters, immediates, handler table, bodies. -/
abbrev Dec : Type := List Nat → List Imm → List Handler → List (List Instr) → Option Instr

/-- Decode `nop`. -/
noncomputable def dec_nop : Dec
  | [], [], [], [] => pure (.nop)
  | _, _, _, _ => none

/-- Decode `unreachable`. -/
noncomputable def dec_unreachable : Dec
  | [], [], [], [] => pure (.unreachable)
  | _, _, _, _ => none

/-- Decode `drop`. -/
noncomputable def dec_drop : Dec
  | [], [], [], [] => pure (.drop)
  | _, _, _, _ => none

/-- Decode `select`. -/
noncomputable def dec_select : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.select x0)
  | _, _, _, _ => none

/-- Decode `block`. -/
noncomputable def dec_block : Dec
  | [], [.nat x0], [], [x1] => do
    let x0 ← uncode? x0
    pure (.block x0 x1)
  | _, _, _, _ => none

/-- Decode `loop`. -/
noncomputable def dec_loop : Dec
  | [], [.nat x0], [], [x1] => do
    let x0 ← uncode? x0
    pure (.loop x0 x1)
  | _, _, _, _ => none

/-- Decode `if`. -/
noncomputable def dec_if_ : Dec
  | [], [.nat x0], [], [x1, x2] => do
    let x0 ← uncode? x0
    pure (.if_ x0 x1 x2)
  | _, _, _, _ => none

/-- Decode `br`. -/
noncomputable def dec_br : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.br x0)
  | _, _, _, _ => none

/-- Decode `brIf`. -/
noncomputable def dec_brIf : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.brIf x0)
  | _, _, _, _ => none

/-- Decode `brTable`. -/
noncomputable def dec_brTable : Dec
  | [], [.nat x0, .nat x1], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.brTable x0 x1)
  | _, _, _, _ => none

/-- Decode `brOnNull`. -/
noncomputable def dec_brOnNull : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.brOnNull x0)
  | _, _, _, _ => none

/-- Decode `brOnNonNull`. -/
noncomputable def dec_brOnNonNull : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.brOnNonNull x0)
  | _, _, _, _ => none

/-- Decode `brOnCast`. -/
noncomputable def dec_brOnCast : Dec
  | [], [.nat x0, .nat x1, .nat x2], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    let x2 ← uncode? x2
    pure (.brOnCast x0 x1 x2)
  | _, _, _, _ => none

/-- Decode `brOnCastFail`. -/
noncomputable def dec_brOnCastFail : Dec
  | [], [.nat x0, .nat x1, .nat x2], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    let x2 ← uncode? x2
    pure (.brOnCastFail x0 x1 x2)
  | _, _, _, _ => none

/-- Decode `call`. -/
noncomputable def dec_call : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.call x0)
  | _, _, _, _ => none

/-- Decode `callRef`. -/
noncomputable def dec_callRef : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.callRef x0)
  | _, _, _, _ => none

/-- Decode `callIndirect`. -/
noncomputable def dec_callIndirect : Dec
  | [], [.nat x0, .nat x1], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.callIndirect x0 x1)
  | _, _, _, _ => none

/-- Decode `return`. -/
noncomputable def dec_return_ : Dec
  | [], [], [], [] => pure (.return_)
  | _, _, _, _ => none

/-- Decode `returnCall`. -/
noncomputable def dec_returnCall : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.returnCall x0)
  | _, _, _, _ => none

/-- Decode `returnCallRef`. -/
noncomputable def dec_returnCallRef : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.returnCallRef x0)
  | _, _, _, _ => none

/-- Decode `returnCallIndirect`. -/
noncomputable def dec_returnCallIndirect : Dec
  | [], [.nat x0, .nat x1], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.returnCallIndirect x0 x1)
  | _, _, _, _ => none

/-- Decode `throw`. -/
noncomputable def dec_throw : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.throw x0)
  | _, _, _, _ => none

/-- Decode `throwRef`. -/
noncomputable def dec_throwRef : Dec
  | [], [], [], [] => pure (.throwRef)
  | _, _, _, _ => none

/-- Decode `tryTable`. -/
noncomputable def dec_tryTable : Dec
  | [], [.nat x0], hs, [x2] => do
    let x0 ← uncode? x0
    let x1 ← hs.mapM uncatch?
    pure (.tryTable x0 x1 x2)
  | _, _, _, _ => none

/-- Decode `localGet`. -/
noncomputable def dec_localGet : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.localGet x0)
  | _, _, _, _ => none

/-- Decode `localSet`. -/
noncomputable def dec_localSet : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.localSet x0)
  | _, _, _, _ => none

/-- Decode `localTee`. -/
noncomputable def dec_localTee : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.localTee x0)
  | _, _, _, _ => none

/-- Decode `globalGet`. -/
noncomputable def dec_globalGet : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.globalGet x0)
  | _, _, _, _ => none

/-- Decode `globalSet`. -/
noncomputable def dec_globalSet : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.globalSet x0)
  | _, _, _, _ => none

/-- Decode `tableGet`. -/
noncomputable def dec_tableGet : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.tableGet x0)
  | _, _, _, _ => none

/-- Decode `tableSet`. -/
noncomputable def dec_tableSet : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.tableSet x0)
  | _, _, _, _ => none

/-- Decode `tableSize`. -/
noncomputable def dec_tableSize : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.tableSize x0)
  | _, _, _, _ => none

/-- Decode `tableGrow`. -/
noncomputable def dec_tableGrow : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.tableGrow x0)
  | _, _, _, _ => none

/-- Decode `tableFill`. -/
noncomputable def dec_tableFill : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.tableFill x0)
  | _, _, _, _ => none

/-- Decode `tableCopy`. -/
noncomputable def dec_tableCopy : Dec
  | [], [.nat x0, .nat x1], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.tableCopy x0 x1)
  | _, _, _, _ => none

/-- Decode `tableInit`. -/
noncomputable def dec_tableInit : Dec
  | [], [.nat x0, .nat x1], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.tableInit x0 x1)
  | _, _, _, _ => none

/-- Decode `elemDrop`. -/
noncomputable def dec_elemDrop : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.elemDrop x0)
  | _, _, _, _ => none

/-- Decode `intLoad`. -/
noncomputable def dec_intLoad : Dec
  | [x0, x1], [.nat x2, .nat x3], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    let x2 ← uncode? x2
    let x3 ← uncode? x3
    pure (.intLoad x0 x1 x2 x3)
  | _, _, _, _ => none

/-- Decode `floatLoad`. -/
noncomputable def dec_floatLoad : Dec
  | [x0], [.nat x1, .nat x2], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    let x2 ← uncode? x2
    pure (.floatLoad x0 x1 x2)
  | _, _, _, _ => none

/-- Decode `intStore`. -/
noncomputable def dec_intStore : Dec
  | [x0, x1], [.nat x2, .nat x3], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    let x2 ← uncode? x2
    let x3 ← uncode? x3
    pure (.intStore x0 x1 x2 x3)
  | _, _, _, _ => none

/-- Decode `floatStore`. -/
noncomputable def dec_floatStore : Dec
  | [x0], [.nat x1, .nat x2], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    let x2 ← uncode? x2
    pure (.floatStore x0 x1 x2)
  | _, _, _, _ => none

/-- Decode `vecLoad`. -/
noncomputable def dec_vecLoad : Dec
  | [x0], [.nat x1, .nat x2], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    let x2 ← uncode? x2
    pure (.vecLoad x0 x1 x2)
  | _, _, _, _ => none

/-- Decode `vecLoadLane`. -/
noncomputable def dec_vecLoadLane : Dec
  | [x0], [.nat x1, .nat x2, .nat x3], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    let x2 ← uncode? x2
    let x3 ← uncode? x3
    pure (.vecLoadLane x0 x1 x2 x3)
  | _, _, _, _ => none

/-- Decode `vecStore`. -/
noncomputable def dec_vecStore : Dec
  | [], [.nat x0, .nat x1], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.vecStore x0 x1)
  | _, _, _, _ => none

/-- Decode `vecStoreLane`. -/
noncomputable def dec_vecStoreLane : Dec
  | [x0], [.nat x1, .nat x2, .nat x3], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    let x2 ← uncode? x2
    let x3 ← uncode? x3
    pure (.vecStoreLane x0 x1 x2 x3)
  | _, _, _, _ => none

/-- Decode `memorySize`. -/
noncomputable def dec_memorySize : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.memorySize x0)
  | _, _, _, _ => none

/-- Decode `memoryGrow`. -/
noncomputable def dec_memoryGrow : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.memoryGrow x0)
  | _, _, _, _ => none

/-- Decode `memoryFill`. -/
noncomputable def dec_memoryFill : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.memoryFill x0)
  | _, _, _, _ => none

/-- Decode `memoryCopy`. -/
noncomputable def dec_memoryCopy : Dec
  | [], [.nat x0, .nat x1], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.memoryCopy x0 x1)
  | _, _, _, _ => none

/-- Decode `memoryInit`. -/
noncomputable def dec_memoryInit : Dec
  | [], [.nat x0, .nat x1], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.memoryInit x0 x1)
  | _, _, _, _ => none

/-- Decode `dataDrop`. -/
noncomputable def dec_dataDrop : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.dataDrop x0)
  | _, _, _, _ => none

/-- Decode `refNull`. -/
noncomputable def dec_refNull : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.refNull x0)
  | _, _, _, _ => none

/-- Decode `refIsNull`. -/
noncomputable def dec_refIsNull : Dec
  | [], [], [], [] => pure (.refIsNull)
  | _, _, _, _ => none

/-- Decode `refAsNonNull`. -/
noncomputable def dec_refAsNonNull : Dec
  | [], [], [], [] => pure (.refAsNonNull)
  | _, _, _, _ => none

/-- Decode `refEq`. -/
noncomputable def dec_refEq : Dec
  | [], [], [], [] => pure (.refEq)
  | _, _, _, _ => none

/-- Decode `refTest`. -/
noncomputable def dec_refTest : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.refTest x0)
  | _, _, _, _ => none

/-- Decode `refCast`. -/
noncomputable def dec_refCast : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.refCast x0)
  | _, _, _, _ => none

/-- Decode `refFunc`. -/
noncomputable def dec_refFunc : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.refFunc x0)
  | _, _, _, _ => none

/-- Decode `refI31`. -/
noncomputable def dec_refI31 : Dec
  | [], [], [], [] => pure (.refI31)
  | _, _, _, _ => none

/-- Decode `i31Get`. -/
noncomputable def dec_i31Get : Dec
  | [x0], [], [], [] => do
    let x0 ← uncode? x0
    pure (.i31Get x0)
  | _, _, _, _ => none

/-- Decode `structNew`. -/
noncomputable def dec_structNew : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.structNew x0)
  | _, _, _, _ => none

/-- Decode `structNewDefault`. -/
noncomputable def dec_structNewDefault : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.structNewDefault x0)
  | _, _, _, _ => none

/-- Decode `structGet`. -/
noncomputable def dec_structGet : Dec
  | [x0], [.nat x1, .nat x2], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    let x2 ← uncode? x2
    pure (.structGet x0 x1 x2)
  | _, _, _, _ => none

/-- Decode `structSet`. -/
noncomputable def dec_structSet : Dec
  | [], [.nat x0, .nat x1], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.structSet x0 x1)
  | _, _, _, _ => none

/-- Decode `arrayNew`. -/
noncomputable def dec_arrayNew : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.arrayNew x0)
  | _, _, _, _ => none

/-- Decode `arrayNewDefault`. -/
noncomputable def dec_arrayNewDefault : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.arrayNewDefault x0)
  | _, _, _, _ => none

/-- Decode `arrayNewFixed`. -/
noncomputable def dec_arrayNewFixed : Dec
  | [], [.nat x0, .nat x1], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.arrayNewFixed x0 x1)
  | _, _, _, _ => none

/-- Decode `arrayNewData`. -/
noncomputable def dec_arrayNewData : Dec
  | [], [.nat x0, .nat x1], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.arrayNewData x0 x1)
  | _, _, _, _ => none

/-- Decode `arrayNewElem`. -/
noncomputable def dec_arrayNewElem : Dec
  | [], [.nat x0, .nat x1], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.arrayNewElem x0 x1)
  | _, _, _, _ => none

/-- Decode `arrayGet`. -/
noncomputable def dec_arrayGet : Dec
  | [x0], [.nat x1], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.arrayGet x0 x1)
  | _, _, _, _ => none

/-- Decode `arraySet`. -/
noncomputable def dec_arraySet : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.arraySet x0)
  | _, _, _, _ => none

/-- Decode `arrayLen`. -/
noncomputable def dec_arrayLen : Dec
  | [], [], [], [] => pure (.arrayLen)
  | _, _, _, _ => none

/-- Decode `arrayFill`. -/
noncomputable def dec_arrayFill : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.arrayFill x0)
  | _, _, _, _ => none

/-- Decode `arrayCopy`. -/
noncomputable def dec_arrayCopy : Dec
  | [], [.nat x0, .nat x1], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.arrayCopy x0 x1)
  | _, _, _, _ => none

/-- Decode `arrayInitData`. -/
noncomputable def dec_arrayInitData : Dec
  | [], [.nat x0, .nat x1], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.arrayInitData x0 x1)
  | _, _, _, _ => none

/-- Decode `arrayInitElem`. -/
noncomputable def dec_arrayInitElem : Dec
  | [], [.nat x0, .nat x1], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.arrayInitElem x0 x1)
  | _, _, _, _ => none

/-- Decode `externConvertAny`. -/
noncomputable def dec_externConvertAny : Dec
  | [], [], [], [] => pure (.externConvertAny)
  | _, _, _, _ => none

/-- Decode `anyConvertExtern`. -/
noncomputable def dec_anyConvertExtern : Dec
  | [], [], [], [] => pure (.anyConvertExtern)
  | _, _, _, _ => none

/-- Decode `intConst`. -/
noncomputable def dec_intConst : Dec
  | [x0], [.nat x1], [], [] => do
    let x0 ← uncode? x0
    pure (.intConst x0 (BitVec.ofNat _ x1))
  | _, _, _, _ => none

/-- Decode `floatConst`. -/
noncomputable def dec_floatConst : Dec
  | [x0], [.nat x1], [], [] => do
    let x0 ← uncode? x0
    pure (.floatConst x0 (BitVec.ofNat _ x1))
  | _, _, _, _ => none

/-- Decode `intUnOp`. -/
noncomputable def dec_intUnOp : Dec
  | [x0, x1], [], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.intUnOp x0 x1)
  | _, _, _, _ => none

/-- Decode `intBinOp`. -/
noncomputable def dec_intBinOp : Dec
  | [x0, x1], [], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.intBinOp x0 x1)
  | _, _, _, _ => none

/-- Decode `intTestOp`. -/
noncomputable def dec_intTestOp : Dec
  | [x0, x1], [], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.intTestOp x0 x1)
  | _, _, _, _ => none

/-- Decode `intRelOp`. -/
noncomputable def dec_intRelOp : Dec
  | [x0, x1], [], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.intRelOp x0 x1)
  | _, _, _, _ => none

/-- Decode `floatUnOp`. -/
noncomputable def dec_floatUnOp : Dec
  | [x0, x1], [], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.floatUnOp x0 x1)
  | _, _, _, _ => none

/-- Decode `floatBinOp`. -/
noncomputable def dec_floatBinOp : Dec
  | [x0, x1], [], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.floatBinOp x0 x1)
  | _, _, _, _ => none

/-- Decode `floatRelOp`. -/
noncomputable def dec_floatRelOp : Dec
  | [x0, x1], [], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.floatRelOp x0 x1)
  | _, _, _, _ => none

/-- Decode `convert`. -/
noncomputable def dec_convert : Dec
  | [x0], [], [], [] => do
    let x0 ← uncode? x0
    pure (.convert x0)
  | _, _, _, _ => none

/-- Decode `vecConst`. -/
noncomputable def dec_vecConst : Dec
  | [], [.nat x0], [], [] => pure (.vecConst (BitVec.ofNat 128 x0))
  | _, _, _, _ => none

/-- Decode `vecUnOp`. -/
noncomputable def dec_vecUnOp : Dec
  | [x0], [], [], [] => do
    let x0 ← uncode? x0
    pure (.vecUnOp x0)
  | _, _, _, _ => none

/-- Decode `vecBinOp`. -/
noncomputable def dec_vecBinOp : Dec
  | [x0], [], [], [] => do
    let x0 ← uncode? x0
    pure (.vecBinOp x0)
  | _, _, _, _ => none

/-- Decode `vecTernOp`. -/
noncomputable def dec_vecTernOp : Dec
  | [x0], [], [], [] => do
    let x0 ← uncode? x0
    pure (.vecTernOp x0)
  | _, _, _, _ => none

/-- Decode `vecTestOp`. -/
noncomputable def dec_vecTestOp : Dec
  | [x0], [], [], [] => do
    let x0 ← uncode? x0
    pure (.vecTestOp x0)
  | _, _, _, _ => none

/-- Decode `vecIntUnOp`. -/
noncomputable def dec_vecIntUnOp : Dec
  | [x0, x1], [], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.vecIntUnOp x0 x1)
  | _, _, _, _ => none

/-- Decode `vecFloatUnOp`. -/
noncomputable def dec_vecFloatUnOp : Dec
  | [x0, x1], [], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.vecFloatUnOp x0 x1)
  | _, _, _, _ => none

/-- Decode `vecIntBinOp`. -/
noncomputable def dec_vecIntBinOp : Dec
  | [x0, x1], [], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.vecIntBinOp x0 x1)
  | _, _, _, _ => none

/-- Decode `vecFloatBinOp`. -/
noncomputable def dec_vecFloatBinOp : Dec
  | [x0, x1], [], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.vecFloatBinOp x0 x1)
  | _, _, _, _ => none

/-- Decode `vecIntTernOp`. -/
noncomputable def dec_vecIntTernOp : Dec
  | [x0, x1], [], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.vecIntTernOp x0 x1)
  | _, _, _, _ => none

/-- Decode `vecFloatTernOp`. -/
noncomputable def dec_vecFloatTernOp : Dec
  | [x0, x1], [], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.vecFloatTernOp x0 x1)
  | _, _, _, _ => none

/-- Decode `vecAllTrue`. -/
noncomputable def dec_vecAllTrue : Dec
  | [x0], [], [], [] => do
    let x0 ← uncode? x0
    pure (.vecAllTrue x0)
  | _, _, _, _ => none

/-- Decode `vecIntRelOp`. -/
noncomputable def dec_vecIntRelOp : Dec
  | [x0, x1], [], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.vecIntRelOp x0 x1)
  | _, _, _, _ => none

/-- Decode `vecFloatRelOp`. -/
noncomputable def dec_vecFloatRelOp : Dec
  | [x0, x1], [], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.vecFloatRelOp x0 x1)
  | _, _, _, _ => none

/-- Decode `vecShiftOp`. -/
noncomputable def dec_vecShiftOp : Dec
  | [x0, x1], [], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.vecShiftOp x0 x1)
  | _, _, _, _ => none

/-- Decode `vecBitmask`. -/
noncomputable def dec_vecBitmask : Dec
  | [x0], [], [], [] => do
    let x0 ← uncode? x0
    pure (.vecBitmask x0)
  | _, _, _, _ => none

/-- Decode `vecSwizzle`. -/
noncomputable def dec_vecSwizzle : Dec
  | [x0], [], [], [] => do
    let x0 ← uncode? x0
    pure (.vecSwizzle x0)
  | _, _, _, _ => none

/-- Decode `vecShuffle`. -/
noncomputable def dec_vecShuffle : Dec
  | [], [.nat x0], [], [] => do
    let x0 ← uncode? x0
    pure (.vecShuffle x0)
  | _, _, _, _ => none

/-- Decode `vecExtUnOp`. -/
noncomputable def dec_vecExtUnOp : Dec
  | [x0, x1, x2], [], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    let x2 ← uncode? x2
    pure (.vecExtUnOp x0 x1 x2)
  | _, _, _, _ => none

/-- Decode `vecExtBinOp`. -/
noncomputable def dec_vecExtBinOp : Dec
  | [x0, x1, x2], [], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    let x2 ← uncode? x2
    pure (.vecExtBinOp x0 x1 x2)
  | _, _, _, _ => none

/-- Decode `vecExtTernOp`. -/
noncomputable def dec_vecExtTernOp : Dec
  | [x0, x1, x2], [], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    let x2 ← uncode? x2
    pure (.vecExtTernOp x0 x1 x2)
  | _, _, _, _ => none

/-- Decode `vecNarrow`. -/
noncomputable def dec_vecNarrow : Dec
  | [x0, x1, x2], [], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    let x2 ← uncode? x2
    pure (.vecNarrow x0 x1 x2)
  | _, _, _, _ => none

/-- Decode `vecConvert`. -/
noncomputable def dec_vecConvert : Dec
  | [x0, x1, x2], [], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    let x2 ← uncode? x2
    pure (.vecConvert x0 x1 x2)
  | _, _, _, _ => none

/-- Decode `vecSplat`. -/
noncomputable def dec_vecSplat : Dec
  | [x0], [], [], [] => do
    let x0 ← uncode? x0
    pure (.vecSplat x0)
  | _, _, _, _ => none

/-- Decode `vecExtractLane`. -/
noncomputable def dec_vecExtractLane : Dec
  | [x0, x1], [.nat x2], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    let x2 ← uncode? x2
    pure (.vecExtractLane x0 x1 x2)
  | _, _, _, _ => none

/-- Decode `vecReplaceLane`. -/
noncomputable def dec_vecReplaceLane : Dec
  | [x0], [.nat x1], [], [] => do
    let x0 ← uncode? x0
    let x1 ← uncode? x1
    pure (.vecReplaceLane x0 x1)
  | _, _, _, _ => none

/-- The decoders, by family number. -/
noncomputable def decTable : List Dec :=
  [dec_nop,
   dec_unreachable,
   dec_drop,
   dec_select,
   dec_block,
   dec_loop,
   dec_if_,
   dec_br,
   dec_brIf,
   dec_brTable,
   dec_brOnNull,
   dec_brOnNonNull,
   dec_brOnCast,
   dec_brOnCastFail,
   dec_call,
   dec_callRef,
   dec_callIndirect,
   dec_return_,
   dec_returnCall,
   dec_returnCallRef,
   dec_returnCallIndirect,
   dec_throw,
   dec_throwRef,
   dec_tryTable,
   dec_localGet,
   dec_localSet,
   dec_localTee,
   dec_globalGet,
   dec_globalSet,
   dec_tableGet,
   dec_tableSet,
   dec_tableSize,
   dec_tableGrow,
   dec_tableFill,
   dec_tableCopy,
   dec_tableInit,
   dec_elemDrop,
   dec_intLoad,
   dec_floatLoad,
   dec_intStore,
   dec_floatStore,
   dec_vecLoad,
   dec_vecLoadLane,
   dec_vecStore,
   dec_vecStoreLane,
   dec_memorySize,
   dec_memoryGrow,
   dec_memoryFill,
   dec_memoryCopy,
   dec_memoryInit,
   dec_dataDrop,
   dec_refNull,
   dec_refIsNull,
   dec_refAsNonNull,
   dec_refEq,
   dec_refTest,
   dec_refCast,
   dec_refFunc,
   dec_refI31,
   dec_i31Get,
   dec_structNew,
   dec_structNewDefault,
   dec_structGet,
   dec_structSet,
   dec_arrayNew,
   dec_arrayNewDefault,
   dec_arrayNewFixed,
   dec_arrayNewData,
   dec_arrayNewElem,
   dec_arrayGet,
   dec_arraySet,
   dec_arrayLen,
   dec_arrayFill,
   dec_arrayCopy,
   dec_arrayInitData,
   dec_arrayInitElem,
   dec_externConvertAny,
   dec_anyConvertExtern,
   dec_intConst,
   dec_floatConst,
   dec_intUnOp,
   dec_intBinOp,
   dec_intTestOp,
   dec_intRelOp,
   dec_floatUnOp,
   dec_floatBinOp,
   dec_floatRelOp,
   dec_convert,
   dec_vecConst,
   dec_vecUnOp,
   dec_vecBinOp,
   dec_vecTernOp,
   dec_vecTestOp,
   dec_vecIntUnOp,
   dec_vecFloatUnOp,
   dec_vecIntBinOp,
   dec_vecFloatBinOp,
   dec_vecIntTernOp,
   dec_vecFloatTernOp,
   dec_vecAllTrue,
   dec_vecIntRelOp,
   dec_vecFloatRelOp,
   dec_vecShiftOp,
   dec_vecBitmask,
   dec_vecSwizzle,
   dec_vecShuffle,
   dec_vecExtUnOp,
   dec_vecExtBinOp,
   dec_vecExtTernOp,
   dec_vecNarrow,
   dec_vecConvert,
   dec_vecSplat,
   dec_vecExtractLane,
   dec_vecReplaceLane]

/-- The decoder of a family number. -/
noncomputable def decAt (k : Nat) : Dec := decTable.getD k fun _ _ _ _ => none

/-- **The decoder**: dispatch on the family number, the first opcode parameter. -/
noncomputable def dec : Dec
  | k :: ps, imms, hs, bs => decAt k ps imms hs bs
  | [], _, _, _ => none

/-! ## Evaluation lemmas (one per family) -/

theorem decAt_0 : decAt 0 = dec_nop := rfl
theorem decAt_1 : decAt 1 = dec_unreachable := rfl
theorem decAt_2 : decAt 2 = dec_drop := rfl
theorem decAt_3 : decAt 3 = dec_select := rfl
theorem decAt_4 : decAt 4 = dec_block := rfl
theorem decAt_5 : decAt 5 = dec_loop := rfl
theorem decAt_6 : decAt 6 = dec_if_ := rfl
theorem decAt_7 : decAt 7 = dec_br := rfl
theorem decAt_8 : decAt 8 = dec_brIf := rfl
theorem decAt_9 : decAt 9 = dec_brTable := rfl
theorem decAt_10 : decAt 10 = dec_brOnNull := rfl
theorem decAt_11 : decAt 11 = dec_brOnNonNull := rfl
theorem decAt_12 : decAt 12 = dec_brOnCast := rfl
theorem decAt_13 : decAt 13 = dec_brOnCastFail := rfl
theorem decAt_14 : decAt 14 = dec_call := rfl
theorem decAt_15 : decAt 15 = dec_callRef := rfl
theorem decAt_16 : decAt 16 = dec_callIndirect := rfl
theorem decAt_17 : decAt 17 = dec_return_ := rfl
theorem decAt_18 : decAt 18 = dec_returnCall := rfl
theorem decAt_19 : decAt 19 = dec_returnCallRef := rfl
theorem decAt_20 : decAt 20 = dec_returnCallIndirect := rfl
theorem decAt_21 : decAt 21 = dec_throw := rfl
theorem decAt_22 : decAt 22 = dec_throwRef := rfl
theorem decAt_23 : decAt 23 = dec_tryTable := rfl
theorem decAt_24 : decAt 24 = dec_localGet := rfl
theorem decAt_25 : decAt 25 = dec_localSet := rfl
theorem decAt_26 : decAt 26 = dec_localTee := rfl
theorem decAt_27 : decAt 27 = dec_globalGet := rfl
theorem decAt_28 : decAt 28 = dec_globalSet := rfl
theorem decAt_29 : decAt 29 = dec_tableGet := rfl
theorem decAt_30 : decAt 30 = dec_tableSet := rfl
theorem decAt_31 : decAt 31 = dec_tableSize := rfl
theorem decAt_32 : decAt 32 = dec_tableGrow := rfl
theorem decAt_33 : decAt 33 = dec_tableFill := rfl
theorem decAt_34 : decAt 34 = dec_tableCopy := rfl
theorem decAt_35 : decAt 35 = dec_tableInit := rfl
theorem decAt_36 : decAt 36 = dec_elemDrop := rfl
theorem decAt_37 : decAt 37 = dec_intLoad := rfl
theorem decAt_38 : decAt 38 = dec_floatLoad := rfl
theorem decAt_39 : decAt 39 = dec_intStore := rfl
theorem decAt_40 : decAt 40 = dec_floatStore := rfl
theorem decAt_41 : decAt 41 = dec_vecLoad := rfl
theorem decAt_42 : decAt 42 = dec_vecLoadLane := rfl
theorem decAt_43 : decAt 43 = dec_vecStore := rfl
theorem decAt_44 : decAt 44 = dec_vecStoreLane := rfl
theorem decAt_45 : decAt 45 = dec_memorySize := rfl
theorem decAt_46 : decAt 46 = dec_memoryGrow := rfl
theorem decAt_47 : decAt 47 = dec_memoryFill := rfl
theorem decAt_48 : decAt 48 = dec_memoryCopy := rfl
theorem decAt_49 : decAt 49 = dec_memoryInit := rfl
theorem decAt_50 : decAt 50 = dec_dataDrop := rfl
theorem decAt_51 : decAt 51 = dec_refNull := rfl
theorem decAt_52 : decAt 52 = dec_refIsNull := rfl
theorem decAt_53 : decAt 53 = dec_refAsNonNull := rfl
theorem decAt_54 : decAt 54 = dec_refEq := rfl
theorem decAt_55 : decAt 55 = dec_refTest := rfl
theorem decAt_56 : decAt 56 = dec_refCast := rfl
theorem decAt_57 : decAt 57 = dec_refFunc := rfl
theorem decAt_58 : decAt 58 = dec_refI31 := rfl
theorem decAt_59 : decAt 59 = dec_i31Get := rfl
theorem decAt_60 : decAt 60 = dec_structNew := rfl
theorem decAt_61 : decAt 61 = dec_structNewDefault := rfl
theorem decAt_62 : decAt 62 = dec_structGet := rfl
theorem decAt_63 : decAt 63 = dec_structSet := rfl
theorem decAt_64 : decAt 64 = dec_arrayNew := rfl
theorem decAt_65 : decAt 65 = dec_arrayNewDefault := rfl
theorem decAt_66 : decAt 66 = dec_arrayNewFixed := rfl
theorem decAt_67 : decAt 67 = dec_arrayNewData := rfl
theorem decAt_68 : decAt 68 = dec_arrayNewElem := rfl
theorem decAt_69 : decAt 69 = dec_arrayGet := rfl
theorem decAt_70 : decAt 70 = dec_arraySet := rfl
theorem decAt_71 : decAt 71 = dec_arrayLen := rfl
theorem decAt_72 : decAt 72 = dec_arrayFill := rfl
theorem decAt_73 : decAt 73 = dec_arrayCopy := rfl
theorem decAt_74 : decAt 74 = dec_arrayInitData := rfl
theorem decAt_75 : decAt 75 = dec_arrayInitElem := rfl
theorem decAt_76 : decAt 76 = dec_externConvertAny := rfl
theorem decAt_77 : decAt 77 = dec_anyConvertExtern := rfl
theorem decAt_78 : decAt 78 = dec_intConst := rfl
theorem decAt_79 : decAt 79 = dec_floatConst := rfl
theorem decAt_80 : decAt 80 = dec_intUnOp := rfl
theorem decAt_81 : decAt 81 = dec_intBinOp := rfl
theorem decAt_82 : decAt 82 = dec_intTestOp := rfl
theorem decAt_83 : decAt 83 = dec_intRelOp := rfl
theorem decAt_84 : decAt 84 = dec_floatUnOp := rfl
theorem decAt_85 : decAt 85 = dec_floatBinOp := rfl
theorem decAt_86 : decAt 86 = dec_floatRelOp := rfl
theorem decAt_87 : decAt 87 = dec_convert := rfl
theorem decAt_88 : decAt 88 = dec_vecConst := rfl
theorem decAt_89 : decAt 89 = dec_vecUnOp := rfl
theorem decAt_90 : decAt 90 = dec_vecBinOp := rfl
theorem decAt_91 : decAt 91 = dec_vecTernOp := rfl
theorem decAt_92 : decAt 92 = dec_vecTestOp := rfl
theorem decAt_93 : decAt 93 = dec_vecIntUnOp := rfl
theorem decAt_94 : decAt 94 = dec_vecFloatUnOp := rfl
theorem decAt_95 : decAt 95 = dec_vecIntBinOp := rfl
theorem decAt_96 : decAt 96 = dec_vecFloatBinOp := rfl
theorem decAt_97 : decAt 97 = dec_vecIntTernOp := rfl
theorem decAt_98 : decAt 98 = dec_vecFloatTernOp := rfl
theorem decAt_99 : decAt 99 = dec_vecAllTrue := rfl
theorem decAt_100 : decAt 100 = dec_vecIntRelOp := rfl
theorem decAt_101 : decAt 101 = dec_vecFloatRelOp := rfl
theorem decAt_102 : decAt 102 = dec_vecShiftOp := rfl
theorem decAt_103 : decAt 103 = dec_vecBitmask := rfl
theorem decAt_104 : decAt 104 = dec_vecSwizzle := rfl
theorem decAt_105 : decAt 105 = dec_vecShuffle := rfl
theorem decAt_106 : decAt 106 = dec_vecExtUnOp := rfl
theorem decAt_107 : decAt 107 = dec_vecExtBinOp := rfl
theorem decAt_108 : decAt 108 = dec_vecExtTernOp := rfl
theorem decAt_109 : decAt 109 = dec_vecNarrow := rfl
theorem decAt_110 : decAt 110 = dec_vecConvert := rfl
theorem decAt_111 : decAt 111 = dec_vecSplat := rfl
theorem decAt_112 : decAt 112 = dec_vecExtractLane := rfl
theorem decAt_113 : decAt 113 = dec_vecReplaceLane := rfl

end Silmaril.Wasm.Unified.Core30
