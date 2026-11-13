module

public import Silmaril.Wasm.Jco.Adaptor.Defs

/-!
# Adaptor modules with memory access and control flow

The adaptor functions of `Silmaril.Wasm.Jco.Adaptor` have only `local.get`, `local.set`,
`i32.const` and `call`. The FFI styles of this directory also need, in their adaptors:

* a `realloc` that moves an old block (a nonzero old pointer): `i32.eqz`, `i32.lt_u`, `select`,
  `memory.copy` and `if … else … end`;
* loads and stores (spilled parameters, results in memory): `load t n sx off` is the Wasm load
  of `n` bytes (`i32.load8_u` is `load i32 1 false`, `i64.load` is `load i64 8 false`, and so
  on), sign-extended when `sx`; `store n off` stores the low `n` bytes of a value.

`XInstr` is that instruction set, with `AInstr` embedded (`base`). Its semantics follows the
Wasm specification on the values that occur here (all addresses are `i32`; a load or store at
`a + off` traps out of bounds, as do `memory.copy`'s source and destination ranges; the copy is
a `memmove`). Operands of a wrong core type trap; validation excludes them. `if` blocks are
not typed: a branch runs on the current operand stack.

`XComp` is a wrapper-style component over one `XMod` adaptor. Its lifts carry the canonical
options that vary between FFI styles (`LiftOpts`: the string encoding). The canonical call they
use is a parameter (`XComp.callExportWith`), so each style supplies its own `canon lift`.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat)
open Silmaril.Wasm (NumType)

/-- Adaptor instructions with memory access and control flow. -/
inductive XInstr where
  | base (i : AInstr)
  | i32Eqz
  | i32LtU
  | select
  | memCopy
  /-- `if (result res) thn else els end` (the result type is used only by the Lime1 encoding). -/
  | ifElse (res : Option NumType) (thn els : List XInstr)
  /-- Load `n` bytes at `addr + off` as a value of type `t` (sign-extended when `sx`). -/
  | load (t : NumType) (n : Nat) (sx : Bool) (off : Nat)
  /-- Store the low `n` bytes of a value of type `t` at `addr + off`. -/
  | store (t : NumType) (n : Nat) (off : Nat)
  deriving Repr, Inhabited

/-- The natural number of little-endian bytes. -/
def leNat : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leNat bs

/-- The `n` low little-endian bytes of `x`. -/
def leBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, x => (x % 256).toUInt8 :: leBytes n (x / 256)

/-- The value of type `t` loaded from `n` bytes. -/
def loadVal (t : NumType) (n : Nat) (sx : Bool) (bs : List UInt8) : Flat :=
  if sx then ⟨t, (BitVec.ofNat (8 * n) (leNat bs)).signExtend t.width⟩
  else ⟨t, BitVec.ofNat t.width (leNat bs)⟩

variable (M : CoreInst)

mutual
/-- One instruction. -/
def XInstr.step : XInstr → Frame → RM M.St Frame
  | .base i, f => i.step M f
  | .i32Eqz, f =>
    match f.stack with
    | v :: st => do
      let x ← RM.ofOption (asI32? v)
      pure ⟨f.locals, Flat.i32 (if x == 0 then 1 else 0) :: st⟩
    | _ => RM.fail
  | .i32LtU, f =>
    match f.stack with
    | vb :: va :: st => do
      let b ← RM.ofOption (asI32? vb)
      let a ← RM.ofOption (asI32? va)
      pure ⟨f.locals, Flat.i32 (if a.toNat < b.toNat then 1 else 0) :: st⟩
    | _ => RM.fail
  | .select, f =>
    match f.stack with
    | vc :: b :: a :: st => do
      let c ← RM.ofOption (asI32? vc)
      pure ⟨f.locals, (if c == 0 then b else a) :: st⟩
    | _ => RM.fail
  | .memCopy, f =>
    match f.stack with
    | vn :: vs :: vd :: st => do
      let n ← RM.ofOption (asI32? vn)
      let s ← RM.ofOption (asI32? vs)
      let d ← RM.ofOption (asI32? vd)
      let bs ← M.load s.toNat n.toNat
      M.store d.toNat bs
      pure ⟨f.locals, st⟩
    | _ => RM.fail
  | .ifElse _ thn els, f =>
    match f.stack with
    | vc :: st => do
      let c ← RM.ofOption (asI32? vc)
      if c == 0 then execX els ⟨f.locals, st⟩ else execX thn ⟨f.locals, st⟩
    | _ => RM.fail
  | .load t n sx off, f =>
    match f.stack with
    | va :: st => do
      let a ← RM.ofOption (asI32? va)
      let bs ← M.load (a.toNat + off) n
      pure ⟨f.locals, loadVal t n sx bs :: st⟩
    | _ => RM.fail
  | .store _ n off, f =>
    match f.stack with
    | v :: va :: st => do
      let a ← RM.ofOption (asI32? va)
      M.store (a.toNat + off) (leBytes n v.bits.toNat)
      pure ⟨f.locals, st⟩
    | _ => RM.fail

/-- A sequence of instructions. -/
def execX : List XInstr → Frame → RM M.St Frame
  | [], f => pure f
  | i :: is, f => do
    let f' ← i.step f
    execX is f'
end

/-- An adaptor function over `XInstr`. -/
structure XFn where
  params : Nat
  locals : Nat := 0
  body : List XInstr
  deriving Repr, Inhabited

/-- Run an adaptor function; the results are the final stack, deepest first. -/
def XFn.run (fn : XFn) (args : List Flat) : RM M.St (List Flat) := do
  RM.check (args.length == fn.params)
  let f ← execX M fn.body ⟨args ++ List.replicate fn.locals (i32n 0), []⟩
  pure f.stack.reverse

/-- An `AFn` as an `XFn`. -/
def AFn.toX (fn : AFn) : XFn := ⟨fn.params, fn.locals, fn.body.map .base⟩

/-- An adaptor module over `XInstr`. -/
structure XMod where
  funcs : List (String × XFn)
  deriving Repr, Inhabited

/-- Canonical options that differ between FFI styles. -/
inductive StrEnc where
  | utf8
  | utf16
  /-- `latin1+utf16`. -/
  | latin1Utf16
  deriving Repr, Inhabited, DecidableEq

/-- A `canon lift` export with its string encoding. -/
structure XLift where
  sig : Sig
  callee : CRef
  realloc : CRef
  enc : StrEnc := .utf8
  deriving Repr, Inhabited, DecidableEq

/-- A wrapper-style component with an `XMod` adaptor. -/
structure XComp where
  adaptor : XMod := ⟨[]⟩
  lifts : List XLift
  deriving Repr, Inhabited

/-- A `canon lift` semantics: given the encoding, `realloc` and callee. -/
abbrev LiftSem (M : CoreInst) :=
  StrEnc → (List Flat → RM M.St (List Flat)) → (List Flat → RM M.St (List Flat)) → Sig →
    List PVal → RM M.St (Option PVal)

namespace XComp

/-- Calling a core function of the component. -/
def callRef (c : XComp) : CRef → List Flat → RM M.St (List Flat)
  | .core n, xs => M.call n xs
  | .adapt i, xs =>
    match c.adaptor.funcs[i]? with
    | some (_, fn) => fn.run M xs
    | none => RM.fail

/-- The behaviour of export `name`, for a given `canon lift` semantics. -/
def callExportWith (lift : LiftSem M) (c : XComp) (name : String) (vs : List PVal) :
    RM M.St (Option PVal) :=
  match c.lifts.find? (·.sig.name == name) with
  | some l => lift l.enc (c.callRef M l.realloc) (c.callRef M l.callee) l.sig vs
  | none => RM.fail

end XComp

end Silmaril.Wasm.Jco
