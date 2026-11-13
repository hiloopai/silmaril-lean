module

public import Silmaril.Wasm.Component.Binary.Encode.Defs
public import Silmaril.Wasm.Component.Iface.Defs

/-!
# `wasm-jco`: component binaries with the async built-ins, and small core modules

The verified component grammar (`Silmaril.Wasm.Component.Binary`) covers `canon lift`,
`canon lower` and the resource built-ins. A component that lifts async exports also defines
the 🔀 built-ins of the Canonical ABI (`task.return`, `stream.new`, `waitable-set.wait`, …).
This module adds them on the encoding side only:

* `Builtin`: the built-ins `wasm-jco` emits, with the opcodes of `Binary.md` (checked
  against `wasm-tools dump` of wit-component 0.262.0 output, see `tools/wasm-jco/tests`);
* `XSection`: a section of the verified grammar, or a `canon` section of built-ins;
* `XAst.encode`: the bytes. On an `XAst` without built-ins it is `Binary.Encode.ast`
  (`XAst.encode_toAst` in `Silmaril.Wasm.JcoTool.Emit.Thms`), so the round trip
  `Binary.parse_encode` applies to the output.

It also has a minimal core-module encoder (`CMod`) for the two helper modules of the
indirect-call pattern of wit-component (`shim` and `fixup`): a table of `funcref`s, functions
that `call_indirect` through it, and an active element segment that fills it.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool

open Silmaril.Parse.ByteParse (Bytes)
open Silmaril.Parse.ByteParse.Enc (u32 sized)
open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component (CoreFuncTy)
open Silmaril.Wasm (NumType)

/-! ## The async built-ins -/

/-- A Canonical ABI built-in (🔀), by its `canon` production. -/
inductive Builtin where
  | taskReturn (result : Option Silmaril.Wasm.Component.Binary.ValType) (opts : List CanonOpt)
  | taskCancel
  | backpressureInc
  | backpressureDec
  | contextGet (slot : Nat)
  | contextSet (slot : Nat)
  | threadYield (cancellable : Bool)
  | subtaskDrop
  | subtaskCancel (async : Bool)
  | streamNew (t : Nat)
  | streamRead (t : Nat) (opts : List CanonOpt)
  | streamWrite (t : Nat) (opts : List CanonOpt)
  | streamCancelRead (t : Nat) (async : Bool)
  | streamCancelWrite (t : Nat) (async : Bool)
  | streamDropReadable (t : Nat)
  | streamDropWritable (t : Nat)
  | futureNew (t : Nat)
  | futureRead (t : Nat) (opts : List CanonOpt)
  | futureWrite (t : Nat) (opts : List CanonOpt)
  | futureCancelRead (t : Nat) (async : Bool)
  | futureCancelWrite (t : Nat) (async : Bool)
  | futureDropReadable (t : Nat)
  | futureDropWritable (t : Nat)
  | waitableSetNew
  | waitableSetWait (cancellable : Bool) (mem : Nat)
  | waitableSetPoll (cancellable : Bool) (mem : Nat)
  | waitableSetDrop
  | waitableJoin
  | errorContextNew (opts : List CanonOpt)
  | errorContextDebugMessage (opts : List CanonOpt)
  | errorContextDrop
  deriving Repr, DecidableEq, Inhabited

namespace Builtin

def flag (b : Bool) : Bytes := if b then [0x01] else [0x00]

def withT (op : UInt8) (t : Nat) : Option Bytes := (op :: ·) <$> u32 t

def withTOpts (op : UInt8) (t : Nat) (opts : List CanonOpt) : Option Bytes := do
  let a ← u32 t
  let b ← Encode.vec Encode.canonOpt opts
  pure (op :: (a ++ b))

def withTFlag (op : UInt8) (t : Nat) (b : Bool) : Option Bytes := do
  let a ← u32 t
  pure (op :: (a ++ flag b))

/-- The bytes of a built-in. -/
def encode : Builtin → Option Bytes
  | .taskReturn r opts => do
    let a ← Encode.resultList r
    let b ← Encode.vec Encode.canonOpt opts
    pure (0x09 :: (a ++ b))
  | .taskCancel => some [0x05]
  | .backpressureInc => some [0x24]
  | .backpressureDec => some [0x25]
  | .contextGet i => (fun b => 0x0a :: 0x7f :: b) <$> u32 i
  | .contextSet i => (fun b => 0x0b :: 0x7f :: b) <$> u32 i
  | .threadYield c => some (0x0c :: flag c)
  | .subtaskDrop => some [0x0d]
  | .subtaskCancel a => some (0x06 :: flag a)
  | .streamNew t => withT 0x0e t
  | .streamRead t o => withTOpts 0x0f t o
  | .streamWrite t o => withTOpts 0x10 t o
  | .streamCancelRead t a => withTFlag 0x11 t a
  | .streamCancelWrite t a => withTFlag 0x12 t a
  | .streamDropReadable t => withT 0x13 t
  | .streamDropWritable t => withT 0x14 t
  | .futureNew t => withT 0x15 t
  | .futureRead t o => withTOpts 0x16 t o
  | .futureWrite t o => withTOpts 0x17 t o
  | .futureCancelRead t a => withTFlag 0x18 t a
  | .futureCancelWrite t a => withTFlag 0x19 t a
  | .futureDropReadable t => withT 0x1a t
  | .futureDropWritable t => withT 0x1b t
  | .waitableSetNew => some [0x1f]
  | .waitableSetWait c m => do
    let b ← u32 m
    pure (0x20 :: (flag c ++ b))
  | .waitableSetPoll c m => do
    let b ← u32 m
    pure (0x21 :: (flag c ++ b))
  | .waitableSetDrop => some [0x22]
  | .waitableJoin => some [0x23]
  | .errorContextNew o => (0x1c :: ·) <$> Encode.vec Encode.canonOpt o
  | .errorContextDebugMessage o => (0x1d :: ·) <$> Encode.vec Encode.canonOpt o
  | .errorContextDrop => some [0x1e]

end Builtin

/-! ## Sections with built-ins -/

/-- A section of an output component: one of the verified grammar, or a `canon` section of
built-ins. -/
inductive XSection where
  | sec (s : Section)
  | builtins (bs : List Builtin)

/-- An output component. -/
structure XAst where
  sections : List XSection

/-- The bytes of a section. -/
def XSection.encode : XSection → Option Bytes
  | .sec s => Encode.section_ s
  | .builtins bs => Encode.vecSection 0x08 Builtin.encode bs

/-- The bytes of the sections. -/
def XSection.encodeAll : List XSection → Option Bytes
  | [] => some []
  | s :: ss => do
    let a ← s.encode
    let b ← encodeAll ss
    pure (a ++ b)

/-- The bytes of an output component. -/
def XAst.encode (c : XAst) : Option ByteArray :=
  (XSection.encodeAll c.sections).map fun b => ⟨(preambleBytes ++ b).toArray⟩

/-- The sections of the verified grammar, when there are no built-ins. -/
def XSection.toSections : List XSection → Option (List Section)
  | [] => some []
  | .sec s :: ss => (s :: ·) <$> toSections ss
  | .builtins _ :: _ => none

/-- The component of the verified grammar, when there are no built-ins. -/
def XAst.toAst (c : XAst) : Option Ast := Ast.mk <$> XSection.toSections c.sections

/-- The core modules of an output component, in order. -/
def XAst.coreModules (c : XAst) : List ByteArray :=
  c.sections.filterMap fun
    | .sec (.coreModule b) => some b
    | _ => none

/-! ## Small core modules -/

/-- A core import of a helper module. -/
inductive CImport where
  | func (ty : Nat)
  | table (min max : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- A minimal core module: function types, imports, functions (type and body, without the
final `end`), one table, exports, a start function and active element segments of table 0. -/
structure CMod where
  types : List CoreFuncTy := []
  imports : List (String × String × CImport) := []
  funcs : List (Nat × Bytes) := []
  table : Option (Nat × Nat) := none
  /-- Name, kind (`0x00` func, `0x01` table) and index. -/
  exports : List (String × UInt8 × Nat) := []
  start : Option Nat := none
  /-- Offset and function indices. -/
  elems : List (Nat × List Nat) := []
  deriving Repr, Inhabited

namespace CMod

def numType : NumType → UInt8
  | .int .i32 => 0x7f
  | .int .i64 => 0x7e
  | .float .f32 => 0x7d
  | .float .f64 => 0x7c

def funcType (t : CoreFuncTy) : Option Bytes := do
  let a ← Encode.vec (fun x => some [numType x]) t.params
  let b ← Encode.vec (fun x => some [numType x]) t.results
  pure (0x60 :: (a ++ b))

def limits (min max : Nat) : Option Bytes := do
  let a ← u32 min
  let b ← u32 max
  pure (0x01 :: (a ++ b))

def import_ (i : String × String × CImport) : Option Bytes := do
  let a ← Encode.name i.1
  let b ← Encode.name i.2.1
  let c ← match i.2.2 with
    | .func t => (0x00 :: ·) <$> u32 t
    | .table mn mx => (fun l => 0x01 :: 0x70 :: l) <$> limits mn mx
  pure (a ++ b ++ c)

def export_ (e : String × UInt8 × Nat) : Option Bytes := do
  let a ← Encode.name e.1
  let b ← u32 e.2.2
  pure (a ++ e.2.1 :: b)

/-- `i32.const n` (signed LEB128; `n < 2^31`). -/
def i32Const (n : Nat) : Option Bytes := (0x41 :: ·) <$> Silmaril.Parse.ByteParse.Enc.sN 32 (n : Int)

/-- An active segment of table 0 in the form `4:u32 e:expr el*:vec(expr)` with `ref.func`
initializers, whose type is `funcref` (the legacy form `0` has type `(ref func)` in Core 3.0,
which the 3.0 → Lime compiler does not take as Lime1). -/
def elem (e : Nat × List Nat) : Option Bytes := do
  let o ← i32Const e.1
  let fs ← Encode.vec (fun f => (fun b => 0xd2 :: (b ++ [0x0b])) <$> u32 f) e.2
  pure (0x04 :: (o ++ [0x0b] ++ fs))

def code (f : Nat × Bytes) : Option Bytes := sized (0x00 :: (f.2 ++ [0x0b]))

def section_ (id : UInt8) (body : Bytes) : Option Bytes := (id :: ·) <$> sized body

def vecSec {α : Type} (id : UInt8) (f : α → Option Bytes) (xs : List α) : Option Bytes :=
  if xs.isEmpty then some [] else do
    let v ← Encode.vec f xs
    section_ id v

/-- The bytes of the module. -/
def encode (m : CMod) : Option ByteArray := do
  let ty ← vecSec 0x01 funcType m.types
  let im ← vecSec 0x02 import_ m.imports
  let fn ← vecSec 0x03 (fun f => u32 f.1) m.funcs
  let tb ← match m.table with
    | none => some []
    | some (mn, mx) => do
      let l ← limits mn mx
      section_ 0x04 (0x01 :: 0x70 :: l)
  let ex ← vecSec 0x07 export_ m.exports
  let st ← match m.start with
    | none => some []
    | some f => do
      let b ← u32 f
      section_ 0x08 b
  let el ← vecSec 0x09 elem m.elems
  let cd ← vecSec 0x0a code m.funcs
  let body := [0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00] ++
    ty ++ im ++ fn ++ tb ++ ex ++ st ++ el ++ cd
  pure ⟨body.toArray⟩

/-- `local.get i`. -/
def localGet (i : Nat) : Option Bytes := (0x20 :: ·) <$> u32 i

/-- The body of a trampoline: pass the parameters on to table slot `slot` at type `ty`. -/
def trampoline (nparams slot ty : Nat) : Option Bytes := do
  let ls ← Silmaril.Parse.ByteParse.Enc.list localGet (List.range nparams)
  let c ← i32Const slot
  let t ← u32 ty
  pure (ls ++ c ++ (0x11 :: t) ++ [0x00])

end CMod

end Silmaril.Wasm.JcoTool
