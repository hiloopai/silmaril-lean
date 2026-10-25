module

public import Silmaril.Wasm.Types

/-!
# WebAssembly 2.0 types

Transcribed from the official SpecTec source
`specification/wasm-2.0/1-syntax.spectec` at WebAssembly/spec revision
`608711107b7f1edb13efd57b7d79b49477462d36` (see `specs/wasm/core-2.0.json`).
Line references of the form `1-syntax:NN` point into that file.

Wasm 2.0 adds reference types (`funcref`/`externref`), a 128-bit vector type,
and multiple tables to the 1.0 type system. It has no subtyping between
concrete types, no recursive types and no heap-type hierarchy: `reftype` is a
two-element enumeration.

The `BOT` alternative of `1-syntax:139` is *not* part of this syntactic
`ValType`. It is a validation-only type, so it lives in
`Silmaril.Wasm.V2.Validation.CValType`, mirroring the Core 3.0 layer. No module
can mention it: the binary format has no production for it and `Func_ok`
(`6-typing:595`) explicitly excludes it from local types.

The primitive enumerations `IntType`, `FloatType`, `NumType`, `VecType`,
`Mutability` and the index family `Idx` are shared with the other Wasm layers
(`Silmaril.Wasm.Types`); reusing them is a representation choice, not a
semantic one.
-/

@[expose] public section

namespace Silmaril.Wasm.V2

/-! ## Value types -/

/-- `reftype ::= FUNCREF | EXTERNREF` (`1-syntax:135`). -/
inductive RefType where
  | funcref
  | externref
  deriving DecidableEq, Repr

/-- `valtype ::= numtype | vectype | reftype` (`1-syntax:138`, without `BOT`). -/
inductive ValType where
  | num (type : NumType)
  | vec (type : VecType)
  | ref (type : RefType)
  deriving DecidableEq, Repr

namespace ValType

def i32 : ValType := .num (.int .i32)
def i64 : ValType := .num (.int .i64)
def f32 : ValType := .num (.float .f32)
def f64 : ValType := .num (.float .f64)
def v128 : ValType := .vec .v128
def funcref : ValType := .ref .funcref
def externref : ValType := .ref .externref

end ValType

/-- `resulttype ::= list(valtype)` (`1-syntax:146`). The length bound `< 2^32`
of `list` (`1-syntax:6`) is a validation-time condition on concrete modules and
is not imposed on the Lean type. -/
abbrev ResultType := List ValType

/-! ## Packed and lane types

`packtype ::= I8 | I16` (`1-syntax:152`) and `lanetype ::= numtype | packtype`
(`1-syntax:153`) are the shared `Silmaril.Wasm.PackType` and the lane types of
`Silmaril.Wasm.IntShape`/`FloatShape`. `$unpack` (`2-syntax-aux:28-30`) maps a
`lanetype` to the `numtype` it unpacks to; its lift to shapes, `$shunpack`
(`2-syntax-aux:44-45`), is `Silmaril.Wasm.Shape.unpacked`. -/

/-! ## External types -/

/-- `limits ::= `[u32 .. u32?]` (`1-syntax:164`). Both bounds are `u32`; a 2.0
memory or table never uses 64-bit limits. -/
structure Limits where
  min : Fin (2 ^ 32)
  max : Option (Fin (2 ^ 32))
  deriving DecidableEq, Repr

/-- `globaltype ::= mut valtype` (`1-syntax:167`). -/
structure GlobalType where
  mutability : Mutability
  value : ValType
  deriving DecidableEq, Repr

/-- `functype ::= resulttype -> resulttype` (`1-syntax:169`). 2.0 allows
multiple results. -/
structure FuncType where
  params : ResultType
  results : ResultType
  deriving DecidableEq, Repr

/-- `tabletype ::= limits reftype` (`1-syntax:171`). -/
structure TableType where
  limits : Limits
  element : RefType
  deriving DecidableEq, Repr

/-- `memtype ::= limits PAGE` (`1-syntax:173`). The `PAGE` marker carries no
information. -/
structure MemoryType where
  limits : Limits
  deriving DecidableEq, Repr

/-- `elemtype ::= reftype` (`1-syntax:175`). -/
abbrev ElemType := RefType

/-- `datatype ::= OK` (`1-syntax:177`). -/
abbrev DataType := Unit

/-- `externtype ::= FUNC functype | GLOBAL globaltype | TABLE tabletype |
MEM memtype` (`1-syntax:179`). -/
inductive ExternType where
  | func (type : FuncType)
  | global (type : GlobalType)
  | table (type : TableType)
  | memory (type : MemoryType)
  deriving DecidableEq, Repr

/-! ## Projections

`$funcsxt`, `$globalsxt`, `$tablesxt`, `$memsxt` (`2-syntax-aux:51-70`). -/

namespace ExternType

def funcs (xs : List ExternType) : List FuncType :=
  xs.filterMap fun | .func t => some t | _ => none

def globals (xs : List ExternType) : List GlobalType :=
  xs.filterMap fun | .global t => some t | _ => none

def tables (xs : List ExternType) : List TableType :=
  xs.filterMap fun | .table t => some t | _ => none

def mems (xs : List ExternType) : List MemoryType :=
  xs.filterMap fun | .memory t => some t | _ => none

end ExternType

/-! ## Shapes

`shape ::= lanetype X dim` (`1-syntax:319`). SpecTec's `dim` ranges over
`1 | 2 | 4 | 8 | 16` independently of the lane type, so `shape` admits
combinations such as `I8 X 2` that no instruction can mention; SpecTec itself
records this as `;; TODO: missing constraints` (`1-syntax:472`). We reuse the
shared six canonical shapes `Silmaril.Wasm.IntShape`, `Silmaril.Wasm.FloatShape`
and `Silmaril.Wasm.Shape`, as the Core 3.0 layer does. Every shape reachable
from the binary format (`A-binary`) is one of these, so this restricts no
program; it is recorded as a deviation in `Silmaril.Wasm.V2.Validation`.

`$lanetype` (`2-syntax-aux:36`), `$dim` (`2-syntax-aux:39`), `$lsize`
(`1-syntax:210`, `|Lnn|`) and `$shunpack` (`2-syntax-aux:44-45`) are the shared
`IntShape.laneWidth`/`lanes`, `FloatShape.laneWidth`/`lanes` and
`Shape.unpacked`. -/

end Silmaril.Wasm.V2
