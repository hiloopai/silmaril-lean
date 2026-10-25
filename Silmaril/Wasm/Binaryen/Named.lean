module
/- Portions derived from Binaryen version_133, src/wasm.h.
Copyright 2015 WebAssembly Community Group participants.
Licensed under Apache-2.0; see NOTICES/Binaryen/LICENSE.txt.
Modified as a scoped Lean transcription with original definitions/proofs.
-/
public import Silmaril.Wasm.Binaryen.Syntax

@[expose] public section

/-! # Binaryen-style IR, layer N: the named surface

A transcription of Binaryen's expression IR (`src/wasm.h`, version_133) for the
first profile (`Binaryen/Profile.lean`): named labels, nameless *implicit*
blocks, the `unreachable` bottom type, `br`/`br_if` with optional value and
condition, `br_table` (`Switch`), direct calls, locals, globals, integer
constants and operators, `select`, `drop`, `return`, `nop`, `unreachable`.

The meaning of an `NExpr` is the meaning of its resolution
(`Binaryen/Resolve.lean`) to layer D, i.e. of the lowering of that. Passes stated
on layer N (inlining's exact Binaryen shape, merge's renaming) reuse every D
theorem through `resolve`.

| Binaryen (`src/wasm.h`) | `NExpr` |
|---|---|
| `Block` (name may be empty) | `block (label : Option Name) body ty` |
| `Loop` | `loop label body ty` |
| `If` | `if_ c t e ty` |
| `Break` (`br`, `br_if` when `condition`) | `br l value cond` |
| `Switch` | `switch ls d value c` |
| `Call` | `call f args` (`isReturn` excluded: no tail calls in v1) |
| `LocalGet`/`LocalSet` (tee iff typed) | `localGet i` / `localSet i v tee` |
| `GlobalGet`/`GlobalSet` | `globalGet g` / `globalSet g v` |
| `Const`/`Unary`/`Binary` | `const` / `unary` / `binary` |
| `Select`/`Drop`/`Return`/`Nop`/`Unreachable` | same names |
-/

namespace Silmaril.Wasm.Binaryen

/-- Binaryen names (`wasm::Name`). -/
abbrev Name := String

/-- Binaryen's `Type` for the profile: `none`, the bottom type `unreachable`, or a
single value type. Tuples are excluded in v1. -/
inductive NTy where
  | none
  | unreachable
  | val (t : ValType)
  deriving DecidableEq, Repr, Inhabited

namespace NTy

/-- The Core block type a construct of type `ty` is written with
(`BinaryenIRWriter`, `src/wasm-stack.h`: an unreachable-typed scope is emitted
with the empty block type). -/
def blockType : NTy → BlockType
  | .val t => .value t
  | _ => .empty

/-- Binaryen subtyping on the profile: `unreachable` is the bottom element. -/
def Sub : NTy → NTy → Prop
  | .unreachable, _ => True
  | a, b => a = b

/-- Least upper bound, `Type::getLeastUpperBound` restricted to the profile. -/
def lub : NTy → NTy → Option NTy
  | .unreachable, b => some b
  | a, .unreachable => some a
  | a, b => if a = b then some a else Option.none

end NTy

/-- Integer literals (`Literal`). -/
inductive Lit where
  | i32 (b : BitVec 32)
  | i64 (b : BitVec 64)
  deriving DecidableEq, Repr

/-- Unary operators of the profile (`UnaryOp`). -/
inductive UnOp where
  | int (t : IntType) (op : IntUnOp)
  | eqz (t : IntType)
  deriving DecidableEq, Repr

/-- Binary operators of the profile (`BinaryOp`). -/
inductive BinOp where
  | int (t : IntType) (op : IntBinOp)
  | rel (t : IntType) (op : IntRelOp)
  deriving DecidableEq, Repr

def Lit.ty : Lit → ValType
  | .i32 _ => .i32
  | .i64 _ => .i64

def Lit.instr : Lit → Instr
  | .i32 b => .intConst .i32 b
  | .i64 b => .intConst .i64 b

def UnOp.instr : UnOp → Instr
  | .int t op => .intUnOp t op
  | .eqz t => .intTestOp t .eqz

def BinOp.instr : BinOp → Instr
  | .int t op => .intBinOp t op
  | .rel t op => .intRelOp t op

def intValType : IntType → ValType
  | .i32 => .i32
  | .i64 => .i64

def UnOp.argTy : UnOp → ValType
  | .int t _ | .eqz t => intValType t

def UnOp.resTy : UnOp → ValType
  | .int t _ => intValType t
  | .eqz _ => .i32

def BinOp.argTy : BinOp → ValType
  | .int t _ | .rel t _ => intValType t

def BinOp.resTy : BinOp → ValType
  | .int t _ => intValType t
  | .rel _ _ => .i32

/-- **Layer N expressions** (Binaryen's `Expression`, profile fragment). `ty` fields
are Binaryen's `Expression::type` annotations, maintained by `refinalize`. -/
inductive NExpr where
  /-- `Block`; `none` is an implicit (unnamed) block, which resolution splices. -/
  | block (label : Option Name) (body : List NExpr) (ty : NTy)
  | loop (label : Option Name) (body : NExpr) (ty : NTy)
  | if_ (c t : NExpr) (e : Option NExpr) (ty : NTy)
  /-- `Break`: `br l`, with a value and, if `cond` is present, `br_if`. -/
  | br (l : Name) (value cond : Option NExpr)
  | switch (ls : List Name) (d : Name) (value : Option NExpr) (c : NExpr)
  | call (f : Name) (args : List NExpr)
  | localGet (i : Nat)
  | localSet (i : Nat) (v : NExpr) (tee : Bool)
  | globalGet (g : Name)
  | globalSet (g : Name) (v : NExpr)
  | const (c : Lit)
  | unary (op : UnOp) (e : NExpr)
  | binary (op : BinOp) (a b : NExpr)
  | select (a b c : NExpr)
  | drop (e : NExpr)
  | return_ (v : Option NExpr)
  | nop
  | unreachable
  deriving Repr

instance : Inhabited NExpr := ⟨.nop⟩

/-- A defined function (`Function`): signature, extra locals ("vars"), body. -/
structure NFunc where
  type : TypeIdx
  params : List ValType
  results : List ValType
  vars : List ValType
  body : NExpr
  deriving Repr

/-- An imported function (`Function` with `module`/`base`). -/
structure NImport where
  module : String
  base : String
  type : TypeIdx
  params : List ValType
  results : List ValType
  deriving Repr

/-- A defined global. -/
structure NGlobal where
  type : GlobalType
  init : NExpr
  deriving Repr

/-- Export kinds of the profile. -/
inductive NExportKind where
  | func
  | global
  deriving DecidableEq, Repr

/-- An export: external name, kind, internal name. -/
structure NExport where
  name : String
  kind : NExportKind
  internal : Name
  deriving Repr

/-- **Layer N modules** (Binaryen's `Module`, profile fragment). Function imports
come first in the function index space, as in the binary format. -/
structure NModule where
  types : List RecType := []
  imports : List (Name × NImport) := []
  funcs : List (Name × NFunc) := []
  globals : List (Name × NGlobal) := []
  exports : List NExport := []
  start : Option Name := none
  deriving Repr

mutual
/-- Labels bound anywhere in an expression. -/
def NExpr.boundLabels : NExpr → List Name
  | .block l body _ => l.toList ++ NExpr.boundLabelsList body
  | .loop l body _ => l.toList ++ NExpr.boundLabels body
  | .if_ c t e _ => NExpr.boundLabels c ++ NExpr.boundLabels t ++ NExpr.boundLabelsOpt e
  | .br _ v c => NExpr.boundLabelsOpt v ++ NExpr.boundLabelsOpt c
  | .switch _ _ v c => NExpr.boundLabelsOpt v ++ NExpr.boundLabels c
  | .call _ args => NExpr.boundLabelsList args
  | .localSet _ v _ | .globalSet _ v | .unary _ v | .drop v => NExpr.boundLabels v
  | .binary _ a b => NExpr.boundLabels a ++ NExpr.boundLabels b
  | .select a b c => NExpr.boundLabels a ++ NExpr.boundLabels b ++ NExpr.boundLabels c
  | .return_ v => NExpr.boundLabelsOpt v
  | .localGet _ | .globalGet _ | .const _ | .nop | .unreachable => []
/-- `boundLabels` on a list. -/
def NExpr.boundLabelsList : List NExpr → List Name
  | [] => []
  | e :: es => NExpr.boundLabels e ++ NExpr.boundLabelsList es
/-- `boundLabels` on an optional child. -/
def NExpr.boundLabelsOpt : Option NExpr → List Name
  | none => []
  | some e => NExpr.boundLabels e
end

mutual
/-- Labels used by a branch and not bound inside the expression. -/
def NExpr.freeLabels : NExpr → List Name
  | .block l body _ => (NExpr.freeLabelsList body).filter (fun n => some n != l)
  | .loop l body _ => (NExpr.freeLabels body).filter (fun n => some n != l)
  | .if_ c t e _ => NExpr.freeLabels c ++ NExpr.freeLabels t ++ NExpr.freeLabelsOpt e
  | .br l v c => l :: (NExpr.freeLabelsOpt v ++ NExpr.freeLabelsOpt c)
  | .switch ls d v c => ls ++ d :: (NExpr.freeLabelsOpt v ++ NExpr.freeLabels c)
  | .call _ args => NExpr.freeLabelsList args
  | .localSet _ v _ | .globalSet _ v | .unary _ v | .drop v => NExpr.freeLabels v
  | .binary _ a b => NExpr.freeLabels a ++ NExpr.freeLabels b
  | .select a b c => NExpr.freeLabels a ++ NExpr.freeLabels b ++ NExpr.freeLabels c
  | .return_ v => NExpr.freeLabelsOpt v
  | .localGet _ | .globalGet _ | .const _ | .nop | .unreachable => []
/-- `freeLabels` on a list. -/
def NExpr.freeLabelsList : List NExpr → List Name
  | [] => []
  | e :: es => NExpr.freeLabels e ++ NExpr.freeLabelsList es
/-- `freeLabels` on an optional child. -/
def NExpr.freeLabelsOpt : Option NExpr → List Name
  | none => []
  | some e => NExpr.freeLabels e
end

mutual
/-- Rename every label (binders and uses) along `σ`. -/
def NExpr.renameLabels (σ : Name → Name) : NExpr → NExpr
  | .block l body ty => .block (l.map σ) (NExpr.renameLabelsList σ body) ty
  | .loop l body ty => .loop (l.map σ) (NExpr.renameLabels σ body) ty
  | .if_ c t e ty =>
      .if_ (NExpr.renameLabels σ c) (NExpr.renameLabels σ t) (NExpr.renameLabelsOpt σ e) ty
  | .br l v c => .br (σ l) (NExpr.renameLabelsOpt σ v) (NExpr.renameLabelsOpt σ c)
  | .switch ls d v c =>
      .switch (ls.map σ) (σ d) (NExpr.renameLabelsOpt σ v) (NExpr.renameLabels σ c)
  | .call f args => .call f (NExpr.renameLabelsList σ args)
  | .localSet i v tee => .localSet i (NExpr.renameLabels σ v) tee
  | .globalSet g v => .globalSet g (NExpr.renameLabels σ v)
  | .unary op v => .unary op (NExpr.renameLabels σ v)
  | .drop v => .drop (NExpr.renameLabels σ v)
  | .binary op a b => .binary op (NExpr.renameLabels σ a) (NExpr.renameLabels σ b)
  | .select a b c =>
      .select (NExpr.renameLabels σ a) (NExpr.renameLabels σ b) (NExpr.renameLabels σ c)
  | .return_ v => .return_ (NExpr.renameLabelsOpt σ v)
  | .localGet i => .localGet i
  | .globalGet g => .globalGet g
  | .const c => .const c
  | .nop => .nop
  | .unreachable => .unreachable
/-- `renameLabels` on a list. -/
def NExpr.renameLabelsList (σ : Name → Name) : List NExpr → List NExpr
  | [] => []
  | e :: es => NExpr.renameLabels σ e :: NExpr.renameLabelsList σ es
/-- `renameLabels` on an optional child. -/
def NExpr.renameLabelsOpt (σ : Name → Name) : Option NExpr → Option NExpr
  | none => none
  | some e => some (NExpr.renameLabels σ e)
end

end Silmaril.Wasm.Binaryen
