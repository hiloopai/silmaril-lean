module

public import Silmaril.Machine.RegisterFile

/-! # AMD64Scalar: the I1/I64, register-only VEX block profile -/

@[expose] public section

namespace Silmaril.Machine.Vex

abbrev Word := BitVec 64

namespace Raw

inductive Expr where
  | const (width value : Nat)
  | get (offset width : Nat)
  | tmp (id : Nat)
  | op (name : String) (args : List Expr)
  | opaque (tag text : String)
  deriving BEq, Repr

inductive Stmt where
  | mark (address length delta : Nat)
  | wrTmp (id : Nat) (value : Expr)
  | put (offset : Nat) (value : Expr)
  | exit (guard : Expr) (target : Nat) (jumpKind : String) (ipOffset : Nat)
  | opaque (tag text : String)
  deriving BEq, Repr

structure Block where
  address : Nat
  types : List Nat
  statements : List Stmt
  next : Expr
  jumpKind : String := "Ijk_Boring"
  ipOffset : Nat := 184
  deriving BEq, Repr

end Raw

namespace AMD64Scalar

inductive Reg where
  | rax | rdi | rsi
  deriving DecidableEq, Repr

inductive Slot where
  | gpr (reg : Reg)
  | rip | ccOp | ccDep1 | ccDep2 | ccNdep
  deriving DecidableEq, Repr

def Slot.offset : Slot → Nat
  | .gpr .rax => 16
  | .gpr .rsi => 64
  | .gpr .rdi => 72
  | .ccOp => 144
  | .ccDep1 => 152
  | .ccDep2 => 160
  | .ccNdep => 168
  | .rip => 184

def Slot.ofOffset : Nat → Option Slot
  | 16 => some (.gpr .rax)
  | 64 => some (.gpr .rsi)
  | 72 => some (.gpr .rdi)
  | 144 => some .ccOp
  | 152 => some .ccDep1
  | 160 => some .ccDep2
  | 168 => some .ccNdep
  | 184 => some .rip
  | _ => none

inductive Ty where
  | i1 | i64
  deriving DecidableEq, Repr

def Ty.width : Ty → Nat
  | .i1 => 1
  | .i64 => 64

def Ty.ofWidth : Nat → Option Ty
  | 1 => some .i1
  | 64 => some .i64
  | _ => none

abbrev Scope := List (Nat × Ty)

/-- A use proves that the named temporary is already bound at the indicated type. -/
inductive Ref : Scope → Ty → Type where
  | here {ctx : Scope} {ty : Ty} (id : Nat) : Ref ((id, ty) :: ctx) ty
  | there {ctx : Scope} {ty : Ty} (head : Nat × Ty) : Ref ctx ty → Ref (head :: ctx) ty

def Ref.id {ctx : Scope} {ty : Ty} : Ref ctx ty → Nat
  | .here id => id
  | .there _ ref => ref.id

def Ref.lookup (id : Nat) : (ctx : Scope) → Option (Σ ty, Ref ctx ty)
  | [] => none
  | (name, ty) :: rest =>
    if id = name then some ⟨ty, .here name⟩
    else (lookup id rest).map fun ⟨found, ref⟩ => ⟨found, .there (name, ty) ref⟩

inductive Expr (ctx : Scope) : Ty → Type where
  | flag (value : Bool) : Expr ctx .i1
  | word (value : Word) : Expr ctx .i64
  | get (slot : Slot) : Expr ctx .i64
  | tmp {ty : Ty} (ref : Ref ctx ty) : Expr ctx ty
  | add (lhs rhs : Expr ctx .i64) : Expr ctx .i64
  | eq (lhs rhs : Expr ctx .i64) : Expr ctx .i1
  | widen (arg : Expr ctx .i1) : Expr ctx .i64
  | low (arg : Expr ctx .i64) : Expr ctx .i1

def Expr.erase {ctx : Scope} {ty : Ty} : Expr ctx ty → Raw.Expr
  | .flag value => .const 1 (if value then 1 else 0)
  | .word value => .const 64 value.toNat
  | .get slot => .get slot.offset 64
  | .tmp ref => .tmp ref.id
  | .add lhs rhs => .op "Iop_Add64" [lhs.erase, rhs.erase]
  | .eq lhs rhs => .op "Iop_CmpEQ64" [lhs.erase, rhs.erase]
  | .widen arg => .op "Iop_1Uto64" [arg.erase]
  | .low arg => .op "Iop_64to1" [arg.erase]

structure Mark where
  address : Word
  length : Nat
  deriving DecidableEq, Repr

inductive Code : Scope → Type where
  | jump {ctx : Scope} (target : Word) : Code ctx
  | branch {ctx : Scope} (guard : Expr ctx .i1) (taken next : Word) : Code ctx
  | mark {ctx : Scope} (marker : Mark) (rest : Code ctx) : Code ctx
  | put {ctx : Scope} (slot : Slot) (value : Expr ctx .i64) (rest : Code ctx) : Code ctx
  | bind {ctx : Scope} {ty : Ty} (id : Nat) (value : Expr ctx ty)
      (rest : Code ((id, ty) :: ctx)) : Code ctx

structure Block where
  address : Word
  types : List Ty
  code : Code []

def Code.erase {ctx : Scope} : Code ctx → List Raw.Stmt × Word
  | .jump target => ([], target)
  | .branch guard taken next => ([.exit guard.erase taken.toNat "Ijk_Boring" Slot.rip.offset], next)
  | .mark marker rest =>
    let (statements, next) := rest.erase
    (.mark marker.address.toNat marker.length 0 :: statements, next)
  | .put slot value rest =>
    let (statements, next) := rest.erase
    (.put slot.offset value.erase :: statements, next)
  | .bind id value rest =>
    let (statements, next) := rest.erase
    (.wrTmp id value.erase :: statements, next)

/-- Embed this subset into the broader, untyped tree; this is not a serializer
for arbitrary LibVEX objects. -/
def Block.erase (block : Block) : Raw.Block :=
  let (statements, next) := block.code.erase
  ⟨block.address.toNat, block.types.map Ty.width, statements, .const 64 next.toNat,
    "Ijk_Boring", Slot.rip.offset⟩

inductive Error where
  | width (width : Nat)
  | offset (offset : Nat)
  | literal (width value : Nat)
  | unbound (id : Nat)
  | undeclared (id : Nat)
  | redefined (id : Nat)
  | mismatch (expected actual : Ty)
  | operator (name : String) (arity : Nat)
  | extension (tag : String)
  | marker (address length delta : Nat)
  | control (jumpKind : String) (ipOffset : Nat)
  | indirectNext
  | nonfinalExit
  deriving DecidableEq, Repr

def checkWord (value : Nat) : Except Error Word :=
  if value < 2^64 then .ok (BitVec.ofNat 64 value) else .error (.literal 64 value)

def requireSome {error value : Type} (failure : error) : Option value → Except error value
  | some result => .ok result
  | none => .error failure

def checkSlot (offset : Nat) : Except Error Slot :=
  requireSome (.offset offset) (Slot.ofOffset offset)

def expect {ctx : Scope} (ty : Ty) (value : Σ actual, Expr ctx actual) :
    Except Error (Expr ctx ty) :=
  if h : value.1 = ty then .ok (h ▸ value.2) else .error (.mismatch ty value.1)

def checkExpr (ctx : Scope) : Raw.Expr → Except Error (Σ ty, Expr ctx ty)
  | .const 1 value =>
    if value < 2 then .ok ⟨.i1, .flag (value == 1)⟩ else .error (.literal 1 value)
  | .const 64 value => return ⟨.i64, .word (← checkWord value)⟩
  | .const width _ => .error (.width width)
  | .get offset 64 => return ⟨.i64, .get (← checkSlot offset)⟩
  | .get _ width => .error (.width width)
  | .tmp id => do
    let ⟨ty, ref⟩ ← requireSome (.unbound id) (Ref.lookup id ctx)
    return ⟨ty, .tmp ref⟩
  | .op "Iop_Add64" [lhs, rhs] => do
    return ⟨.i64, .add (← expect .i64 (← checkExpr ctx lhs)) (← expect .i64 (← checkExpr ctx rhs))⟩
  | .op "Iop_CmpEQ64" [lhs, rhs] => do
    return ⟨.i1, .eq (← expect .i64 (← checkExpr ctx lhs)) (← expect .i64 (← checkExpr ctx rhs))⟩
  | .op "Iop_1Uto64" [arg] => return ⟨.i64, .widen (← expect .i1 (← checkExpr ctx arg))⟩
  | .op "Iop_64to1" [arg] => return ⟨.i1, .low (← expect .i64 (← checkExpr ctx arg))⟩
  | .op name args => .error (.operator name args.length)
  | .opaque tag _ => .error (.extension tag)

def checkControl (jumpKind : String) (ipOffset : Nat) : Except Error Unit :=
  if jumpKind == "Ijk_Boring" && ipOffset == Slot.rip.offset then .ok ()
  else .error (.control jumpKind ipOffset)

def checkCode (types : List Ty) (next : Word) (ctx : Scope) :
    List Raw.Stmt → Except Error (Code ctx)
  | [] => .ok (.jump next)
  | [.exit guard target jumpKind ipOffset] => do
    checkControl jumpKind ipOffset
    return .branch (← expect .i1 (← checkExpr ctx guard)) (← checkWord target) next
  | .exit .. :: _ => .error .nonfinalExit
  | .mark address length delta :: rest => do
    if delta != 0 || length == 0 || length > 15 then throw (.marker address length delta)
    return .mark ⟨← checkWord address, length⟩ (← checkCode types next ctx rest)
  | .put offset value :: rest => do
    return .put (← checkSlot offset) (← expect .i64 (← checkExpr ctx value))
      (← checkCode types next ctx rest)
  | .wrTmp id value :: rest => do
    let ty ← requireSome (.undeclared id) types[id]?
    if (Ref.lookup id ctx).isSome then throw (.redefined id)
    return .bind id (← expect ty (← checkExpr ctx value)) (← checkCode types next ((id, ty) :: ctx) rest)
  | .opaque tag _ :: _ => .error (.extension tag)
termination_by structural statements => statements

def check (block : Raw.Block) : Except Error Block := do
  let address ← checkWord block.address
  let types ← block.types.mapM fun width => requireSome (.width width) (Ty.ofWidth width)
  checkControl block.jumpKind block.ipOffset
  let next ← match block.next with
    | .const 64 value => checkWord value
    | _ => throw .indirectNext
  return ⟨address, types, ← checkCode types next [] block.statements⟩

def Code.marks {ctx : Scope} : Code ctx → List Mark
  | .jump _ | .branch .. => []
  | .mark marker rest => marker :: rest.marks
  | .put _ _ rest | .bind _ _ rest => rest.marks

def Code.targets {ctx : Scope} : Code ctx → List Word
  | .jump target => [target]
  | .branch _ taken next => [taken, next]
  | .mark _ rest | .put _ _ rest | .bind _ _ rest => rest.targets

end AMD64Scalar
end Silmaril.Machine.Vex
