module

public import Silmaril.Machine.Vex.Scalar.Defs

/-! # Compositional guest execution and first-order observation plans -/

@[expose] public section

namespace Silmaril.Machine.Vex.AMD64Scalar

/-- The explicitly projected machine state. `rip` is a block boundary, not a trace. -/
structure State (value flag : Type) where
  rax : value
  rdi : value
  rsi : value
  zf : flag
  rip : Word
  deriving DecidableEq, Repr

abbrev Input := State Word Bool

def State.read {value flag : Type} (state : State value flag) : Reg → value
  | .rax => state.rax
  | .rdi => state.rdi
  | .rsi => state.rsi

/-- A tiny second IR: expressions over entry observations, with no VEX temporaries,
guest offsets, or lazy flag recipes. Predicate results use the words 0 and 1. -/
inductive Term where
  | const (value : Word)
  | reg (reg : Reg)
  | initialZF
  | initialFlags
  | add (lhs rhs : Term)
  | eq (lhs rhs : Term)
  | bit (index : Nat) (value : Term)
  deriving DecidableEq, Repr

def flagWord (value : Bool) : Word := if value then 1 else 0

def Term.eval (input : Input) : Term → Word
  | .const value => value
  | .reg name => input.read name
  | .initialZF => flagWord input.zf
  | .initialFlags => if input.zf then 64 else 0
  | .add lhs rhs => lhs.eval input + rhs.eval input
  | .eq lhs rhs => flagWord (lhs.eval input == rhs.eval input)
  | .bit index term => flagWord ((term.eval input).getLsbD index)

def Term.test (input : Input) (term : Term) : Bool := (term.eval input).getLsbD 0

/-- Normalize only the bit projections needed by VEX's I1 casts and COPY recipe. -/
def Term.selectBit : Nat → Term → Term
  | index, .const value => .const (flagWord (value.getLsbD index))
  | index, .eq lhs rhs => if index = 0 then .eq lhs rhs else .bit index (.eq lhs rhs)
  | index, .initialZF => if index = 0 then .initialZF else .bit index .initialZF
  | index, .initialFlags => if index = 6 then .initialZF else .bit index .initialFlags
  | index, term => .bit index term

inductive Next (flag : Type) where
  | jump (target : Word)
  | branch (guard : flag) (taken next : Word)
  deriving DecidableEq, Repr

def Next.target : Next Bool → Word
  | .jump target => target
  | .branch guard taken next => if guard then taken else next

def Next.map {flag flag' : Type} (f : flag → flag') : Next flag → Next flag'
  | .jump target => .jump target
  | .branch guard taken next => .branch (f guard) taken next

structure Plan where
  rax : Term
  rdi : Term
  rsi : Term
  zf : Term
  next : Next Term
  deriving DecidableEq, Repr

def Plan.eval (input : Input) (plan : Plan) : Input :=
  ⟨plan.rax.eval input, plan.rdi.eval input, plan.rsi.eval input, plan.zf.test input,
    (plan.next.map (Term.test input)).target⟩

abbrev Guest := RegisterFile Slot Term

def entryGuest (rip : Word) : Guest
  | .gpr name => .reg name
  | .rip => .const rip
  | .ccDep1 => .initialFlags
  | _ => .const 0

def Env (ctx : Scope) := {ty : Ty} → Ref ctx ty → Term

def Env.nil : Env [] := fun ref => nomatch ref

def Env.cons {ctx : Scope} {id : Nat} {ty : Ty} (value : Term) (env : Env ctx) :
    Env ((id, ty) :: ctx) := fun ref =>
  match ref with
  | .here _ => value
  | .there _ prev => env prev

def Expr.lower {ctx : Scope} {ty : Ty} (guest : Guest) (env : Env ctx) : Expr ctx ty → Term
  | .flag value => .const (flagWord value)
  | .word value => .const value
  | .get slot => guest slot
  | .tmp ref => env ref
  | .add lhs rhs => .add (lhs.lower guest env) (rhs.lower guest env)
  | .eq lhs rhs => .eq (lhs.lower guest env) (rhs.lower guest env)
  | .widen arg => arg.lower guest env
  | .low arg => .selectBit 0 (arg.lower guest env)

/-- Execute statements in order. A temporary captures its value at the binding point.
The caller commits the selected direct successor to RIP at the boundary. -/
def Code.lower {ctx : Scope} (guest : Guest) (env : Env ctx) : Code ctx → Guest × Next Term
  | .jump target => (guest, .jump target)
  | .branch guard taken next => (guest, .branch (guard.lower guest env) taken next)
  | .mark _ rest => rest.lower guest env
  | .put slot value rest => rest.lower (RegisterFile.write guest slot (value.lower guest env)) env
  | .bind _ value rest => rest.lower guest (env.cons (value.lower guest env))

inductive ObservationError where
  | flagRecipe
  deriving DecidableEq, Repr

/-- Recognize only VEX's COPY, ADDQ and SUBQ recipes, projected to ZF. Static
recognition failure is not an architectural fault or UB. -/
def observeZF (guest : Guest) : Except ObservationError Term := do
  let .const op := guest .ccOp | throw .flagRecipe
  if op == 0 then return .selectBit 6 (guest .ccDep1)
  if op == 4 then return .eq (.add (guest .ccDep1) (guest .ccDep2)) (.const 0)
  if op == 8 then return .eq (guest .ccDep1) (guest .ccDep2)
  throw .flagRecipe

def Block.lower (block : Block) : Except ObservationError Plan := do
  let (guest, next) := block.code.lower (entryGuest block.address) Env.nil
  return ⟨guest (.gpr .rax), guest (.gpr .rdi), guest (.gpr .rsi), ← observeZF guest, next⟩

/-- The block semantics on the stated COPY entry profile. The interface is partial
in the program, not in the values of the input registers or input ZF. -/
def Block.run (block : Block) (input : Input) : Except ObservationError Input :=
  block.lower.map (Plan.eval input)

end Silmaril.Machine.Vex.AMD64Scalar
