module

public import Silmaril.Machine.CBackend.Lir.Syntax.Defs
/-!
# RTL: a CompCert-style control-flow graph over pseudo-registers

RTL is a control-flow graph of numbered nodes. Each node holds one instruction,
and each instruction names its own successors: there is no fallthrough and no
notion of a basic block. This is the shape CompCert's RTL has, and it is the
shape a machine-code recovery pass produces naturally, one node per recovered
instruction.

The value and operator vocabulary is `Lir`'s, verbatim: `Lir.Word` (64-bit),
`Lir.Unop`, `Lir.Binop`, `Lir.Width`, `Lir.Ext`, `Lir.Cond` and `Lir.Memory`,
with `Lir.Binop.eval` partial on division. Nothing is redefined here, so a
lowering from RTL to `Lir` relates syntax and leaves arithmetic alone.
`Machine.RegisterIR` is a smaller three-address vocabulary used by the
instruction-selection experiments; `Lir`'s operators are the richer set and the
one RTL uses.

The differences from `Lir` are deliberate and small:

* a function is an array of instructions indexed by node, not a list of blocks
  of straight-line operations ending in a terminator;
* calls are instructions with a successor, not a terminator, and their
  arguments and results are registers rather than register-or-slot locations:
  RTL has no stack slots, since a CFG over pseudo-registers is produced before
  any frame layout exists;
* a function carries a `Signature` recording how many words it takes and
  returns, which `WellFormedSig` checks against the parameter list and the
  `ret` instructions.

A node outside a function's code array is stuck, as is a jump or successor
naming one. `WellFormedSig` rules this out and is decidable.
-/

@[expose] public section

namespace Silmaril.Machine.RTL

/-- Nodes index a function's code array. -/
abbrev Node := Nat
/-- Function identifiers index the program's function table. -/
abbrev FuncId := Nat

/-- A function signature: how many words come in and how many go out. -/
structure Signature where
  params : Nat
  results : Nat
  deriving DecidableEq, Repr

/-- Instructions. Every instruction names its successors explicitly; there is
no fallthrough. `R` is the type of pseudo-registers. The address of a memory
access is the unsigned value of `base` plus the constant `offset`, computed
without wrap-around, exactly as in `Lir`. -/
inductive Instr (R : Type) where
  | nop (succ : Node)
  | const (dest : R) (value : Lir.Word) (succ : Node)
  | move (dest source : R) (succ : Node)
  | unary (op : Lir.Unop) (dest source : R) (succ : Node)
  | binary (op : Lir.Binop) (dest first second : R) (succ : Node)
  | load (width : Lir.Width) (ext : Lir.Ext) (dest base : R) (offset : Nat) (succ : Node)
  | store (width : Lir.Width) (base : R) (offset : Nat) (source : R) (succ : Node)
  | call (callee : FuncId) (args : List R) (results : List R) (succ : Node)
  | cond (c : R) (ifNonzero ifZero : Node)
  | jump (target : Node)
  | ret (values : List R)
  | trap
  deriving DecidableEq, Repr

namespace Instr

variable {R : Type}

/-- The nodes an instruction may continue at. -/
def successors : Instr R → List Node
  | .nop s | .const _ _ s | .move _ _ s | .unary _ _ _ s | .binary _ _ _ _ s
  | .load _ _ _ _ _ s | .store _ _ _ _ s | .call _ _ _ s => [s]
  | .cond _ s₁ s₂ => [s₁, s₂]
  | .jump t => [t]
  | .ret _ | .trap => []

/-- The single register an instruction writes, when it has one. A `call` writes
a list of results and the remaining instructions write nothing. -/
def dest? : Instr R → Option R
  | .const d _ _ | .move d _ _ | .unary _ d _ _ | .binary _ d _ _ _ | .load _ _ d _ _ _ => some d
  | _ => none

/-- The registers an instruction reads. -/
def uses : Instr R → List R
  | .nop _ | .const _ _ _ | .jump _ | .trap => []
  | .move _ s _ | .unary _ _ s _ => [s]
  | .binary _ _ a b _ => [a, b]
  | .load _ _ _ base _ _ => [base]
  | .store _ base _ src _ => [base, src]
  | .call _ args _ _ => args
  | .cond c _ _ => [c]
  | .ret values => values

/-- The registers an instruction writes. -/
def defs : Instr R → List R
  | .call _ _ results _ => results
  | i => i.dest?.toList

/-- `i` fits a function with `results` return values and `nodes` nodes: its
successors exist and a `ret` returns the declared number of values. -/
def okIn (results nodes : Nat) (i : Instr R) : Bool :=
  i.successors.all (fun n => decide (n < nodes)) &&
    (match i with
     | .ret values => values.length == results
     | _ => true)

end Instr

/-- A function: a signature, parameter registers, an entry node, and a code
array indexed by node. A node outside the array is stuck. -/
structure Func (R : Type) where
  sig : Signature
  params : List R
  entry : Node
  code : List (Instr R)
  deriving DecidableEq, Repr

/-- A program is a function table indexed by `FuncId`. -/
structure Prog (R : Type) where
  funcs : List (Func R)
  deriving DecidableEq, Repr

namespace Func

variable {R : Type}

/-- The instruction at a node, if the node exists. -/
def instr? (fn : Func R) (n : Node) : Option (Instr R) := fn.code[n]?

/-- The successors of a node; a missing node has none. -/
def succ (fn : Func R) (n : Node) : List Node :=
  match fn.instr? n with
  | some i => i.successors
  | none => []

/-- A function agrees with its signature: the parameter list has the declared
length, the entry node exists, every successor exists and every `ret` returns
the declared number of values. -/
def WellFormedSig (fn : Func R) : Prop :=
  fn.params.length = fn.sig.params ∧ fn.entry < fn.code.length ∧
    fn.code.all (Instr.okIn fn.sig.results fn.code.length) = true

instance (fn : Func R) : Decidable fn.WellFormedSig := inferInstanceAs (Decidable (_ ∧ _))

end Func

namespace Prog

variable {R : Type}

/-- The function with the given identifier. -/
def func? (p : Prog R) (f : FuncId) : Option (Func R) := p.funcs[f]?

/-- The instruction at a node of a function. -/
def instr? (p : Prog R) (f : FuncId) (n : Node) : Option (Instr R) :=
  (p.func? f).bind fun fn => fn.instr? n

/-- Every function agrees with its signature. -/
def WellFormedSig (p : Prog R) : Prop := ∀ fn ∈ p.funcs, fn.WellFormedSig

instance (p : Prog R) : Decidable p.WellFormedSig := inferInstanceAs (Decidable (∀ _ ∈ _, _))

end Prog

end Silmaril.Machine.RTL
