module

public import Silmaril.Compiler.Mir.DeadCode.Defs
/-!
# Independent symbolic validation of the local SSA round trip

Registers and frame slots start as distinct symbolic inputs. The validator
interns expression DAG nodes, records potentially faulting operations and
memory/call effects in order, and compares all original register outputs, frame
slots and the terminator. Fresh temporary outputs may be discarded. It does not
run the renamer, infer its substitution, or sample concrete input values.

The executable checker is deliberately separate from the transformation.
Its soundness against Mir block semantics is proved for admitted, call-free
fragments only (`check_sound` in `PureSoundness`, `Slots.Soundness`,
`Effects.Soundness`, `Floating.Soundness`, `Address.Effects.Soundness`): if both
blocks' instructions are admitted and `check` accepts, every successful finite
source run has a candidate run with the same exit and memory, agreeing on the
original registers and slots. Blocks with calls are not admitted, so acceptance
of such a block is translation-validation evidence, not a kernel theorem.
Soundness against native machine semantics is not stated.
-/

@[expose] public section

namespace Silmaril.Compiler.Native.Optimize.Validation

open Silmaril.Compile
open Silmaril.Machine

inductive Expr where
  | input (reg : Nat)
  | slot (index : Nat)
  | const (value : Lir.Word)
  | unary (op : Lir.Unop) (source : Nat)
  | binary (op : Lir.Binop) (left right : Nat)
  | float (op : Lir.FOp) (left right : Nat)
  | addr (symbol : String) (offset : Nat)
  | load (event : Nat)
  | result (event index : Nat)
  deriving BEq, DecidableEq, Repr

inductive Effect where
  | load (width : Lir.Width) (ext : Lir.Ext) (base offset : Nat)
  | store (width : Lir.Width) (base offset source : Nat)
  | faulting (op : Lir.Binop) (left right : Nat)
  | call (symbol : String) (args : List Nat) (results : Nat)
  | indirect (target : Nat) (args : List Nat) (results : Nat)
  deriving BEq, DecidableEq, Repr

/-- These DAG leaves can fail independently of tracked memory/call effects:
unwritten input registers/slots and unresolved symbolic addresses. -/
def Expr.isPartialLeaf : Expr → Bool
  | .input _ | .slot _ | .addr _ _ => true
  | _ => false

structure State where
  nodes : Array Expr := #[]
  regs : List (Nat × Nat) := []
  slots : List (Nat × Nat) := []
  effects : Array Effect := #[]
  deriving Inhabited

/-- Normalize known integer operands using the IR's own arithmetic definitions.
This lets the independent checker compare folded arithmetic with its source. -/
def normalize (nodes : Array Expr) : Expr → Expr
  | .unary op a =>
    match nodes[a]? with
    | some (.const x) => .const (op.eval x)
    | _ => .unary op a
  | .binary op a b =>
    match nodes[a]?, nodes[b]? with
    | some (.const x), some (.const y) =>
      match op.eval x y with
      | some z => .const z
      | none => .binary op a b
    | _, _ => .binary op a b
  | e => e

def intern (raw : Expr) : StateM State Nat := do
  let s ← get
  let e := normalize s.nodes raw
  match s.nodes.findIdx? (· == e) with
  | some i => return i
  | none =>
    set { s with nodes := s.nodes.push e }
    return s.nodes.size

def readReg (r : Nat) : StateM State Nat := do
  let s ← get
  match s.regs.find? (·.1 == r) with
  | some (_, v) => return v
  | none => intern (.input r)

def readSlot (n : Nat) : StateM State Nat := do
  let s ← get
  match s.slots.find? (·.1 == n) with
  | some (_, v) => return v
  | none => intern (.slot n)

def writeReg (r v : Nat) : StateM State Unit :=
  modify fun s => { s with regs := (r, v) :: s.regs.filter (·.1 != r) }

def writeSlot (n v : Nat) : StateM State Unit :=
  modify fun s => { s with slots := (n, v) :: s.slots.filter (·.1 != n) }

def effect (e : Effect) : StateM State Nat := do
  let s ← get
  set { s with effects := s.effects.push e }
  return s.effects.size

def evalOp (o : Lir.Op Nat) : StateM State Unit := do
  match o with
  | .const d v => writeReg d (← intern (.const v))
  | .move d a => writeReg d (← readReg a)
  | .unary op d a => writeReg d (← intern (.unary op (← readReg a)))
  | .binary op d a b =>
    let x ← readReg a
    let y ← readReg b
    if Mir.DeadCode.faults op then discard <| effect (.faulting op x y)
    writeReg d (← intern (.binary op x y))
  | .load w e d base off =>
    let event ← effect (.load w e (← readReg base) off)
    writeReg d (← intern (.load event))
  | .store w base off a => discard <| effect (.store w (← readReg base) off (← readReg a))
  | .slotGet d n => writeReg d (← readSlot n)
  | .slotSet n a => writeSlot n (← readReg a)

def writeResults (event : Nat) (results : List Nat) : StateM State Unit := do
  for (r, index) in results.zipIdx do
    writeReg r (← intern (.result event index))

def evalInstr (i : Mir.Instr) : StateM State Unit := do
  match i with
  | .op o => evalOp o
  | .fop op d a b => writeReg d (← intern (.float op (← readReg a) (← readReg b)))
  | .addr d sym off => writeReg d (← intern (.addr sym off))
  | .call sym args results =>
    let event ← effect (.call sym (← args.mapM readReg) results.length)
    writeResults event results
  | .callIndirect target args results =>
    let event ← effect (.indirect (← readReg target) (← args.mapM readReg) results.length)
    writeResults event results

inductive Term where
  | jump (label : Nat)
  | branch (condition ifNonzero ifZero : Nat)
  | ret (values : List Nat)
  | trap
  deriving BEq, DecidableEq, Repr

def evalLoc : Lir.Loc Nat → StateM State Nat
  | .reg r => readReg r
  | .slot n => readSlot n

def evalTerm (t : Lir.Term Nat) : StateM State Term := do
  match t with
  | .jump l => return .jump l
  | .branch c a b => return .branch (← readReg c) a b
  | .ret values => return .ret (← values.mapM evalLoc)
  | .trap => return .trap

def evalBlock (b : Mir.Block) (observed : List Nat) : StateM State (Term × List Nat) := do
  for i in b.instrs do evalInstr i
  return (← evalTerm b.term, ← observed.mapM readReg)

def defs : Mir.Instr → List Nat
  | .op o => (Mir.DeadCode.opDef o).toList
  | .fop _ d _ _ | .addr d _ _ => [d]
  | .call _ _ results | .callIndirect _ _ results => results

/-- A bounded independent check. Too-large blocks and any mismatch fall back to
the unchanged source block. Effects and original register outputs must match;
all candidate writes below `freshBase` must name source-written registers.
Candidate-added partial input/slot/address leaves are rejected even when unused;
source leaves may be reused. Only the appended candidate DAG suffix is scanned. -/
def check (freshBase : Nat) (source candidate : Mir.Block) : Bool := Id.run do
  if source.instrs.size > 4096 || candidate.instrs.size > 8192 then return false
  let observed := (source.instrs.toList.flatMap defs).dedup
  if !(candidate.instrs.all fun i => (defs i).all fun r =>
      freshBase ≤ r || observed.contains r) then return false
  let (out₁, s₁) := (evalBlock source observed).run {}
  let (out₂, s₂) := (evalBlock candidate observed).run { nodes := s₁.nodes }
  -- Candidate evaluation starts with the source DAG; intern only appends.
  -- Reusing source leaves is allowed, but new partial leaves could introduce
  -- failure even if their fresh register outputs are otherwise discarded.
  if s₂.nodes.any Expr.isPartialLeaf s₁.nodes.size then return false
  if out₁ != out₂ || s₁.effects != s₂.effects then return false
  let slots := (s₁.slots.map (·.1) ++ s₂.slots.map (·.1)).dedup
  let (values₁, s₃) := (slots.mapM readSlot).run { s₁ with nodes := s₂.nodes }
  let (values₂, _) := (slots.mapM readSlot).run { s₂ with nodes := s₃.nodes }
  return values₁ == values₂

end Silmaril.Compiler.Native.Optimize.Validation
