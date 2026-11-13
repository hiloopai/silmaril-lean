module

public import Silmaril.Compiler.Mir.DeadCode.Defs
/-! Block-local SSA names and explicit mutable-register boundary commits. -/

@[expose] public section

namespace Silmaril.Compiler.Native.Optimize

open Silmaril.Compile
open Silmaril.Machine

/-- Register operands read by an instruction, including indirect call targets. -/
def uses : Mir.Instr → List Nat
  | .op o => Mir.DeadCode.opUses o
  | .fop _ _ a b => [a, b]
  | .addr .. => []
  | .call _ args _ => args
  | .callIndirect target args _ => target :: args

/-- Register operands written by an instruction. -/
def defs : Mir.Instr → List Nat
  | .op o => (Mir.DeadCode.opDef o).toList
  | .fop _ dest _ _ | .addr dest _ _ => [dest]
  | .call _ _ results | .callIndirect _ _ results => results

/-- A fresh range disjoint from every original register mentioned by a function. -/
def freshBase (f : Mir.Func) : Nat :=
  let regs := f.params ++ f.blocks.toList.flatMap fun b =>
    Mir.DeadCode.termUses b.term ++ b.instrs.toList.flatMap fun i => uses i ++ defs i
  regs.foldl Nat.max 0 + 1

/-- A local SSA block, retaining an explicit exit map to mutable Mir registers. -/
structure Block where
  inputs : List Nat
  body : Mir.Block
  outputs : List (Nat × Nat)
  deriving Inhabited

/-- Static SSA condition within one block: input and destination names are unique. -/
def Block.isSSA (b : Block) : Bool :=
  decide (b.inputs ++ b.body.instrs.toList.flatMap defs).Nodup

structure Rename where
  versions : List (Nat × Nat) := []
  next : Nat
  deriving Inhabited

def Rename.read (s : Rename) (r : Nat) : Nat :=
  ((s.versions.find? (·.1 == r)).map (·.2)).getD r

def define (r : Nat) : StateM Rename Nat := do
  let s ← get
  set ({ versions := (r, s.next) :: s.versions.filter (·.1 != r), next := s.next + 1 } : Rename)
  return s.next

def renameOp (o : Lir.Op Nat) : StateM Rename (Lir.Op Nat) := do
  let s ← get
  match o with
  | .const d v => return .const (← define d) v
  | .move d a => return .move (← define d) (s.read a)
  | .unary op d a => return .unary op (← define d) (s.read a)
  | .binary op d a b => return .binary op (← define d) (s.read a) (s.read b)
  | .load w e d base off => return .load w e (← define d) (s.read base) off
  | .store w base off a => return .store w (s.read base) off (s.read a)
  | .slotGet d slot => return .slotGet (← define d) slot
  | .slotSet slot a => return .slotSet slot (s.read a)

/-- All source operands are read before any destination name is allocated. -/
def renameInstr (i : Mir.Instr) : StateM Rename Mir.Instr := do
  let s ← get
  match i with
  | .op o => return .op (← renameOp o)
  | .fop op d a b => return .fop op (← define d) (s.read a) (s.read b)
  | .addr d sym off => return .addr (← define d) sym off
  | .call sym args results =>
    return .call sym (args.map s.read) (← results.mapM define)
  | .callIndirect target args results =>
    return .callIndirect (s.read target) (args.map s.read) (← results.mapM define)

def renameLoc (s : Rename) : Lir.Loc Nat → Lir.Loc Nat
  | .reg r => .reg (s.read r)
  | .slot n => .slot n

def renameTerm (s : Rename) : Lir.Term Nat → Lir.Term Nat
  | .branch c a b => .branch (s.read c) a b
  | .ret vals => .ret (vals.map (renameLoc s))
  | t => t

/-- Enter local SSA without changing block order, successors or symbolic callees. -/
def enter (base : Nat) (b : Mir.Block) : Block :=
  let (instrs, s) := (b.instrs.mapM renameInstr).run { next := base }
  let inputs := (b.instrs.toList.flatMap uses ++ Mir.DeadCode.termUses b.term).dedup
  { inputs, body := ⟨instrs, renameTerm s b.term⟩, outputs := s.versions }

/-- Commit every live-out register version. The commits have disjoint original
destinations and fresh SSA sources, so their order cannot clobber another source. -/
def leave (b : Block) : Mir.Block :=
  { b.body with instrs := b.body.instrs ++
      b.outputs.toArray.map (fun (original, version) => .op (.move original version)) }

/-- Every source register has a current target name below the allocation cursor. -/
def Rename.Bounded (base : Nat) (s : Rename) : Prop :=
  base ≤ s.next ∧ ∀ reg, reg < base → s.read reg < s.next

/-- A source frame and SSA frame agree through the current renaming. -/
def Rename.Agrees (base : Nat) (s : Rename) (source target : Lir.Frame Nat) : Prop :=
  source.slots = target.slots ∧
    ∀ reg, reg < base → target.get (s.read reg) = source.get reg

/-! Open-block semantics parameterized by arbitrary symbolic call summaries. -/

/-- Symbol addresses and direct/indirect call summaries for one open Mir block.
The summaries are arbitrary relations, retaining nondeterministic effects. -/
structure OpenCalls where
  address : String → Nat → Option Lir.Word
  direct : String → List Lir.Word → Lir.Memory → List Lir.Word → Lir.Memory → Prop
  indirect : Lir.Word → List Lir.Word → Lir.Memory → List Lir.Word → Lir.Memory → Prop

/-- Successful execution of one Mir instruction using actual Lir operations
and frame reads/writes, with externally supplied address/call meanings. -/
inductive InstructionExec (calls : OpenCalls) : Silmaril.Compile.Mir.Instr →
    Lir.Frame Nat → Lir.Memory → Lir.Frame Nat → Lir.Memory → Prop where
  | op {o source memory source' memory'} :
      o.exec source memory = some (source', memory') →
      InstructionExec calls (.op o) source memory source' memory'
  | fop {o dest a b source memory source'} :
      Lir.FOp.exec o dest a b source = some source' →
      InstructionExec calls (.fop o dest a b) source memory source' memory
  | addr {dest symbol offset source memory value} :
      calls.address symbol offset = some value →
      InstructionExec calls (.addr dest symbol offset) source memory (source.set dest value) memory
  | call {symbol args results source memory values returned source' memory'} :
      source.readAll (args.map .reg) = some values →
      calls.direct symbol values memory returned memory' →
      source.writeAll (results.map .reg) returned = some source' →
      InstructionExec calls (.call symbol args results) source memory source' memory'
  | indirect {reg args results source memory pointer values returned source' memory'} :
      source.get reg = some pointer →
      source.readAll (args.map .reg) = some values →
      calls.indirect pointer values memory returned memory' →
      source.writeAll (results.map .reg) returned = some source' →
      InstructionExec calls (.callIndirect reg args results) source memory source' memory'

/-- Finite successful execution of a block's instruction sequence. -/
inductive InstructionsExec (calls : OpenCalls) : List Silmaril.Compile.Mir.Instr →
    Lir.Frame Nat → Lir.Memory → Lir.Frame Nat → Lir.Memory → Prop where
  | nil {source memory} : InstructionsExec calls [] source memory source memory
  | cons {i rest source memory middle middleMem source' memory'} :
      InstructionExec calls i source memory middle middleMem →
      InstructionsExec calls rest middle middleMem source' memory' →
      InstructionsExec calls (i :: rest) source memory source' memory'

/-! SSA exit certificates and open-block observations. -/

def commitInstrs (versions : List (Nat × Nat)) : List Silmaril.Compile.Mir.Instr :=
  versions.map fun (original, version) => .op (.move original version)


/-- Original exit destinations are below `base`; SSA sources are fresh and
agree with the current renaming environment. -/
def Rename.Valid (base : Nat) (s : Rename) : Prop :=
  s.Bounded base ∧ ∀ p ∈ s.versions, p.1 < base ∧ base ≤ p.2 ∧ s.read p.1 = p.2

/-- Every register written so far has a value in the successful source run. -/
def Rename.Defined (s : Rename) (source : Lir.Frame Nat) : Prop :=
  ∀ p ∈ s.versions, ∃ w, source.get p.1 = some w


/-- Values observed at an open block's control-flow boundary. -/
inductive BlockExit where
  | jump (label : Nat)
  | returned (values : List Lir.Word)
  | trapped

/-- Successful branch/return/trap observations, retaining partial register reads. -/
inductive TermExec : Lir.Term Nat → Lir.Frame Nat → BlockExit → Prop where
  | jump {label source} : TermExec (.jump label) source (.jump label)
  | zero {reg yes no source} : source.get reg = some 0 →
      TermExec (.branch reg yes no) source (.jump no)
  | nonzero {reg yes no source value} : source.get reg = some value → value ≠ 0 →
      TermExec (.branch reg yes no) source (.jump yes)
  | ret {locs source values} : source.readAll locs = some values →
      TermExec (.ret locs) source (.returned values)
  | trap {source} : TermExec .trap source .trapped

/-- A finite successful open-block execution with its final frame and memory. -/
def BlockExec (calls : OpenCalls) (b : Silmaril.Compile.Mir.Block)
    (source : Lir.Frame Nat) (memory : Lir.Memory) (exit : BlockExit)
    (source' : Lir.Frame Nat) (memory' : Lir.Memory) : Prop :=
  InstructionsExec calls b.instrs.toList source memory source' memory' ∧
    TermExec b.term source' exit

end Silmaril.Compiler.Native.Optimize
