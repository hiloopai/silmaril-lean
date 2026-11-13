module

public import Silmaril.Compiler.Native.Optimize.Validation.Slots.Source.Thms
/-! Ordered concrete load/store/faulting events use the actual partial Lir
operations. Calls and indirect calls remain separate. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Effects
open Silmaril.Machine Silmaril.Compile

inductive Event where
  | load (width : Lir.Width) (ext : Lir.Ext) (address : Nat)
  | store (width : Lir.Width) (address : Nat) (word : Lir.Word)
  | faulting (op : Lir.Binop) (left right : Lir.Word)
  deriving DecidableEq, Repr

/-- A store has no word result; loads and successful faulting arithmetic do.
Every event records the real intermediate memory through this evaluator. -/
def Event.exec : Event → Lir.Memory → Option (Option Lir.Word × Lir.Memory)
  | .load width ext address, memory =>
    (memory.load width ext address).map fun word => (some word, memory)
  | .store width address word, memory =>
    (memory.store width address word).map fun after => (none, after)
  | .faulting op left right, memory =>
    (op.eval left right).map fun word => (some word, memory)

def runEvents : List Event → Lir.Memory → Option (List (Option Lir.Word) × Lir.Memory)
  | [], memory => some ([], memory)
  | event :: rest, memory =>
    (event.exec memory).bind fun head =>
      (runEvents rest head.2).map fun tail => (head.1 :: tail.1, tail.2)

/-- Concrete source operands are read from the actual partial frame. Pure and
slot primitives contribute no event; successful execution is proved separately. -/
def sourceEvents : Lir.Op Nat → Lir.Frame Nat → Option (List Event)
  | .load width ext _ base offset, frame =>
    (frame.get base).map fun word => [.load width ext (word.toNat + offset)]
  | .store width base offset source, frame =>
    (frame.get base).bind fun address =>
      (frame.get source).map fun word => [.store width (address.toNat + offset) word]
  | .binary op _ left right, frame =>
    if Mir.DeadCode.faults op then
      (frame.get left).bind fun x => (frame.get right).map fun y => [.faulting op x y]
    else some []
  | _, _ => some []

/-- The actual symbolic Effect interpreted through partial DAG values.
Call effects are deliberately outside this initial event semantics. -/
def concreteEffect (meaning : Interpretation) : Effect → Option Event
  | .load width ext base offset =>
    (meaning.value base).map fun address => .load width ext (address.toNat + offset)
  | .store width base offset source =>
    (meaning.value base).bind fun address =>
      (meaning.value source).map fun word => .store width (address.toNat + offset) word
  | .faulting op left right =>
    (meaning.value left).bind fun x => (meaning.value right).map fun y => .faulting op x y
  | .call .. | .indirect .. => none

def runEffects (meaning : Interpretation) (effects : List Effect) (memory : Lir.Memory) :
    Option (List (Option Lir.Word) × Lir.Memory) :=
  (effects.mapM (concreteEffect meaning)).bind fun events => runEvents events memory

/-- A generated event sequence alongside actual source instruction execution.
The constructors require only actual primitive execution and actual partial
source operand extraction; they contain no candidate execution premise. -/
inductive SourceTrace (calls : OpenCalls) : List Mir.Instr → Lir.Frame Nat → Lir.Memory →
    List Event → Lir.Frame Nat → Lir.Memory → Prop
  | nil (frame memory) : SourceTrace calls [] frame memory [] frame memory
  | cons (operation : Lir.Op Nat) (rest : List Mir.Instr)
      (frame middle final : Lir.Frame Nat) (memory middleMemory finalMemory : Lir.Memory)
      (head tail : List Event)
      (executed : operation.exec frame memory = some (middle, middleMemory))
      (events : sourceEvents operation frame = some head)
      (later : SourceTrace calls rest middle middleMemory tail final finalMemory) :
      SourceTrace calls (.op operation :: rest) frame memory (head ++ tail) final finalMemory

/-- All actual primitives are admitted here. Address/floating instructions and
calls have their own semantics and are not silently made effect-free. -/
def AdmittedInstr : Mir.Instr → Prop
  | .op _ => True
  | _ => False

def Admitted (instructions : List Mir.Instr) : Prop :=
  ∀ instruction ∈ instructions, AdmittedInstr instruction

end Silmaril.Compiler.Native.Optimize.Validation.Effects
