module

public import Silmaril.Compiler.Native.IR.Defs
public import Silmaril.Compiler.Native.Optimize.LocalSSA.Defs
public import Silmaril.Compiler.Contract.Defs
/-! Open native function invocation with an explicit reserved-frame address.
Calls retain actual native metadata and are supplied as finite summaries.
This does not interpret assembly, allocate stack frames or derive ABI adequacy. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Semantics.OpenFrame

open Silmaril.Compile Silmaril.Machine
open Silmaril.Compiler.Native.Optimize

def frameSymbol : String := "__ccomp_frame"

/-- External interpretation of one invocation. The current frame address is
fixed for the invocation. Direct summaries see the actual optional `CallInfo`
and original operands, including any indirect target or aggregate-result area.
They must supply the metadata/key/ABI interpretation; it is not assumed proved. -/
structure Environment where
  frameAddress : Lir.Word
  address : String → Nat → Option Lir.Word
  direct : Option CallInfo → String → List Lir.Word → Lir.Memory →
    List Lir.Word → Lir.Memory → Prop
  indirect : Lir.Word → List Lir.Word → Lir.Memory →
    List Lir.Word → Lir.Memory → Prop

/-- Interpret the reserved frame exactly as the emitter's dedicated branch:
it denotes the supplied frame word and ignores the instruction's offset.
Other symbols and all call effects remain explicit open interpretations. -/
def calls (artifact : Artifact) (environment : Environment) : OpenCalls where
  address symbol offset :=
    if symbol = frameSymbol then some environment.frameAddress
    else environment.address symbol offset
  direct symbol := environment.direct (artifact.calls.find? (·.key == symbol)) symbol
  indirect := environment.indirect

/-- State at a real Mir block boundary, retaining partial registers and memory. -/
structure State where
  label : Nat
  frame : Lir.Frame Nat
  memory : Lir.Memory

/-- One real block execution that selects the next block. -/
inductive Step (summaries : OpenCalls) (function : Mir.Func) : State → State → Prop where
  | jump {source block label frame memory} :
      function.blocks[source.label]? = some block →
      BlockExec summaries block source.frame source.memory (.jump label) frame memory →
      Step summaries function source ⟨label, frame, memory⟩

/-- Actual terminating block observations, or a block that cannot complete.
External calls are finite summaries; divergence inside a call is not represented
by this interface. Call-free functions have no such external-call boundary. -/
def Stops (summaries : OpenCalls) (function : Mir.Func) (source : State) :
    Lir.Behavior → Prop
  | .returned values memory => ∃ block frame,
      function.blocks[source.label]? = some block ∧
      BlockExec summaries block source.frame source.memory (.returned values) frame memory
  | .trapped memory => ∃ block frame,
      function.blocks[source.label]? = some block ∧
      BlockExec summaries block source.frame source.memory .trapped frame memory
  | .stuck => ∀ block, function.blocks[source.label]? = some block →
      ¬ ∃ exit frame memory, BlockExec summaries block source.frame source.memory exit frame memory
  | .diverges => False

/-- Complete observations relative to the explicit finite call summaries.
Finite observations follow actual block jumps; divergence is an infinite block
trace. In particular, no successful target trace is built into the definition. -/
def Behaves (summaries : OpenCalls) (function : Mir.Func) (source : State) :
    Lir.Behavior → Prop
  | .diverges => Silmaril.InfiniteTrace (Step summaries function) source
  | behavior => ∃ final,
      Relation.ReflTransGen (Step summaries function) source final ∧
      Stops summaries function final behavior

/-- The independently selected native function, its actual metadata and entry. -/
structure Invocation where
  function : Mir.Func
  info : FunctionInfo
  state : State

/-- Start a named function of the actual Artifact. Selection and parameter writes
can fail independently of any later behavior. The supplied memory and frame word
remain external; no loader, stack allocator or machine entry is postulated. -/
def start (artifact : Artifact) (name : String) (arguments : List Lir.Word)
    (memory : Lir.Memory) : Option Invocation := do
  let function ← artifact.mir.funcs.find? (·.name == name)
  let info ← artifact.functions.find? (·.name == name)
  let frame ← Contract.MirSem.enter function arguments
  return ⟨function, info, ⟨0, frame, memory⟩⟩

/-- Named invocation observations of the unmodified native Artifact. -/
def Observes (artifact : Artifact) (environment : Environment) (name : String)
    (arguments : List Lir.Word) (memory : Lir.Memory) (behavior : Lir.Behavior) : Prop :=
  ∃ invocation, start artifact name arguments memory = some invocation ∧
    Behaves (calls artifact environment) invocation.function invocation.state behavior

/-- Calls are excluded syntactically, independently of successful execution. -/
def CallFree : Mir.Instr → Prop
  | .call .. | .callIndirect .. => False
  | _ => True

def BlockCallFree (block : Mir.Block) : Prop := ∀ instruction ∈ block.instrs.toList,
  CallFree instruction

def FunctionCallFree (function : Mir.Func) : Prop := ∀ (label : Nat) (block : Mir.Block),
  function.blocks[label]? = some block → BlockCallFree block

/-- A finite run, with no assumed outcome or compiler contract. -/
inductive Run (summaries : OpenCalls) (function : Mir.Func) : State → Lir.Behavior → Prop where
  | stop {source behavior} : Stops summaries function source behavior →
      Run summaries function source behavior
  | next {source target behavior} : Step summaries function source target →
      Run summaries function target behavior → Run summaries function source behavior

end Silmaril.Compiler.Native.Semantics.OpenFrame
