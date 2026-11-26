module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Defs
public import Silmaril.Wasm.Execution.Core.Inversion.Defs
public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Thms
public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Source.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Common
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Core
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Lime1

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop

open Execution
open Execution.Runtime (Value)
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked
open Wasm.SingleThreaded.Det (noHost)

variable {entry : Entry} {program : Graph.Program} {tables : Source.Tables} {outerFrame : Runtime.Frame}
  {index : FuncIdx} {args : List Value}

theorem graph_checked (ready : entry.Checked program tables outerFrame index args) :
    program.checkDirect = true :=
  Proofs.graph_checked ready

theorem caller_admitted (ready : entry.Checked program tables outerFrame index args)
    {locals : List Value} (typed : entry.Typed ⟨locals, .caller⟩) :
    Graph.Admitted program entry.owner (entry.callerPhase locals) :=
  Proofs.caller_admitted ready typed


theorem initial_typed (ready : entry.Checked program tables outerFrame index args) :
    entry.Typed (entry.initial args) :=
  Proofs.initial_typed ready

theorem edge_preserves (ready : entry.Checked program tables outerFrame index args)
    {a b : State} (typed : entry.Typed a) (move : Edge entry a b) : entry.Typed b :=
  Proofs.preserve ready typed move

section Core

open Execution.Core

variable {H : Type} {P : Numerics.Profile} {s : Store H}

/-- Invert a step under the entered loop when its label cannot exit. -/
theorem core_loop_wrap_step_iff {body dst : Config H}
    (stays : ∀ out, ¬ LabelExit 0 [entry.coreLoop] body.code out) :
    Step P noHost (entry.coreLoopWrap outerFrame body) dst ↔
      ∃ mid, Step P noHost body mid ∧ dst = entry.coreLoopWrap outerFrame mid :=
  Proofs.Core.loop_wrap_iff stays

/-- Exact native successors before execution reaches the site or the enclosing tail. -/
theorem core_step_iff (ready : entry.Checked program tables outerFrame index args) {a : State} {dst : Config H}
    (typed : entry.Typed a) (live : a.phase.Pending) :
    Step P noHost (entry.coreConfig s outerFrame a) dst ↔
      ∃ b, Edge entry a b ∧ dst = entry.coreConfig s outerFrame b :=
  Proofs.Core.step_iff (P := P) (s := s) ready typed live

/-- Read back finite loop entry, restart, and exit, including all prefixes of
continued restart. The empty arm runs the checked function tail.
Native evaluation from a reached site checkpoint is left as a suffix. -/
theorem core_run_iff (ready : entry.Checked program tables outerFrame index args)
    (allocated : s.funcs[entry.address.value]? = some entry.coreInstance)
    (links : program.CoreLinksAllocated s) {dst : Config H} :
    let start := coreSource s outerFrame index args
    let invoke := (⟨entry.cont, entry.op, entry.before⟩ : GraphEntry.Entry).coreInvoke s outerFrame args
    Steps P noHost start dst ↔ dst ∈ [start, invoke] ∨
      Observation entry args (entry.coreConfig s outerFrame)
        (fun locals out => ∃ phase, program.FrameRuns entry.address (entry.callerPhase locals) phase ∧
          Graph.Admitted program entry.owner phase ∧ out = Graph.coreConfig s outerFrame entry.cont.target phase)
        (Step P noHost) dst :=
  Proofs.Core.run_iff (P := P) (s := s) ready allocated links

/-- After entering the site arm, exact finite prefixes of numeric evaluation require no native table allocation. -/
theorem core_operand_run_iff {locals : List Value} {states : List OperandState} {result : OperandResult}
    (trace : OperandTrace locals [] entry.before states result) {dst : Config H} :
    Steps P noHost (entry.coreConfig s outerFrame ⟨locals, .site⟩) dst ↔
      dst ∈ states.map (entry.coreOperands s outerFrame locals) ∨
        Steps P noHost (entry.coreOperandResult s outerFrame locals result) dst :=
  Proofs.Core.operand_run_iff trace

/-- A successfully prepared operand stack is the initial native lookup configuration. -/
theorem core_lookup_start {locals stack : List Value} {active : Source.Activation}
    (prepared : entry.op.prepare program tables (entry.frame locals) stack = some active) :
    entry.coreOperandResult s outerFrame locals (.values stack) = entry.coreLookup s outerFrame active .start :=
  Proofs.Core.lookup_start prepared

/-- Exact native lookup through a pending invocation or the first lookup trap, under the active arm and loop labels. -/
theorem core_lookup_exact {active : Source.Activation} {out : Outcome}
    (ready : active.Checked program tables) (targets : active.binding.site.CoreAllocated program s)
    (allocated : Source.Tables.CoreAllocated tables s) (resolved : active.resolve program = some out) :
    (out.coreTrace.map (entry.coreLookup s outerFrame active)).IsChain
      (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) :=
  Proofs.Core.lookup_exact ready targets allocated resolved

theorem core_entry_chain (ready : entry.Checked program tables outerFrame index args)
    (allocated : s.funcs[entry.address.value]? = some entry.coreInstance) :
    let start := coreSource s outerFrame index args
    let invoke := (⟨entry.cont, entry.op, entry.before⟩ : GraphEntry.Entry).coreInvoke s outerFrame args
    ([start, invoke] ++ [entry.coreConfig s outerFrame (entry.initial args)]).IsChain
        (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) :=
  Proofs.Core.entry_chain (P := P) ready allocated

theorem core_site_operands (locals : List Value) :
    entry.coreConfig s outerFrame ⟨locals, .site⟩ = entry.coreOperands s outerFrame locals ([], entry.before) :=
  Proofs.Core.site_operands locals

theorem core_operand_chain {locals stack : List Value} {code : List Prefix.Op}
    {states : List OperandState} {result : OperandResult}
    (trace : OperandTrace locals stack code states result) :
    (states.map (entry.coreOperands s outerFrame locals) ++ [entry.coreOperandResult s outerFrame locals result]).IsChain
      (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) :=
  Proofs.Core.operand_chain (P := P) trace

end Core

section Lime

open Wasm.Lime1.Execution

variable {H : Type} {s : Store H}

/-- Invert a step under the entered loop when its label cannot exit. -/
theorem lime_loop_wrap_step_iff {body dst : Config H}
    (stays : ∀ out, ¬ PureStep body.frame.module.types [.label 0 [entry.limeLoop] body.code] out) :
    Step CallFrame.limeNoHost (entry.limeLoopWrap outerFrame body) dst ↔
      ∃ mid, Step CallFrame.limeNoHost body mid ∧ dst = entry.limeLoopWrap outerFrame mid :=
  Proofs.Lime1.loop_wrap_iff stays

/-- Exact native successors before execution reaches the site or the enclosing tail. -/
theorem lime_step_iff (ready : entry.Checked program tables outerFrame index args) {a : State} {dst : Config H}
    (typed : entry.Typed a) (live : a.phase.Pending) :
    Step CallFrame.limeNoHost (entry.limeConfig s outerFrame a) dst ↔
      ∃ b, Edge entry a b ∧ dst = entry.limeConfig s outerFrame b :=
  Proofs.Lime1.step_iff ready typed live

/-- Read back finite loop entry, restart, and exit, including all prefixes of
continued restart. The empty arm runs the checked function tail.
Native evaluation from a reached site checkpoint is left as a suffix. -/
theorem lime_run_iff (ready : entry.Checked program tables outerFrame index args)
    (allocated : s.funcs[entry.address.value]? = some entry.limeInstance)
    (links : program.LimeLinksAllocated s) {dst : Config H} :
    let start := limeSource s outerFrame index args
    let invoke := (⟨entry.cont, entry.op, entry.before⟩ : GraphEntry.Entry).limeInvoke s outerFrame args
    Steps CallFrame.limeNoHost start dst ↔ dst ∈ [start, invoke] ∨
      Observation entry args (entry.limeConfig s outerFrame)
        (fun locals out => ∃ phase, program.FrameRuns entry.address (entry.callerPhase locals) phase ∧
          Graph.Admitted program entry.owner phase ∧ out = Graph.limeConfig s outerFrame entry.cont.target phase)
        (Step CallFrame.limeNoHost) dst :=
  Proofs.Lime1.run_iff ready allocated links

/-- After entering the site arm, exact finite prefixes of numeric evaluation require no native table allocation. -/
theorem lime_operand_run_iff {locals : List Value} {states : List OperandState} {result : OperandResult}
    (trace : OperandTrace locals [] entry.before states result) {dst : Config H} :
    Steps CallFrame.limeNoHost (entry.limeConfig s outerFrame ⟨locals, .site⟩) dst ↔
      dst ∈ states.map (entry.limeOperands s outerFrame locals) ∨
        Steps CallFrame.limeNoHost (entry.limeOperandResult s outerFrame locals result) dst :=
  Proofs.Lime1.operand_run_iff trace

/-- A successfully prepared operand stack is the initial native lookup configuration. -/
theorem lime_lookup_start {locals stack : List Value} {active : Source.Activation}
    (prepared : entry.op.prepare program tables (entry.frame locals) stack = some active) :
    entry.limeOperandResult s outerFrame locals (.values stack) = entry.limeLookup s outerFrame active :=
  Proofs.Lime1.lookup_start prepared

/-- Exact native lookup through a pending invocation or the first lookup trap, under the active arm and loop labels. -/
theorem lime_lookup_exact {active : Source.Activation} {out : Outcome}
    (ready : active.Checked program tables) (targets : active.binding.site.LimeAllocated program s)
    (allocated : Source.Tables.LimeAllocated tables s) (resolved : active.resolve program = some out)
    (dst : Config H) :
    Step CallFrame.limeNoHost (entry.limeLookup s outerFrame active) dst ↔
      dst = entry.limeLookupResult s outerFrame active out :=
  Proofs.Lime1.lookup_exact ready targets allocated resolved dst

theorem lime_entry_chain (ready : entry.Checked program tables outerFrame index args)
    (allocated : s.funcs[entry.address.value]? = some entry.limeInstance) :
    let start := limeSource s outerFrame index args
    let invoke := (⟨entry.cont, entry.op, entry.before⟩ : GraphEntry.Entry).limeInvoke s outerFrame args
    ([start, invoke] ++ [entry.limeConfig s outerFrame (entry.initial args)]).IsChain
        (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) :=
  Proofs.Lime1.entry_chain ready allocated

theorem lime_site_operands (locals : List Value) :
    entry.limeConfig s outerFrame ⟨locals, .site⟩ = entry.limeOperands s outerFrame locals ([], entry.before) :=
  Proofs.Lime1.site_operands locals

theorem lime_operand_chain {locals stack : List Value} {code : List Prefix.Op}
    {states : List OperandState} {result : OperandResult}
    (trace : OperandTrace locals stack code states result) :
    (states.map (entry.limeOperands s outerFrame locals) ++ [entry.limeOperandResult s outerFrame locals result]).IsChain
      (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) :=
  Proofs.Lime1.operand_chain trace

end Lime

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop
