module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Resume.Defs
public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Resume.Common
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Resume.Core
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Resume.Lime1

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Resume

open Execution
open Execution.Runtime (Value)
open CallContinuation
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Ranked
open Wasm.SingleThreaded.Det (noHost)

variable {entry : Entry} {program : Graph.Program} {tables : Source.Tables}
  {outerFrame : Runtime.Frame} {index : FuncIdx} {args : List Value} {call : Context.Invocation}

theorem split_run {S C : Type} {edge : S → S → Prop} {native : C → C → Prop}
    (render : S → C) (live : S → Prop) (next : S → C → Prop) {start : S}
    (step : ∀ {a dst}, Relation.ReflTransGen edge start a → live a →
      (native (render a) dst ↔ ∃ b, edge a b ∧ dst = render b))
    (source : ∀ {a b}, Relation.ReflTransGen edge start a → edge a b → live a)
    (handoff : ∀ {a dst}, Relation.ReflTransGen edge start a → ¬ live a →
      (Relation.ReflTransGen native (render a) dst ↔ next a dst)) {dst : C} :
    Relation.ReflTransGen native (render start) dst ↔
      (∃ a, Relation.ReflTransGen edge start a ∧ dst = render a) ∨
      (∃ a, Relation.ReflTransGen edge start a ∧ ¬ live a ∧ next a dst) :=
  Proofs.split_run render live next step source handoff

theorem edge_preserves {A : Type} {entry : Entry} {a b : Phase A} (ready : Admitted entry a)
    (move : Edge a b) : Admitted entry b :=
  Proofs.preserve ready move

theorem empty_stack {A : Type} {entry : Entry} {locals stack : List Value}
    (ready : Admitted entry (A := A) (.write locals stack [])) : stack = [] :=
  Proofs.empty_stack ready

section Core

open Execution.Core

variable {H : Type} {P : Numerics.Profile} {s : Store H}

/-- Exact arbitrary successors during arm writes, trap discard, and the two label exits. -/
theorem core_finish_step_iff {a : Phase Admin} {dst : Config H} (ready : Admitted entry a) (live : a.Live) :
    Step P noHost (corePhase entry s outerFrame a) dst ↔
      ∃ b, Edge a b ∧ dst = corePhase entry s outerFrame b :=
  Proofs.Core.finish_step (P := P) (s := s) ready live

/-- Read back the arm and loop exits, then the checked function tail or
the caller function’s native trap discard and frame exit. -/
theorem core_finish_run (ready : entry.Checked program tables outerFrame index args)
    (links : program.CoreLinksAllocated s) {a : Phase Admin} (typed : Admitted entry a) {dst : Config H} :
    Steps P noHost (corePhase entry s outerFrame a) dst ↔
      Finish entry program (corePhase entry s outerFrame) (Graph.coreConfig s outerFrame entry.cont.target) a dst :=
  Proofs.Core.finish_run (P := P) (s := s) ready links typed

/-- Read back a selected successful lookup from its operand prefix through
callee entry, the first return or callee trap, and the caller execution. -/
theorem core_resolved_run (ready : entry.Checked program tables outerFrame index args)
    {locals stack : List Value} {states : List OperandState} {active : Source.Activation}
    (trace : OperandTrace locals [] entry.before states (.values stack))
    (prepared : entry.op.prepare program tables (entry.frame locals) stack = some active)
    (localTypes : locals.map Value.type = entry.owner.localTypes)
    (invoked : active.invocation program = some call)
    (tablesFound : Source.Tables.CoreAllocated tables s) (targets : active.binding.site.CoreAllocated program s)
    (links : program.CoreLinksAllocated s) (writes : Writes entry call.saved call.site.signature.results)
    {dst : Config H} :
    Steps P noHost (entry.coreConfig s outerFrame ⟨locals, .site⟩) dst ↔
      dst ∈ states.map (entry.coreOperands s outerFrame locals) ++ ((Outcome.resolved call.address).coreTrace.map (entry.coreLookup s outerFrame active)) ∨
      CalleeFinish program call (coreCallee entry s outerFrame call)
        (fun result => Finish entry program (corePhase entry s outerFrame) (Graph.coreConfig s outerFrame entry.cont.target)
          (delivery call.caller call.saved writes.indices (entry.insideTail.map Graph.coreEmit) result)) dst :=
  Proofs.Core.resolved_run (P := P) (s := s) ready trace prepared localTypes invoked tablesFound targets links writes

/-- Read back a failed lookup and all native trap cleanup under the live loop. -/
theorem core_lookup_trap_run (ready : entry.Checked program tables outerFrame index args)
    {locals stack : List Value} {states : List OperandState} {active : Source.Activation} {out : Outcome}
    (trace : OperandTrace locals [] entry.before states (.values stack))
    (prepared : entry.op.prepare program tables (entry.frame locals) stack = some active)
    (localTypes : locals.map Value.type = entry.owner.localTypes)
    (resolved : active.resolve program = some out) (trap : LookupTrap out)
    (tablesFound : Source.Tables.CoreAllocated tables s) (targets : active.binding.site.CoreAllocated program s)
    (links : program.CoreLinksAllocated s) {dst : Config H} :
    Steps P noHost (entry.coreConfig s outerFrame ⟨locals, .site⟩) dst ↔
      dst ∈ states.map (entry.coreOperands s outerFrame locals) ++
        (out.coreTrace.map (entry.coreLookup s outerFrame active)).dropLast ∨
      Finish entry program (corePhase entry s outerFrame) (Graph.coreConfig s outerFrame entry.cont.target)
        (coreTrap entry active out) dst :=
  Proofs.Core.lookup_trap_run (P := P) (s := s) ready trace prepared localTypes resolved trap tablesFound targets links

/-- Compose recurrent entry with a checked continuation at each reached site.
Only the reached-site proof needs native table allocation. -/
theorem core_run_through_site (ready : entry.Checked program tables outerFrame index args)
    (allocated : s.funcs[entry.address.value]? = some entry.coreInstance)
    (links : program.CoreLinksAllocated s) (site : List Value → Config H → Prop) {dst : Config H}
    (read : ∀ locals, Loop.Runs entry (entry.initial args) ⟨locals, .site⟩ →
      (Steps P noHost (entry.coreConfig s outerFrame ⟨locals, .site⟩) dst ↔ site locals dst)) :
    let start := coreSource s outerFrame index args
    let invoke := (⟨entry.cont, entry.op, entry.before⟩ : GraphEntry.Entry).coreInvoke s outerFrame args
    Steps P noHost start dst ↔ dst ∈ [start, invoke] ∨
      ObservationWithSite entry args (entry.coreConfig s outerFrame)
        (fun locals out => ∃ phase, program.FrameRuns entry.address (entry.callerPhase locals) phase ∧
          Graph.Admitted program entry.owner phase ∧ out = Graph.coreConfig s outerFrame entry.cont.target phase)
        site dst :=
  Proofs.Core.through_site (P := P) ready allocated links site read

theorem core_callee_step (checked : call.Checked program) (links : program.CoreLinksAllocated s)
    {a : Graph.Phase} {dst : Config H} (typed : Graph.Admitted program call.callee a) (live : a.LabelOutcome) :
    Step P noHost (coreCallee entry s outerFrame call a) dst ↔
      ∃ b, program.FrameEdge call.address a b ∧ dst = coreCallee entry s outerFrame call b :=
  Proofs.Core.callee_step (P := P) checked links typed live

theorem core_enter_allocated {active : Source.Activation} (invoked : active.invocation program = some call)
    (checked : call.Checked program) (targets : active.binding.site.CoreAllocated program s)
    (dst : Config H) :
    Step P noHost (entry.coreLookup s outerFrame active (.call (some call.address))) dst ↔
      dst = coreCallee entry s outerFrame call call.entered :=
  Proofs.Core.enter_allocated (P := P) invoked checked targets dst

theorem core_set_step (locals stack : List Value) (i : LocalIdx) (pending : List Admin) (dst : Config H) :
    Step P noHost (entry.coreArmWrap outerFrame
      ⟨s, (entry.frame locals).toCore, coreValues stack ++ .plain (.localSet i) :: pending⟩) dst ↔
      ∃ saved value next, stack = saved ++ [value] ∧ Locals.Edge ⟨locals, [.value value, .set i]⟩ ⟨next, []⟩ ∧
        dst = entry.coreArmWrap outerFrame ⟨s, (entry.frame next).toCore, coreValues saved ++ pending⟩ :=
  Proofs.Core.set_step (P := P) locals stack i pending dst

end Core

section Lime1

open Wasm.Lime1.Execution

variable {H : Type} {s : Store H}

/-- Exact arbitrary successors during arm writes, trap discard, and the two label exits. -/
theorem lime_finish_step_iff {a : Phase Admin} {dst : Config H} (ready : Admitted entry a) (live : a.Live) :
    Step CallFrame.limeNoHost (limePhase entry s outerFrame a) dst ↔
      ∃ b, Edge a b ∧ dst = limePhase entry s outerFrame b :=
  Proofs.Lime1.finish_step ready live

/-- Read back the arm and loop exits, then the checked function tail or
the caller function’s native trap discard and frame exit. -/
theorem lime_finish_run (ready : entry.Checked program tables outerFrame index args)
    (links : program.LimeLinksAllocated s) {a : Phase Admin} (typed : Admitted entry a) {dst : Config H} :
    Steps CallFrame.limeNoHost (limePhase entry s outerFrame a) dst ↔
      Finish entry program (limePhase entry s outerFrame) (Graph.limeConfig s outerFrame entry.cont.target) a dst :=
  Proofs.Lime1.finish_run ready links typed

/-- Read back a selected successful lookup from its operand prefix through
callee entry, the first return or callee trap, and the caller execution. -/
theorem lime_resolved_run (ready : entry.Checked program tables outerFrame index args)
    {locals stack : List Value} {states : List OperandState} {active : Source.Activation}
    (trace : OperandTrace locals [] entry.before states (.values stack))
    (prepared : entry.op.prepare program tables (entry.frame locals) stack = some active)
    (localTypes : locals.map Value.type = entry.owner.localTypes)
    (invoked : active.invocation program = some call)
    (tablesFound : Source.Tables.LimeAllocated tables s) (targets : active.binding.site.LimeAllocated program s)
    (links : program.LimeLinksAllocated s) (writes : Writes entry call.saved call.site.signature.results)
    {dst : Config H} :
    Steps CallFrame.limeNoHost (entry.limeConfig s outerFrame ⟨locals, .site⟩) dst ↔
      dst ∈ states.map (entry.limeOperands s outerFrame locals) ++ [entry.limeLookup s outerFrame active, entry.limeLookupResult s outerFrame active (.resolved call.address)] ∨
      CalleeFinish program call (limeCallee entry s outerFrame call)
        (fun result => Finish entry program (limePhase entry s outerFrame) (Graph.limeConfig s outerFrame entry.cont.target)
          (delivery call.caller call.saved writes.indices (entry.insideTail.map Graph.limeEmit) result)) dst :=
  Proofs.Lime1.resolved_run ready trace prepared localTypes invoked tablesFound targets links writes

/-- Read back a failed lookup and all native trap cleanup under the live loop. -/
theorem lime_lookup_trap_run (ready : entry.Checked program tables outerFrame index args)
    {locals stack : List Value} {states : List OperandState} {active : Source.Activation} {out : Outcome}
    (trace : OperandTrace locals [] entry.before states (.values stack))
    (prepared : entry.op.prepare program tables (entry.frame locals) stack = some active)
    (localTypes : locals.map Value.type = entry.owner.localTypes)
    (resolved : active.resolve program = some out) (trap : LookupTrap out)
    (tablesFound : Source.Tables.LimeAllocated tables s) (targets : active.binding.site.LimeAllocated program s)
    (links : program.LimeLinksAllocated s) {dst : Config H} :
    Steps CallFrame.limeNoHost (entry.limeConfig s outerFrame ⟨locals, .site⟩) dst ↔
      dst ∈ states.map (entry.limeOperands s outerFrame locals) ++ [entry.limeLookup s outerFrame active] ∨
      Finish entry program (limePhase entry s outerFrame) (Graph.limeConfig s outerFrame entry.cont.target)
        (limeTrap entry active) dst :=
  Proofs.Lime1.lookup_trap_run ready trace prepared localTypes resolved trap tablesFound targets links

/-- Compose recurrent entry with a checked continuation at each reached site.
Only the reached-site proof needs native table allocation. -/
theorem lime_run_through_site (ready : entry.Checked program tables outerFrame index args)
    (allocated : s.funcs[entry.address.value]? = some entry.limeInstance)
    (links : program.LimeLinksAllocated s) (site : List Value → Config H → Prop) {dst : Config H}
    (read : ∀ locals, Loop.Runs entry (entry.initial args) ⟨locals, .site⟩ →
      (Steps CallFrame.limeNoHost (entry.limeConfig s outerFrame ⟨locals, .site⟩) dst ↔ site locals dst)) :
    let start := limeSource s outerFrame index args
    let invoke := (⟨entry.cont, entry.op, entry.before⟩ : GraphEntry.Entry).limeInvoke s outerFrame args
    Steps CallFrame.limeNoHost start dst ↔ dst ∈ [start, invoke] ∨
      ObservationWithSite entry args (entry.limeConfig s outerFrame)
        (fun locals out => ∃ phase, program.FrameRuns entry.address (entry.callerPhase locals) phase ∧
          Graph.Admitted program entry.owner phase ∧ out = Graph.limeConfig s outerFrame entry.cont.target phase)
        site dst :=
  Proofs.Lime1.through_site ready allocated links site read

theorem lime_callee_step (checked : call.Checked program) (links : program.LimeLinksAllocated s)
    {a : Graph.Phase} {dst : Config H} (typed : Graph.Admitted program call.callee a) (live : a.LabelOutcome) :
    Step CallFrame.limeNoHost (limeCallee entry s outerFrame call a) dst ↔
      ∃ b, program.FrameEdge call.address a b ∧ dst = limeCallee entry s outerFrame call b :=
  Proofs.Lime1.callee_step checked links typed live

theorem lime_enter_allocated {active : Source.Activation} (invoked : active.invocation program = some call)
    (checked : call.Checked program) (targets : active.binding.site.LimeAllocated program s)
    (dst : Config H) :
    Step CallFrame.limeNoHost (entry.limeLookupResult s outerFrame active (.resolved call.address)) dst ↔
      dst = limeCallee entry s outerFrame call call.entered :=
  Proofs.Lime1.enter_allocated invoked checked targets dst

theorem lime_set_step (locals stack : List Value) (i : LocalIdx) (pending : List Admin) (dst : Config H) :
    Step CallFrame.limeNoHost (entry.limeArmWrap outerFrame
      ⟨s, entry.frame locals, values stack ++ .source (.localSet i) :: pending⟩) dst ↔
      ∃ saved value next, stack = saved ++ [value] ∧ Locals.Edge ⟨locals, [.value value, .set i]⟩ ⟨next, []⟩ ∧
        dst = entry.limeArmWrap outerFrame ⟨s, entry.frame next, values saved ++ pending⟩ :=
  Proofs.Lime1.set_step locals stack i pending dst

end Lime1

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Resume
