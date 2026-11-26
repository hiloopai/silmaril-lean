module

public import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Resume.Common
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Thms
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Wasm.Institution.Operational.Locals.Native.Thms
import Silmaril.Wasm.Institution.Operational.Loops.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Mathlib.Data.List.Chain

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Resume.Proofs.Lime1

open Execution
open Wasm.Lime1.Execution
open Execution.Runtime (Value)
open CallContinuation
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked
open Wasm.SingleThreaded.Det (noHost)

variable {H : Type} {s : Store H} {entry : Entry} {program : Graph.Program}
  {tables : Source.Tables} {outer : Runtime.Frame} {index : FuncIdx} {args : List Value}
  {call : Context.Invocation}

private theorem arm_cases {body dst : Config H} :
    Step CallFrame.limeNoHost (entry.limeArmWrap outer body) dst ↔
      (∃ mid, Step CallFrame.limeNoHost body mid ∧ dst = entry.limeArmWrap outer mid) ∨
      ∃ out, PureStep body.frame.module.types [.label entry.result.toList.length [] body.code] out ∧
        dst = entry.limeLoopWrap outer { body with code := out } := by
  have remains (out : List Admin) :
      ¬ PureStep body.frame.module.types [.label 0 [entry.limeLoop] [.label entry.result.toList.length [] body.code]] out :=
    Computed.lime_label_stays (types := body.frame.module.types) (head := .label entry.result.toList.length [] body.code)
      (stack := []) (rest := []) rfl (by simp) (by simp) (by simp)
  rw [Entry.limeArmWrap, Loop.lime_loop_wrap_step_iff remains]
  have invert (mid : Config H) := Blocks.Context.lime_label_iff (s := body.store) (f := body.frame)
    (n := entry.result.toList.length) (saved := []) (rest := []) (body := body.code) (dst := mid)
  constructor
  · rintro ⟨mid, move, rfl⟩
    rcases (invert mid).mp move with ⟨next, inside, eq⟩ | ⟨out, leave, eq⟩
    · exact .inl ⟨next, inside, by rw [eq]; rfl⟩
    · exact .inr ⟨out, leave, by simp [eq, values]⟩
  · rintro (⟨mid, move, rfl⟩ | ⟨out, leave, rfl⟩)
    · exact ⟨_, (invert _).mpr (.inl ⟨mid, move, rfl⟩), rfl⟩
    · exact ⟨_, (invert _).mpr (.inr ⟨out, leave, by simp [List.nil_append, List.append_nil, values]⟩), rfl⟩

private theorem under_arm {body dst : Config H}
    (stays : ∀ out, ¬ PureStep body.frame.module.types [.label entry.result.toList.length [] body.code] out) :
    Step CallFrame.limeNoHost (entry.limeArmWrap outer body) dst ↔
      ∃ mid, Step CallFrame.limeNoHost body mid ∧ dst = entry.limeArmWrap outer mid := by
  rw [arm_cases]
  exact or_iff_left (fun ⟨out, exit, _⟩ => stays out exit)

theorem set_step (locals stack : List Value) (i : LocalIdx) (pending : List Admin) (dst : Config H) :
    Step CallFrame.limeNoHost (entry.limeArmWrap outer
      ⟨s, entry.frame locals, values stack ++ .source (.localSet i) :: pending⟩) dst ↔
      ∃ saved value next, stack = saved ++ [value] ∧ Locals.Edge ⟨locals, [.value value, .set i]⟩ ⟨next, []⟩ ∧
        dst = entry.limeArmWrap outer ⟨s, entry.frame next, values saved ++ pending⟩ := by
  have stays (out : List Admin) :
      ¬ PureStep (entry.frame locals).module.types [.label entry.result.toList.length [] (values stack ++ .source (.localSet i) :: pending)] out :=
    Computed.lime_label_stays (types := (entry.frame locals).module.types) (head := .source (.localSet i))
      rfl (by simp) (by simp) (by simp)
  change Step CallFrame.limeNoHost (entry.limeArmWrap outer ⟨s, entry.frame locals, values stack ++ .source (.localSet i) :: pending⟩) dst ↔ _
  rw [under_arm stays]
  constructor
  · rintro ⟨mid, moved, rfl⟩
    obtain ⟨saved, value, next, rfl, wrote, rfl⟩ := Computed.lime_set_read (f := entry.frame locals) moved
    exact ⟨saved, value, next, rfl, wrote, rfl⟩
  · rintro ⟨saved, value, next, rfl, wrote, rfl⟩
    refine ⟨⟨s, entry.frame next, values saved ++ pending⟩, ?_, rfl⟩
    have head := Locals.lime_sound (host := CallFrame.limeNoHost) (s := s)
      (m := entry.owner.declaration.module) wrote
    have lifted := Step.context head saved pending
    rcases value with ⟨ty, bits⟩
    cases ty <;>
      simpa [Locals.Codec.encode, Locals.limeCodec, Locals.legacyCodec, Locals.limeInstr,
        values, List.map_append, List.append_assoc] using! lifted


private theorem write_step (locals stack : List Value) (i : LocalIdx) (rest : List LocalIdx) (dst : Config H) :
    Step CallFrame.limeNoHost (limePhase entry s outer (.write locals stack (i :: rest))) dst ↔
      ∃ b, Edge (.write locals stack (i :: rest)) b ∧ dst = limePhase entry s outer b := by
  let pending := rest.map (fun j => Execution.Runtime.AdminInstr.source (Wasm.Lime1.Instr.localSet j))
  refine (set_step locals stack i pending dst).trans ⟨?_, ?_⟩
  · rintro ⟨_, _, _, rfl, wrote, rfl⟩
    exact ⟨_, .write rfl wrote, rfl⟩
  · rintro ⟨b, move, rfl⟩
    cases move with
    | write split wrote => exact ⟨_, _, _, split, wrote, rfl⟩

private theorem trap_arm_step (locals stack : List Value) (pending : List Admin) (dst : Config H) :
    Step CallFrame.limeNoHost (limePhase entry s outer (.armTrap locals stack pending)) dst ↔
      ∃ b, Edge (.armTrap locals stack pending) b ∧ dst = limePhase entry s outer b := by
  change Step CallFrame.limeNoHost (entry.limeArmWrap outer ⟨s, entry.frame locals, values stack ++ .trap :: pending⟩) dst ↔ _
  rw [arm_cases]
  have discard (mid : Config H) : Step CallFrame.limeNoHost ⟨s, entry.frame locals, values stack ++ .trap :: pending⟩ mid ↔
      ∃ kept rest, Prefix.Discard stack pending kept rest ∧ mid = ⟨s, entry.frame locals, values kept ++ .trap :: rest⟩ := by
    simpa only [List.map_id] using Prefix.lime_discard_iff (s := s) (f := entry.frame locals) id (dst := mid)
  constructor
  · rintro (⟨mid, move, rfl⟩ | ⟨out, pop, rfl⟩)
    · obtain ⟨kept, rest, cut, rfl⟩ := (discard mid).mp move
      exact ⟨_, .discard cut, rfl⟩
    · have empty : stack = [] ∧ pending = [] := by
        by_contra nonempty
        refine Computed.lime_label_stays (types := (entry.frame locals).module.types) (stack := stack) (rest := pending)
          (head := .trap) rfl (by simp) (by simp) ?_ pop
        intro _
        rcases not_and_or.mp nonempty with before | after
        · exact .inl before
        · exact .inr after
      obtain ⟨rfl, rfl⟩ := empty
      exact ⟨_, .leaveTrapArm locals, by rw [Nested.lime_label_result (r := .trap) pop]; rfl⟩
  · rintro ⟨b, move, rfl⟩
    cases move with
    | discard cut => exact .inl ⟨_, (discard _).mpr ⟨_, _, cut, rfl⟩, rfl⟩
    | leaveTrapArm => exact .inr ⟨[.trap], (.labelTrap _ []), rfl⟩

private theorem empty_arm_step (locals : List Value) (dst : Config H) :
    Step CallFrame.limeNoHost (limePhase entry s outer (.write locals [] [])) dst ↔ dst = limePhase entry s outer (.loop locals false) := by
  change Step CallFrame.limeNoHost (entry.limeArmWrap outer ⟨s, entry.frame locals, []⟩) dst ↔ _
  rw [arm_cases]
  constructor
  · rintro (⟨mid, move, _⟩ | ⟨out, pop, rfl⟩)
    · exact (Nested.lime_result_stuck (r := .values []) move).elim
    · rw [Nested.lime_label_result (r := .values []) pop]
      rfl
  · rintro rfl
    exact .inr ⟨[], (.labelDone _ [] []), rfl⟩

private theorem exit_loop_step (locals : List Value) (trapped : Bool) (dst : Config H) :
    Step CallFrame.limeNoHost (limePhase entry s outer (.loop locals trapped)) dst ↔
      dst = limePhase entry s outer (.caller locals trapped) := by
  let code : List Admin := if trapped then [.trap] else []
  let body : Config H := ⟨s, entry.frame locals, values entry.owner.initial ++
    .label 0 [entry.limeLoop] code :: entry.tail.map Graph.limeEmit⟩
  have stays (out : List Admin) :
      ¬ PureStep body.frame.module.types [.label entry.owner.declaration.results.length [] body.code] out :=
    Computed.lime_label_stays (types := body.frame.module.types) (head := .label 0 [entry.limeLoop] code)
      rfl (by simp) (by simp) (by simp)
  change Step CallFrame.limeNoHost (entry.cont.limeWrap outer body) dst ↔ _
  rw [Context.Resume.lime_wrap_step_iff stays]
  have exactStep (mid : Config H) : Step CallFrame.limeNoHost body mid ↔
      mid = ⟨s, entry.frame locals, values entry.owner.initial ++ code ++ entry.tail.map Graph.limeEmit⟩ := by
    cases trapped with
    | false =>
      simpa only [code, body, Nested.resultCode, values,
        List.map_nil, List.nil_append, List.append_nil, Bool.false_eq_true, ite_false] using!
        Loops.lime_result_iff (s := s) (f := entry.frame locals) (r := .values [])
          (cont := [entry.limeLoop]) (saved := entry.owner.initial) (rest := entry.tail.map Graph.limeEmit) (dst := mid)
    | true =>
      simpa only [code, body, Nested.resultCode, ite_true] using!
        Loops.lime_result_iff (s := s) (f := entry.frame locals) (r := .trap)
          (cont := [entry.limeLoop]) (saved := entry.owner.initial) (rest := entry.tail.map Graph.limeEmit) (dst := mid)
  simp only [exactStep, exists_eq_left]
  cases trapped <;>
    simp [code, limePhase, entryPhase, Entry.callerPhase, Graph.limeConfig, Graph.Phase.render,
      Graph.Phase.renderAt, Graph.Body.render, Graph.limeAdmin, Graph.LabelKind.arity, Graph.LabelKind.cont,
      Entry.frame, Context.Resume.Continuation.target, Context.Resume.Continuation.limeWrap,
      List.append_assoc] <;> rfl

theorem finish_step {a : Phase Admin} {dst : Config H} (ready : Admitted entry a) (live : a.Live) :
    Step CallFrame.limeNoHost (limePhase entry s outer a) dst ↔
      ∃ b, Edge a b ∧ dst = limePhase entry s outer b := by
  cases a with
  | write locals stack indices =>
    cases indices with
    | cons i rest => exact write_step locals stack i rest dst
    | nil =>
      obtain rfl := empty_stack ready
      rw [empty_arm_step]
      exact ⟨fun eq => ⟨_, .leaveArm locals, eq⟩, fun ⟨_, move, eq⟩ => by cases move; exact eq⟩
  | armTrap locals stack rest => exact trap_arm_step locals stack rest dst
  | loop locals trapped =>
    rw [exit_loop_step]
    exact ⟨fun eq => ⟨_, .leaveLoop locals trapped, eq⟩, fun ⟨_, move, eq⟩ => by cases move; exact eq⟩
  | caller => exact live.elim

theorem finish_run (ready : entry.Checked program tables outer index args)
    (links : program.LimeLinksAllocated s) {a : Phase Admin} (typed : Admitted entry a) {dst : Config H} :
    Steps CallFrame.limeNoHost (limePhase entry s outer a) dst ↔
      Finish entry program (limePhase entry s outer) (Graph.limeConfig s outer entry.cont.target) a dst := by
  apply finish_iff _ _ _ typed finish_step
  intro locals trapped out current
  have valid : Graph.Admitted program entry.owner (entryPhase entry locals trapped) := by
    cases trapped
    · exact Loop.caller_admitted ready current
    · exact .trapped current
  have live : (entryPhase entry locals trapped).LabelOutcome := by cases trapped <;> trivial
  exact (Context.linked_runs (Loop.graph_checked ready) ready.found
    (Graph.limeConfig s outer entry.cont.target) (Step CallFrame.limeNoHost)
    (fun h entered => Graph.lime_entered_frame_step_iff (Loop.graph_checked ready) links ready.found rfl h entered)
    valid live).trans
      ⟨fun ⟨phase, run, _, eq⟩ => ⟨phase, run, eq⟩, fun ⟨phase, run, eq⟩ =>
        ⟨phase, run, program.frame_admitted_run (Loop.graph_checked ready) ready.found valid run, eq⟩⟩

theorem callee_step (checked : call.Checked program) (links : program.LimeLinksAllocated s)
    {a : Graph.Phase} {dst : Config H} (typed : Graph.Admitted program call.callee a) (live : a.LabelOutcome) :
    Step CallFrame.limeNoHost (limeCallee entry s outer call a) dst ↔
      ∃ b, program.FrameEdge call.address a b ∧ dst = limeCallee entry s outer call b := by
  obtain ⟨n, frame, code, render⟩ := Context.lime_frame_shape (call := call) live
  have stays (out : List Admin) :
      ¬ PureStep call.caller.module.types [.label entry.result.toList.length [] (call.limeCallee s (entry.insideTail.map Graph.limeEmit) a).code] out := by
    simp only [Context.Invocation.limeCallee, render, List.append_assoc, List.singleton_append]
    exact Computed.lime_label_stays (head := Execution.Runtime.AdminInstr.frame n frame code)
      rfl (by simp) (by simp) (by simp)
  change Step CallFrame.limeNoHost (entry.limeArmWrap outer (call.limeCallee s (entry.insideTail.map Graph.limeEmit) a)) dst ↔ _
  rw [under_arm stays]
  constructor
  · rintro ⟨mid, move, rfl⟩
    obtain ⟨b, step, rfl⟩ := (Context.lime_linked_frame_step_iff checked links typed live).mp move
    exact ⟨b, step, rfl⟩
  · rintro ⟨b, step, rfl⟩
    exact ⟨_, (Context.lime_linked_frame_step_iff checked links typed live).mpr ⟨b, step, rfl⟩, rfl⟩

private theorem deliver_eq (same : call.caller.module = entry.owner.declaration.module)
    (writes : Writes entry call.saved call.site.signature.results) (result : Nested.Result) :
    limeCallee entry s outer call (.done result) =
      limePhase entry s outer (delivery call.caller call.saved writes.indices
        (entry.insideTail.map Graph.limeEmit) result) := by
  have frame : entry.frame call.caller.locals = call.caller :=
    congrArg (fun m => (⟨call.caller.locals, m⟩ : Runtime.Frame)) same.symm
  cases result <;>
    simp [frame, limeCallee, limePhase, delivery, Context.Invocation.limeCallee, Graph.Phase.render,
      Graph.Phase.renderAt, Graph.limeAdmin, Graph.limeEmit, Graph.Op.emit, Graph.limeCodeSyntax,
      Nested.resultCode, values, writes.source, List.map_append,
      List.map_map, List.append_assoc, Function.comp_def]

theorem callee_run (ready : entry.Checked program tables outer index args)
    (checked : call.Checked program) (links : program.LimeLinksAllocated s)
    (same : call.caller.module = entry.owner.declaration.module)
    (locals : call.caller.locals.map Value.type = entry.owner.localTypes)
    (writes : Writes entry call.saved call.site.signature.results) {dst : Config H} :
    Steps CallFrame.limeNoHost (limeCallee entry s outer call call.entered) dst ↔
      CalleeFinish program call (limeCallee entry s outer call)
        (fun result => Finish entry program (limePhase entry s outer) (Graph.limeConfig s outer entry.cont.target)
          (delivery call.caller call.saved writes.indices (entry.insideTail.map Graph.limeEmit) result)) dst := by
  apply callee_iff checked _ _ _ (callee_step checked links)
  intro result out admitted
  rw [deliver_eq same writes]
  exact finish_run ready links (deliver_admitted checked locals writes admitted _)


private theorem enter {active : Source.Activation} (invoked : active.invocation program = some call)
    (checked : call.Checked program) (allocated : s.funcs[call.address.value]? = some (.wasm call.callee.declaration.type call.callee.declaration.module call.callee.limeFunc))
    (dst : Config H) :
    Step CallFrame.limeNoHost (entry.limeLookupResult s outer active (.resolved call.address)) dst ↔
      dst = limeCallee entry s outer call call.entered := by
  obtain ⟨address, callee, _, _, rfl⟩ := Source.invocation_fields invoked
  let body := Indirect.limeResolved s active.caller (active.operands.saved ++ active.operands.args)
    (entry.insideTail.map Graph.limeEmit) (.resolved address)
  have stays (out : List Admin) : ¬ PureStep active.caller.module.types
      [.label entry.result.toList.length [] body.code] out :=
    Indirect.lime_invoke_stays _ out
  change Step CallFrame.limeNoHost (entry.limeArmWrap outer body) dst ↔ _
  rw [under_arm stays]
  have move (target : Config H) := Indirect.lime_enter_at_iff (caller := active.caller)
    (saved := active.operands.saved) (rest := entry.insideTail.map Graph.limeEmit)
    (dst := target) allocated checked.found checked.resolved checked.typed
  simp only [body, move, exists_eq_left]
  let resolvedCall : Context.Invocation := ⟨active.binding.site, active.caller, active.operands.selector,
    active.operands.saved, active.operands.args, address, callee⟩
  have entered := Context.lime_entered_config (s := s) (call := resolvedCall)
    (rest := entry.insideTail.map Graph.limeEmit)
  exact Iff.of_eq (congrArg (fun cfg => dst = entry.limeArmWrap outer cfg) entered)



private theorem allocation {active : Source.Activation}
    (invoked : active.invocation program = some call) (targets : active.binding.site.LimeAllocated program s) :
    s.funcs[call.address.value]? = some (.wasm call.callee.declaration.type call.callee.declaration.module call.callee.limeFunc) := by
  obtain ⟨address, callee, resolved, found, rfl⟩ := Source.invocation_fields invoked
  cases Indirect.resolve_iff.mp resolved with
  | resolved selected _ _ => exact targets address callee (List.mem_of_getElem? selected) found

theorem enter_allocated {active : Source.Activation} (invoked : active.invocation program = some call)
    (checked : call.Checked program) (targets : active.binding.site.LimeAllocated program s)
    (dst : Config H) :
    Step CallFrame.limeNoHost (entry.limeLookupResult s outer active (.resolved call.address)) dst ↔
      dst = limeCallee entry s outer call call.entered :=
  enter invoked checked (allocation invoked targets) dst

theorem resolved_run (ready : entry.Checked program tables outer index args)
    {locals stack : List Value} {states : List OperandState} {active : Source.Activation}
    (trace : OperandTrace locals [] entry.before states (.values stack))
    (prepared : entry.op.prepare program tables (entry.frame locals) stack = some active)
    (localTypes : locals.map Value.type = entry.owner.localTypes)
    (invoked : active.invocation program = some call)
    (tablesFound : Source.Tables.LimeAllocated tables s) (targets : active.binding.site.LimeAllocated program s)
    (links : program.LimeLinksAllocated s) (writes : Writes entry call.saved call.site.signature.results)
    {dst : Config H} :
    Steps CallFrame.limeNoHost (entry.limeConfig s outer ⟨locals, .site⟩) dst ↔
      dst ∈ states.map (entry.limeOperands s outer locals) ++ [entry.limeLookup s outer active, entry.limeLookupResult s outer active (.resolved call.address)] ∨
      CalleeFinish program call (limeCallee entry s outer call)
        (fun result => Finish entry program (limePhase entry s outer) (Graph.limeConfig s outer entry.cont.target)
          (delivery call.caller call.saved writes.indices (entry.insideTail.map Graph.limeEmit) result)) dst := by
  have facts := Source.prepare_spec prepared
  have checked := Source.invocation_checked facts.checked (Loop.graph_checked ready) invoked
  have caller : call.caller = entry.frame locals := by
    obtain ⟨_, _, _, _, rfl⟩ := Source.invocation_fields invoked
    exact facts.caller_eq
  have resolved : active.resolve program = some (.resolved call.address) := by
    obtain ⟨_, _, resolved, _, rfl⟩ := Source.invocation_fields invoked
    exact resolved
  let before := [entry.limeLookup s outer active, entry.limeLookupResult s outer active (.resolved call.address)]
  have linked : (before ++ [limeCallee entry s outer call call.entered]).IsChain
      (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) :=
    List.isChain_cons_cons.mpr ⟨Loop.lime_lookup_exact facts.checked targets tablesFound resolved,
      List.isChain_pair.mpr (enter invoked checked (allocation invoked targets))⟩
  have fromSite := Loop.lime_operand_run_iff (s := s) (outerFrame := outer) trace (dst := dst)
  rw [Loop.lime_lookup_start prepared] at fromSite
  have path := Context.Resume.prefix_run_iff (dst := dst) before _ linked
  refine (fromSite.trans (or_congr Iff.rfl
    (path.trans (or_congr Iff.rfl (callee_run ready checked links ?_ ?_ writes))))).trans ?_
  · rw [caller]
    rfl
  · simpa only [caller, Entry.frame, Graph.currentFrame] using localTypes
  · rw [List.mem_append, or_assoc]

theorem lookup_trap_run (ready : entry.Checked program tables outer index args)
    {locals stack : List Value} {states : List OperandState} {active : Source.Activation} {out : Outcome}
    (trace : OperandTrace locals [] entry.before states (.values stack))
    (prepared : entry.op.prepare program tables (entry.frame locals) stack = some active)
    (localTypes : locals.map Value.type = entry.owner.localTypes)
    (resolved : active.resolve program = some out) (trap : LookupTrap out)
    (tablesFound : Source.Tables.LimeAllocated tables s) (targets : active.binding.site.LimeAllocated program s)
    (links : program.LimeLinksAllocated s) {dst : Config H} :
    Steps CallFrame.limeNoHost (entry.limeConfig s outer ⟨locals, .site⟩) dst ↔
      dst ∈ states.map (entry.limeOperands s outer locals) ++ [entry.limeLookup s outer active] ∨
      Finish entry program (limePhase entry s outer) (Graph.limeConfig s outer entry.cont.target)
        (limeTrap entry active) dst := by
  have facts := Source.prepare_spec prepared
  let trapped := limePhase entry s outer (limeTrap entry active)
  have last : entry.limeLookupResult s outer active out = trapped := by
    cases trap <;> simp [trapped, Entry.limeLookupResult, Source.Activation.limeResolved, Indirect.limeResolved,
      limeTrap, limePhase, facts.caller_eq, Entry.limeArmWrap, Entry.armScope, Context.limeNestWith, values] <;> rfl
  have step (target : Config H) := Loop.lime_lookup_exact (entry := entry) (outerFrame := outer)
    facts.checked targets tablesFound resolved target
  have chain : ([entry.limeLookup s outer active] ++ [trapped]).IsChain
      (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) :=
    List.isChain_pair.mpr (fun target => (step target).trans (by rw [last]))
  have read := Context.Resume.prefix_run_iff (dst := dst) [entry.limeLookup s outer active] trapped chain
  have fromSite := Loop.lime_operand_run_iff (s := s) (outerFrame := outer) trace (dst := dst)
  rw [Loop.lime_lookup_start prepared] at fromSite
  have live : Admitted entry (limeTrap entry active) := by
    simpa only [limeTrap, Admitted, facts.caller_eq, Entry.frame, Graph.currentFrame] using localTypes
  refine (fromSite.trans (or_congr Iff.rfl (read.trans (or_congr Iff.rfl
    (finish_run ready links live))))).trans ?_
  rw [List.mem_append, or_assoc]

theorem through_site (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.address.value]? = some entry.limeInstance)
    (links : program.LimeLinksAllocated s) (site : List Value → Config H → Prop) {dst : Config H}
    (read : ∀ locals, Loop.Runs entry (entry.initial args) ⟨locals, .site⟩ →
      (Steps CallFrame.limeNoHost (entry.limeConfig s outer ⟨locals, .site⟩) dst ↔ site locals dst)) :
    let start := limeSource s outer index args
    let invoke := (⟨entry.cont, entry.op, entry.before⟩ : GraphEntry.Entry).limeInvoke s outer args
    Steps CallFrame.limeNoHost start dst ↔ dst ∈ [start, invoke] ∨
      ObservationWithSite entry args (entry.limeConfig s outer)
        (fun locals out => ∃ phase, program.FrameRuns entry.address (entry.callerPhase locals) phase ∧
          Graph.Admitted program entry.owner phase ∧ out = Graph.limeConfig s outer entry.cont.target phase)
        site dst := by
  exact (Loop.lime_run_iff ready allocated links).trans
    (or_congr Iff.rfl (observation_iff _ (Step CallFrame.limeNoHost) _ site read))

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Resume.Proofs.Lime1
