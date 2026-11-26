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

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Resume.Proofs.Core

open Execution
open Execution.Core
open Execution.Runtime (Value)
open CallContinuation
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked
open Wasm.SingleThreaded.Det (noHost)

variable {H : Type} {P : Numerics.Profile} {s : Store H} {entry : Entry} {program : Graph.Program}
  {tables : Source.Tables} {outer : Runtime.Frame} {index : FuncIdx} {args : List Value}
  {call : Context.Invocation}

private theorem arm_cases {body dst : Config H} :
    Step P noHost (entry.coreArmWrap outer body) dst ↔
      (∃ mid, Step P noHost body mid ∧ dst = entry.coreArmWrap outer mid) ∨
      ∃ out, LabelExit entry.result.toList.length [] body.code out ∧
        dst = entry.coreLoopWrap outer { body with code := out } := by
  have remains (out : List Admin) :
      ¬ LabelExit 0 [entry.coreLoop] [.label entry.result.toList.length [] body.code] out :=
    Computed.core_label_stays (head := .label entry.result.toList.length [] body.code)
      (stack := []) (rest := []) rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp)
  rw [Entry.coreArmWrap, Loop.core_loop_wrap_step_iff remains]
  have invert (mid : Config H) := Blocks.Context.core_label_iff (P := P) (s := body.store) (f := body.frame)
    (n := entry.result.toList.length) (saved := []) (rest := []) (body := body.code) (dst := mid)
  constructor
  · rintro ⟨mid, move, rfl⟩
    rcases (invert mid).mp move with ⟨next, inside, eq⟩ | ⟨out, leave, eq⟩
    · exact .inl ⟨next, inside, by rw [eq]; rfl⟩
    · exact .inr ⟨out, leave, by simp [eq, vals]⟩
  · rintro (⟨mid, move, rfl⟩ | ⟨out, leave, rfl⟩)
    · exact ⟨_, (invert _).mpr (.inl ⟨mid, move, rfl⟩), rfl⟩
    · exact ⟨_, (invert _).mpr (.inr ⟨out, leave, by simp [List.nil_append, List.append_nil, vals]⟩), rfl⟩

private theorem under_arm {body dst : Config H}
    (stays : ∀ out, ¬ LabelExit entry.result.toList.length [] body.code out) :
    Step P noHost (entry.coreArmWrap outer body) dst ↔
      ∃ mid, Step P noHost body mid ∧ dst = entry.coreArmWrap outer mid := by
  rw [arm_cases]
  exact or_iff_left (fun ⟨out, exit, _⟩ => stays out exit)

theorem set_step (locals stack : List Value) (i : LocalIdx) (pending : List Admin) (dst : Config H) :
    Step P noHost (entry.coreArmWrap outer
      ⟨s, (entry.frame locals).toCore, coreValues stack ++ .plain (.localSet i) :: pending⟩) dst ↔
      ∃ saved value next, stack = saved ++ [value] ∧ Locals.Edge ⟨locals, [.value value, .set i]⟩ ⟨next, []⟩ ∧
        dst = entry.coreArmWrap outer ⟨s, (entry.frame next).toCore, coreValues saved ++ pending⟩ := by
  have stays (out : List Admin) :
      ¬ LabelExit entry.result.toList.length [] (coreValues stack ++ .plain (.localSet i) :: pending) out :=
    Computed.core_label_stays (head := .plain (.localSet i))
      rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp)
  change Step P noHost (entry.coreArmWrap outer ⟨s, (entry.frame locals).toCore, coreValues stack ++ .plain (.localSet i) :: pending⟩) dst ↔ _
  rw [under_arm stays]
  constructor
  · rintro ⟨mid, moved, rfl⟩
    obtain ⟨saved, value, next, rfl, wrote, rfl⟩ := Computed.core_set_read (f := entry.frame locals) moved
    exact ⟨saved, value, next, rfl, wrote, rfl⟩
  · rintro ⟨saved, value, next, rfl, wrote, rfl⟩
    refine ⟨⟨s, (entry.frame next).toCore, coreValues saved ++ pending⟩, ?_, rfl⟩
    have head := Locals.core_sound (P := P) (s := s) (m := entry.owner.declaration.module.toCore) wrote
    have lifted := Wasm.SingleThreaded.Det.lift_instrs (saved.map Value.toCore) pending _ _ head
    rcases value with ⟨ty, bits⟩
    cases ty <;>
      simpa [Locals.coreConfig, Locals.Codec.encode, Locals.coreCodec, Locals.coreInstr,
        coreValues, vals, List.map_append, List.append_assoc] using! lifted


private theorem write_step (locals stack : List Value) (i : LocalIdx) (rest : List LocalIdx) (dst : Config H) :
    Step P noHost (corePhase entry s outer (.write locals stack (i :: rest))) dst ↔
      ∃ b, Edge (.write locals stack (i :: rest)) b ∧ dst = corePhase entry s outer b := by
  let pending := rest.map (fun j => Admin.plain (.localSet j))
  refine (set_step (P := P) locals stack i pending dst).trans ⟨?_, ?_⟩
  · rintro ⟨_, _, _, rfl, wrote, rfl⟩
    exact ⟨_, .write rfl wrote, rfl⟩
  · rintro ⟨b, move, rfl⟩
    cases move with
    | write split wrote => exact ⟨_, _, _, split, wrote, rfl⟩

private theorem trap_arm_step (locals stack : List Value) (pending : List Admin) (dst : Config H) :
    Step P noHost (corePhase entry s outer (.armTrap locals stack pending)) dst ↔
      ∃ b, Edge (.armTrap locals stack pending) b ∧ dst = corePhase entry s outer b := by
  change Step P noHost (entry.coreArmWrap outer ⟨s, (entry.frame locals).toCore, coreValues stack ++ .trap :: pending⟩) dst ↔ _
  rw [arm_cases]
  have discard (mid : Config H) : Step P noHost ⟨s, (entry.frame locals).toCore, coreValues stack ++ .trap :: pending⟩ mid ↔
      ∃ kept rest, Prefix.Discard stack pending kept rest ∧ mid = ⟨s, (entry.frame locals).toCore, coreValues kept ++ .trap :: rest⟩ := by
    simpa only [List.map_id] using Prefix.core_discard_iff (P := P) (s := s) (f := entry.frame locals) id (dst := mid)
  constructor
  · rintro (⟨mid, move, rfl⟩ | ⟨out, pop, rfl⟩)
    · obtain ⟨kept, rest, cut, rfl⟩ := (discard mid).mp move
      exact ⟨_, .discard cut, rfl⟩
    · have empty : stack = [] ∧ pending = [] := by
        by_contra nonempty
        refine Computed.core_label_stays (stack := stack.map Value.toCore) (rest := pending)
          (head := .trap) rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) ?_ pop
        intro _
        rcases not_and_or.mp nonempty with before | after
        · exact .inl (fun nil => before (List.map_eq_nil_iff.mp nil))
        · exact .inr after
      obtain ⟨rfl, rfl⟩ := empty
      exact ⟨_, .leaveTrapArm locals, by rw [Nested.core_label_result (r := .trap) pop]; rfl⟩
  · rintro ⟨b, move, rfl⟩
    cases move with
    | discard cut => exact .inl ⟨_, (discard _).mpr ⟨_, _, cut, rfl⟩, rfl⟩
    | leaveTrapArm => exact .inr ⟨[.trap], .trap, rfl⟩

private theorem empty_arm_step (locals : List Value) (dst : Config H) :
    Step P noHost (corePhase entry s outer (.write locals [] [])) dst ↔ dst = corePhase entry s outer (.loop locals false) := by
  change Step P noHost (entry.coreArmWrap outer ⟨s, (entry.frame locals).toCore, []⟩) dst ↔ _
  rw [arm_cases]
  constructor
  · rintro (⟨mid, move, _⟩ | ⟨out, pop, rfl⟩)
    · exact (Nested.core_result_stuck (r := .values []) move).elim
    · rw [Nested.core_label_result (r := .values []) pop]
      rfl
  · rintro rfl
    exact .inr ⟨[], .vals [], rfl⟩

private theorem exit_loop_step (locals : List Value) (trapped : Bool) (dst : Config H) :
    Step P noHost (corePhase entry s outer (.loop locals trapped)) dst ↔
      dst = corePhase entry s outer (.caller locals trapped) := by
  let code : List Admin := if trapped then [.trap] else []
  let body : Config H := ⟨s, (entry.frame locals).toCore, coreValues entry.owner.initial ++
    .label 0 [entry.coreLoop] code :: entry.tail.map Graph.coreEmit⟩
  have stays (out : List Admin) :
      ¬ LabelExit entry.owner.declaration.results.length [] body.code out :=
    Computed.core_label_stays (head := .label 0 [entry.coreLoop] code)
      rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp)
  change Step P noHost (entry.cont.coreWrap outer body) dst ↔ _
  rw [Context.Resume.core_wrap_step_iff stays]
  have exactStep (mid : Config H) : Step P noHost body mid ↔
      mid = ⟨s, (entry.frame locals).toCore, coreValues entry.owner.initial ++ code ++ entry.tail.map Graph.coreEmit⟩ := by
    cases trapped with
    | false =>
      simpa only [code, body, Nested.resultCode, Blocks.Context.coreValues, coreValues, vals,
        List.map_nil, List.nil_append, List.append_nil, Bool.false_eq_true, ite_false] using!
        Loops.core_result_iff (P := P) (s := s) (f := (entry.frame locals).toCore) (r := .values [])
          (cont := [entry.coreLoop]) (saved := entry.owner.initial.map Value.toCore) (rest := entry.tail.map Graph.coreEmit) (dst := mid)
    | true =>
      simpa only [code, body, Nested.resultCode, ite_true] using!
        Loops.core_result_iff (P := P) (s := s) (f := (entry.frame locals).toCore) (r := .trap)
          (cont := [entry.coreLoop]) (saved := entry.owner.initial.map Value.toCore) (rest := entry.tail.map Graph.coreEmit) (dst := mid)
  simp only [exactStep, exists_eq_left]
  cases trapped <;>
    simp [code, corePhase, entryPhase, Entry.callerPhase, Graph.coreConfig, Graph.Phase.render,
      Graph.Phase.renderAt, Graph.Body.render, Graph.coreAdmin, Graph.LabelKind.arity, Graph.LabelKind.cont,
      Entry.frame, Context.Resume.Continuation.target, Context.Resume.Continuation.coreWrap,
      List.append_assoc] <;> rfl

theorem finish_step {a : Phase Admin} {dst : Config H} (ready : Admitted entry a) (live : a.Live) :
    Step P noHost (corePhase entry s outer a) dst ↔
      ∃ b, Edge a b ∧ dst = corePhase entry s outer b := by
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
    (links : program.CoreLinksAllocated s) {a : Phase Admin} (typed : Admitted entry a) {dst : Config H} :
    Steps P noHost (corePhase entry s outer a) dst ↔
      Finish entry program (corePhase entry s outer) (Graph.coreConfig s outer entry.cont.target) a dst := by
  apply finish_iff _ _ _ typed finish_step
  intro locals trapped out current
  have valid : Graph.Admitted program entry.owner (entryPhase entry locals trapped) := by
    cases trapped
    · exact Loop.caller_admitted ready current
    · exact .trapped current
  have live : (entryPhase entry locals trapped).LabelOutcome := by cases trapped <;> trivial
  exact (Context.linked_runs (Loop.graph_checked ready) ready.found
    (Graph.coreConfig s outer entry.cont.target) (Step P noHost)
    (fun h entered => Graph.core_entered_frame_step_iff (Loop.graph_checked ready) links ready.found rfl h entered)
    valid live).trans
      ⟨fun ⟨phase, run, _, eq⟩ => ⟨phase, run, eq⟩, fun ⟨phase, run, eq⟩ =>
        ⟨phase, run, program.frame_admitted_run (Loop.graph_checked ready) ready.found valid run, eq⟩⟩

theorem callee_step (checked : call.Checked program) (links : program.CoreLinksAllocated s)
    {a : Graph.Phase} {dst : Config H} (typed : Graph.Admitted program call.callee a) (live : a.LabelOutcome) :
    Step P noHost (coreCallee entry s outer call a) dst ↔
      ∃ b, program.FrameEdge call.address a b ∧ dst = coreCallee entry s outer call b := by
  obtain ⟨n, frame, code, render⟩ := Context.core_frame_shape (call := call) live
  have stays (out : List Admin) :
      ¬ LabelExit entry.result.toList.length [] (call.coreCallee s (entry.insideTail.map Graph.coreEmit) a).code out := by
    simp only [Context.Invocation.coreCallee, render, List.append_assoc, List.singleton_append]
    exact Computed.core_label_stays (head := Core.Admin.frame n frame code)
      rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp)
  change Step P noHost (entry.coreArmWrap outer (call.coreCallee s (entry.insideTail.map Graph.coreEmit) a)) dst ↔ _
  rw [under_arm stays]
  constructor
  · rintro ⟨mid, move, rfl⟩
    obtain ⟨b, step, rfl⟩ := (Context.core_linked_frame_step_iff checked links typed live).mp move
    exact ⟨b, step, rfl⟩
  · rintro ⟨b, step, rfl⟩
    exact ⟨_, (Context.core_linked_frame_step_iff checked links typed live).mpr ⟨b, step, rfl⟩, rfl⟩

private theorem deliver_eq (same : call.caller.module = entry.owner.declaration.module)
    (writes : Writes entry call.saved call.site.signature.results) (result : Nested.Result) :
    coreCallee entry s outer call (.done result) =
      corePhase entry s outer (delivery call.caller call.saved writes.indices
        (entry.insideTail.map Graph.coreEmit) result) := by
  have frame : entry.frame call.caller.locals = call.caller :=
    congrArg (fun m => (⟨call.caller.locals, m⟩ : Runtime.Frame)) same.symm
  cases result <;>
    simp [frame, coreCallee, corePhase, delivery, Context.Invocation.coreCallee, Graph.Phase.render,
      Graph.Phase.renderAt, Graph.coreAdmin, Graph.coreEmit, Graph.Op.emit, Graph.coreCodeSyntax,
      Nested.resultCode, Core.vals, coreValues, writes.source, List.map_append,
      List.map_map, List.append_assoc, Function.comp_def]

theorem callee_run (ready : entry.Checked program tables outer index args)
    (checked : call.Checked program) (links : program.CoreLinksAllocated s)
    (same : call.caller.module = entry.owner.declaration.module)
    (locals : call.caller.locals.map Value.type = entry.owner.localTypes)
    (writes : Writes entry call.saved call.site.signature.results) {dst : Config H} :
    Steps P noHost (coreCallee entry s outer call call.entered) dst ↔
      CalleeFinish program call (coreCallee entry s outer call)
        (fun result => Finish entry program (corePhase entry s outer) (Graph.coreConfig s outer entry.cont.target)
          (delivery call.caller call.saved writes.indices (entry.insideTail.map Graph.coreEmit) result)) dst := by
  apply callee_iff checked _ _ _ (callee_step checked links)
  intro result out admitted
  rw [deliver_eq same writes]
  exact finish_run ready links (deliver_admitted checked locals writes admitted _)


private theorem enter {active : Source.Activation} (invoked : active.invocation program = some call)
    (checked : call.Checked program) (allocated : s.funcs[call.address.value]? = some call.callee.coreInstance)
    (dst : Config H) :
    Step P noHost (entry.coreLookup s outer active (.call (some call.address))) dst ↔
      dst = coreCallee entry s outer call call.entered := by
  obtain ⟨address, callee, _, _, rfl⟩ := Source.invocation_fields invoked
  let body := Indirect.coreConfig s active.caller active.binding.site active.operands.selector
    (active.operands.saved ++ active.operands.args) (entry.insideTail.map Graph.coreEmit)
    (.call (some address))
  have stays (out : List Admin) : ¬ LabelExit entry.result.toList.length [] body.code out :=
    Indirect.core_lookup_stays (phase := .call (some address)) trivial _ out
  change Step P noHost (entry.coreArmWrap outer body) dst ↔ _
  rw [under_arm stays]
  have move (target : Config H) := Indirect.core_enter_at_iff (P := P) (caller := active.caller)
    (saved := active.operands.saved) (rest := entry.insideTail.map Graph.coreEmit)
    (dst := target) allocated checked.found checked.resolved checked.typed
  simp only [body, move, exists_eq_left]
  let resolvedCall : Context.Invocation := ⟨active.binding.site, active.caller, active.operands.selector,
    active.operands.saved, active.operands.args, address, callee⟩
  have entered := Context.core_entered_config (s := s) (call := resolvedCall)
    (rest := entry.insideTail.map Graph.coreEmit)
  exact Iff.of_eq (congrArg (fun cfg => dst = entry.coreArmWrap outer cfg) entered)



private theorem allocation {active : Source.Activation}
    (invoked : active.invocation program = some call) (targets : active.binding.site.CoreAllocated program s) :
    s.funcs[call.address.value]? = some call.callee.coreInstance := by
  obtain ⟨address, callee, resolved, found, rfl⟩ := Source.invocation_fields invoked
  cases Indirect.resolve_iff.mp resolved with
  | resolved selected _ _ => exact targets address callee (List.mem_of_getElem? selected) found

theorem enter_allocated {active : Source.Activation} (invoked : active.invocation program = some call)
    (checked : call.Checked program) (targets : active.binding.site.CoreAllocated program s)
    (dst : Config H) :
    Step P noHost (entry.coreLookup s outer active (.call (some call.address))) dst ↔
      dst = coreCallee entry s outer call call.entered :=
  enter invoked checked (allocation invoked targets) dst

theorem resolved_run (ready : entry.Checked program tables outer index args)
    {locals stack : List Value} {states : List OperandState} {active : Source.Activation}
    (trace : OperandTrace locals [] entry.before states (.values stack))
    (prepared : entry.op.prepare program tables (entry.frame locals) stack = some active)
    (localTypes : locals.map Value.type = entry.owner.localTypes)
    (invoked : active.invocation program = some call)
    (tablesFound : Source.Tables.CoreAllocated tables s) (targets : active.binding.site.CoreAllocated program s)
    (links : program.CoreLinksAllocated s) (writes : Writes entry call.saved call.site.signature.results)
    {dst : Config H} :
    Steps P noHost (entry.coreConfig s outer ⟨locals, .site⟩) dst ↔
      dst ∈ states.map (entry.coreOperands s outer locals) ++ ((Outcome.resolved call.address).coreTrace.map (entry.coreLookup s outer active)) ∨
      CalleeFinish program call (coreCallee entry s outer call)
        (fun result => Finish entry program (corePhase entry s outer) (Graph.coreConfig s outer entry.cont.target)
          (delivery call.caller call.saved writes.indices (entry.insideTail.map Graph.coreEmit) result)) dst := by
  have facts := Source.prepare_spec prepared
  have checked := Source.invocation_checked facts.checked (Loop.graph_checked ready) invoked
  have caller : call.caller = entry.frame locals := by
    obtain ⟨_, _, _, _, rfl⟩ := Source.invocation_fields invoked
    exact facts.caller_eq
  have resolved : active.resolve program = some (.resolved call.address) := by
    obtain ⟨_, _, resolved, _, rfl⟩ := Source.invocation_fields invoked
    exact resolved
  let before := (Outcome.resolved call.address).coreTrace.map (entry.coreLookup s outer active)
  have chain := Loop.core_lookup_exact (P := P) (entry := entry) (outerFrame := outer)
    facts.checked targets tablesFound resolved
  have after := enter (entry := entry) (outer := outer) (P := P) invoked checked (allocation invoked targets)
  have linked : (before ++ [coreCallee entry s outer call call.entered]).IsChain
      (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) := by
    refine List.isChain_append.mpr ⟨chain, .singleton _, ?_⟩
    intro a ha b hb
    have lastStep : a = entry.coreLookup s outer active (.call (some call.address)) :=
      (Option.mem_some.mp (show a ∈ some _ from ha)).symm
    have firstEntered : b = coreCallee entry s outer call call.entered :=
      (Option.mem_some.mp (show b ∈ some _ from hb)).symm
    rw [lastStep, firstEntered]
    exact after
  have fromSite := Loop.core_operand_run_iff (P := P) (s := s) (outerFrame := outer) trace (dst := dst)
  rw [Loop.core_lookup_start prepared] at fromSite
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
    (tablesFound : Source.Tables.CoreAllocated tables s) (targets : active.binding.site.CoreAllocated program s)
    (links : program.CoreLinksAllocated s) {dst : Config H} :
    Steps P noHost (entry.coreConfig s outer ⟨locals, .site⟩) dst ↔
      dst ∈ states.map (entry.coreOperands s outer locals) ++
        (out.coreTrace.map (entry.coreLookup s outer active)).dropLast ∨
      Finish entry program (corePhase entry s outer) (Graph.coreConfig s outer entry.cont.target)
        (coreTrap entry active out) dst := by
  have facts := Source.prepare_spec prepared
  let path := out.coreTrace.map (entry.coreLookup s outer active)
  let trapped := corePhase entry s outer (coreTrap entry active out)
  have last : path.getLast? = some trapped := by
    cases trap <;> simp [path, trapped, Outcome.coreTrace, Entry.coreLookup, Source.Activation.coreConfig,
      Indirect.coreConfig, Site.coreCode, coreTrap, corePhase, facts.caller_eq, Entry.coreArmWrap, Entry.armScope,
      Context.coreNestWith, coreValues, List.append_assoc] <;> rfl
  have chain := Loop.core_lookup_exact (P := P) (entry := entry) (outerFrame := outer)
    facts.checked targets tablesFound resolved
  have same : path.dropLast ++ [trapped] = path := List.dropLast_append_getLast? trapped (by rw [last]; simp)
  have exactPath : (path.dropLast ++ [trapped]).IsChain (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) :=
    same.symm ▸ (show path.IsChain _ from chain)
  have head : path.dropLast.headD trapped = entry.coreLookup s outer active .start := by cases trap <;> rfl
  have read := Context.Resume.prefix_run_iff (dst := dst) path.dropLast trapped exactPath
  rw [head] at read
  have fromSite := Loop.core_operand_run_iff (P := P) (s := s) (outerFrame := outer) trace (dst := dst)
  rw [Loop.core_lookup_start prepared] at fromSite
  have live : Admitted entry (coreTrap entry active out) := by
    simpa only [coreTrap, Admitted, facts.caller_eq, Entry.frame, Graph.currentFrame] using localTypes
  refine (fromSite.trans (or_congr Iff.rfl (read.trans (or_congr Iff.rfl
    (finish_run ready links live))))).trans ?_
  rw [List.mem_append, or_assoc]

theorem through_site (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.address.value]? = some entry.coreInstance)
    (links : program.CoreLinksAllocated s) (site : List Value → Config H → Prop) {dst : Config H}
    (read : ∀ locals, Loop.Runs entry (entry.initial args) ⟨locals, .site⟩ →
      (Steps P noHost (entry.coreConfig s outer ⟨locals, .site⟩) dst ↔ site locals dst)) :
    let start := coreSource s outer index args
    let invoke := (⟨entry.cont, entry.op, entry.before⟩ : GraphEntry.Entry).coreInvoke s outer args
    Steps P noHost start dst ↔ dst ∈ [start, invoke] ∨
      ObservationWithSite entry args (entry.coreConfig s outer)
        (fun locals out => ∃ phase, program.FrameRuns entry.address (entry.callerPhase locals) phase ∧
          Graph.Admitted program entry.owner phase ∧ out = Graph.coreConfig s outer entry.cont.target phase)
        site dst := by
  exact (Loop.core_run_iff (P := P) ready allocated links).trans
    (or_congr Iff.rfl (observation_iff _ (Step P noHost) _ site read))

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Resume.Proofs.Core
