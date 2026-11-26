module

public import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Repeat.Common
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Resume.Thms
import Silmaril.Wasm.Institution.Operational.Loops.Native.Thms
import Silmaril.Wasm.Institution.Operational.BranchExit.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Mathlib.Data.List.Chain

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Repeat.Proofs.Lime1

open Execution
open Wasm.Lime1.Execution
open Execution.Runtime (Value)
open CallContinuation
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked
open Wasm.SingleThreaded.Det (noHost)

variable {indices : List LocalIdx}

variable {H : Type} {s : Store H} {entry : Entry}
  {program : Graph.Program} {tables : Source.Tables} {outer : Runtime.Frame}
  {index : FuncIdx} {args : List Value}

private theorem branch_arm (ls : List Value) (dst : Config H) :
    Step CallFrame.limeNoHost (limeWrite entry s outer ls [] []) dst ↔ dst = limePhase entry s outer (.branch ls) := by
  let frame := entry.frame ls
  let body : Config H := ⟨s, frame, [.label entry.result.toList.length [] [.source (.br ⟨1⟩)]]⟩
  have stays (out : List Admin) :
      ¬ PureStep frame.module.types [.label 0 [entry.limeLoop] body.code] out :=
    Computed.lime_label_stays (types := (entry.frame ls).module.types) (stack := []) (rest := [])
      (head := .label entry.result.toList.length [] [.source (.br ⟨1⟩)])
      rfl (by simp) (by simp) (by simp)
  change Step CallFrame.limeNoHost (entry.limeLoopWrap outer body) dst ↔ _
  rw [Loop.lime_loop_wrap_step_iff stays]
  have invert (mid : Config H) := BranchExit.lime_label_br_cont_iff (host := CallFrame.limeNoHost)
    (s := s) (f := frame) (stack := []) (n := entry.result.toList.length)
    (cont := []) (depth := ⟨1⟩) (rest := []) (dst := mid)
  have move (mid : Config H) : Step CallFrame.limeNoHost body mid ↔ mid = ⟨s, frame, [.source (.br ⟨0⟩)]⟩ := by
    constructor
    · intro edge
      rcases (invert mid).mp edge with ⟨_, _, _, _, zero, _⟩ | ⟨_, same⟩
      · contradiction
      · exact same
    · intro eq
      exact (invert mid).mpr (.inr ⟨by decide, eq⟩)
  simp only [move, exists_eq_left]
  rfl

private theorem restart (ls : List Value) (dst : Config H) :
    Step CallFrame.limeNoHost (limePhase entry s outer (.branch ls)) dst ↔
      dst = limePhase entry s outer (.control ⟨ls, .enter⟩) := by
  let body : Config H := ⟨s, entry.frame ls, values entry.owner.initial ++
    .label 0 [entry.limeLoop] [.source (.br ⟨0⟩)] :: entry.tail.map Graph.limeEmit⟩
  have stays (out : List Admin) :
      ¬ PureStep body.frame.module.types [.label entry.owner.declaration.results.length [] body.code] out :=
    Computed.lime_label_stays (types := (entry.frame ls).module.types) (head := .label 0 [entry.limeLoop] [.source (.br ⟨0⟩)])
      rfl (by simp) (by simp) (by simp)
  change Step CallFrame.limeNoHost (entry.cont.limeWrap outer body) dst ↔ _
  rw [Context.Resume.lime_wrap_step_iff stays]
  have move (mid : Config H) : Step CallFrame.limeNoHost body mid ↔ mid = ⟨s, entry.frame ls,
      values entry.owner.initial ++ .source entry.limeLoop :: entry.tail.map Graph.limeEmit⟩ := by
    simpa only [expression, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc] using!
      Loops.lime_restart_iff (s := s) (f := entry.frame ls) (cont := [entry.limeLoop])
        (saved := entry.owner.initial) (scratch := []) (pending := []) (rest := entry.tail.map Graph.limeEmit) (dst := mid)
  simp only [move, exists_eq_left]
  rfl

private theorem write_step (guard : Guard entry program tables)
    {ls stack : List Value} {more : List LocalIdx} {dst : Config H}
    (typed : Resume.Admitted entry (.write ls stack more : Resume.Phase Admin)) :
    Step CallFrame.limeNoHost (limePhase entry s outer (.write ls stack more)) dst ↔
      ∃ b, Edge entry program guard.indices (limeRecipes entry program tables s outer) (.write ls stack more) b ∧
        dst = limePhase entry s outer b := by
  cases more with
  | nil =>
    obtain rfl := Resume.empty_stack typed
    change Step CallFrame.limeNoHost (limeWrite entry s outer ls [] []) dst ↔ _
    rw [branch_arm]
    exact ⟨fun eq => ⟨_, .armBranch, eq⟩, fun ⟨_, move, eq⟩ => by cases move; exact eq⟩
  | cons i more =>
    let pending : List Admin := more.map (fun j => Execution.Runtime.AdminInstr.source (Wasm.Lime1.Instr.localSet j)) ++
      [.source (.br ⟨1⟩)]
    change Step CallFrame.limeNoHost (entry.limeArmWrap outer ⟨s, entry.frame ls, values stack ++ .source (.localSet i) :: pending⟩) dst ↔ _
    refine (Resume.lime_set_step ls stack i pending dst).trans ⟨?_, ?_⟩
    · rintro ⟨_, _, _, rfl, wrote, rfl⟩
      exact ⟨_, .write rfl wrote, rfl⟩
    · rintro ⟨_, move, rfl⟩
      cases move with
      | write split wrote => exact ⟨_, _, _, split, wrote, rfl⟩

private theorem return_eq (guard : Guard entry program tables)
    {call : Context.Invocation} {returned : List Value}
    (ready : CallReady entry program guard.indices call) :
    limePhase entry s outer (.callee call (.done (.values returned))) =
      limePhase entry s outer (.write call.caller.locals (call.saved ++ returned) guard.indices) := by
  have frame : entry.frame call.caller.locals = call.caller :=
    congrArg (fun m => (⟨call.caller.locals, m⟩ : Runtime.Frame)) ready.module_eq.symm
  simp [frame, limePhase, Resume.limeCallee, limeWrite, Context.Invocation.limeCallee, Graph.Phase.render,
    Graph.Phase.renderAt, Graph.limeAdmin, Graph.limeEmit, Graph.Op.emit, Graph.limeCodeSyntax,
    Nested.resultCode, values, guard.source, List.map_append, List.map_map,
    List.append_assoc, Function.comp_def]

private theorem trap_eq {call : Context.Invocation} (ready : CallReady entry program indices call) :
    limePhase entry s outer (.callee call (.done .trap)) =
      Resume.limePhase entry s outer (.armTrap call.caller.locals call.saved (entry.insideTail.map Graph.limeEmit)) := by
  have frame : entry.frame call.caller.locals = call.caller :=
    congrArg (fun m => (⟨call.caller.locals, m⟩ : Runtime.Frame)) ready.module_eq.symm
  simp [frame, limePhase, Resume.limeCallee, Resume.limePhase, Context.Invocation.limeCallee,
    Graph.Phase.render, Graph.Phase.renderAt, Graph.limeAdmin, Nested.resultCode, values]

private theorem stop (ready : entry.Checked program tables outer index args) (links : program.LimeLinksAllocated s)
    {a : Phase Admin (Config H)} {dst : Config H}
    (typed : Ready entry program indices (Step CallFrame.limeNoHost) (limePhase entry s outer) a) (halted : ¬ a.Live) :
    Steps CallFrame.limeNoHost (limePhase entry s outer a) dst ↔ Stop entry program (Resume.limePhase entry s outer)
      (Graph.limeConfig s outer entry.cont.target) (entry.insideTail.map Graph.limeEmit) a dst := by
  cases a with
  | control state =>
    rcases state with ⟨ls, phase⟩
    cases phase with
    | caller =>
      have admitted := Loop.caller_admitted ready typed
      refine (Context.linked_runs (Loop.graph_checked ready) ready.found
        (Graph.limeConfig s outer entry.cont.target) (Step CallFrame.limeNoHost)
        (fun h live => Graph.lime_entered_frame_step_iff (Loop.graph_checked ready) links ready.found rfl h live)
        admitted trivial).trans ⟨?_, ?_⟩
      · rintro ⟨phase, walk, _, eq⟩
        exact ⟨phase, walk, eq⟩
      · rintro ⟨phase, walk, eq⟩
        exact ⟨phase, walk, program.frame_admitted_run (Loop.graph_checked ready) ready.found admitted walk, eq⟩
    | _ => exact (halted trivial).elim
  | trap phase => exact Resume.lime_finish_run ready links typed
  | callee call phase =>
    cases phase with
    | done result =>
      cases result with
      | trap =>
        rw [trap_eq typed.1]
        exact Resume.lime_finish_run ready links
          (a := .armTrap call.caller.locals call.saved (entry.insideTail.map Graph.limeEmit)) typed.1.locals
      | values => exact (halted trivial).elim
    | _ => exact (halted trivial).elim
  | _ => exact (halted trivial).elim

private theorem prepend_operands (ls : List Value) {states : List OperandState} {result : OperandResult}
    (trace : OperandTrace ls [] entry.before states result) (rest : List (Config H)) (next : Handoff Admin)
    (head : rest.headD (limePhase entry s outer (.resume next)) = entry.limeOperandResult s outer ls result)
    (chain : (rest ++ [limePhase entry s outer (.resume next)]).IsChain
      (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b))
    (ready : HandoffReady entry program indices next)
    (nonempty : states ≠ [] ∨ rest ≠ []) :
    Valid entry program indices (Step CallFrame.limeNoHost) (limePhase entry s outer) ls
      ⟨states.map (entry.limeOperands s outer ls) ++ rest, next⟩ := by
  refine ⟨?_, ?_, append_chain _ rest _ _ (Loop.lime_operand_chain trace) chain head, ready⟩
  · intro nil
    obtain ⟨left, right⟩ := List.append_eq_nil_iff.mp nil
    exact nonempty.elim (fun h => h (List.map_eq_nil_iff.mp left)) (fun h => h right)
  · change ((states.map (entry.limeOperands s outer ls)) ++ rest).headD _ =
      entry.limeConfig s outer ⟨ls, .site⟩
    rw [head_append, head, Loop.lime_site_operands]
    exact operand_head _ _ (fun _ => rfl) trace

private theorem recipe_exact (ready : entry.Checked program tables outer index args)
    (guard : Guard entry program tables) (allocated : Source.Tables.LimeAllocated tables s)
    (targets : ∀ active : Source.Activation, active.Checked program tables → active.binding.site.LimeAllocated program s)
    {ls : List Value} (typed : ls.map Value.type = entry.owner.localTypes)
    (site : Site entry program tables ls) :
    Valid entry program guard.indices (Step CallFrame.limeNoHost) (limePhase entry s outer) ls (limeRecipe s outer site) := by
  cases site with
  | call trace prepared invoked =>
    have facts := Source.prepare_spec prepared
    have callReady := call_ready guard (Loop.graph_checked ready) typed trace prepared invoked
    have lookup := (GraphEntry.resolved_entry_ref invoked).2.2
    have step := Loop.lime_lookup_exact (entry := entry) (outerFrame := outer)
      facts.checked (targets _ facts.checked) allocated lookup
    have endStep := Resume.lime_enter_allocated (entry := entry) (outerFrame := outer)
      invoked callReady.checked (targets _ facts.checked)
    refine prepend_operands ls trace _ (.call _) (Loop.lime_lookup_start prepared).symm ?_ callReady (.inr ?_)
    · exact List.isChain_cons_cons.mpr ⟨step, List.isChain_pair.mpr endStep⟩
    · exact List.cons_ne_nil _ _
  | lookupTrap trace prepared resolved trap =>
    have facts := Source.prepare_spec prepared
    have step (dst : Config H) := Loop.lime_lookup_exact (entry := entry) (outerFrame := outer)
      facts.checked (targets _ facts.checked) allocated resolved dst
    refine prepend_operands ls trace _ (.trap _) (Loop.lime_lookup_start prepared).symm ?_ ?_ (.inr ?_)
    · apply List.isChain_pair.mpr
      intro dst
      refine (step dst).trans ?_
      cases trap <;>
        simp [Entry.limeLookupResult, Source.Activation.limeResolved, Indirect.limeResolved,
          Resume.limeTrap, limePhase, Phase.resume, Resume.limePhase, facts.caller_eq, Entry.limeArmWrap, Entry.armScope,
          Context.limeNestWith, values] <;> rfl
    · simpa only [HandoffReady, Resume.limeTrap, Resume.Admitted, facts.caller_eq, Entry.frame, Graph.currentFrame]
        using typed
    · exact List.cons_ne_nil _ _
  | @operandTrap states saved pending trace =>
    simpa only [limeRecipe, List.append_nil] using
      prepend_operands (s := s) (outer := outer) (program := program) (indices := guard.indices)
        ls trace [] (.trap (.armTrap ls saved (entry.limeSiteCode pending)))
        rfl (.singleton _) typed (.inl (trap_nonempty trace))

theorem whole_run (ready : entry.Checked program tables outer index args)
    (guard : Guard entry program tables)
    (allocated : s.funcs[entry.address.value]? = some entry.limeInstance)
    (table : Source.Tables.LimeAllocated tables s)
    (targets : ∀ active : Source.Activation, active.Checked program tables → active.binding.site.LimeAllocated program s)
    (links : program.LimeLinksAllocated s) {dst : Config H} :
    let start := limeSource s outer index args
    let invoke := (⟨entry.cont, entry.op, entry.before⟩ : GraphEntry.Entry).limeInvoke s outer args
    Steps CallFrame.limeNoHost start dst ↔ dst ∈ [start, invoke] ∨
      Readback entry program guard.indices (limeRecipes entry program tables s outer) (limePhase entry s outer)
        (Stop entry program (Resume.limePhase entry s outer) (Graph.limeConfig s outer entry.cont.target)
          (entry.insideTail.map Graph.limeEmit)) (entry.initial args) dst := by
  intro start invoke
  have loop := run_iff (native := Step CallFrame.limeNoHost) (render := limePhase entry s outer)
    (recipe := limeRecipes entry program tables s outer) (indices := guard.indices)
    (initial := entry.initial args) (dst := dst) (Loop.initial_typed ready) (Loop.edge_preserves ready) (fun _ _ _ => rfl)
    (fun typed accepted => by
      obtain ⟨site, rfl⟩ := accepted
      exact recipe_exact ready guard table targets typed site)
    (fun typed => by obtain ⟨site⟩ := site_exists guard typed; exact ⟨limeRecipe s outer site, site, rfl⟩)
    (Loop.lime_step_iff ready) (fun checked => Resume.lime_callee_step checked.checked links)
    (return_eq guard) (write_step guard) (fun {ls dst} => restart ls dst) (stop ready links)
  exact (Context.Resume.prefix_run_iff (dst := dst) [start, invoke] _
    (Loop.lime_entry_chain ready allocated)).trans (or_congr Iff.rfl loop)

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Repeat.Proofs.Lime1
