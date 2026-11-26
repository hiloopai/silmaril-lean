module

public import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Repeat.Common
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Resume.Thms
import Silmaril.Wasm.Institution.Operational.Loops.Native.Thms
import Silmaril.Wasm.Institution.Operational.BranchExit.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Mathlib.Data.List.Chain

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Repeat.Proofs.Core

open Execution
open Core
open Execution.Runtime (Value)
open CallContinuation
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked
open Wasm.SingleThreaded.Det (noHost)

variable {indices : List LocalIdx}

variable {H : Type} {P : Numerics.Profile} {s : Store H} {entry : Entry}
  {program : Graph.Program} {tables : Source.Tables} {outer : Runtime.Frame}
  {index : FuncIdx} {args : List Value}

private theorem branch_arm (ls : List Value) (dst : Config H) :
    Step P noHost (coreWrite entry s outer ls [] []) dst ↔ dst = corePhase entry s outer (.branch ls) := by
  let frame := (entry.frame ls).toCore
  let body : Config H := ⟨s, frame, [.label entry.result.toList.length [] [.plain (.br ⟨1⟩)]]⟩
  have stays (out : List Admin) :
      ¬ LabelExit 0 [entry.coreLoop] body.code out :=
    Computed.core_label_stays (stack := []) (rest := [])
      (head := .label entry.result.toList.length [] [.plain (.br ⟨1⟩)])
      rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp)
  change Step P noHost (entry.coreLoopWrap outer body) dst ↔ _
  rw [Loop.core_loop_wrap_step_iff stays]
  have invert (mid : Config H) := BranchExit.core_label_br_cont_iff (P := P)
    (s := s) (f := frame) (stack := []) (n := entry.result.toList.length)
    (cont := []) (depth := ⟨1⟩) (rest := []) (dst := mid)
  have move (mid : Config H) : Step P noHost body mid ↔ mid = ⟨s, frame, [.plain (.br ⟨0⟩)]⟩ := by
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
    Step P noHost (corePhase entry s outer (.branch ls)) dst ↔
      dst = corePhase entry s outer (.control ⟨ls, .enter⟩) := by
  let body : Config H := ⟨s, (entry.frame ls).toCore, coreValues entry.owner.initial ++
    .label 0 [entry.coreLoop] [.plain (.br ⟨0⟩)] :: entry.tail.map Graph.coreEmit⟩
  have stays (out : List Admin) :
      ¬ LabelExit entry.owner.declaration.results.length [] body.code out :=
    Computed.core_label_stays (head := .label 0 [entry.coreLoop] [.plain (.br ⟨0⟩)])
      rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp)
  change Step P noHost (entry.cont.coreWrap outer body) dst ↔ _
  rw [Context.Resume.core_wrap_step_iff stays]
  have move (mid : Config H) : Step P noHost body mid ↔ mid = ⟨s, (entry.frame ls).toCore,
      coreValues entry.owner.initial ++ .plain entry.coreLoop :: entry.tail.map Graph.coreEmit⟩ := by
    simpa only [expression, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc] using!
      Loops.core_restart_iff (P := P) (s := s) (f := (entry.frame ls).toCore) (cont := [entry.coreLoop])
        (saved := (entry.owner.initial.map Value.toCore)) (scratch := []) (pending := []) (rest := entry.tail.map Graph.coreEmit) (dst := mid)
  simp only [move, exists_eq_left]
  rfl

private theorem write_step (guard : Guard entry program tables)
    {ls stack : List Value} {more : List LocalIdx} {dst : Config H}
    (typed : Resume.Admitted entry (.write ls stack more : Resume.Phase Admin)) :
    Step P noHost (corePhase entry s outer (.write ls stack more)) dst ↔
      ∃ b, Edge entry program guard.indices (coreRecipes entry program tables s outer) (.write ls stack more) b ∧
        dst = corePhase entry s outer b := by
  cases more with
  | nil =>
    obtain rfl := Resume.empty_stack typed
    change Step P noHost (coreWrite entry s outer ls [] []) dst ↔ _
    rw [branch_arm]
    exact ⟨fun eq => ⟨_, .armBranch, eq⟩, fun ⟨_, move, eq⟩ => by cases move; exact eq⟩
  | cons i more =>
    let pending : List Admin := more.map (fun j => Admin.plain (Instr.localSet j)) ++
      [.plain (.br ⟨1⟩)]
    change Step P noHost (entry.coreArmWrap outer ⟨s, (entry.frame ls).toCore, coreValues stack ++ .plain (.localSet i) :: pending⟩) dst ↔ _
    refine (Resume.core_set_step (P := P) ls stack i pending dst).trans ⟨?_, ?_⟩
    · rintro ⟨_, _, _, rfl, wrote, rfl⟩
      exact ⟨_, .write rfl wrote, rfl⟩
    · rintro ⟨_, move, rfl⟩
      cases move with
      | write split wrote => exact ⟨_, _, _, split, wrote, rfl⟩

private theorem return_eq (guard : Guard entry program tables)
    {call : Context.Invocation} {returned : List Value}
    (ready : CallReady entry program guard.indices call) :
    corePhase entry s outer (.callee call (.done (.values returned))) =
      corePhase entry s outer (.write call.caller.locals (call.saved ++ returned) guard.indices) := by
  have frame : entry.frame call.caller.locals = call.caller :=
    congrArg (fun m => (⟨call.caller.locals, m⟩ : Runtime.Frame)) ready.module_eq.symm
  simp [frame, corePhase, Resume.coreCallee, coreWrite, Context.Invocation.coreCallee, Graph.Phase.render,
    Graph.Phase.renderAt, Graph.coreAdmin, Graph.coreEmit, Graph.Op.emit, Graph.coreCodeSyntax,
    Nested.resultCode, Core.vals, coreValues, guard.source, List.map_append, List.map_map,
    List.append_assoc, Function.comp_def]

private theorem trap_eq {call : Context.Invocation} (ready : CallReady entry program indices call) :
    corePhase entry s outer (.callee call (.done .trap)) =
      Resume.corePhase entry s outer (.armTrap call.caller.locals call.saved (entry.insideTail.map Graph.coreEmit)) := by
  have frame : entry.frame call.caller.locals = call.caller :=
    congrArg (fun m => (⟨call.caller.locals, m⟩ : Runtime.Frame)) ready.module_eq.symm
  simp [frame, corePhase, Resume.coreCallee, Resume.corePhase, Context.Invocation.coreCallee,
    Graph.Phase.render, Graph.Phase.renderAt, Graph.coreAdmin, Nested.resultCode, coreValues]

private theorem stop (ready : entry.Checked program tables outer index args) (links : program.CoreLinksAllocated s)
    {a : Phase Admin (Config H)} {dst : Config H}
    (typed : Ready entry program indices (Step P noHost) (corePhase entry s outer) a) (halted : ¬ a.Live) :
    Steps P noHost (corePhase entry s outer a) dst ↔ Stop entry program (Resume.corePhase entry s outer)
      (Graph.coreConfig s outer entry.cont.target) (entry.insideTail.map Graph.coreEmit) a dst := by
  cases a with
  | control state =>
    rcases state with ⟨ls, phase⟩
    cases phase with
    | caller =>
      have admitted := Loop.caller_admitted ready typed
      refine (Context.linked_runs (Loop.graph_checked ready) ready.found
        (Graph.coreConfig s outer entry.cont.target) (Step P noHost)
        (fun h live => Graph.core_entered_frame_step_iff (Loop.graph_checked ready) links ready.found rfl h live)
        admitted trivial).trans ⟨?_, ?_⟩
      · rintro ⟨phase, walk, _, eq⟩
        exact ⟨phase, walk, eq⟩
      · rintro ⟨phase, walk, eq⟩
        exact ⟨phase, walk, program.frame_admitted_run (Loop.graph_checked ready) ready.found admitted walk, eq⟩
    | _ => exact (halted trivial).elim
  | trap phase => exact Resume.core_finish_run (P := P) ready links typed
  | callee call phase =>
    cases phase with
    | done result =>
      cases result with
      | trap =>
        rw [trap_eq typed.1]
        exact Resume.core_finish_run (P := P) ready links
          (a := .armTrap call.caller.locals call.saved (entry.insideTail.map Graph.coreEmit)) typed.1.locals
      | values => exact (halted trivial).elim
    | _ => exact (halted trivial).elim
  | _ => exact (halted trivial).elim

private theorem prepend_operands (ls : List Value) {states : List OperandState} {result : OperandResult}
    (trace : OperandTrace ls [] entry.before states result) (rest : List (Config H)) (next : Handoff Admin)
    (head : rest.headD (corePhase entry s outer (.resume next)) = entry.coreOperandResult s outer ls result)
    (chain : (rest ++ [corePhase entry s outer (.resume next)]).IsChain
      (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b))
    (ready : HandoffReady entry program indices next)
    (nonempty : states ≠ [] ∨ rest ≠ []) :
    Valid entry program indices (Step P noHost) (corePhase entry s outer) ls
      ⟨states.map (entry.coreOperands s outer ls) ++ rest, next⟩ := by
  refine ⟨?_, ?_, append_chain _ rest _ _ (Loop.core_operand_chain (P := P) trace) chain head, ready⟩
  · intro nil
    obtain ⟨left, right⟩ := List.append_eq_nil_iff.mp nil
    exact nonempty.elim (fun h => h (List.map_eq_nil_iff.mp left)) (fun h => h right)
  · change ((states.map (entry.coreOperands s outer ls)) ++ rest).headD _ =
      entry.coreConfig s outer ⟨ls, .site⟩
    rw [head_append, head, Loop.core_site_operands]
    exact operand_head _ _ (fun _ => rfl) trace

private theorem recipe_exact (ready : entry.Checked program tables outer index args)
    (guard : Guard entry program tables) (allocated : Source.Tables.CoreAllocated tables s)
    (targets : ∀ active : Source.Activation, active.Checked program tables → active.binding.site.CoreAllocated program s)
    {ls : List Value} (typed : ls.map Value.type = entry.owner.localTypes)
    (site : Site entry program tables ls) :
    Valid entry program guard.indices (Step P noHost) (corePhase entry s outer) ls (coreRecipe s outer site) := by
  cases site with
  | call trace prepared invoked =>
    have facts := Source.prepare_spec prepared
    have callReady := call_ready guard (Loop.graph_checked ready) typed trace prepared invoked
    have lookup := (GraphEntry.resolved_entry_ref invoked).2.2
    have chain := Loop.core_lookup_exact (entry := entry) (outerFrame := outer) (P := P)
      facts.checked (targets _ facts.checked) allocated lookup
    have endStep := Resume.core_enter_allocated (entry := entry) (outerFrame := outer) (P := P)
      invoked callReady.checked (targets _ facts.checked)
    refine prepend_operands ls trace _ (.call _) (Loop.core_lookup_start prepared).symm ?_ callReady (.inr ?_)
    · refine List.isChain_append.mpr ⟨chain, .singleton _, ?_⟩
      intro a ha b hb
      obtain rfl := Option.mem_some.mp ha
      obtain rfl := Option.mem_some.mp hb
      exact endStep
    · exact List.cons_ne_nil _ _
  | lookupTrap trace prepared resolved trap =>
    have facts := Source.prepare_spec prepared
    have chain := Loop.core_lookup_exact (entry := entry) (outerFrame := outer) (P := P)
      facts.checked (targets _ facts.checked) allocated resolved
    have eq : _ := Loop.core_lookup_start (s := s) (outerFrame := outer) prepared
    refine prepend_operands ls trace _ (.trap _) ?_ ?_ ?_ (.inr ?_)
    · cases trap <;> exact eq.symm
    · have writeLast : _ := chain
      cases trap <;>
        simpa [Outcome.coreTrace, Entry.coreLookup, Source.Activation.coreConfig,
          Indirect.coreConfig, Site.coreCode, Resume.coreTrap, corePhase, Phase.resume, Resume.corePhase,
          facts.caller_eq, Entry.coreArmWrap, Entry.armScope, Context.coreNestWith, coreValues,
          List.append_assoc] using! writeLast
    · simpa only [HandoffReady, Resume.coreTrap, Resume.Admitted, facts.caller_eq, Entry.frame, Graph.currentFrame]
        using typed
    · cases trap <;> exact List.cons_ne_nil _ _
  | @operandTrap states saved pending trace =>
    simpa only [coreRecipe, List.append_nil] using
      prepend_operands (P := P) (s := s) (outer := outer) (program := program) (indices := guard.indices)
        ls trace [] (.trap (.armTrap ls saved (entry.coreSiteCode pending)))
        rfl (.singleton _) typed (.inl (trap_nonempty trace))

theorem whole_run (ready : entry.Checked program tables outer index args)
    (guard : Guard entry program tables)
    (allocated : s.funcs[entry.address.value]? = some entry.coreInstance)
    (table : Source.Tables.CoreAllocated tables s)
    (targets : ∀ active : Source.Activation, active.Checked program tables → active.binding.site.CoreAllocated program s)
    (links : program.CoreLinksAllocated s) {dst : Config H} :
    let start := coreSource s outer index args
    let invoke := (⟨entry.cont, entry.op, entry.before⟩ : GraphEntry.Entry).coreInvoke s outer args
    Steps P noHost start dst ↔ dst ∈ [start, invoke] ∨
      Readback entry program guard.indices (coreRecipes entry program tables s outer) (corePhase entry s outer)
        (Stop entry program (Resume.corePhase entry s outer) (Graph.coreConfig s outer entry.cont.target)
          (entry.insideTail.map Graph.coreEmit)) (entry.initial args) dst := by
  intro start invoke
  have loop := run_iff (native := Step P noHost) (render := corePhase entry s outer)
    (recipe := coreRecipes entry program tables s outer) (indices := guard.indices)
    (initial := entry.initial args) (dst := dst) (Loop.initial_typed ready) (Loop.edge_preserves ready) (fun _ _ _ => rfl)
    (fun typed accepted => by
      obtain ⟨site, rfl⟩ := accepted
      exact recipe_exact ready guard table targets typed site)
    (fun typed => by obtain ⟨site⟩ := site_exists guard typed; exact ⟨coreRecipe s outer site, site, rfl⟩)
    (Loop.core_step_iff (P := P) ready) (fun checked => Resume.core_callee_step (P := P) checked.checked links)
    (return_eq guard) (write_step guard) (fun {ls dst} => restart ls dst) (stop ready links)
  exact (Context.Resume.prefix_run_iff (dst := dst) [start, invoke] _
    (Loop.core_entry_chain (P := P) ready allocated)).trans (or_congr Iff.rfl loop)

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Repeat.Proofs.Core
