module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Repeat.Defs
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Resume.Thms
import Mathlib.Data.List.Chain

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Repeat.Proofs

open Execution.Runtime (Value)
open CallContinuation
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked

variable {entry : Entry} {program : Graph.Program} {tables : Source.Tables} {locals : List Value}
  {A C : Type} {indices : List LocalIdx}

private def operandTypes (guard : Guard entry program tables) : List NumType :=
  .int .i32 :: entry.op.signature.params.reverse ++ guard.saved

private theorem wellTyped (guard : Guard entry program tables) (typed : locals.map Value.type = entry.owner.localTypes) :
    Prefix.WellTyped locals [] entry.before (operandTypes guard).reverse := by
  simpa only [Prefix.WellTyped, typed, Prefix.stackTypes, List.map_nil, List.reverse_nil, List.reverse_reverse, operandTypes]
    using guard.operands

theorem site_exists (guard : Guard entry program tables) (typed : locals.map Value.type = entry.owner.localTypes) :
    Nonempty (Site entry program tables locals) := by
  obtain ⟨states, result, trace⟩ := GraphEntry.trace_exists (wellTyped guard typed)
  cases result with
  | trap stack rest => exact ⟨.operandTrap trace⟩
  | values stack =>
    have stackEq := GraphEntry.trace_values trace (wellTyped guard typed)
    have accepts : entry.op.checkStack (entry.frame locals).module.types (Prefix.stackTypes stack) =
        some (entry.op.signature.results.reverse ++ guard.saved) := by
      rw [stackEq, List.reverse_reverse]
      simp [operandTypes, Source.Op.checkStack, Entry.frame, Graph.currentFrame, guard.typeIndex]
    obtain ⟨active, prepared⟩ := Source.prepare_of_check (caller := entry.frame locals) guard.binding accepts
    obtain ⟨out, resolved⟩ := Source.resolve_total (Source.prepare_spec prepared).checked
    cases out with
    | bounds => exact ⟨.lookupTrap trace prepared resolved .bounds⟩
    | null => exact ⟨.lookupTrap trace prepared resolved .null⟩
    | mismatch addr => exact ⟨.lookupTrap trace prepared resolved (.mismatch addr)⟩
    | resolved addr =>
      cases Indirect.resolve_iff.mp resolved with
      | @resolved _ fn _ found _ =>
        let call : Context.Invocation := ⟨active.binding.site, active.caller, active.operands.selector,
          active.operands.saved, active.operands.args, addr, fn⟩
        exact ⟨.call (call := call) trace prepared (by simp [Source.Activation.invocation, resolved, found, call])⟩

structure CallReady (entry : Entry) (program : Graph.Program) (indices : List LocalIdx)
    (call : Context.Invocation) : Prop where
  checked : call.Checked program
  module_eq : call.caller.module = entry.owner.declaration.module
  locals : call.caller.locals.map Value.type = entry.owner.localTypes
  writes : Locals.check entry.owner.localTypes (call.site.signature.results.reverse ++ Prefix.stackTypes call.saved)
    (indices.map Locals.Op.set) = some []

theorem call_ready (guard : Guard entry program tables) (graph : program.checkDirect = true)
    (typed : locals.map Value.type = entry.owner.localTypes) {states stack active call}
    (trace : OperandTrace locals [] entry.before states (.values stack))
    (prepared : entry.op.prepare program tables (entry.frame locals) stack = some active)
    (invoked : active.invocation program = some call) :
    CallReady entry program guard.indices call := by
  have facts := Source.prepare_spec prepared
  have checked := Source.invocation_checked facts.checked graph invoked
  obtain ⟨_, _, _, _, rfl⟩ := Source.invocation_fields invoked
  have stackEq := GraphEntry.trace_values trace (wellTyped guard typed)
  rw [facts.stack_eq, List.reverse_reverse] at stackEq
  have stackType : Prefix.stackTypes (active.operands.saved ++ active.operands.args ++ [Value.int .i32 active.operands.selector]) =
      .int .i32 :: active.binding.site.signature.params.reverse ++ Prefix.stackTypes active.operands.saved := by
    simp [Prefix.stackTypes, List.reverse_append, Value.int, facts.checked.args]
  rw [stackType, facts.signature_eq] at stackEq
  have saved : Prefix.stackTypes active.operands.saved = guard.saved :=
    List.append_cancel_left (List.cons.inj stackEq).2
  exact ⟨checked, by rw [facts.caller_eq]; rfl,
    by simpa only [facts.caller_eq, Entry.frame, Graph.currentFrame] using typed,
    by simpa only [facts.signature_eq, saved] using guard.writes⟩

def HandoffReady (entry : Entry) (program : Graph.Program) (indices : List LocalIdx) : Handoff A → Prop
  | .call call => CallReady entry program indices call
  | .trap phase => Resume.Admitted entry phase

def Ready (entry : Entry) (program : Graph.Program) (indices : List LocalIdx)
    (native : C → C → Prop) (render : Phase A C → C) : Phase A C → Prop
  | .control state => entry.Typed state
  | .pending head rest next =>
      ((head :: rest) ++ [render (.resume next)]).IsChain (fun a b => ∀ dst, native a dst ↔ dst = b) ∧
      HandoffReady entry program indices next
  | .callee call phase => CallReady entry program indices call ∧ Graph.Admitted program call.callee phase ∧
      (phase.LabelOutcome ∨ ∃ r, phase = .done r)
  | .write ls stack more => Resume.Admitted entry (.write ls stack more : Resume.Phase A)
  | .branch ls => ls.map Value.type = entry.owner.localTypes
  | .trap phase => Resume.Admitted entry phase

structure Valid (entry : Entry) (program : Graph.Program) (indices : List LocalIdx)
    (native : C → C → Prop) (render : Phase A C → C) (locals : List Value) (path : Recipe A C) : Prop where
  nonempty : path.before ≠ []
  head : path.before.headD (render (.resume path.next)) = render (.control ⟨locals, .site⟩)
  chain : (path.before ++ [render (.resume path.next)]).IsChain (fun a b => ∀ dst, native a dst ↔ dst = b)
  ready : HandoffReady entry program indices path.next

private theorem resumed {native : C → C → Prop} {render : Phase A C → C} {next : Handoff A}
    (ready : HandoffReady entry program indices next) :
    Ready entry program indices native render (.resume next) := by
  cases next with
  | call call => exact ⟨ready, Context.entered_admitted ready.checked, .inl trivial⟩
  | trap phase => exact ready

private theorem next_ready {native : C → C → Prop} {render : Phase A C → C} {rest : List C} {next : Handoff A}
    (chain : (rest ++ [render (.resume next)]).IsChain (fun a b => ∀ dst, native a dst ↔ dst = b))
    (ready : HandoffReady entry program indices next) :
    Ready entry program indices native render (.advance next rest) := by
  cases rest with
  | nil => exact resumed ready
  | cons head rest => exact ⟨chain, ready⟩

private theorem return_ready {call : Context.Invocation} {values : List Value}
    (checked : CallReady entry program indices call)
    (admitted : Graph.Admitted program call.callee (.done (.values values))) :
    Resume.Admitted entry (.write call.caller.locals (call.saved ++ values) indices : Resume.Phase A) := by
  cases admitted with
  | done typed =>
    have types := typed.trans (congrArg Wasm.V1.FuncType.results
      (resolved_signature checked.checked.resolved checked.checked.found))
    exact ⟨checked.locals, by simpa [Prefix.stackTypes, List.map_append, List.reverse_append, types] using checked.writes⟩

theorem append_chain {R : C → C → Prop} (first rest : List C) (middle last : C)
    (front : (first ++ [middle]).IsChain R) (back : (rest ++ [last]).IsChain R)
    (head : rest.headD last = middle) : (first ++ rest ++ [last]).IsChain R := by
  rw [List.append_assoc]
  refine List.isChain_append.mpr ⟨(List.isChain_append.mp front).1, back, ?_⟩
  intro a ha b hb
  have firstStep := (List.isChain_append.mp front).2.2 a ha middle (by simp)
  cases rest with
  | nil =>
    have same : last = b := Option.mem_some.mp hb
    change last = middle at head
    simpa only [← same, head] using firstStep
  | cons x xs =>
    have same : x = b := Option.mem_some.mp hb
    change x = middle at head
    simpa only [← same, head] using firstStep

theorem operand_head (render : OperandState → C) (finish : OperandResult → C)
    (empty : ∀ stack, finish (.values stack) = render (stack, []))
    {ls stack code states result} (trace : OperandTrace ls stack code states result) :
    (states.map render).headD (finish result) = render (stack, code) := by
  cases trace <;> first | rfl | exact empty _

theorem trap_nonempty {ls stack code states saved rest}
    (trace : OperandTrace ls stack code states (.trap saved rest)) : states ≠ [] := by
  cases trace <;> simp

theorem head_append (first rest : List C) (last : C) :
    (first ++ rest).headD last = first.headD (rest.headD last) := by
  cases first <;> rfl

theorem run_iff {native : C → C → Prop} {render : Phase A C → C}
    {recipe : List Value → Recipe A C → Prop} {stop : Phase A C → C → Prop}
    {initial : Loop.State}
    (controlReady : entry.Typed initial)
    (controlPreserve : ∀ {a b}, entry.Typed a → Loop.Edge entry a b → entry.Typed b)
    (prefixRender : ∀ head rest next, render (.pending head rest next) = head)
    (valid : ∀ {ls path}, ls.map Value.type = entry.owner.localTypes → recipe ls path →
      Valid entry program indices native render ls path)
    (hasRecipe : ∀ {ls}, ls.map Value.type = entry.owner.localTypes → ∃ path, recipe ls path)
    (controlStep : ∀ {a dst}, entry.Typed a → a.phase.Pending →
      (native (render (.control a)) dst ↔ ∃ b, Loop.Edge entry a b ∧ dst = render (.control b)))
    (calleeStep : ∀ {call a dst}, CallReady entry program indices call → Graph.Admitted program call.callee a →
      a.LabelOutcome → (native (render (.callee call a)) dst ↔
        ∃ b, program.FrameEdge call.address a b ∧ dst = render (.callee call b)))
    (returnEq : ∀ {call values}, CallReady entry program indices call →
      render (.callee call (.done (.values values))) = render (.write call.caller.locals (call.saved ++ values) indices))
    (writeStep : ∀ {ls stack more dst}, Resume.Admitted entry (.write ls stack more : Resume.Phase A) →
      (native (render (.write ls stack more)) dst ↔
        ∃ b, Edge entry program indices recipe (.write ls stack more) b ∧ dst = render b))
    (restart : ∀ {ls dst}, native (render (.branch ls)) dst ↔ dst = render (.control ⟨ls, .enter⟩))
    (finish : ∀ {a dst}, Ready entry program indices native render a → ¬ a.Live →
      (Relation.ReflTransGen native (render a) dst ↔ stop a dst)) {dst : C} :
    Relation.ReflTransGen native (render (.control initial)) dst ↔
      Readback entry program indices recipe render stop initial dst := by
  have chainStep {head : C} {rest : List C} {next : Handoff A}
      (chain : ((head :: rest) ++ [render (.resume next)]).IsChain (fun a b => ∀ dst, native a dst ↔ dst = b)) :
      (∀ dst, native head dst ↔ dst = render (.advance next rest)) ∧
        (rest ++ [render (.resume next)]).IsChain (fun a b => ∀ dst, native a dst ↔ dst = b) := by
    cases rest with
    | nil => exact List.isChain_cons_cons.mp chain
    | cons h t =>
      obtain ⟨step, tail⟩ := List.isChain_cons_cons.mp chain
      refine ⟨fun dst => ?_, tail⟩
      change native head dst ↔ dst = render (.pending h t next)
      rw [prefixRender]
      exact step dst
  have keeps {a b} (ready : Ready entry program indices native render a) (move : Edge entry program indices recipe a b) :
      Ready entry program indices native render b := by
    induction move with
    | control step => exact controlPreserve ready step
    | site path =>
      have plan := valid ready path
      exact next_ready (chainStep plan.chain).2 plan.ready
    | pending => exact next_ready (chainStep ready.1).2 ready.2
    | callee live step =>
      exact ⟨ready.1, program.frame_admitted_step ready.1.checked.graph ready.1.checked.found ready.2.1 step,
        Context.entered_frame_edge ready.1.checked.found live step⟩
    | @write locals stack i more saved value updated split move =>
      subst stack
      exact Resume.edge_preserves (a := (.write locals (saved ++ [value]) (i :: more) : Resume.Phase A))
        (b := .write updated saved more) ready (.write rfl move)
    | armBranch => exact ready.1
    | return_ _ ih => exact ih (return_ready (A := A) ready.1 ready.2.1)
    | restart => exact ready
  have step {a dst} (ready : Ready entry program indices native render a) (live : a.Live) :
      native (render a) dst ↔ ∃ b, Edge entry program indices recipe a b ∧ dst = render b := by
    cases a with
    | control state =>
      rcases state with ⟨ls, phase⟩
      cases phase with
      | site =>
        constructor
        · intro move
          obtain ⟨⟨before, next⟩, path⟩ := hasRecipe ready
          have plan := valid ready path
          cases before with
          | nil => exact (plan.nonempty rfl).elim
          | cons head rest =>
            rw [← plan.head] at move
            exact ⟨_, .site path, ((chainStep plan.chain).1 _).mp move⟩
        · rintro ⟨b, edge, eq⟩
          cases edge with
          | control move => cases move
          | site path =>
            have plan := valid ready path
            rw [← plan.head]
            exact ((chainStep plan.chain).1 _).mpr eq
      | caller => exact live.elim
      | _ =>
        refine (controlStep ready trivial).trans ⟨?_, ?_⟩
        · rintro ⟨b, move, eq⟩
          exact ⟨_, .control move, eq⟩
        · rintro ⟨b, move, eq⟩
          cases move with
          | control move => exact ⟨_, move, eq⟩
    | pending head rest next =>
      rw [prefixRender, (chainStep ready.1).1 dst]
      exact ⟨fun eq => ⟨_, .pending, eq⟩, fun ⟨_, move, eq⟩ => by cases move; exact eq⟩
    | callee call a =>
      rcases ready.2.2 with active | ⟨result, rfl⟩
      · refine (calleeStep ready.1 ready.2.1 active).trans ⟨?_, ?_⟩
        · rintro ⟨b, move, eq⟩
          exact ⟨_, .callee active move, eq⟩
        · rintro ⟨b, move, eq⟩
          cases move with
          | callee _ move => exact ⟨_, move, eq⟩
          | return_ => cases active
      · cases result with
        | trap => exact live.elim
        | values values =>
          rw [returnEq ready.1]
          refine (writeStep (return_ready (A := A) ready.1 ready.2.1)).trans ⟨?_, ?_⟩
          · rintro ⟨b, move, eq⟩
            exact ⟨_, .return_ move, eq⟩
          · rintro ⟨b, move, eq⟩
            cases move with
            | callee active => cases active
            | return_ move => exact ⟨_, move, eq⟩
    | write => exact writeStep ready
    | branch =>
      rw [restart]
      exact ⟨fun eq => ⟨_, .restart, eq⟩, fun ⟨_, move, eq⟩ => by cases move; exact eq⟩
    | trap => exact live.elim
  have checked {a} (run : Runs entry program indices recipe (.control initial) a) :
      Ready entry program indices native render a := by
    induction run with
    | refl => exact controlReady
    | tail _ move ih => exact keeps ih move
  refine Resume.split_run render Phase.Live stop (fun run live => step (checked run) live) ?_
    (fun run halted => finish (checked run) halted)
  intro a b _ move
  cases move with
  | control move => cases move <;> trivial
  | @callee call a b live _ => cases a <;> first | exact trivial | exact live.elim
  | _ => trivial

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Repeat.Proofs
