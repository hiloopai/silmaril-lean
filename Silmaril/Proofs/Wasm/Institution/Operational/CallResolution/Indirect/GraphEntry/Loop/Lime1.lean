module

public import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Common
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Wasm.Institution.Operational.Locals.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Source.Thms
import Silmaril.Wasm.Institution.Operational.Loops.Native.Thms
import Mathlib.Data.List.Chain

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Proofs.Lime1

open Execution
open Wasm.Lime1.Execution
open Execution.Runtime (Frame Value)
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked
open Wasm.SingleThreaded.Det (noHost)

variable {H : Type} {s : Store H} {entry : Entry} {program : Graph.Program}
  {tables : Source.Tables} {outer : Frame} {index : FuncIdx} {args : List Value}

private theorem expression_prefix (fn : Graph.Function) (code : Wasm.Lime1.Expr) :
    expression (fn.initial.map Graph.limeCodeSyntax.ops.value ++ code) =
      values fn.initial ++ expression code := by
  have literals := Graph.lime_body_expression { fn with code := [] }
  change expression (fn.initial.map Graph.limeCodeSyntax.ops.value ++ []) = values fn.initial ++ [] at literals
  simp only [List.append_nil, expression, List.map_append] at literals ⊢
  rw [literals]

private theorem expression_loop (entry : Entry) :
    expression (entry.limeLoop :: Graph.Op.emitList Graph.limeCodeSyntax entry.tail) =
      .source entry.limeLoop :: entry.tail.map Graph.limeEmit := by
  have tail := Graph.lime_body_expression { entry.owner with initial := [], code := entry.tail }
  exact congrArg (fun code => .source entry.limeLoop :: code) tail

private theorem wrap_iff {body after dst : Config H}
    (stays : ∀ out, ¬ PureStep body.frame.module.types [.label entry.owner.declaration.results.length [] body.code] out)
    (move : ∀ target, Step CallFrame.limeNoHost body target ↔ target = after) :
    Step CallFrame.limeNoHost (entry.cont.limeWrap outer body) dst ↔ dst = entry.cont.limeWrap outer after := by
  rw [Context.Resume.lime_wrap_step_iff stays]
  simp only [move, exists_eq_left]

theorem loop_wrap_iff {body dst : Config H}
    (stays : ∀ out, ¬ PureStep body.frame.module.types [.label 0 [entry.limeLoop] body.code] out) :
    Step CallFrame.limeNoHost (entry.limeLoopWrap outer body) dst ↔
      ∃ mid, Step CallFrame.limeNoHost body mid ∧ dst = entry.limeLoopWrap outer mid := by
  let outerLabel : Config H := ⟨body.store, body.frame, values entry.owner.initial ++
    .label 0 [entry.limeLoop] body.code :: entry.tail.map Graph.limeEmit⟩
  have keep (out : List Admin) : ¬ PureStep outerLabel.frame.module.types [.label entry.owner.declaration.results.length [] outerLabel.code] out :=
    Computed.lime_label_stays (head := .label 0 [entry.limeLoop] body.code) rfl (by simp) (by simp) (by simp)
  change Step CallFrame.limeNoHost (entry.cont.limeWrap outer outerLabel) dst ↔ _
  rw [Context.Resume.lime_wrap_step_iff keep]
  have invert (mid : Config H) := Blocks.Context.lime_label_cont_iff (s := body.store)
    (f := body.frame) (n := 0) (cont := [entry.limeLoop]) (saved := entry.owner.initial) (body := body.code)
    (rest := entry.tail.map Graph.limeEmit) (dst := mid)
  constructor
  · rintro ⟨mid, move, rfl⟩
    rcases (invert mid).mp move with ⟨next, edge, rfl⟩ | ⟨out, pop, _⟩
    · exact ⟨next, edge, rfl⟩
    · exact (stays out pop).elim
  · rintro ⟨mid, edge, rfl⟩
    exact ⟨_, (invert _).mpr (.inl ⟨mid, edge, rfl⟩), rfl⟩

private theorem loop_step_exact {body after dst : Config H}
    (stays : ∀ out, ¬ PureStep body.frame.module.types [.label 0 [entry.limeLoop] body.code] out)
    (move : ∀ target, Step CallFrame.limeNoHost body target ↔ target = after) :
    Step CallFrame.limeNoHost (entry.limeLoopWrap outer body) dst ↔ dst = entry.limeLoopWrap outer after := by
  rw [loop_wrap_iff stays]
  simp only [move, exists_eq_left]

private theorem get_exact {locals stack : List Value} {i : LocalIdx} {value : BitVec 32}
    (read : locals[i.toNat]? = some (.int .i32 value)) (rest : List Admin) (dst : Config H) :
    Step CallFrame.limeNoHost (entry.limeLoopWrap outer ⟨s, entry.frame locals,
      values stack ++ .source (.localGet i) :: rest⟩) dst ↔
      dst = entry.limeLoopWrap outer ⟨s, entry.frame locals, values (stack ++ [.int .i32 value]) ++ rest⟩ := by
  apply loop_step_exact
  · intro out exit
    exact Computed.lime_label_stays (head := .source (.localGet i)) rfl (by simp) (by simp) (by simp) exit
  · intro target
    have reduced : Prefix.Reduce locals stack (.get i) (.values (stack ++ [.int .i32 value])) := .get read
    refine (Prefix.lime_step_iff (s := s) (f := entry.frame locals) (op := .get i) (tail := rest)).trans ⟨?_, ?_⟩
    · rintro ⟨out, h, rfl⟩
      rw [Prefix.reduce_unique h reduced]
      rfl
    · rintro rfl
      exact ⟨_, reduced, rfl⟩

private theorem write_exact (locals : List Value) (old next : BitVec 32) (rest : List Admin) (dst : Config H) :
    Step CallFrame.limeNoHost (entry.limeLoopWrap outer ⟨s, entry.frame locals,
      values [.int .i32 old, .int .i32 next] ++ .source (.localSet entry.restart) :: rest⟩) dst ↔
    ∃ nextLocals, Locals.Edge ⟨locals, [.value (.int .i32 next), .set entry.restart]⟩ ⟨nextLocals, []⟩ ∧
      dst = entry.limeLoopWrap outer ⟨s, entry.frame nextLocals, (values [Value.int .i32 old]) ++ rest⟩ := by
  have stays {out : List Admin} := Computed.lime_label_stays (types := (entry.frame locals).module.types) (head := .source (.localSet entry.restart))
    rfl (by simp) (by simp) (by simp)
    (stack := [.int .i32 old, .int .i32 next])
    (n := 0) (cont := [entry.limeLoop]) (rest := rest) (out := out)
  rw [loop_wrap_iff (fun _ => stays)]
  constructor
  · rintro ⟨mid, move, rfl⟩
    obtain ⟨saved, v, nextLocals, split, write, rfl⟩ := Computed.lime_set_read (f := entry.frame locals) move
    have last := congrArg List.getLast? split
    simp at last
    subst v
    have same : [Value.int .i32 old] ++ [Value.int .i32 next] = saved ++ [Value.int .i32 next] := split
    have first : saved = [Value.int .i32 old] := (List.append_cancel_right same).symm
    subst saved
    exact ⟨_, write, rfl⟩
  · rintro ⟨nextLocals, write, rfl⟩
    refine ⟨_, ?_, rfl⟩
    have head := Locals.lime_sound (host := CallFrame.limeNoHost) (s := s) (m := entry.owner.declaration.module) write
    exact Step.context head [.int .i32 old] rest

private theorem single {a b : State} {dst : Config H}
    (edge : Edge entry a b) (unique : ∀ q, Edge entry a q → q = b)
    (native : Step CallFrame.limeNoHost (entry.limeConfig s outer a) dst ↔ dst = entry.limeConfig s outer b) :
    Step CallFrame.limeNoHost (entry.limeConfig s outer a) dst ↔
      ∃ q, Edge entry a q ∧ dst = entry.limeConfig s outer q := by
  rw [native]
  constructor
  · intro eq
    exact ⟨b, edge, eq⟩
  · rintro ⟨q, move, eq⟩
    exact eq.trans (congrArg (entry.limeConfig s outer) (unique q move))

theorem step_iff (ready : entry.Checked program tables outer index args) {a : State} {dst : Config H}
    (typed : entry.Typed a) (live : a.phase.Pending) :
    Step CallFrame.limeNoHost (entry.limeConfig s outer a) dst ↔
      ∃ b, Edge entry a b ∧ dst = entry.limeConfig s outer b := by
  obtain ⟨_, chosen⟩ := progress ready typed live
  cases chosen with
  | @enter locals =>
    apply single .enter (by intro _ move; cases move; rfl)
    apply wrap_iff
    · intro out exit
      exact Computed.lime_label_stays (head := .source entry.limeLoop) rfl
        (by simp [Entry.limeLoop]) (by simp [Entry.limeLoop]) (by simp) exit
    · intro target
      exact Loops.lime_entry_iff (s := s) (f := entry.frame locals) (saved := entry.owner.initial)
        (result := entry.result) (body := entry.iteration Graph.limeCodeSyntax Source.Op.limeInstr)
        (rest := entry.tail.map Graph.limeEmit) (dst := target)
  | @readRestart locals old read =>
    apply single (.readRestart read)
    · intro _ move
      cases move with
      | readRestart next => cases Option.some.inj (read.symm.trans next); rfl
    · exact get_exact (entry := entry) (s := s) (outer := outer) (stack := [])
        read (expression ((entry.iteration Graph.limeCodeSyntax Source.Op.limeInstr).drop 1)) dst
  | @readNext locals old next read =>
    apply single (.readNext read)
    · intro _ move
      cases move with
      | readNext next => cases Option.some.inj (read.symm.trans next); rfl
    · exact get_exact (entry := entry) (s := s) (outer := outer) (stack := [.int .i32 old])
        read (expression ((entry.iteration Graph.limeCodeSyntax Source.Op.limeInstr).drop 2)) dst
  | @writeRestart locals _ old next _ =>
    refine (write_exact locals old next _ dst).trans ⟨?_, ?_⟩
    · rintro ⟨newLocals, write, eq⟩
      exact ⟨⟨newLocals, .testRestart old⟩, .writeRestart write, eq⟩
    · rintro ⟨out, move, eq⟩
      cases move with
      | writeRestart write => exact ⟨_, write, eq⟩
  | @testRestart locals old =>
    apply single .testRestart (by intro _ move; cases move; rfl)
    by_cases zero : old = (0 : BitVec 32)
    · rw [ite_eq_left zero]
      apply loop_step_exact
      · intro out exit
        exact Computed.lime_label_stays (head := .source (.brIf ⟨0⟩)) rfl
          (by simp) (by simp) (by simp) exit
      · intro target
        simpa only [ite_eq_left zero, Entry.iterationCode, Entry.iteration, Entry.prefix, Source.Body.lime,
          Graph.limeCodeSyntax, Graph.limeAdmin, Graph.Op.emitList, Graph.Op.emit, Graph.limeEmit, expression,
          List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.drop_succ_cons, List.drop_zero,
          List.append_assoc, values] using!
          (Computed.lime_br_if_iff (s := s) (f := entry.frame locals)
            (saved := []) (condition := old) (depth := ⟨0⟩)
            (rest := expression ((entry.iteration Graph.limeCodeSyntax Source.Op.limeInstr).drop 4)) (dst := target))
    · rw [ite_eq_right zero]
      apply loop_step_exact
      · intro out exit
        exact Computed.lime_label_stays (head := .source (.brIf ⟨0⟩)) rfl
          (by simp) (by simp) (by simp) exit
      · intro target
        simpa only [ite_eq_right zero, Entry.iterationCode, Entry.iteration, Entry.prefix, Source.Body.lime,
          Graph.limeCodeSyntax, Graph.limeAdmin, Graph.Op.emitList, Graph.Op.emit, Graph.limeEmit, expression,
          List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.drop_succ_cons, List.drop_zero,
          List.append_assoc, values] using!
          (Computed.lime_br_if_iff (s := s) (f := entry.frame locals)
            (saved := []) (condition := old) (depth := ⟨0⟩)
            (rest := expression ((entry.iteration Graph.limeCodeSyntax Source.Op.limeInstr).drop 4)) (dst := target))
  | @restart locals =>
    apply single .restart (by intro _ move; cases move; rfl)
    apply wrap_iff
    · intro out exit
      exact Computed.lime_label_stays (head := .label 0 [entry.limeLoop] _) rfl
        (by simp) (by simp) (by simp) exit
    · intro target
      simpa only [Entry.iterationCode, Entry.iteration, Entry.prefix, Source.Body.lime, Graph.limeCodeSyntax,
        Graph.limeAdmin, Graph.Op.emitList, Graph.Op.emit, Graph.limeEmit, expression, List.cons_append,
        List.nil_append, List.map_cons, List.map_nil, List.drop_succ_cons, List.drop_zero, List.append_assoc,
        values] using!
        (Loops.lime_restart_iff (s := s) (f := entry.frame locals) (saved := entry.owner.initial) (scratch := [])
        (cont := [entry.limeLoop]) (pending := expression ((entry.iteration Graph.limeCodeSyntax Source.Op.limeInstr).drop 4))
        (rest := entry.tail.map Graph.limeEmit) (dst := target))
  | @readChoice locals value read =>
    apply single (.readChoice read)
    · intro _ move
      cases move with
      | readChoice next => cases Option.some.inj (read.symm.trans next); rfl
    · exact get_exact (entry := entry) (s := s) (outer := outer) (stack := [])
        read (expression ((entry.iteration Graph.limeCodeSyntax Source.Op.limeInstr).drop 5)) dst
  | @testChoice locals value =>
    apply single .testChoice (by intro _ move; cases move; rfl)
    have move (target : Config H) := Computed.lime_if_iff (s := s) (f := entry.frame locals)
      (saved := []) (condition := value) (bt := Blocks.limeType entry.result)
      (thenBody := entry.siteBody.lime) (elseBody := []) (rest := []) (dst := target)
    by_cases zero : value = (0#32)
    · have choice : decide (value ≠ 0) = false := by
        exact decide_eq_false (fun nonzero => nonzero zero)
      rw [choice]
      apply loop_step_exact
      · intro out exit
        exact Computed.lime_label_stays (head := .source (.if_ (Blocks.limeType entry.result)
          entry.siteBody.lime [])) rfl (by simp) (by simp) (by simp) exit
      · intro target
        have selected := move target
        rw [ite_eq_left (show value = (0 : BitVec 32) from zero)] at selected
        simpa only [Entry.iterationCode, Entry.iteration, Entry.prefix, Source.Body.lime, Graph.limeCodeSyntax,
          Graph.limeAdmin, Graph.Op.emitList, Graph.Op.emit, Graph.limeEmit, expression, List.cons_append,
          List.nil_append, List.map_cons, List.map_nil, List.drop_succ_cons, List.drop_zero, List.append_assoc,
          values] using! selected
    · have choice : decide (value ≠ 0) = true := decide_eq_true zero
      rw [choice]
      apply loop_step_exact
      · intro out exit
        exact Computed.lime_label_stays (head := .source (.if_ (Blocks.limeType entry.result)
          entry.siteBody.lime [])) rfl (by simp) (by simp) (by simp) exit
      · intro target
        have selected := move target
        rw [ite_eq_right (show ¬ value = (0 : BitVec 32) from zero)] at selected
        simpa only [Entry.iterationCode, Entry.iteration, Entry.prefix, Source.Body.lime, Graph.limeCodeSyntax,
          Graph.limeAdmin, Graph.Op.emitList, Graph.Op.emit, Graph.limeEmit, expression, List.cons_append,
          List.nil_append, List.map_cons, List.map_nil, List.drop_succ_cons, List.drop_zero, List.append_assoc,
          values] using! selected
  | @enterSite locals =>
    apply single .enterSite (by intro _ move; cases move; rfl)
    apply loop_step_exact
    · intro out exit
      change PureStep (entry.frame locals).module.types [.label 0 [entry.limeLoop] [.source (.block (Blocks.limeType entry.result) entry.siteBody.lime)]] out at exit
      exact Computed.lime_label_stays (stack := []) (rest := []) (head := .source (.block (Blocks.limeType entry.result) entry.siteBody.lime)) rfl
        (by simp) (by simp) (by simp) exit
    · intro target
      exact Computed.lime_block_iff (s := s) (f := entry.frame locals)
        (stack := []) (result := entry.result) (body := entry.siteBody.lime) (rest := []) (dst := target)
  | @enterEmpty locals =>
    apply single .enterEmpty (by intro _ move; cases move; rfl)
    apply loop_step_exact
    · intro out exit
      change PureStep (entry.frame locals).module.types [.label 0 [entry.limeLoop] [.source (.block (Blocks.limeType entry.result) ([] : List _))]] out at exit
      exact Computed.lime_label_stays (stack := []) (rest := []) (head := .source (.block (Blocks.limeType entry.result) [])) rfl
        (by simp) (by simp) (by simp) exit
    · intro target
      exact Computed.lime_block_iff (s := s) (f := entry.frame locals)
        (stack := []) (result := entry.result) (body := []) (rest := []) (dst := target)
  | @leaveEmpty locals =>
    apply single .leaveEmpty (by intro _ move; cases move; rfl)
    apply loop_step_exact
    · intro out exit
      exact Computed.lime_label_stays (head := .label entry.result.toList.length [] []) (stack := []) rfl
        (by simp) (by simp) (by simp) exit
    · intro target
      exact Blocks.Context.lime_result_iff (s := s) (f := entry.frame locals) (dst := target) (scope := ⟨entry.result.toList.length, [], []⟩) (r := .values [])
  | @leaveLoop locals =>
    apply single .leaveLoop (by intro _ move; cases move; rfl)
    change Step CallFrame.limeNoHost (entry.limeLoopWrap outer ⟨s, entry.frame locals, []⟩) dst ↔
      dst = entry.cont.limeWrap outer ⟨s, entry.frame locals,
        values entry.owner.initial ++ entry.tail.map Graph.limeEmit⟩
    apply wrap_iff
    · intro out exit
      exact Computed.lime_label_stays (head := .label 0 [entry.limeLoop] []) rfl
        (by simp) (by simp) (by simp) exit
    · intro target
      simpa only [CallContinuation.Nested.resultCode, List.nil_append, List.append_nil, List.map_nil, values] using!
        (Loops.lime_result_iff (s := s) (f := entry.frame locals) (rest := entry.tail.map Graph.limeEmit) (dst := target) (r := .values []) (cont := [entry.limeLoop]) (saved := entry.owner.initial))

theorem site_operands (locals : List Value) :
    entry.limeConfig s outer ⟨locals, .site⟩ = entry.limeOperands s outer locals ([], entry.before) := by
  have tail := Graph.lime_body_expression { entry.owner with initial := [], code := entry.insideTail }
  change expression (Graph.Op.emitList Graph.limeCodeSyntax entry.insideTail) =
    entry.insideTail.map Graph.limeEmit at tail
  have numeric : expression (entry.before.map (fun p => Graph.Op.emit Graph.limeCodeSyntax (.numeric p))) =
      entry.before.map (Prefix.emit limeSyntax) := by
    induction entry.before with
    | nil => rfl
    | cons op rest ih => cases op <;> exact congrArg (fun code => _ :: code) ih
  change entry.limeArmWrap outer ⟨s, entry.frame locals, expression entry.siteBody.lime⟩ =
    entry.limeArmWrap outer ⟨s, entry.frame locals, entry.limeSiteCode entry.before⟩
  suffices code : expression entry.siteBody.lime = entry.limeSiteCode entry.before by rw [code]
  have split (a b : List _) : expression (a ++ b) = expression a ++ expression b := List.map_append
  change expression ((entry.before.map (fun p => Graph.Op.emit Graph.limeCodeSyntax (.numeric p))) ++
    entry.op.limeInstr :: Graph.Op.emitList Graph.limeCodeSyntax entry.insideTail) = _
  rw [split, numeric]
  change entry.before.map (Prefix.emit limeSyntax) ++ .source entry.op.limeInstr ::
    expression (Graph.Op.emitList Graph.limeCodeSyntax entry.insideTail) = entry.limeSiteCode entry.before
  rw [tail]
  rfl

private theorem operand_iff {locals stack : List Value} {op : Prefix.Op} {rest : List Prefix.Op}
    {ans : Prefix.Outcome} (move : Prefix.Reduce locals stack op ans) (dst : Config H) :
    Step CallFrame.limeNoHost (entry.limeOperands s outer locals (stack, op :: rest)) dst ↔
      dst = match ans with
        | .values next => entry.limeOperands s outer locals (next, rest)
        | .trap saved => entry.limeOperandResult s outer locals (.trap saved rest) := by
  let tail := entry.limeSiteCode rest
  let inside : Config H := ⟨s, entry.frame locals, values stack ++ Prefix.emit limeSyntax op :: tail⟩
  have armStays (out : List Admin) : ¬ PureStep inside.frame.module.types [.label entry.result.toList.length [] inside.code] out :=
    Computed.lime_label_stays (by cases op <;> rfl)
      (by cases op <;> simp [Prefix.emit, limeSyntax])
      (by cases op <;> simp [Prefix.emit, limeSyntax])
      (by cases op <;> simp [Prefix.emit, limeSyntax])
  have loopStays (out : List Admin) : ¬ PureStep inside.frame.module.types [.label 0 [entry.limeLoop] [.label entry.result.toList.length [] inside.code]] out :=
    Computed.lime_label_stays (stack := []) (rest := []) (head := .label _ [] _)
      rfl (by simp) (by simp) (by simp)
  change Step CallFrame.limeNoHost (entry.limeArmWrap outer inside) dst ↔ _
  rw [Entry.limeArmWrap, loop_wrap_iff loopStays]
  have arm (mid : Config H) := Blocks.Context.lime_label_iff (s := s) (f := entry.frame locals)
    (n := entry.result.toList.length) (saved := []) (rest := []) (body := inside.code) (dst := mid)
  have exactOp (target : Config H) := Prefix.lime_step_iff (s := s) (f := entry.frame locals) (stack := stack) (op := op) (tail := tail) (dst := target)
  constructor
  · rintro ⟨mid, wrapped, rfl⟩
    rcases (arm mid).mp wrapped with ⟨after, stepped, rfl⟩ | ⟨out, exit, _⟩
    · obtain ⟨actual, reduced, rfl⟩ := (exactOp after).mp stepped
      cases Prefix.reduce_unique reduced move
      cases ans <;> rfl
    · exact (armStays out exit).elim
  · intro eq
    have step := (exactOp _).mpr ⟨ans, move, rfl⟩
    cases ans <;> exact ⟨_, (arm _).mpr (.inl ⟨_, step, rfl⟩), eq⟩

theorem operand_chain {locals stack : List Value} {code : List Prefix.Op}
    {states : List OperandState} {result : OperandResult}
    (trace : OperandTrace locals stack code states result) :
    (states.map (entry.limeOperands s outer locals) ++ [entry.limeOperandResult s outer locals result]).IsChain
      (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) := by
  induction trace with
  | done => exact .singleton _
  | value step next ih =>
    apply ih.cons
    intro b found dst
    cases next <;>
      have eq := Option.mem_some.mp found <;>
      subst b <;> exact operand_iff step dst
  | trap step => exact List.isChain_pair.mpr (operand_iff step)

theorem operand_run_iff {locals : List Value} {states : List OperandState} {result : OperandResult}
    (trace : OperandTrace locals [] entry.before states result) {dst : Config H} :
    Steps CallFrame.limeNoHost (entry.limeConfig s outer ⟨locals, .site⟩) dst ↔
      dst ∈ states.map (entry.limeOperands s outer locals) ∨
        Steps CallFrame.limeNoHost (entry.limeOperandResult s outer locals result) dst := by
  have chain := operand_chain (entry := entry) (s := s) (outer := outer) trace
  have head {stack code path result}
      (walk : OperandTrace locals stack code path result) :
      (path.map (entry.limeOperands s outer locals)).headD (entry.limeOperandResult s outer locals result) =
        entry.limeOperands s outer locals (stack, code) := by
    cases walk <;> rfl
  rw [site_operands, ← head trace]
  exact Context.Resume.prefix_run_iff _ _ chain

theorem lookup_start {locals stack : List Value} {active : Source.Activation}
    (prepared : entry.op.prepare program tables (entry.frame locals) stack = some active) :
    entry.limeOperandResult s outer locals (.values stack) = entry.limeLookup s outer active := by
  have facts := Source.prepare_spec prepared
  rw [facts.stack_eq]
  simp only [Entry.limeOperandResult, Entry.limeOperands, Entry.limeSiteCode, Entry.limeLookup,
    Source.Activation.limeSource, Indirect.limeSource, Entry.limeArmWrap, Source.limeNest,
    Context.limeNest, Context.limeNestWith, List.foldr_cons, List.foldr_nil, Entry.armScope,
    List.map_nil, values, List.map_append, List.append_assoc]
  rw [facts.caller_eq, facts.typeIndex_eq]
  rfl

theorem lookup_exact {active : Source.Activation} {out : Outcome}
    (ready : active.Checked program tables) (targets : active.binding.site.LimeAllocated program s)
    (allocated : Source.Tables.LimeAllocated tables s) (resolved : active.resolve program = some out)
    (dst : Config H) :
    Step CallFrame.limeNoHost (entry.limeLookup s outer active) dst ↔
      dst = entry.limeLookupResult s outer active out := by
  apply loop_step_exact
  · intro out exit
    exact Computed.lime_label_stays (stack := []) (rest := []) (head := .label _ [] _)
      rfl (by simp) (by simp) (by simp) exit
  · exact Source.lime_resolution_allocated ready targets allocated resolved [entry.armScope] entry.insideTail

private theorem invoke_iff (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.address.value]? = some entry.limeInstance) (dst : Config H) :
    Step CallFrame.limeNoHost ((⟨entry.cont, entry.op, entry.before⟩ : GraphEntry.Entry).limeInvoke s outer args) dst ↔
      dst = entry.limeConfig s outer (entry.initial args) := by
  have count : args.length = entry.owner.declaration.type.params.length :=
    (List.length_map ..).symm.trans (congrArg List.length ready.typed)
  have enter := CallFrame.lime_invoke_wasm_exact (caller := outer) (dst := dst) allocated count
  change _ ↔ dst = entry.cont.limeWrap outer ⟨s, entry.owner.declaration.frame args, expression entry.limeFunc.body⟩ at enter
  rw [Entry.limeFunc, expression_prefix entry.owner, expression_loop] at enter
  exact enter

theorem entry_chain (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.address.value]? = some entry.limeInstance) :
    let start := limeSource s outer index args
    let invoke := (⟨entry.cont, entry.op, entry.before⟩ : GraphEntry.Entry).limeInvoke s outer args
    ([start, invoke] ++ [entry.limeConfig s outer (entry.initial args)]).IsChain
        (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) := by
  intro start invoke
  exact List.isChain_cons_cons.mpr ⟨fun _ => Computed.lime_direct_call_iff (s := s) (stack := args)
      (tail := []) ready.resolves, List.isChain_pair.mpr (invoke_iff ready allocated)⟩

theorem run_iff (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.address.value]? = some entry.limeInstance)
    (links : program.LimeLinksAllocated s) {dst : Config H} :
    let start := limeSource s outer index args
    let invoke := (⟨entry.cont, entry.op, entry.before⟩ : GraphEntry.Entry).limeInvoke s outer args
    Steps CallFrame.limeNoHost start dst ↔ dst ∈ [start, invoke] ∨
      Observation entry args (entry.limeConfig s outer)
        (fun locals out => ∃ phase, program.FrameRuns entry.address (entry.callerPhase locals) phase ∧
          Graph.Admitted program entry.owner phase ∧ out = Graph.limeConfig s outer entry.cont.target phase)
        (Step CallFrame.limeNoHost) dst := by
  let start := limeSource s outer index args
  let invoke := (⟨entry.cont, entry.op, entry.before⟩ : GraphEntry.Entry).limeInvoke s outer args
  have chain := entry_chain ready allocated
  have native := Context.Resume.prefix_run_iff (dst := dst) [start, invoke] _ chain
  refine native.trans (or_congr Iff.rfl (observe (entry.limeConfig s outer) (Step CallFrame.limeNoHost) _
    (initial_typed ready) (preserve ready) (step_iff ready) ?_ dst))
  intro locals target typed
  exact Context.linked_runs (graph_checked ready) ready.found
    (Graph.limeConfig s outer entry.cont.target) (Step CallFrame.limeNoHost)
    (fun h entered => Graph.lime_entered_frame_step_iff (graph_checked ready) links ready.found rfl h entered)
    (caller_admitted ready typed) trivial

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Proofs.Lime1
