module

public import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Common
public import Silmaril.Wasm.Execution.Core.Inversion.Defs
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Wasm.Institution.Operational.Locals.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Source.Thms
import Silmaril.Wasm.Institution.Operational.Loops.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Thms
import Silmaril.Wasm.Institution.Operational.Blocks.Native.Thms
import Mathlib.Data.List.Chain

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Proofs.Core

open Execution
open Execution.Core
open Execution.Runtime (Value)

open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked
open Wasm.SingleThreaded.Det (noHost)

variable {H : Type} {P : Numerics.Profile} {s : Store H} {entry : Entry} {program : Graph.Program}
  {tables : Source.Tables} {outer : Runtime.Frame} {index : FuncIdx} {args : List Value}

private theorem expression_prefix (fn : Graph.Function) (code : List Instr) :
    expression (fn.initial.map Graph.coreCodeSyntax.ops.value ++ code) =
      coreValues fn.initial ++ expression code := by
  have literals := Graph.core_body_expression { fn with code := [] }
  change expression (fn.initial.map Graph.coreCodeSyntax.ops.value ++ []) = coreValues fn.initial ++ [] at literals
  simp only [List.append_nil, expression, List.map_append] at literals ⊢
  rw [literals]

private theorem expression_loop (entry : Entry) :
    expression (entry.coreLoop :: Graph.Op.emitList Graph.coreCodeSyntax entry.tail) =
      .plain entry.coreLoop :: entry.tail.map Graph.coreEmit := by
  have tail := Graph.core_body_expression { entry.owner with initial := [], code := entry.tail }
  exact congrArg (fun code => .plain entry.coreLoop :: code) tail

private theorem wrap_iff {body after dst : Config H}
    (stays : ∀ out, ¬ LabelExit entry.owner.declaration.results.length [] body.code out)
    (move : ∀ target, Step P noHost body target ↔ target = after) :
    Step P noHost (entry.cont.coreWrap outer body) dst ↔ dst = entry.cont.coreWrap outer after := by
  rw [Context.Resume.core_wrap_step_iff stays]
  simp only [move, exists_eq_left]

theorem loop_wrap_iff {body dst : Config H}
    (stays : ∀ out, ¬ LabelExit 0 [entry.coreLoop] body.code out) :
    Step P noHost (entry.coreLoopWrap outer body) dst ↔
      ∃ mid, Step P noHost body mid ∧ dst = entry.coreLoopWrap outer mid := by
  let outerLabel : Config H := ⟨body.store, body.frame, coreValues entry.owner.initial ++
    .label 0 [entry.coreLoop] body.code :: entry.tail.map Graph.coreEmit⟩
  have keep (out : List Admin) : ¬ LabelExit entry.owner.declaration.results.length [] outerLabel.code out :=
    Computed.core_label_stays (head := .label 0 [entry.coreLoop] body.code) rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp)
  change Step P noHost (entry.cont.coreWrap outer outerLabel) dst ↔ _
  rw [Context.Resume.core_wrap_step_iff keep]
  have invert (mid : Config H) := Blocks.Context.core_label_cont_iff (P := P) (s := body.store)
    (f := body.frame) (n := 0) (cont := [entry.coreLoop]) (saved := (entry.owner.initial.map Value.toCore)) (body := body.code)
    (rest := entry.tail.map Graph.coreEmit) (dst := mid)
  constructor
  · rintro ⟨mid, move, rfl⟩
    rcases (invert mid).mp move with ⟨next, edge, rfl⟩ | ⟨out, pop, _⟩
    · exact ⟨next, edge, rfl⟩
    · exact (stays out pop).elim
  · rintro ⟨mid, edge, rfl⟩
    exact ⟨_, (invert _).mpr (.inl ⟨mid, edge, rfl⟩), rfl⟩

private theorem loop_step_exact {body after dst : Config H}
    (stays : ∀ out, ¬ LabelExit 0 [entry.coreLoop] body.code out)
    (move : ∀ target, Step P noHost body target ↔ target = after) :
    Step P noHost (entry.coreLoopWrap outer body) dst ↔ dst = entry.coreLoopWrap outer after := by
  rw [loop_wrap_iff stays]
  simp only [move, exists_eq_left]

private theorem get_exact {locals stack : List Value} {i : LocalIdx} {value : BitVec 32}
    (read : locals[i.toNat]? = some (.int .i32 value)) (rest : List Admin) (dst : Config H) :
    Step P noHost (entry.coreLoopWrap outer ⟨s, (entry.frame locals).toCore,
      coreValues stack ++ .plain (.localGet i) :: rest⟩) dst ↔
      dst = entry.coreLoopWrap outer ⟨s, (entry.frame locals).toCore, coreValues (stack ++ [.int .i32 value]) ++ rest⟩ := by
  apply loop_step_exact
  · intro out exit
    exact Computed.core_label_stays (head := .plain (.localGet i)) rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) exit
  · intro target
    have reduced : Prefix.Reduce locals stack (.get i) (.values (stack ++ [.int .i32 value])) := .get read
    refine (Prefix.core_step_iff (P := P) (s := s) (f := entry.frame locals) (op := .get i) (tail := rest)).trans ⟨?_, ?_⟩
    · rintro ⟨out, h, rfl⟩
      rw [Prefix.reduce_unique h reduced]
      rfl
    · rintro rfl
      exact ⟨_, reduced, rfl⟩

private theorem write_exact (locals : List Value) (old next : BitVec 32) (rest : List Admin) (dst : Config H) :
    Step P noHost (entry.coreLoopWrap outer ⟨s, (entry.frame locals).toCore,
      coreValues [.int .i32 old, .int .i32 next] ++ .plain (.localSet entry.restart) :: rest⟩) dst ↔
    ∃ nextLocals, Locals.Edge ⟨locals, [.value (.int .i32 next), .set entry.restart]⟩ ⟨nextLocals, []⟩ ∧
      dst = entry.coreLoopWrap outer ⟨s, (entry.frame nextLocals).toCore, (coreValues [Value.int .i32 old]) ++ rest⟩ := by
  have stays {out : List Admin} := Computed.core_label_stays (head := .plain (.localSet entry.restart))
    rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp)
    (stack := [Value.toCore (.int .i32 old), Value.toCore (.int .i32 next)])
    (n := 0) (cont := [entry.coreLoop]) (rest := rest) (out := out)
  rw [loop_wrap_iff (fun _ => stays)]
  constructor
  · rintro ⟨mid, move, rfl⟩
    obtain ⟨saved, v, nextLocals, split, write, rfl⟩ := Computed.core_set_read (f := entry.frame locals) move
    have last := congrArg List.getLast? split
    simp at last
    subst v
    have same : [Value.int .i32 old] ++ [Value.int .i32 next] = saved ++ [Value.int .i32 next] := split
    have first : saved = [Value.int .i32 old] := (List.append_cancel_right same).symm
    subst saved
    exact ⟨_, write, rfl⟩
  · rintro ⟨nextLocals, write, rfl⟩
    refine ⟨_, ?_, rfl⟩
    have head := Locals.core_sound (P := P) (s := s) (m := entry.owner.declaration.module.toCore) write
    have lift := Wasm.SingleThreaded.Det.lift_instrs [(Value.int .i32 old).toCore] rest _ _ head
    exact lift

private theorem single {a b : State} {dst : Config H}
    (edge : Edge entry a b) (unique : ∀ q, Edge entry a q → q = b)
    (native : Step P noHost (entry.coreConfig s outer a) dst ↔ dst = entry.coreConfig s outer b) :
    Step P noHost (entry.coreConfig s outer a) dst ↔
      ∃ q, Edge entry a q ∧ dst = entry.coreConfig s outer q := by
  rw [native]
  constructor
  · intro eq
    exact ⟨b, edge, eq⟩
  · rintro ⟨q, move, eq⟩
    exact eq.trans (congrArg (entry.coreConfig s outer) (unique q move))

theorem step_iff (ready : entry.Checked program tables outer index args) {a : State} {dst : Config H}
    (typed : entry.Typed a) (live : a.phase.Pending) :
    Step P noHost (entry.coreConfig s outer a) dst ↔
      ∃ b, Edge entry a b ∧ dst = entry.coreConfig s outer b := by
  obtain ⟨_, chosen⟩ := progress ready typed live
  cases chosen with
  | @enter locals =>
    apply single .enter (by intro _ move; cases move; rfl)
    apply wrap_iff
    · intro out exit
      exact Computed.core_label_stays (head := .plain entry.coreLoop) rfl
        (by simp [Entry.coreLoop]) (by simp [Entry.coreLoop]) (by simp [Entry.coreLoop, Admin.IsReturnCallRef]) (by simp [Entry.coreLoop]) (by simp) exit
    · intro target
      exact Loops.core_entry_iff (s := s) (P := P) (f := (entry.frame locals).toCore) (saved := (entry.owner.initial.map Value.toCore))
        (result := entry.result) (body := entry.iteration Graph.coreCodeSyntax Source.Op.coreInstr)
        (rest := entry.tail.map Graph.coreEmit) (dst := target)
  | @readRestart locals old read =>
    apply single (.readRestart read)
    · intro _ move
      cases move with
      | readRestart next => cases Option.some.inj (read.symm.trans next); rfl
    · exact get_exact (P := P) (entry := entry) (s := s) (outer := outer) (stack := [])
        read (expression ((entry.iteration Graph.coreCodeSyntax Source.Op.coreInstr).drop 1)) dst
  | @readNext locals old next read =>
    apply single (.readNext read)
    · intro _ move
      cases move with
      | readNext next => cases Option.some.inj (read.symm.trans next); rfl
    · exact get_exact (P := P) (entry := entry) (s := s) (outer := outer) (stack := [.int .i32 old])
        read (expression ((entry.iteration Graph.coreCodeSyntax Source.Op.coreInstr).drop 2)) dst
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
        exact Computed.core_label_stays (head := .plain (.brIf ⟨0⟩)) rfl
          (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) exit
      · intro target
        simpa only [ite_eq_left zero, Entry.iterationCode, Entry.iteration, Entry.prefix, Source.Body.core,
          Graph.coreCodeSyntax, Graph.coreAdmin, Graph.Op.emitList, Graph.Op.emit, Graph.coreEmit, expression,
          List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.drop_succ_cons, List.drop_zero,
          List.append_assoc, coreValues, vals] using!
          (Computed.core_br_if_iff (P := P) (s := s) (f := (entry.frame locals).toCore)
            (saved := []) (condition := old) (depth := ⟨0⟩)
            (rest := expression ((entry.iteration Graph.coreCodeSyntax Source.Op.coreInstr).drop 4)) (dst := target))
    · rw [ite_eq_right zero]
      apply loop_step_exact
      · intro out exit
        exact Computed.core_label_stays (head := .plain (.brIf ⟨0⟩)) rfl
          (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) exit
      · intro target
        simpa only [ite_eq_right zero, Entry.iterationCode, Entry.iteration, Entry.prefix, Source.Body.core,
          Graph.coreCodeSyntax, Graph.coreAdmin, Graph.Op.emitList, Graph.Op.emit, Graph.coreEmit, expression,
          List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.drop_succ_cons, List.drop_zero,
          List.append_assoc, coreValues, vals] using!
          (Computed.core_br_if_iff (P := P) (s := s) (f := (entry.frame locals).toCore)
            (saved := []) (condition := old) (depth := ⟨0⟩)
            (rest := expression ((entry.iteration Graph.coreCodeSyntax Source.Op.coreInstr).drop 4)) (dst := target))
  | @restart locals =>
    apply single .restart (by intro _ move; cases move; rfl)
    apply wrap_iff
    · intro out exit
      exact Computed.core_label_stays (head := .label 0 [entry.coreLoop] _) rfl
        (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) exit
    · intro target
      simpa only [Entry.iterationCode, Entry.iteration, Entry.prefix, Source.Body.core, Graph.coreCodeSyntax,
        Graph.coreAdmin, Graph.Op.emitList, Graph.Op.emit, Graph.coreEmit, expression, List.cons_append,
        List.nil_append, List.map_cons, List.map_nil, List.drop_succ_cons, List.drop_zero, List.append_assoc,
        coreValues, vals] using!
        (Loops.core_restart_iff (s := s) (P := P) (f := (entry.frame locals).toCore) (saved := (entry.owner.initial.map Value.toCore)) (scratch := [])
        (cont := [entry.coreLoop]) (pending := expression ((entry.iteration Graph.coreCodeSyntax Source.Op.coreInstr).drop 4))
        (rest := entry.tail.map Graph.coreEmit) (dst := target))
  | @readChoice locals value read =>
    apply single (.readChoice read)
    · intro _ move
      cases move with
      | readChoice next => cases Option.some.inj (read.symm.trans next); rfl
    · exact get_exact (P := P) (entry := entry) (s := s) (outer := outer) (stack := [])
        read (expression ((entry.iteration Graph.coreCodeSyntax Source.Op.coreInstr).drop 5)) dst
  | @testChoice locals value =>
    apply single .testChoice (by intro _ move; cases move; rfl)
    have move (target : Config H) := Computed.core_if_iff (P := P) (s := s) (f := (entry.frame locals).toCore)
      (saved := []) (condition := value) (bt := Blocks.coreType entry.result)
      (thenBody := entry.siteBody.core) (elseBody := []) (rest := []) (dst := target)
    by_cases zero : value = (0#32)
    · have choice : decide (value ≠ 0) = false := by
        exact decide_eq_false (fun nonzero => nonzero zero)
      rw [choice]
      apply loop_step_exact
      · intro out exit
        exact Computed.core_label_stays (head := .plain (.if_ (Blocks.coreType entry.result)
          entry.siteBody.core [])) rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) exit
      · intro target
        have selected := move target
        rw [ite_eq_left (show value = (0 : BitVec 32) from zero)] at selected
        simpa only [Entry.iterationCode, Entry.iteration, Entry.prefix, Source.Body.core, Graph.coreCodeSyntax,
          Graph.coreAdmin, Graph.Op.emitList, Graph.Op.emit, Graph.coreEmit, expression, List.cons_append,
          List.nil_append, List.map_cons, List.map_nil, List.drop_succ_cons, List.drop_zero, List.append_assoc,
          coreValues, vals] using! selected
    · have choice : decide (value ≠ 0) = true := decide_eq_true zero
      rw [choice]
      apply loop_step_exact
      · intro out exit
        exact Computed.core_label_stays (head := .plain (.if_ (Blocks.coreType entry.result)
          entry.siteBody.core [])) rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) exit
      · intro target
        have selected := move target
        rw [ite_eq_right (show ¬ value = (0 : BitVec 32) from zero)] at selected
        simpa only [Entry.iterationCode, Entry.iteration, Entry.prefix, Source.Body.core, Graph.coreCodeSyntax,
          Graph.coreAdmin, Graph.Op.emitList, Graph.Op.emit, Graph.coreEmit, expression, List.cons_append,
          List.nil_append, List.map_cons, List.map_nil, List.drop_succ_cons, List.drop_zero, List.append_assoc,
          coreValues, vals] using! selected
  | @enterSite locals =>
    apply single .enterSite (by intro _ move; cases move; rfl)
    apply loop_step_exact
    · intro out exit
      change LabelExit 0 [entry.coreLoop] [.plain (.block (Blocks.coreType entry.result) entry.siteBody.core)] out at exit
      exact Computed.core_label_stays (stack := []) (rest := []) (head := .plain (.block (Blocks.coreType entry.result) entry.siteBody.core)) rfl
        (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) exit
    · intro target
      exact Blocks.core_context_entry_iff (P := P) (s := s) (f := (entry.frame locals).toCore)
        (saved := []) (result := entry.result) (body := entry.siteBody.core) (rest := []) (dst := target)
  | @enterEmpty locals =>
    apply single .enterEmpty (by intro _ move; cases move; rfl)
    apply loop_step_exact
    · intro out exit
      change LabelExit 0 [entry.coreLoop] [.plain (.block (Blocks.coreType entry.result) ([] : List _))] out at exit
      exact Computed.core_label_stays (stack := []) (rest := []) (head := .plain (.block (Blocks.coreType entry.result) [])) rfl
        (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) exit
    · intro target
      exact Blocks.core_context_entry_iff (P := P) (s := s) (f := (entry.frame locals).toCore)
        (saved := []) (result := entry.result) (body := []) (rest := []) (dst := target)
  | @leaveEmpty locals =>
    apply single .leaveEmpty (by intro _ move; cases move; rfl)
    apply loop_step_exact
    · intro out exit
      exact Computed.core_label_stays (head := .label entry.result.toList.length [] []) (stack := []) rfl
        (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) exit
    · intro target
      exact Blocks.Context.core_result_iff (P := P) (s := s) (f := (entry.frame locals).toCore) (dst := target) (scope := ⟨entry.result.toList.length, [], []⟩) (r := .values [])
  | @leaveLoop locals =>
    apply single .leaveLoop (by intro _ move; cases move; rfl)
    change Step P noHost (entry.coreLoopWrap outer ⟨s, (entry.frame locals).toCore, []⟩) dst ↔
      dst = entry.cont.coreWrap outer ⟨s, (entry.frame locals).toCore,
        coreValues entry.owner.initial ++ entry.tail.map Graph.coreEmit⟩
    apply wrap_iff
    · intro out exit
      exact Computed.core_label_stays (head := .label 0 [entry.coreLoop] []) rfl
        (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) exit
    · intro target
      simpa only [CallContinuation.Nested.resultCode, Blocks.Context.coreValues, List.nil_append, List.append_nil,
        List.map_nil, coreValues, vals] using!
        (Loops.core_result_iff (P := P) (s := s) (f := (entry.frame locals).toCore) (rest := entry.tail.map Graph.coreEmit) (dst := target) (r := .values []) (cont := [entry.coreLoop]) (saved := (entry.owner.initial.map Value.toCore)))

theorem site_operands (locals : List Value) :
    entry.coreConfig s outer ⟨locals, .site⟩ = entry.coreOperands s outer locals ([], entry.before) := by
  have tail := Graph.core_body_expression { entry.owner with initial := [], code := entry.insideTail }
  change expression (Graph.Op.emitList Graph.coreCodeSyntax entry.insideTail) =
    entry.insideTail.map Graph.coreEmit at tail
  have numeric : expression (entry.before.map (fun p => Graph.Op.emit Graph.coreCodeSyntax (.numeric p))) =
      entry.before.map (Prefix.emit coreSyntax) := by
    induction entry.before with
    | nil => rfl
    | cons op rest ih => cases op <;> exact congrArg (fun code => _ :: code) ih
  change entry.coreArmWrap outer ⟨s, (entry.frame locals).toCore, expression entry.siteBody.core⟩ =
    entry.coreArmWrap outer ⟨s, (entry.frame locals).toCore, entry.coreSiteCode entry.before⟩
  suffices code : expression entry.siteBody.core = entry.coreSiteCode entry.before by rw [code]
  have split (a b : List _) : expression (a ++ b) = expression a ++ expression b := List.map_append
  change expression ((entry.before.map (fun p => Graph.Op.emit Graph.coreCodeSyntax (.numeric p))) ++
    entry.op.coreInstr :: Graph.Op.emitList Graph.coreCodeSyntax entry.insideTail) = _
  rw [split, numeric]
  change entry.before.map (Prefix.emit coreSyntax) ++ .plain entry.op.coreInstr ::
    expression (Graph.Op.emitList Graph.coreCodeSyntax entry.insideTail) = entry.coreSiteCode entry.before
  rw [tail]
  rfl

private theorem operand_iff {locals stack : List Value} {op : Prefix.Op} {rest : List Prefix.Op}
    {ans : Prefix.Outcome} (move : Prefix.Reduce locals stack op ans) (dst : Config H) :
    Step P noHost (entry.coreOperands s outer locals (stack, op :: rest)) dst ↔
      dst = match ans with
        | .values next => entry.coreOperands s outer locals (next, rest)
        | .trap saved => entry.coreOperandResult s outer locals (.trap saved rest) := by
  let tail := entry.coreSiteCode rest
  let inside : Config H := ⟨s, (entry.frame locals).toCore, coreValues stack ++ Prefix.emit coreSyntax op :: tail⟩
  have armStays (out : List Admin) : ¬ LabelExit entry.result.toList.length [] inside.code out :=
    Computed.core_label_stays (by cases op <;> rfl)
      (by cases op <;> simp [Prefix.emit, coreSyntax])
      (by cases op <;> simp [Prefix.emit, coreSyntax])
      (by cases op <;> simp [Prefix.emit, coreSyntax, Admin.IsReturnCallRef])
      (by cases op <;> simp [Prefix.emit, coreSyntax])
      (by cases op <;> simp [Prefix.emit, coreSyntax])
  have loopStays (out : List Admin) : ¬ LabelExit 0 [entry.coreLoop] [.label entry.result.toList.length [] inside.code] out :=
    Computed.core_label_stays (stack := []) (rest := []) (head := .label _ [] _)
      rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp)
  change Step P noHost (entry.coreArmWrap outer inside) dst ↔ _
  rw [Entry.coreArmWrap, loop_wrap_iff loopStays]
  have arm (mid : Config H) := Blocks.Context.core_label_iff (P := P) (s := s) (f := (entry.frame locals).toCore)
    (n := entry.result.toList.length) (saved := []) (rest := []) (body := inside.code) (dst := mid)
  have exactOp (target : Config H) := Prefix.core_step_iff (P := P) (s := s) (f := entry.frame locals) (stack := stack) (op := op) (tail := tail) (dst := target)
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
    (states.map (entry.coreOperands s outer locals) ++ [entry.coreOperandResult s outer locals result]).IsChain
      (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) := by
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
    Steps P noHost (entry.coreConfig s outer ⟨locals, .site⟩) dst ↔
      dst ∈ states.map (entry.coreOperands s outer locals) ∨
        Steps P noHost (entry.coreOperandResult s outer locals result) dst := by
  have chain := operand_chain (entry := entry) (s := s) (outer := outer) (P := P) trace
  have head {stack code path result}
      (walk : OperandTrace locals stack code path result) :
      (path.map (entry.coreOperands s outer locals)).headD (entry.coreOperandResult s outer locals result) =
        entry.coreOperands s outer locals (stack, code) := by
    cases walk <;> rfl
  rw [site_operands, ← head trace]
  exact Context.Resume.prefix_run_iff _ _ chain

theorem lookup_start {locals stack : List Value} {active : Source.Activation}
    (prepared : entry.op.prepare program tables (entry.frame locals) stack = some active) :
    entry.coreOperandResult s outer locals (.values stack) = entry.coreLookup s outer active .start := by
  have facts := Source.prepare_spec prepared
  rw [facts.stack_eq]
  simp only [Entry.coreOperandResult, Entry.coreOperands, Entry.coreSiteCode, Entry.coreLookup,
    Source.Activation.coreConfig, Indirect.coreConfig, Site.coreCode, Entry.coreArmWrap, Source.coreNest,
    Context.coreNest, Context.coreNestWith, List.foldr_cons, List.foldr_nil, Entry.armScope,
    List.map_nil, coreValues, Core.vals, List.map_append, List.append_assoc]
  rw [facts.caller_eq, facts.typeIndex_eq]
  rfl

theorem lookup_exact {active : Source.Activation} {out : Outcome}
    (ready : active.Checked program tables) (targets : active.binding.site.CoreAllocated program s)
    (allocated : Source.Tables.CoreAllocated tables s) (resolved : active.resolve program = some out) :
    (out.coreTrace.map (entry.coreLookup s outer active)).IsChain
      (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) := by
  have chain := Source.core_resolution_allocated (P := P) ready targets allocated resolved
    [entry.armScope] entry.insideTail
  refine List.isChain_map_of_isChain _ (fun a b move dst => ?_) chain
  apply loop_step_exact
  · intro out exit
    exact Computed.core_label_stays (stack := []) (rest := []) (head := .label _ [] _)
      rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) exit
  · exact move

private theorem invoke_iff (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.address.value]? = some entry.coreInstance) (dst : Config H) :
    Step P noHost ((⟨entry.cont, entry.op, entry.before⟩ : GraphEntry.Entry).coreInvoke s outer args) dst ↔
      dst = entry.coreConfig s outer (entry.initial args) := by
  have enter := Sequence.wasm_entry_iff (P := P) (caller := outer) (dst := dst) allocated ready.typed
  have frame := Sequence.core_frame_forCall entry.owner.declaration.module args entry.owner.declaration.locals
  change Core.Frame.forCall entry.owner.declaration.module.toCore (args.map Value.toCore) entry.coreFunc.locals =
    (entry.owner.declaration.frame args).toCore at frame
  rw [frame] at enter
  change _ ↔ dst = entry.cont.coreWrap outer ⟨s, (entry.owner.declaration.frame args).toCore, expression entry.coreFunc.body⟩ at enter
  rw [Entry.coreFunc, expression_prefix entry.owner, expression_loop] at enter
  exact enter

theorem entry_chain (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.address.value]? = some entry.coreInstance) :
    let start := coreSource s outer index args
    let invoke := (⟨entry.cont, entry.op, entry.before⟩ : GraphEntry.Entry).coreInvoke s outer args
    ([start, invoke] ++ [entry.coreConfig s outer (entry.initial args)]).IsChain
        (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) := by
  intro start invoke
  exact List.isChain_cons_cons.mpr ⟨fun _ => Computed.core_direct_call_iff (s := s) (P := P) (stack := args)
      (tail := []) ready.resolves allocated, List.isChain_pair.mpr (invoke_iff ready allocated)⟩

theorem run_iff (ready : entry.Checked program tables outer index args)
    (allocated : s.funcs[entry.address.value]? = some entry.coreInstance)
    (links : program.CoreLinksAllocated s) {dst : Config H} :
    let start := coreSource s outer index args
    let invoke := (⟨entry.cont, entry.op, entry.before⟩ : GraphEntry.Entry).coreInvoke s outer args
    Steps P noHost start dst ↔ dst ∈ [start, invoke] ∨
      Observation entry args (entry.coreConfig s outer)
        (fun locals out => ∃ phase, program.FrameRuns entry.address (entry.callerPhase locals) phase ∧
          Graph.Admitted program entry.owner phase ∧ out = Graph.coreConfig s outer entry.cont.target phase)
        (Step P noHost) dst := by
  let start := coreSource s outer index args
  let invoke := (⟨entry.cont, entry.op, entry.before⟩ : GraphEntry.Entry).coreInvoke s outer args
  have chain := entry_chain (P := P) ready allocated
  have native := Context.Resume.prefix_run_iff (dst := dst) [start, invoke] _ chain
  refine native.trans (or_congr Iff.rfl (observe (entry.coreConfig s outer) (Step P noHost) _
    (initial_typed ready) (preserve ready) (step_iff ready) ?_ dst))
  intro locals target typed
  exact Context.linked_runs (graph_checked ready) ready.found
    (Graph.coreConfig s outer entry.cont.target) (Step P noHost)
    (fun h entered => Graph.core_entered_frame_step_iff (graph_checked ready) links ready.found rfl h entered)
    (caller_admitted ready typed) trivial

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Proofs.Core
