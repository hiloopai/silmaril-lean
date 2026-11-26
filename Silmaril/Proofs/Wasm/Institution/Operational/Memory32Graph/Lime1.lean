module

public import Silmaril.Wasm.Institution.Operational.Memory32Graph.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Thms
import Silmaril.Wasm.Institution.Operational.Memory32Context.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.Memory32Graph.Typing

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Memory32Graph.Proofs.Lime1

open Execution
open Execution.Runtime (Frame Value MemAddr MemInst)
open Wasm.Lime1.Execution
open CallContinuation
open CallContinuation.OuterCall
open Computed

abbrev Native {H : Type} := Wasm.Lime1.Execution.Step (H := H) CallFrame.limeNoHost
private abbrev emit : Op → Admin := .source ∘ Op.lime

private theorem emit_numeric (op : Prefix.Op) :
    emit (.numeric op) = Prefix.emit Computed.limeSyntax op := by
  cases op <;> rfl

private theorem expression_code (fn : Function) :
    expression fn.limeFunc.body = values fn.initial ++ fn.code.map emit := by
  change expression (fn.initial.map Ranked.Graph.limeCodeSyntax.ops.value ++ _) = _
  rw [expression_append, expression, List.map_map]
  congr 1
  apply List.map_congr_left
  intro v _
  rcases v with ⟨t, bits⟩
  cases t <;> rfl
  exact (List.map_map ..)

private theorem allocated_memory {H : Type} {p : Program} {s : Store H} {a : MemAddr} {m : MemInst}
    (layout : LimeLayout p s a m) {addr : Runtime.FuncAddr} {f : Function}
    (found : p.lookup addr = some f) (bytes : ByteArray) (locals : List Value) :
    frameMemory (limeStore s a m bytes) ⟨locals, f.decl.module⟩ = some (a, { m with data := bytes }) := by
  have index := layout.slot _ _ found
  have bound : a.value < s.memories.length := (List.getElem?_eq_some_iff.mp layout.mem).choose
  simp [frameMemory, limeStore, setMemory, index, List.getElem?_set, bound]

private theorem allocated_func {H : Type} {p : Program} {s : Store H} {a : MemAddr} {m : MemInst}
    (layout : LimeLayout p s a m) (bytes : ByteArray) {addr : Runtime.FuncAddr} {f : Function}
    (found : p.lookup addr = some f) :
    (limeStore s a m bytes).funcs[addr.value]? = some (.wasm f.decl.type f.decl.module f.limeFunc) :=
  layout.funcs _ _ found

private theorem memory_update {H : Type} (s : Store H) (a : MemAddr) (m : MemInst)
    (bytes : ByteArray) (out : Memory32Context.Outcome) :
    out.limeStore (limeStore s a m bytes) a { m with data := bytes } =
      limeStore s a m (nextBytes bytes out) := by
  cases out <;> simp [Memory32Context.Outcome.limeStore, limeStore, nextBytes, setMemory, List.set_set]

private theorem entry_iff {H : Type} {s : Store H} {caller : Frame}
    {fn : Function} {target : CallTarget} {saved args : List Value} {rest : List Admin} {dst : Config H}
    (declared : fn.decl = target.declaration)
    (alloc : s.funcs[target.address.value]? = some (.wasm fn.decl.type fn.decl.module fn.limeFunc))
    (typed : args.map Value.type = fn.decl.params) :
    Native ⟨s, caller, values (saved ++ args) ++ limeSyntax.admin.invoke target ++ rest⟩ dst ↔
      dst = ⟨s, caller, values saved ++
        (Phase.running (fn.decl.frame args).locals fn.initial fn.code).render limeSyntax target ++ rest⟩ := by
  have count : args.length = fn.decl.type.params.length := by simpa [Declaration.type] using congrArg List.length typed
  have entry (out : Config H) :=
    CallFrame.lime_invoke_wasm_prefix_iff (caller := caller) (saved := saved) (dst := out) alloc count
  have entered : [.frame fn.decl.type.results.length
      ⟨args ++ fn.limeFunc.locals.map Value.zero, fn.decl.module⟩
      [.label fn.decl.type.results.length [] (expression fn.limeFunc.body)]] =
      (Phase.running (fn.decl.frame args).locals fn.initial fn.code).render limeSyntax target := by
    rw [expression_code, Phase.render, renderLabel, renderFrame, ← declared]
    rfl
  constructor
  · intro move
    have move' : Native ⟨s, caller, values (saved ++ args) ++ .invoke target.address :: rest⟩ dst := by simpa only [limeSyntax, Ranked.Graph.limeAdmin, List.append_assoc, List.singleton_append] using move
    obtain ⟨mid, step, eq⟩ := CallContinuation.lime_invoke_strip_suffix move'
    obtain rfl := (entry mid).mp step
    simpa only [← entered, List.append_assoc] using eq
  · rintro rfl
    have step := (entry _).mpr rfl
    rw [← entered]
    simpa only [values, List.map_nil, List.nil_append, List.append_assoc, List.singleton_append,
      limeSyntax, Ranked.Graph.limeAdmin] using Wasm.Lime1.Execution.Step.context step [] rest

private theorem stays {types : List Wasm.Lime1.FuncType} {arity : Nat} {vs : List Value}
    {op : Op} {rest out : List Admin} (pop : PureStep types [.label arity [] (values vs ++ emit op :: rest)] out) :
    False := by
  have safe {head : Admin} (none : asValue? head = none) (notBr : ∀ i, head ≠ .source (.br i))
      (notRet : head ≠ .source .return_) (notTrap : head ≠ .trap)
      (h : PureStep types [.label arity [] (values vs ++ head :: rest)] out) : False :=
    Computed.lime_label_stays none notBr notRet (fun e => (notTrap e).elim) h
  cases op
  case numeric op => cases op <;> exact safe rfl (fun _ h => by cases h) (fun h => by cases h) (fun h => by cases h) pop
  all_goals exact safe rfl (fun _ h => by cases h) (fun h => by cases h) (fun h => by cases h) pop

private theorem label_iff {H : Type} {s : Store H} {caller inner : Frame} {n : Nat}
    {body : List Admin} {dst : Config H} (noPop : ∀ {out}, PureStep inner.module.types [.label n [] body] out → False) :
    Native ⟨s, caller, [.frame n inner [.label n [] body]]⟩ dst ↔
      ∃ next, Native ⟨s, inner, body⟩ next ∧
        dst = ⟨next.store, caller, [.frame n next.frame [.label n [] next.code]]⟩ := by
  constructor
  · intro step
    rcases Computed.lime_body_step_cases step with mid | ⟨_, pop, _⟩
    · exact mid
    · exact (noPop pop).elim
  · rintro ⟨⟨_, _, _⟩, step, rfl⟩
    exact .frame (.label step n []) n caller

private theorem result_iff {H : Type} {s : Store H} {caller inner : Frame} {n : Nat}
    {r : Nested.Result} {dst : Config H} :
    Native ⟨s, caller, [.frame n inner [.label n [] (Nested.resultCode values .trap r)]]⟩ dst ↔
      dst = ⟨s, caller, [.frame n inner (Nested.resultCode values .trap r)]⟩ := by
  constructor
  · intro step
    rcases Computed.lime_body_step_cases step with ⟨_, move, _⟩ | ⟨_, pop, rfl⟩
    · exact (Nested.lime_result_stuck move).elim
    · rw [Nested.lime_label_result pop]
  · rintro rfl
    cases r with
    | trap => exact .frame (.pure _ _ (.labelTrap _ _)) n caller
    | values vs =>
      exact .frame (.pure _ _ (.labelDone _ [] vs)) n caller

private theorem attach_code (locals saved : List Value) (target : CallTarget) (rest : List Op)
    (child : Phase) (root : CallTarget) (_shape : child.Frame ∨ ∃ r, child = .done r) :
    (afterChild locals saved target rest child).render limeSyntax root =
      renderLabel limeSyntax root locals (values saved ++ child.render limeSyntax target ++ rest.map emit) := by
  cases child <;> try rfl
  case done r => cases r <;> simp [afterChild, Phase.render, Nested.resultCode, limeSyntax, Ranked.Graph.limeAdmin,
    values_append, List.append_assoc]

private theorem active_form {child : Phase} (live : child.Frame) (target : CallTarget) :
    ∃ n frame code, child.render limeSyntax target = [.frame n frame code] := by
  cases child <;> first | contradiction | exact ⟨_, _, _, rfl⟩

theorem readback {H : Type} {p : Program} {s : Store H} {a : MemAddr} {m : MemInst}
    (layout : LimeLayout p s a m) {root : CallTarget} {caller : Runtime.Frame} {f : Function}
    (foundRoot : p.lookup root.address = some f) (sameRoot : f.decl = root.declaration)
    {phase : Phase}
    (resolveRoot : ∀ args, phase = .call args → root.Resolves caller) (ready : Ready p f phase) (bytes : ByteArray)
    {dst : Config H} (step : Native (limeConfig s a m caller root ⟨bytes, phase⟩) dst) :
    ∃ next, Memory32Graph.Step p f ⟨bytes, phase⟩ next ∧ dst = limeConfig s a m caller root next := by
  induction ready generalizing caller root dst with
  | call typed =>
    have read := (Computed.lime_direct_call_iff (resolveRoot _ rfl)).mp step
    refine ⟨_, .resolve, ?_⟩
    simpa [limeConfig, Phase.render, limeSyntax, Ranked.Graph.limeAdmin, ← sameRoot] using read
  | @invoke f args typed =>
    have read := (entry_iff (caller := caller) (saved := []) (rest := []) sameRoot
      (allocated_func layout bytes foundRoot) typed).mp (by simpa [limeConfig, Phase.render, limeSyntax, Ranked.Graph.limeAdmin] using step)
    exact ⟨_, .enter, by simpa [limeConfig, values] using read⟩
  | @running f locals stack rest typed code =>
    cases code with
    | done shape =>
      have read := (result_iff (r := .values stack)).mp (by simpa only [limeConfig, Phase.render, renderLabel, renderFrame,
        List.map_nil, List.append_nil, limeSyntax, Ranked.Graph.limeAdmin,
        Ranked.Graph.LabelKind.arity, Ranked.Graph.LabelKind.cont, Nested.resultCode] using step)
      exact ⟨_, .complete, read⟩
    | @numeric _ next op rest opCheck tail =>
      obtain ⟨mid, move, rfl⟩ := (label_iff (noPop := fun h => stays (op := .numeric op) h)).mp step
      obtain ⟨out, reduction, rfl⟩ := (Prefix.lime_step_iff (s := limeStore s a m bytes)
        (op := op) (f := ⟨locals, root.declaration.module⟩) (stack := stack) (tail := rest.map limeSyntax.emit)
        (dst := mid)).mp (by simpa only [emit_numeric] using move)
      exact ⟨_, .numeric reduction, by cases out <;> simp [limeConfig, afterNumeric, Phase.render,
        Prefix.outcomeCode, renderLabel, renderFrame, limeSyntax, Ranked.Graph.limeAdmin,
        Ranked.Graph.LabelKind.arity, Ranked.Graph.LabelKind.cont]⟩
    | @load _ keep rest types tail =>
      obtain ⟨saved, address, rfl, _⟩ := split_load types
      obtain ⟨mid, move, rfl⟩ := (label_iff (noPop := fun h => stays (op := .load) h)).mp step
      have memory := allocated_memory layout foundRoot bytes locals
      rw [sameRoot] at memory
      obtain ⟨out, edge, rfl⟩ := (Memory32Context.lime_iff (q := .load address) memory).mp move
      refine ⟨_, .load edge, ?_⟩
      rw [memory_update]
      cases out <;> simp [limeConfig, afterAccess, Phase.render, renderLabel, renderFrame,
        limeSyntax, Ranked.Graph.limeAdmin, Ranked.Graph.LabelKind.arity, Ranked.Graph.LabelKind.cont, Memory32Context.Outcome.code, values, List.append_assoc]
    | @store _ keep rest types tail =>
      obtain ⟨saved, address, word, rfl, _⟩ := split_store types
      obtain ⟨mid, move, rfl⟩ := (label_iff (noPop := fun h => stays (op := .store) h)).mp step
      have memory := allocated_memory layout foundRoot bytes locals
      rw [sameRoot] at memory
      obtain ⟨out, edge, rfl⟩ := (Memory32Context.lime_iff (q := .store address word) memory).mp move
      refine ⟨_, .store edge, ?_⟩
      rw [memory_update]
      cases out <;> simp [limeConfig, afterAccess, Phase.render, renderLabel, renderFrame,
        limeSyntax, Ranked.Graph.limeAdmin, Ranked.Graph.LabelKind.arity, Ranked.Graph.LabelKind.cont, Memory32Context.Outcome.code, values, List.append_assoc]
    | @call _ keep rest target callee types resolves found declared tail =>
      obtain ⟨saved, args, rfl, _, inputs⟩ := List.map_eq_append_iff.mp types
      obtain ⟨mid, move, rfl⟩ := (label_iff (noPop := fun h => stays (op := .call target) h)).mp step
      have resolve : (⟨locals, root.declaration.module⟩ : Runtime.Frame).module.funcs[target.index.toNat]? =
          some target.address := by simpa only [← sameRoot] using resolves
      have eq := (Computed.lime_direct_call_iff resolve).mp move
      refine ⟨_, .call inputs, ?_⟩

      simp [eq, limeConfig, Phase.render, renderLabel, renderFrame, limeSyntax, Ranked.Graph.limeAdmin,
        Ranked.Graph.LabelKind.arity, Ranked.Graph.LabelKind.cont, List.append_assoc]
    | unreachable =>
      obtain ⟨mid, move, rfl⟩ := (label_iff (noPop := fun h => stays (op := .unreachable) h)).mp step
      have eq := Computed.lime_unreachable_iff.mp move
      exact ⟨_, .unreachable, by rw [eq]; rfl⟩
  | @pending f locals saved target args rest callee typed found declared inputs resume =>
    have staysInvoke {out : List Admin} (pop : PureStep root.declaration.module.types
        [.label root.declaration.results.length [] (values (saved ++ args) ++
          .invoke target.address :: rest.map emit)] out) : False :=
      Computed.lime_label_stays rfl (by simp) (by simp) (by simp) pop
    obtain ⟨mid, move, rfl⟩ := (label_iff (fun {out} h => staysInvoke (out := out) (by
      simpa only [limeSyntax, Ranked.Graph.limeAdmin, List.append_assoc, List.singleton_append] using h))).mp step
    have eq := (entry_iff (caller := ⟨locals, root.declaration.module⟩) (saved := saved) (rest := rest.map emit) declared (allocated_func layout bytes found) (declared.symm ▸ inputs)).mp move
    exact ⟨_, .pending found, by rw [eq]; rfl⟩
  | @active f locals saved target child rest callee typed found declared live inside resume ih =>
    obtain ⟨n, inner, body, rendered⟩ := active_form live target
    change Native ⟨_, caller, [.frame _ _ [.label _ []
      (values saved ++ child.render limeSyntax target ++ rest.map emit)]]⟩ dst at step
    rw [rendered, List.append_assoc, List.singleton_append] at step
    obtain ⟨mid, move, rfl⟩ := Ranked.Graph.lime_entered_child_iff.mp step
    have childStep : Native (limeConfig s a m ⟨locals, root.declaration.module⟩ target ⟨bytes, child⟩) mid := by
      simpa only [limeConfig, rendered] using move
    obtain ⟨next, edge, rfl⟩ := ih found declared (fun args eq => by change child = .call args at eq; rw [eq] at live; exact live.elim) childStep
    refine ⟨_, .active found edge, ?_⟩
    simp only [limeConfig]
    rw [attach_code locals saved target rest next.phase root (frame_or_done edge live)]
    rfl
  | @trapped f locals saved rest =>
    rcases Computed.lime_body_step_cases step with ⟨mid, move, rfl⟩ | ⟨out, pop, rfl⟩
    · obtain ⟨kept, tail, discard, rfl⟩ := (Prefix.lime_discard_iff emit).mp move
      exact ⟨_, .discard discard, rfl⟩
    · have empty : saved = [] ∧ rest = [] := by
        by_contra notEmpty
        exact Computed.lime_label_stays (head := .trap) rfl (by simp) (by simp)
          (fun _ => by simpa using not_and_or.mp notEmpty) pop
      obtain ⟨rfl, rfl⟩ := empty
      exact ⟨_, .trapExit, by rw [Nested.lime_label_result (r := .trap) pop]; rfl⟩
  | exit typed =>
    exact ⟨_, .exit, Nested.lime_frame_result step⟩
  | done typed =>
    exact (Nested.lime_result_stuck step).elim

private theorem wrap {H : Type} {s t : Store H} {caller parent : Frame} {n : Nat}
    {before after : List Admin} (move : Native ⟨s, parent, before⟩ ⟨t, parent, after⟩) :
    Native ⟨s, caller, [.frame n parent [.label n [] before]]⟩
      ⟨t, caller, [.frame n parent [.label n [] after]]⟩ :=
  .frame (.label move n []) n caller

theorem sound {H : Type} {p : Program} {s : Store H} {a : MemAddr} {m : MemInst}
    (layout : LimeLayout p s a m) {root : CallTarget} {caller : Runtime.Frame} {f : Function}
    (foundRoot : p.lookup root.address = some f) (sameRoot : f.decl = root.declaration)
    {src dst : State} (resolveRoot : ∀ args, src.phase = .call args → root.Resolves caller)
    (ready : Ready p f src.phase) (step : Memory32Graph.Step p f src dst) :
    Native (limeConfig s a m caller root src) (limeConfig s a m caller root dst) := by
  induction step generalizing caller root with
  | resolve =>
    apply (Computed.lime_direct_call_iff (resolveRoot _ rfl)).mpr
    simp [limeConfig, Phase.render, limeSyntax, Ranked.Graph.limeAdmin]
  | @enter f bytes args =>
    cases ready with
    | @invoke f args typed =>
      have move := (entry_iff (caller := caller) (saved := []) (rest := []) sameRoot
        (allocated_func layout bytes foundRoot) typed).mpr rfl
      simpa [limeConfig, Phase.render, limeSyntax, Ranked.Graph.limeAdmin, values] using move
  | @numeric f bytes locals stack op rest out reduction =>
    have move := (Prefix.lime_step_iff (s := limeStore s a m bytes) (f := ⟨locals, root.declaration.module⟩)
      (tail := rest.map emit)).mpr ⟨out, reduction, rfl⟩
    rw [← emit_numeric] at move
    cases out <;> exact wrap move
  | @load f bytes locals saved address rest out edge =>
    have memory := allocated_memory layout foundRoot bytes locals
    rw [sameRoot] at memory
    have move := (Memory32Context.lime_iff (q := .load address)
      (saved := saved) (rest := rest.map emit) memory).mpr ⟨out, edge, rfl⟩
    rw [memory_update] at move
    have lifted := wrap (caller := caller) (n := root.declaration.results.length) move
    cases out <;> simpa [limeConfig, afterAccess, Phase.render, renderLabel, renderFrame, limeSyntax,
      Ranked.Graph.limeAdmin, Ranked.Graph.LabelKind.arity, Ranked.Graph.LabelKind.cont, Memory32Context.Outcome.code, Memory32Context.Access.args, Memory32Context.Access.limeOp,
      emit, Op.lime, values, List.append_assoc] using lifted
  | @store f bytes locals saved address word rest out edge =>
    have memory := allocated_memory layout foundRoot bytes locals
    rw [sameRoot] at memory
    have move := (Memory32Context.lime_iff (q := .store address word)
      (saved := saved) (rest := rest.map emit) memory).mpr ⟨out, edge, rfl⟩
    rw [memory_update] at move
    have lifted := wrap (caller := caller) (n := root.declaration.results.length) move
    cases out <;> simpa [limeConfig, afterAccess, Phase.render, renderLabel, renderFrame, limeSyntax,
      Ranked.Graph.limeAdmin, Ranked.Graph.LabelKind.arity, Ranked.Graph.LabelKind.cont, Memory32Context.Outcome.code, Memory32Context.Access.args, Memory32Context.Access.limeOp,
      emit, Op.lime, values, List.append_assoc] using lifted
  | @call f bytes locals saved args target rest inputs =>
    cases ready with
    | running typed code =>
      cases code with
      | call _ resolves found declared tail =>
        have resolve : (⟨locals, root.declaration.module⟩ : Runtime.Frame).module.funcs[target.index.toNat]? =
            some target.address := by simpa only [← sameRoot] using resolves
        have move := (Computed.lime_direct_call_iff (s := limeStore s a m bytes) (stack := saved ++ args)
          (tail := rest.map emit) resolve).mpr rfl
        simpa [limeConfig, Phase.render, renderLabel, renderFrame, limeSyntax, Ranked.Graph.limeAdmin,
          Ranked.Graph.LabelKind.arity, Ranked.Graph.LabelKind.cont, Op.lime, List.append_assoc] using wrap move
  | @pending f bytes locals saved target args rest callee found =>
    cases ready with
    | pending typed matched declared inputs resume =>
      rw [found] at matched
      cases matched
      exact wrap ((entry_iff (caller := ⟨locals, root.declaration.module⟩) (saved := saved) (rest := rest.map emit) declared (allocated_func layout bytes found) (declared.symm ▸ inputs)).mpr rfl)
  | @active f bytes locals saved target child rest callee next found move ih =>
    cases ready with
    | active typed matched declared live inside resume =>
      rw [found] at matched
      cases matched
      obtain ⟨n, inner, body, rendered⟩ := active_form live target
      have childMove := ih (caller := ⟨locals, root.declaration.module⟩)
        found declared (fun args eq => by change child = .call args at eq; rw [eq] at live; exact live.elim) inside
      change Native ⟨_, caller, [.frame _ _ [.label _ []
        (values saved ++ child.render limeSyntax target ++ rest.map emit)]]⟩ _
      rw [rendered, List.append_assoc, List.singleton_append]
      apply Ranked.Graph.lime_entered_child_iff.mpr
      refine ⟨_, by simpa only [limeConfig, rendered] using childMove, ?_⟩
      simp only [limeConfig]
      rw [attach_code locals saved target rest next.phase root (frame_or_done move live)]
      rfl
  | unreachable =>
    exact wrap (Computed.lime_unreachable_iff.mpr rfl)
  | discard discard =>
    exact wrap ((Prefix.lime_discard_iff emit).mpr ⟨_, _, discard, rfl⟩)
  | @complete f bytes locals stack =>
    cases ready with
    | running typed code =>
      cases code with
      | done types =>
        have out := (result_iff (r := .values stack) (n := root.declaration.results.length)
          (s := limeStore s a m bytes) (caller := caller)
          (inner := ⟨locals, root.declaration.module⟩)).mpr rfl
        simpa [limeConfig, Phase.render, renderLabel, renderFrame, limeSyntax, Ranked.Graph.limeAdmin,
          Ranked.Graph.LabelKind.arity, Ranked.Graph.LabelKind.cont, Nested.resultCode] using out
  | trapExit => exact .frame (.pure _ _ (.labelTrap _ _)) _ caller
  | @exit f bytes locals result =>
    cases ready with
    | exit typed =>
      cases result with
      | trap => exact .pure _ _ (.frameTrap _ _)
      | values vs =>
        change vs.map Value.type = f.decl.results at typed
        apply Wasm.Lime1.Execution.Step.pure
        apply PureStep.frameDone
        simpa [sameRoot] using congrArg List.length typed

end Silmaril.Wasm.Institution.Operational.Memory32Graph.Proofs.Lime1
