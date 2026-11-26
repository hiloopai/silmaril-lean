module

public import Silmaril.Wasm.Institution.Operational.Memory32Graph.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Thms
import Silmaril.Wasm.Institution.Operational.Memory32Context.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Wasm.Execution.Core.Sim.Context
import Silmaril.Proofs.Wasm.Institution.Operational.Memory32Graph.Typing

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Memory32Graph.Proofs.Core

open Execution Execution.Core
open Execution.Runtime (Value MemAddr)
open CallContinuation
open CallContinuation.OuterCall
open Computed
open Wasm.Numerics (Profile)
open Wasm.SingleThreaded.Det (noHost)

abbrev Native {H : Type} (P : Profile) := Execution.Core.Step (H := H) P noHost
private abbrev emit : Op → Admin := .plain ∘ Op.core

private theorem values_append (xs ys : List Value) :
    coreValues (xs ++ ys) = coreValues xs ++ coreValues ys := by
  simp only [coreValues, List.map_append, vals_append]

private theorem emit_numeric (op : Prefix.Op) :
    emit (.numeric op) = Prefix.emit Computed.coreSyntax op := by
  cases op <;> rfl

private theorem expression_code (fn : Function) :
    expression fn.coreFunc.body = coreValues fn.initial ++ fn.code.map emit := by
  change expression (fn.initial.map Ranked.Graph.coreCodeSyntax.ops.value ++ _) = _
  unfold expression
  rw [List.map_append, List.map_map]
  congr 1
  simp only [coreValues, vals, List.map_map]
  apply List.map_congr_left
  intro v _
  rcases v with ⟨t, bits⟩
  cases t <;> rfl
  exact List.map_map ..

private theorem allocated_memory {H : Type} {p : Program} {s : Store H} {a : MemAddr} {m : MemInst}
    (layout : CoreLayout p s a m) {addr : Runtime.FuncAddr} {f : Function}
    (found : p.lookup addr = some f) (bytes : ByteArray) (locals : List Value) :
    (coreStore s a m bytes).mem? (⟨locals, f.decl.module⟩ : Runtime.Frame).toCore MemoryQuery.index =
      some (a.value, { m with bytes := bytes }) := by
  have index := layout.slot _ _ found
  have bound : a.value < s.mems.length := List.getElem?_eq_some_iff.mp layout.mem |>.choose
  unfold Store.mem?
  change (do
    let address ← (f.decl.module.memories.map (fun a : MemAddr => a.value))[0]?
    return (address, ← (s.mems.set a.value { m with bytes := bytes })[address]?)
    ) = _
  simp [index, List.getElem?_set, bound]

private theorem allocated_func {H : Type} {p : Program} {s : Store H} {a : MemAddr} {m : MemInst}
    (layout : CoreLayout p s a m) (bytes : ByteArray) {addr : Runtime.FuncAddr} {f : Function}
    (found : p.lookup addr = some f) :
    (coreStore s a m bytes).funcs[addr.value]? = some f.coreInstance :=
  layout.funcs _ _ found

private theorem memory_update {H : Type} (s : Store H) (a : MemAddr) (m : MemInst)
    (bytes : ByteArray) (out : Memory32Context.Outcome) :
    out.coreStore (coreStore s a m bytes) a.value { m with bytes := bytes } =
      coreStore s a m (nextBytes bytes out) := by
  cases out <;> simp [Memory32Context.Outcome.coreStore, coreStore, nextBytes, Store.setMem, List.set_set]

private theorem entry_iff {H : Type} {P : Profile} {s : Store H} {caller : Runtime.Frame}
    {fn : Function} {target : CallTarget} {saved args : List Value} {rest : List Admin} {dst : Config H}
    (declared : fn.decl = target.declaration)
    (alloc : s.funcs[target.address.value]? = some fn.coreInstance)
    (typed : args.map Value.type = fn.decl.params) :
    Native P ⟨s, caller.toCore, coreValues (saved ++ args) ++ coreSyntax.admin.invoke target ++ rest⟩ dst ↔
      dst = ⟨s, caller.toCore, coreValues saved ++
        (Phase.running (fn.decl.frame args).locals fn.initial fn.code).render coreSyntax target ++ rest⟩ := by
  have enter := Sequence.wasm_entry_context_iff (P := P) (caller := caller) (saved := saved) (rest := rest) (dst := dst)
    alloc typed
  have init := Sequence.core_frame_forCall fn.decl.module args fn.decl.locals
  change Frame.forCall fn.decl.module.toCore (args.map Value.toCore) fn.coreFunc.locals =
    (fn.decl.frame args).toCore at init
  rw [init, expression_code] at enter
  rw [Phase.render, renderLabel, renderFrame, ← declared]
  simpa only [List.append_assoc, List.cons_append, List.nil_append, ← declared, coreSyntax, Ranked.Graph.coreAdmin,
    Ranked.Graph.LabelKind.arity, Ranked.Graph.LabelKind.cont, Declaration.frame, Declaration.type] using enter

private theorem stays {arity : Nat} {vs : List Value} {op : Op} {rest : List Admin}
    {out : List Admin} (pop : LabelExit arity [] (coreValues vs ++ emit op :: rest) out) : False := by
  have safe {head : Admin}
      (none : head.val? = none) (notBr : ∀ i, head ≠ .plain (.br i))
      (notRet : head ≠ .plain .return_) (notTail : ¬ head.IsReturnCallRef)
      (notThrow : head ≠ .plain .throwRef) (notTrap : head ≠ .trap)
      (h : LabelExit arity [] (coreValues vs ++ head :: rest) out) : False :=
    Computed.core_label_stays none notBr notRet notTail notThrow (fun e => (notTrap e).elim) h
  cases op
  case numeric op => cases op <;> exact safe rfl (fun _ h => by cases h) (fun h => by cases h) (by change False → False; exact id) (fun h => by cases h) (fun h => by cases h) pop
  all_goals exact safe rfl (fun _ h => by cases h) (fun h => by cases h) (by change False → False; exact id) (fun h => by cases h) (fun h => by cases h) pop

private theorem label_iff {H : Type} {P : Profile} {s : Store H} {caller inner : Frame} {n : Nat}
    {body : List Admin} {dst : Config H} (noPop : ∀ {out}, LabelExit n [] body out → False) :
    Native P ⟨s, caller, [.frame n inner [.label n [] body]]⟩ dst ↔
      ∃ next, Native P ⟨s, inner, body⟩ next ∧
        dst = ⟨next.store, caller, [.frame n next.frame [.label n [] next.code]]⟩ := by
  constructor
  · intro step
    rcases Computed.core_body_step_cases step with mid | ⟨_, pop, _⟩
    · exact mid
    · exact (noPop pop).elim
  · rintro ⟨⟨_, _, _⟩, step, rfl⟩
    exact .ctxtFrame (.ctxtLabel step)

private theorem result_iff {H : Type} {P : Profile} {s : Store H} {caller inner : Frame} {n : Nat}
    {r : Nested.Result} {dst : Config H} :
    Native P ⟨s, caller, [.frame n inner [.label n [] (Nested.resultCode coreValues .trap r)]]⟩ dst ↔
      dst = ⟨s, caller, [.frame n inner (Nested.resultCode coreValues .trap r)]⟩ := by
  constructor
  · intro step
    rcases Computed.core_body_step_cases step with ⟨_, move, _⟩ | ⟨_, pop, rfl⟩
    · exact (Nested.core_result_stuck move).elim
    · rw [Nested.core_label_result pop]
  · rintro rfl
    cases r with
    | trap => exact .ctxtFrame Step.trapLabel
    | values vs => exact .ctxtFrame Step.labelVals

private theorem attach_code (locals saved : List Value) (target : CallTarget) (rest : List Op)
    (child : Phase) (root : CallTarget) (_shape : child.Frame ∨ ∃ r, child = .done r) :
    (afterChild locals saved target rest child).render coreSyntax root =
      renderLabel coreSyntax root locals (coreValues saved ++ child.render coreSyntax target ++ rest.map emit) := by
  cases child <;> try rfl
  case done r => cases r <;> simp [afterChild, Phase.render, Nested.resultCode, coreSyntax, Ranked.Graph.coreAdmin,
    values_append, List.append_assoc]

private theorem active_form {child : Phase} (live : child.Frame) (target : CallTarget) :
    ∃ n frame code, child.render coreSyntax target = [.frame n frame code] := by
  cases child <;> first | contradiction | exact ⟨_, _, _, rfl⟩

theorem readback {H : Type} {P : Profile} {p : Program} {s : Store H} {a : MemAddr} {m : MemInst}
    (layout : CoreLayout p s a m) {root : CallTarget} {caller : Runtime.Frame} {f : Function}
    (foundRoot : p.lookup root.address = some f) (sameRoot : f.decl = root.declaration)
    {phase : Phase}
    (resolveRoot : ∀ args, phase = .call args → root.Resolves caller) (ready : Ready p f phase) (bytes : ByteArray)
    {dst : Config H} (step : Native P (coreConfig s a m caller root ⟨bytes, phase⟩) dst) :
    ∃ next, Memory32Graph.Step p f ⟨bytes, phase⟩ next ∧ dst = coreConfig s a m caller root next := by
  induction ready generalizing caller root dst with
  | call typed =>
    have read := (Computed.core_direct_call_iff (resolveRoot _ rfl) (allocated_func layout bytes foundRoot)).mp step
    refine ⟨_, .resolve, ?_⟩
    simpa [coreConfig, Phase.render, coreSyntax, Ranked.Graph.coreAdmin, Function.coreInstance, ← sameRoot] using read
  | @invoke f args typed =>
    have read := (entry_iff (caller := caller) (P := P) (saved := []) (rest := []) sameRoot
      (allocated_func layout bytes foundRoot) typed).mp (by simpa [coreConfig, Phase.render, coreSyntax, Ranked.Graph.coreAdmin] using step)
    exact ⟨_, .enter, by simpa [coreConfig, coreValues] using read⟩
  | @running f locals stack rest typed code =>
    cases code with
    | done shape =>
      have read := (result_iff (r := .values stack)).mp (by simpa only [coreConfig, Phase.render, renderLabel, renderFrame,
        List.map_nil, List.append_nil, coreSyntax, Ranked.Graph.coreAdmin,
        Ranked.Graph.LabelKind.arity, Ranked.Graph.LabelKind.cont, Nested.resultCode] using step)
      exact ⟨_, .complete, read⟩
    | @numeric _ next op rest opCheck tail =>
      obtain ⟨mid, move, rfl⟩ := (label_iff (noPop := fun h => stays (op := .numeric op) h)).mp step
      obtain ⟨out, reduction, rfl⟩ := (Prefix.core_step_iff (P := P) (s := coreStore s a m bytes)
        (op := op) (f := ⟨locals, root.declaration.module⟩) (stack := stack) (tail := rest.map coreSyntax.emit)
        (dst := mid)).mp (by simpa only [emit_numeric] using move)
      exact ⟨_, .numeric reduction, by cases out <;> simp [coreConfig, afterNumeric, Phase.render,
        Prefix.outcomeCode, renderLabel, renderFrame, coreSyntax, Ranked.Graph.coreAdmin,
        Ranked.Graph.LabelKind.arity, Ranked.Graph.LabelKind.cont]⟩
    | @load _ keep rest types tail =>
      obtain ⟨saved, address, rfl, _⟩ := split_load types
      obtain ⟨mid, move, rfl⟩ := (label_iff (noPop := fun h => stays (op := .load) h)).mp step
      have memory := allocated_memory layout foundRoot bytes locals
      rw [sameRoot] at memory
      obtain ⟨out, edge, rfl⟩ := (Memory32Context.core_iff (q := .load address)
        (saved := saved.map Value.toCore) memory layout.width).mp (by
          simpa only [coreValues, List.map_append, Memory32Context.Access.args, Memory32Context.Access.coreOp, emit, Op.core, Function.comp_def] using move)
      refine ⟨_, .load edge, ?_⟩
      rw [memory_update]
      cases out <;> simp [coreConfig, afterAccess, Phase.render, renderLabel, renderFrame,
        coreSyntax, Ranked.Graph.coreAdmin, Ranked.Graph.LabelKind.arity, Ranked.Graph.LabelKind.cont, Memory32Context.Outcome.code, coreValues,
        vals_append, List.append_assoc]
    | @store _ keep rest types tail =>
      obtain ⟨saved, address, word, rfl, _⟩ := split_store types
      obtain ⟨mid, move, rfl⟩ := (label_iff (noPop := fun h => stays (op := .store) h)).mp step
      have memory := allocated_memory layout foundRoot bytes locals
      rw [sameRoot] at memory
      obtain ⟨out, edge, rfl⟩ := (Memory32Context.core_iff (q := .store address word)
        (saved := saved.map Value.toCore) memory layout.width).mp (by
          simpa only [coreValues, List.map_append, Memory32Context.Access.args, Memory32Context.Access.coreOp, emit, Op.core, Function.comp_def] using move)
      refine ⟨_, .store edge, ?_⟩
      rw [memory_update]
      cases out <;> simp [coreConfig, afterAccess, Phase.render, renderLabel, renderFrame,
        coreSyntax, Ranked.Graph.coreAdmin, Ranked.Graph.LabelKind.arity, Ranked.Graph.LabelKind.cont, Memory32Context.Outcome.code, coreValues,
        vals_append, List.append_assoc]
    | @call _ keep rest target callee types resolves found declared tail =>
      obtain ⟨saved, args, rfl, _, inputs⟩ := List.map_eq_append_iff.mp types
      obtain ⟨mid, move, rfl⟩ := (label_iff (noPop := fun h => stays (op := .call target) h)).mp step
      have resolve : (⟨locals, root.declaration.module⟩ : Runtime.Frame).module.funcs[target.index.toNat]? =
          some target.address := by simpa only [← sameRoot] using resolves
      have eq := (Computed.core_direct_call_iff resolve (allocated_func layout bytes found)).mp move
      refine ⟨_, .call inputs, ?_⟩
      simp only [Function.coreInstance, declared] at eq

      simp [eq, coreConfig, Phase.render, renderLabel, renderFrame, coreSyntax, Ranked.Graph.coreAdmin,
        Ranked.Graph.LabelKind.arity, Ranked.Graph.LabelKind.cont, List.append_assoc]
    | unreachable =>
      obtain ⟨mid, move, rfl⟩ := (label_iff (noPop := fun h => stays (op := .unreachable) h)).mp step
      have eq := Computed.core_unreachable_iff.mp move
      exact ⟨_, .unreachable, by rw [eq]; rfl⟩
  | @pending f locals saved target args rest callee typed found declared inputs resume =>
    have staysInvoke {out : List Admin} (pop : LabelExit root.declaration.results.length []
        (coreValues (saved ++ args) ++ coreSyntax.admin.invoke target ++ rest.map emit) out) : False := by
      have prefixEq : vals ((saved ++ args).map Value.toCore ++ [.ref (.func target.address.value)]) ++
          .callRefType target.declaration.type.toDefType :: rest.map emit =
          coreValues (saved ++ args) ++ coreSyntax.admin.invoke target ++ rest.map emit := by
        simp [vals_append, coreValues, coreSyntax, Ranked.Graph.coreAdmin, List.append_assoc, Val.toAdmin]
      rw [← prefixEq] at pop
      exact Computed.core_label_stays rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef])
        (by simp) (by simp) pop
    obtain ⟨mid, move, rfl⟩ := (label_iff staysInvoke).mp step
    have eq := (entry_iff (caller := ⟨locals, root.declaration.module⟩) (saved := saved) (rest := rest.map emit) (P := P) declared (allocated_func layout bytes found) (declared.symm ▸ inputs)).mp move
    exact ⟨_, .pending found, by rw [eq]; rfl⟩
  | @active f locals saved target child rest callee typed found declared live inside resume ih =>
    obtain ⟨n, inner, body, rendered⟩ := active_form live target
    change Native P ⟨_, caller.toCore, [.frame _ _ [.label _ []
      (coreValues saved ++ child.render coreSyntax target ++ rest.map emit)]]⟩ dst at step
    rw [rendered, List.append_assoc, List.singleton_append] at step
    obtain ⟨mid, move, rfl⟩ := Ranked.Graph.core_entered_child_iff.mp step
    have childStep : Native P (coreConfig s a m ⟨locals, root.declaration.module⟩ target ⟨bytes, child⟩) mid := by
      simpa only [coreConfig, rendered] using move
    obtain ⟨next, edge, rfl⟩ := ih found declared (fun args eq => by change child = .call args at eq; rw [eq] at live; exact live.elim) childStep
    refine ⟨_, .active found edge, ?_⟩
    simp only [coreConfig]
    rw [attach_code locals saved target rest next.phase root (frame_or_done edge live)]
    rfl
  | @trapped f locals saved rest =>
    rcases Computed.core_body_step_cases step with ⟨mid, move, rfl⟩ | ⟨out, pop, rfl⟩
    · obtain ⟨kept, tail, discard, rfl⟩ := (Prefix.core_discard_iff emit).mp move
      exact ⟨_, .discard discard, rfl⟩
    · have empty : saved = [] ∧ rest = [] := by
        by_contra notEmpty
        exact Computed.core_label_stays (head := .trap) rfl (by simp) (by simp)
          (by simp [Admin.IsReturnCallRef]) (by simp)
          (fun _ => by simpa [coreValues] using not_and_or.mp notEmpty) pop
      obtain ⟨rfl, rfl⟩ := empty
      exact ⟨_, .trapExit, by rw [Nested.core_label_result (r := .trap) pop]; rfl⟩
  | exit typed =>
    exact ⟨_, .exit, Nested.core_frame_result step⟩
  | done typed =>
    exact (Nested.core_result_stuck step).elim

private theorem wrap {H : Type} {P : Profile} {s t : Store H} {caller parent : Frame} {n : Nat}
    {before after : List Admin} (move : Native P ⟨s, parent, before⟩ ⟨t, parent, after⟩) :
    Native P ⟨s, caller, [.frame n parent [.label n [] before]]⟩
      ⟨t, caller, [.frame n parent [.label n [] after]]⟩ :=
  .ctxtFrame (.ctxtLabel move)

theorem sound {H : Type} {P : Profile} {p : Program} {s : Store H} {a : MemAddr} {m : MemInst}
    (layout : CoreLayout p s a m) {root : CallTarget} {caller : Runtime.Frame} {f : Function}
    (foundRoot : p.lookup root.address = some f) (sameRoot : f.decl = root.declaration)
    {src dst : State} (resolveRoot : ∀ args, src.phase = .call args → root.Resolves caller)
    (ready : Ready p f src.phase) (step : Memory32Graph.Step p f src dst) :
    Native P (coreConfig s a m caller root src) (coreConfig s a m caller root dst) := by
  induction step generalizing caller root with
  | @resolve f bytes args =>
    apply (Computed.core_direct_call_iff (resolveRoot _ rfl) (allocated_func layout bytes foundRoot)).mpr
    simp [coreConfig, Phase.render, coreSyntax, Ranked.Graph.coreAdmin, Function.coreInstance, sameRoot]
  | @enter f bytes args =>
    cases ready with
    | @invoke f args typed =>
      have move := (entry_iff (caller := caller) (P := P) (saved := []) (rest := []) sameRoot
        (allocated_func layout bytes foundRoot) typed).mpr rfl
      simpa [coreConfig, Phase.render, coreSyntax, Ranked.Graph.coreAdmin, coreValues] using move
  | @numeric f bytes locals stack op rest out reduction =>
    have move := (Prefix.core_step_iff (P := P) (s := coreStore s a m bytes) (f := ⟨locals, root.declaration.module⟩)
      (tail := rest.map emit)).mpr ⟨out, reduction, rfl⟩
    rw [← emit_numeric] at move
    cases out <;> exact wrap move
  | @load f bytes locals saved address rest out edge =>
    have memory := allocated_memory layout foundRoot bytes locals
    rw [sameRoot] at memory
    have move := (Memory32Context.core_iff (q := .load address) (P := P)
      (saved := saved.map Value.toCore) (rest := rest.map emit) memory layout.width).mpr ⟨out, edge, rfl⟩
    rw [memory_update] at move
    have lifted := wrap (caller := caller.toCore) (n := root.declaration.results.length) move
    cases out <;> simpa [coreConfig, afterAccess, Phase.render, renderLabel, renderFrame, coreSyntax,
      Ranked.Graph.coreAdmin, Ranked.Graph.LabelKind.arity, Ranked.Graph.LabelKind.cont, Memory32Context.Outcome.code, Memory32Context.Access.args, Memory32Context.Access.coreOp,
      emit, Op.core, coreValues, vals_append, List.append_assoc] using lifted
  | @store f bytes locals saved address word rest out edge =>
    have memory := allocated_memory layout foundRoot bytes locals
    rw [sameRoot] at memory
    have move := (Memory32Context.core_iff (q := .store address word) (P := P)
      (saved := saved.map Value.toCore) (rest := rest.map emit) memory layout.width).mpr ⟨out, edge, rfl⟩
    rw [memory_update] at move
    have lifted := wrap (caller := caller.toCore) (n := root.declaration.results.length) move
    cases out <;> simpa [coreConfig, afterAccess, Phase.render, renderLabel, renderFrame, coreSyntax,
      Ranked.Graph.coreAdmin, Ranked.Graph.LabelKind.arity, Ranked.Graph.LabelKind.cont, Memory32Context.Outcome.code, Memory32Context.Access.args, Memory32Context.Access.coreOp,
      emit, Op.core, coreValues, vals_append, List.append_assoc] using lifted
  | @call f bytes locals saved args target rest inputs =>
    cases ready with
    | running typed code =>
      cases code with
      | call _ resolves found declared tail =>
        have resolve : (⟨locals, root.declaration.module⟩ : Runtime.Frame).module.funcs[target.index.toNat]? =
            some target.address := by simpa only [← sameRoot] using resolves
        have move := (Computed.core_direct_call_iff (P := P) (stack := saved ++ args)
          (tail := rest.map emit) resolve (allocated_func layout bytes found)).mpr rfl
        simp only [Function.coreInstance, declared] at move
        simpa [coreConfig, Phase.render, renderLabel, renderFrame, coreSyntax, Ranked.Graph.coreAdmin,
          Ranked.Graph.LabelKind.arity, Ranked.Graph.LabelKind.cont, Op.core, List.append_assoc] using wrap move
  | @pending f bytes locals saved target args rest callee found =>
    cases ready with
    | pending typed matched declared inputs resume =>
      rw [found] at matched
      cases matched
      exact wrap ((entry_iff (caller := ⟨locals, root.declaration.module⟩) (saved := saved) (rest := rest.map emit) (P := P) declared (allocated_func layout bytes found) (declared.symm ▸ inputs)).mpr rfl)
  | @active f bytes locals saved target child rest callee next found move ih =>
    cases ready with
    | active typed matched declared live inside resume =>
      rw [found] at matched
      cases matched
      obtain ⟨n, inner, body, rendered⟩ := active_form live target
      have childMove := ih (caller := ⟨locals, root.declaration.module⟩)
        found declared (fun args eq => by change child = .call args at eq; rw [eq] at live; exact live.elim) inside
      change Native P ⟨_, caller.toCore, [.frame _ _ [.label _ []
        (coreValues saved ++ child.render coreSyntax target ++ rest.map emit)]]⟩ _
      rw [rendered, List.append_assoc, List.singleton_append]
      apply Ranked.Graph.core_entered_child_iff.mpr
      refine ⟨_, by simpa only [coreConfig, rendered] using childMove, ?_⟩
      simp only [coreConfig]
      rw [attach_code locals saved target rest next.phase root (frame_or_done move live)]
      rfl
  | unreachable =>
    exact wrap (Computed.core_unreachable_iff.mpr rfl)
  | discard discard =>
    exact wrap ((Prefix.core_discard_iff emit).mpr ⟨_, _, discard, rfl⟩)
  | @complete f bytes locals stack =>
    cases ready with
    | running typed code =>
      cases code with
      | done types =>
        have out := (result_iff (P := P) (r := .values stack) (n := root.declaration.results.length)
          (s := coreStore s a m bytes) (caller := caller.toCore)
          (inner := (⟨locals, root.declaration.module⟩ : Runtime.Frame).toCore)).mpr rfl
        simpa [coreConfig, Phase.render, renderLabel, renderFrame, coreSyntax, Ranked.Graph.coreAdmin,
          Ranked.Graph.LabelKind.arity, Ranked.Graph.LabelKind.cont, Nested.resultCode] using out
  | trapExit => exact .ctxtFrame Execution.Core.Step.trapLabel
  | @exit f bytes locals result =>
    cases ready with
    | exit typed =>
      cases result with
      | trap => exact Execution.Core.Step.trapFrame
      | values vs =>
        change vs.map Value.type = f.decl.results at typed
        apply Execution.Core.Step.frameVals
        simpa [sameRoot] using congrArg List.length typed

end Silmaril.Wasm.Institution.Operational.Memory32Graph.Proofs.Core
