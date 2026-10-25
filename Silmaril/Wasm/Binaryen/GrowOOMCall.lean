module

public import Silmaril.Wasm.Binaryen.GrowOOMRun

@[expose] public section

namespace Silmaril.Wasm.Binaryen.GrowOOM

open Execution.Core Execution.Core.Sim Numerics Validation MemoryGrowFailure
open Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.SingleThreaded.Exec
open GrowWrapper (Forced)

variable {H : Type} {P : Profile}

def callStore (s : Store H) (a : AddrType) (guarded : Bool) : Store H :=
  if guarded then store s a else GrowWrapper.store s a 0 false

def callFunc (a : AddrType) (guarded : Bool) : Func :=
  if guarded then func a else GrowWrapper.func a 0 false

def callRest (a : AddrType) (guarded : Bool) : List Admin :=
  if guarded then guardRest a else []

def callResult (a : AddrType) (guarded failure : Bool) : Result :=
  if guarded then guardResult a failure
  else .values [addrVal a (if failure then BitVec.allOnes _ else 0)]

def decision (s : Store H) (a : AddrType) (guarded : Bool) : Config H :=
  ⟨callStore s a guarded, {}, [.frame 1 {module := GrowWrapper.moduleInst s a}
    [.label 1 [] ([aconst a 0, .plain (.memoryGrow ⟨0⟩)] ++ callRest a guarded)]]⟩

def afterGrowth (s : Store H) (a : AddrType) (guarded failure : Bool) : Config H :=
  ⟨callStore s a guarded, {}, [.frame 1 {module := GrowWrapper.moduleInst s a}
    [.label 1 [] (aconst a (if failure then BitVec.allOnes _ else 0) :: callRest a guarded)]]⟩

def final (s : Store H) (a : AddrType) (guarded failure : Bool) : Config H :=
  ⟨callStore s a guarded, {}, (callResult a guarded failure).toAdmin⟩

def Permitted (P : Profile) (address : Nat) (failure : Bool) : Prop :=
  if failure then P.growMayFail .memory address 0 0
  else P.growMaySucceed .memory address 0 0

theorem call_mem (s : Store H) (a : AddrType) (guarded : Bool) :
    (callStore s a guarded).mem? {module := GrowWrapper.moduleInst s a} ⟨0⟩ =
      some (s.mems.length, emptyMemory a) := by
  cases guarded <;> simp [callStore, store, GrowWrapper.store, GrowWrapper.moduleInst,
    Store.mem?, Idx.toNat]

theorem call_setMem (s : Store H) (a : AddrType) (guarded : Bool) :
    (callStore s a guarded).setMem s.mems.length (emptyMemory a) = callStore s a guarded := by
  cases guarded <;> simp [callStore, store, GrowWrapper.store, Store.setMem]

theorem call_func (s : Store H) (a : AddrType) (guarded : Bool) :
    (callStore s a guarded).funcs[s.funcs.length]? =
      some ⟨GrowWrapper.dt a, GrowWrapper.moduleInst s a, .wasm (callFunc a guarded)⟩ := by
  cases guarded <;> simp [callStore, callFunc, func_lookup, GrowWrapper.func_lookup]

/-- Entry into either actual allocated wrapper is one forced Core call step. -/
theorem call_prefix (s : Store H) (a : AddrType) (guarded : Bool) :
    Forced (P := P) (invoke (callStore s a guarded) s.funcs.length [])
      (decision s a guarded) := by
  have first : Step P closedHost (invoke (callStore s a guarded) s.funcs.length [])
      (decision s a guarded) := by
    cases guarded
    · simpa [callStore, decision, callRest, GrowWrapper.func, expression] using
        GrowWrapper.invoke_first (P := P) s a 0 false
    · simpa [callStore, decision, callRest, guardRest, func, expression] using
        invoke_first (P := P) s a
  refine .step first ?_ (.done _)
  intro c hc
  have unique := GrowWrapper.invoke_first_unique (call_func s a guarded)
    (Expand.iff.mpr (GrowWrapper.expand_dt a)) rfl hc
  cases guarded <;>
    simpa [decision, callStore, callRest, callFunc, guardRest,
      GrowWrapper.func, func, expression, Frame.forCall] using unique

/-- Once growth has selected an outcome, the guard and administrative exits are
forced. The shared memory and all ambient store components are retained. -/
theorem call_finish (s : Store H) (a : AddrType) (guarded failure : Bool) :
    Forced (P := P) (afterGrowth s a guarded failure) (final s a guarded failure) := by
  cases guarded with
  | false =>
    simpa [afterGrowth, final, callResult, callRest, Result.toAdmin, vals, addrVal, Val.toAdmin, aconst] using
      finish_values_forced (P := P) (callStore s a false) {}
        {module := GrowWrapper.moduleInst s a}
        (addrVal a (if failure then BitVec.allOnes _ else 0))
  | true =>
    have body := guard_forced (P := P) (callStore s a true)
      {module := GrowWrapper.moduleInst s a} a failure
    have nested := forced_frame (forced_label body 1 []) 1 {}
    apply forced_trans (by simpa [afterGrowth, callRest] using nested)
    cases failure
    · simpa [final, callResult, guardResult, Result.toAdmin, vals, addrVal, Val.toAdmin, aconst] using
        finish_values_forced (P := P) (callStore s a true) {}
          {module := GrowWrapper.moduleInst s a} (addrVal a 0)
    · simpa [final, callResult, guardResult, Result.toAdmin] using
        finish_trap_forced (P := P) (callStore s a true) {}
          {module := GrowWrapper.moduleInst s a}

/-- Preserve the same growth choice at the actual nested Core step. -/
theorem call_step (s : Store H) (a : AddrType) (guarded failure : Bool)
    (allowed : Permitted P s.mems.length failure) :
    Step P closedHost (decision s a guarded) (afterGrowth s a guarded failure) := by
  have body : Step P closedHost
      ⟨callStore s a guarded, {module := GrowWrapper.moduleInst s a},
        [aconst a 0, .plain (.memoryGrow ⟨0⟩)] ++ callRest a guarded⟩
      ⟨callStore s a guarded, {module := GrowWrapper.moduleInst s a},
        aconst a (if failure then BitVec.allOnes _ else 0) :: callRest a guarded⟩ := by
    cases failure with
    | false =>
      have h := Step.append_right (Step.memory (P := P) (host := closedHost)
        (MemoryStep.growSucceed (n := (0 : BitVec a.intType.width)) (call_mem s a guarded)
          (by simpa using empty_grow_zero a) (by simpa [Permitted, emptyMemory, MemInst.pages] using allowed)))
        (callRest a guarded)
      rw [call_setMem] at h
      simpa [emptyMemory, MemInst.pages] using h
    | true =>
      simpa using source_fail (P := P) (host := closedHost) (n := (0 : BitVec a.intType.width))
        (call_mem s a guarded) (.inl (by simpa [Permitted, emptyMemory, MemInst.pages] using allowed))
        [] (callRest a guarded)
  exact .ctxtFrame (.ctxtLabel body)

/-- Every nested growth step is one of those same allowed choices. -/
theorem call_step_inv (s : Store H) (a : AddrType) (guarded : Bool) {c : Config H}
    (h : Step P closedHost (decision s a guarded) c) :
    ∃ failure, Permitted P s.mems.length failure ∧ c = afterGrowth s a guarded failure := by
  unfold decision at h
  obtain ⟨t, gi, code, hlabel, hc⟩ := GrowWrapper.frame_single_inv h rfl (by simp) (by simp)
  have hn : ([aconst a 0, .plain (.memoryGrow ⟨0⟩)] ++ callRest a guarded).all Admin.isVal = false := by
    cases a <;> simp [Admin.isVal, Admin.val?, aconst]
  have he : ¬ ExitShape ([aconst a 0, .plain (.memoryGrow ⟨0⟩)] ++ callRest a guarded) :=
    not_exit_shape (vs := [addrVal a 0]) rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef])
      (by simp) (by simp)
  obtain ⟨t', gi', body, hbody, hl⟩ := label_context_inv hn he hlabel
  rcases grow_zero_step_inv (call_mem s a guarded) (call_setMem s a guarded) hbody with
    ⟨allowed, hb⟩ | ⟨allowed, hb⟩
  · simp only [Config.mk.injEq] at hb hl
    obtain ⟨rfl, rfl, rfl⟩ := hb
    obtain ⟨rfl, rfl, rfl⟩ := hl
    exact ⟨false, allowed, by simpa [afterGrowth] using hc⟩
  · simp only [Config.mk.injEq] at hb hl
    obtain ⟨rfl, rfl, rfl⟩ := hb
    obtain ⟨rfl, rfl, rfl⟩ := hl
    exact ⟨true, allowed, by simpa [afterGrowth] using hc⟩

theorem final_terminal (s : Store H) (a : AddrType) (guarded failure : Bool) :
    (final s a guarded failure).Terminal := ⟨callResult a guarded failure, rfl⟩

theorem decision_not_terminal (s : Store H) (a : AddrType) (guarded : Bool) :
    ¬ (decision s a guarded).Terminal := by
  rintro ⟨r, hr⟩
  cases r with
  | values vs => exact (LoopCex.single_ne_vals rfl hr).elim
  | trap => cases hr
  | throw address => cases hr

/-- A completed invocation determines one allowed growth choice, the full final
store, and the exact return/trap. No deterministic profile is required. -/
theorem call_run_inv (s : Store H) (a : AddrType) (guarded : Bool)
    {c : Config H} {r : Result}
    (run : Steps P closedHost (invoke (callStore s a guarded) s.funcs.length []) c)
    (hr : c.code = r.toAdmin) :
    ∃ failure, Permitted P s.mems.length failure ∧
      c = final s a guarded failure ∧ r = callResult a guarded failure := by
  have terminal : c.Terminal := ⟨r, hr⟩
  have tail := forced_terminal_tail (call_prefix s a guarded) run terminal
  rcases tail.cases_head with he | ⟨d, hs, rest⟩
  · have ht : (decision s a guarded).Terminal := he ▸ terminal
    exact (decision_not_terminal s a guarded ht).elim
  · obtain ⟨failure, allowed, rfl⟩ := call_step_inv s a guarded hs
    have hc := (call_finish (P := P) s a guarded failure).terminal_eq
      (fun _ hs => BehaviourRefinement.not_step_of_terminal (final_terminal s a guarded failure) hs)
      rest terminal
    refine ⟨failure, allowed, hc, ?_⟩
    rw [hc] at hr
    exact Option.some.inj
      ((BehaviourRefinement.outcome?_eq_some_of_code hr).symm.trans
        (BehaviourRefinement.outcome?_eq_some_of_code (r := callResult a guarded failure) rfl))

/-- Neither wrapper can diverge: there is one growth step between finite forced
prefix/suffix paths. This still permits the profile's nondeterministic choices. -/
theorem call_not_diverges (s : Store H) (a : AddrType) (guarded : Bool) :
    ¬ Diverges P closedHost (invoke (callStore s a guarded) s.funcs.length []) := by
  intro diverges
  have hd := forced_diverges_tail (call_prefix s a guarded) diverges
  obtain ⟨d, hs, tail⟩ := InfiniteTrace.unfold hd
  obtain ⟨failure, _, rfl⟩ := call_step_inv s a guarded hs
  exact (call_finish (P := P) s a guarded failure).not_diverges
    (fun _ hs => BehaviourRefinement.not_step_of_terminal (final_terminal s a guarded failure) hs) tail

theorem call_run (s : Store H) (a : AddrType) (guarded failure : Bool)
    (allowed : Permitted P s.mems.length failure) :
    Steps P closedHost (invoke (callStore s a guarded) s.funcs.length [])
      (final s a guarded failure) :=
  (call_prefix s a guarded).steps.trans
    ((call_step s a guarded failure allowed).steps.trans (call_finish s a guarded failure).steps)

end Silmaril.Wasm.Binaryen.GrowOOM
