module

public import Silmaril.Wasm.Binaryen.GrowOOMLiteralRun

@[expose] public section

namespace Silmaril.Wasm.Binaryen.GrowOOMLiteral

open Execution.Core Execution.Core.Sim Numerics Validation MemoryGrowFailure
open Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.SingleThreaded.Exec
open GrowWrapper (Forced)
open GrowOOM (forced_trans forced_label forced_frame)

variable {H : Type} {P : Profile}

/-- The original allocated function layout, with the current shared memory
explicit rather than reset to its initial empty contents at each call. -/
def callStore (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (guarded : Bool) (mi : MemInst) : Store H :=
  { s with mems := s.mems ++ [mi], funcs := s.funcs ++
    [⟨GrowWrapper.dt a, GrowWrapper.moduleInst s a,
      .wasm (if guarded then func a n else GrowWrapper.func a n false)⟩] }

def callFunc (a : AddrType) (n : BitVec a.intType.width) (guarded : Bool) : Func :=
  if guarded then func a n else GrowWrapper.func a n false

def callFrame (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (guarded : Bool) : Frame :=
  Frame.forCall (GrowWrapper.moduleInst s a) [] (callFunc a n guarded).locals

def callRest (a : AddrType) (guarded : Bool) : List Admin :=
  if guarded then guardRest a else []

/-- A chosen actual growth edge. Failure may be profile-permitted or physically
forced by the memory bound; success carries the exact enlarged memory. -/
inductive Choice (P : Profile) (a : AddrType) (n : BitVec a.intType.width)
    (address : Nat) (mi : MemInst) where
  | success (mi' : MemInst) (grown : mi.grow? n.toNat = some mi')
      (allowed : P.growMaySucceed .memory address mi.pages n.toNat)
  | failure (allowed : P.growMayFail .memory address mi.pages n.toNat ∨ mi.grow? n.toNat = none)

namespace Choice

def memory {a : AddrType} {n : BitVec a.intType.width} {address : Nat} {mi : MemInst} :
    Choice P a n address mi → MemInst
  | .success mi' _ _ => mi'
  | .failure _ => mi

def result {a : AddrType} {n : BitVec a.intType.width} {address : Nat} {mi : MemInst} :
    Choice P a n address mi → BitVec a.intType.width
  | .success _ _ _ => BitVec.ofNat _ mi.pages
  | .failure _ => BitVec.allOnes _

end Choice

def callResult {a : AddrType} {n : BitVec a.intType.width} {address : Nat} {mi : MemInst}
    (guarded : Bool) (choice : Choice P a n address mi) : Result :=
  if guarded then guardResult a choice.result else .values [addrVal a choice.result]

def decision (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (guarded : Bool) (mi : MemInst) : Config H :=
  ⟨callStore s a n guarded mi, {}, [.frame 1 (callFrame s a n guarded)
    [.label 1 [] ([aconst a n, .plain (.memoryGrow ⟨0⟩)] ++ callRest a guarded)]]⟩

def afterGrowth (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (guarded : Bool) {mi : MemInst} (choice : Choice P a n s.mems.length mi) : Config H :=
  ⟨callStore s a n guarded choice.memory, {}, [.frame 1 (callFrame s a n guarded)
    [.label 1 [] (aconst a choice.result :: callRest a guarded)]]⟩

def final (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (guarded : Bool) {mi : MemInst} (choice : Choice P a n s.mems.length mi) : Config H :=
  ⟨callStore s a n guarded choice.memory, {}, (callResult guarded choice).toAdmin⟩

theorem call_mem (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (guarded : Bool) (mi : MemInst) :
    (callStore s a n guarded mi).mem? (callFrame s a n guarded) ⟨0⟩ =
      some (s.mems.length, mi) := by
  simp [callStore, callFrame, Frame.forCall, GrowWrapper.moduleInst, Store.mem?, Idx.toNat]

theorem call_setMem (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (guarded : Bool) (mi mi' : MemInst) :
    (callStore s a n guarded mi).setMem s.mems.length mi' = callStore s a n guarded mi' := by
  simp [callStore, Store.setMem]

theorem call_func (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (guarded : Bool) (mi : MemInst) :
    (callStore s a n guarded mi).funcs[s.funcs.length]? =
      some ⟨GrowWrapper.dt a, GrowWrapper.moduleInst s a, .wasm (callFunc a n guarded)⟩ := by
  simp [callStore, callFunc]

/-- The actual call entry, including the new local's initialized frame. -/
theorem call_prefix (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (guarded : Bool) (mi : MemInst) :
    Forced (P := P) (invoke (callStore s a n guarded mi) s.funcs.length [])
      (decision s a n guarded mi) := by
  have first := Step.callRefFunc (P := P) (host := closedHost)
    (s := callStore s a n guarded mi) (f := {}) (c := .callRefType (GrowWrapper.dt a))
    (vs := []) trivial (call_func s a n guarded mi)
    (Expand.iff.mpr (GrowWrapper.expand_dt a)) rfl rfl
  refine .step ?_ ?_ (.done _)
  · cases guarded <;>
      simpa [invoke, call_func, decision, callFrame, callFunc, callRest,
        GrowWrapper.func, func, guardRest, expression, vals, Ty.length] using first
  · intro c hc
    have unique := GrowWrapper.invoke_first_unique (call_func s a n guarded mi)
      (Expand.iff.mpr (GrowWrapper.expand_dt a)) rfl hc
    cases guarded <;>
      simpa [decision, callFrame, callFunc, callRest, guardRest,
        GrowWrapper.func, func, expression, Frame.forCall] using unique

/-- The chosen new memory is retained through both return and trap exits. -/
theorem call_finish (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (guarded : Bool) {mi : MemInst} (choice : Choice P a n s.mems.length mi) :
    Forced (P := P) (afterGrowth s a n guarded choice) (final s a n guarded choice) := by
  cases guarded with
  | false =>
    simpa [afterGrowth, final, callResult, callRest, Result.toAdmin, vals, addrVal, Val.toAdmin, aconst] using
      GrowOOM.finish_values_forced (P := P) (callStore s a n false choice.memory) {}
        (callFrame s a n false) (addrVal a choice.result)
  | true =>
    have hl : 0 < (callFrame s a n true).locals.length := by
      cases a <;> simp [callFrame, callFunc, func, Frame.forCall, defaultVal?]
    have body := guard_forced (P := P) (callStore s a n true choice.memory)
      (callFrame s a n true) a choice.result hl
    have nested := forced_frame (forced_label body 1 []) 1 {}
    apply forced_trans (by simpa [afterGrowth, callRest] using nested)
    by_cases failure : choice.result = BitVec.allOnes _
    · simpa [final, callResult, guardResult, failure, Result.toAdmin] using
        GrowOOM.finish_trap_forced (P := P) (callStore s a n true choice.memory) {}
          ((callFrame s a n true).setLocal ⟨0⟩ (addrVal a choice.result))
    · simpa [final, callResult, guardResult, failure, Result.toAdmin, vals, addrVal, Val.toAdmin, aconst] using
        GrowOOM.finish_values_forced (P := P) (callStore s a n true choice.memory) {}
          ((callFrame s a n true).setLocal ⟨0⟩ (addrVal a choice.result)) (addrVal a choice.result)

theorem call_step (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (guarded : Bool) {mi : MemInst} (choice : Choice P a n s.mems.length mi) :
    Step P closedHost (decision s a n guarded mi) (afterGrowth s a n guarded choice) := by
  apply Step.ctxtFrame
  apply Step.ctxtLabel
  cases choice with
  | success mi' hg hp =>
    have h := Step.append_right (Step.memory (P := P) (host := closedHost)
      (MemoryStep.growSucceed (n := n) (call_mem s a n guarded mi) hg hp)) (callRest a guarded)
    rw [call_setMem] at h
    exact h
  | failure hp =>
    exact source_fail (P := P) (host := closedHost) (n := n)
      (call_mem s a n guarded mi) hp [] (callRest a guarded)

/-- Typed address values identify both address width and literal bits. -/
theorem addrVal_inj {a b : AddrType} {n : BitVec a.intType.width} {m : BitVec b.intType.width}
    (h : addrVal a n = addrVal b m) : ∃ _e : a = b, HEq n m := by
  cases a <;> cases b <;> cases h <;> exact ⟨rfl, HEq.rfl⟩

/-- Invert a complete grow edge, exposing the same exact enlarged memory. -/
theorem grow_step_inv {s : Store H} {f : Frame} {a : AddrType}
    {n : BitVec a.intType.width} {ma : Nat} {mi : MemInst} {rest : List Admin} {c : Config H}
    (hm : s.mem? f ⟨0⟩ = some (ma, mi))
    (h : Step P closedHost ⟨s, f, [aconst a n, .plain (.memoryGrow ⟨0⟩)] ++ rest⟩ c) :
    ∃ choice : Choice P a n ma mi,
      c = ⟨(match choice with | .success mi' _ _ => s.setMem ma mi' | .failure _ => s),
        f, aconst a choice.result :: rest⟩ := by
  have h' : Step P closedHost
      ⟨s, f, vals [addrVal a n] ++ .plain (.memoryGrow ⟨0⟩) :: rest⟩ c := h
  obtain ⟨pre, args, cfg, hw, hh, hc⟩ := GuardSim.head_inv rfl (by simp) (by simp) h'
  obtain ⟨b, m, addr, mem, rfl, hm', choices⟩ := GrowOOM.head_grow hh
  obtain ⟨rfl, hv⟩ := (append_singleton_inj (l₁ := [])).mp hw
  obtain ⟨rfl, hn⟩ := addrVal_inj hv
  obtain rfl := eq_of_heq hn
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hm.symm.trans hm'))
  rcases choices with ⟨mi', hg, hp, rfl⟩ | ⟨hp, rfl⟩
  · exact ⟨.success mi' hg hp, by simpa [Choice.result] using hc⟩
  · exact ⟨.failure hp, by simpa [Choice.result] using hc⟩

theorem call_step_inv (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (guarded : Bool) (mi : MemInst) {c : Config H}
    (h : Step P closedHost (decision s a n guarded mi) c) :
    ∃ choice : Choice P a n s.mems.length mi, c = afterGrowth s a n guarded choice := by
  unfold decision at h
  obtain ⟨t, gi, code, hlabel, hc⟩ := GrowWrapper.frame_single_inv h rfl (by simp) (by simp)
  have hn : ([aconst a n, .plain (.memoryGrow ⟨0⟩)] ++ callRest a guarded).all Admin.isVal = false := by
    cases a <;> simp [Admin.isVal, Admin.val?, aconst]
  have he : ¬ ExitShape ([aconst a n, .plain (.memoryGrow ⟨0⟩)] ++ callRest a guarded) :=
    GrowOOM.not_exit_shape (vs := [addrVal a n]) rfl (by simp) (by simp)
      (by simp [Admin.IsReturnCallRef]) (by simp) (by simp)
  obtain ⟨t', gi', body, hbody, hl⟩ := GrowOOM.label_context_inv hn he hlabel
  obtain ⟨choice, hb⟩ := grow_step_inv (call_mem s a n guarded mi) hbody
  cases choice with
  | success mi' hg hp =>
    simp only [Choice.result] at hb
    rw [call_setMem] at hb
    simp only [Config.mk.injEq] at hb hl
    obtain ⟨rfl, rfl, rfl⟩ := hb
    obtain ⟨rfl, rfl, rfl⟩ := hl
    exact ⟨.success mi' hg hp, by simpa [afterGrowth, Choice.memory, Choice.result] using hc⟩
  | failure hp =>
    simp only [Choice.result] at hb
    simp only [Config.mk.injEq] at hb hl
    obtain ⟨rfl, rfl, rfl⟩ := hb
    obtain ⟨rfl, rfl, rfl⟩ := hl
    exact ⟨.failure hp, by simpa [afterGrowth, Choice.memory, Choice.result] using hc⟩

theorem final_terminal (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (guarded : Bool) {mi : MemInst} (choice : Choice P a n s.mems.length mi) :
    (final s a n guarded choice).Terminal := ⟨callResult guarded choice, rfl⟩

theorem decision_not_terminal (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (guarded : Bool) (mi : MemInst) : ¬ (decision s a n guarded mi).Terminal := by
  rintro ⟨r, hr⟩
  cases r with
  | values vs => exact (LoopCex.single_ne_vals rfl hr).elim
  | trap => cases hr
  | throw address => cases hr

theorem call_run_inv (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (guarded : Bool) (mi : MemInst) {c : Config H} {r : Result}
    (run : Steps P closedHost (invoke (callStore s a n guarded mi) s.funcs.length []) c)
    (hr : c.code = r.toAdmin) :
    ∃ choice : Choice P a n s.mems.length mi,
      c = final s a n guarded choice ∧ r = callResult guarded choice := by
  have terminal : c.Terminal := ⟨r, hr⟩
  have tail := GrowOOM.forced_terminal_tail (call_prefix s a n guarded mi) run terminal
  rcases tail.cases_head with he | ⟨d, hs, rest⟩
  · exact (decision_not_terminal s a n guarded mi (he ▸ terminal)).elim
  · obtain ⟨choice, rfl⟩ := call_step_inv s a n guarded mi hs
    have hc := (call_finish (P := P) s a n guarded choice).terminal_eq
      (fun _ hs => BehaviourRefinement.not_step_of_terminal (final_terminal s a n guarded choice) hs) rest terminal
    refine ⟨choice, hc, ?_⟩
    rw [hc] at hr
    exact Option.some.inj ((BehaviourRefinement.outcome?_eq_some_of_code hr).symm.trans
      (BehaviourRefinement.outcome?_eq_some_of_code (r := callResult guarded choice) rfl))

theorem call_not_diverges (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (guarded : Bool) (mi : MemInst) :
    ¬ Diverges P closedHost (invoke (callStore s a n guarded mi) s.funcs.length []) := by
  intro diverges
  have hd := GrowOOM.forced_diverges_tail (call_prefix s a n guarded mi) diverges
  obtain ⟨d, hs, tail⟩ := InfiniteTrace.unfold hd
  obtain ⟨choice, rfl⟩ := call_step_inv s a n guarded mi hs
  exact (call_finish (P := P) s a n guarded choice).not_diverges
    (fun _ hs => BehaviourRefinement.not_step_of_terminal (final_terminal s a n guarded choice) hs) tail

theorem call_run (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (guarded : Bool) {mi : MemInst} (choice : Choice P a n s.mems.length mi) :
    Steps P closedHost (invoke (callStore s a n guarded mi) s.funcs.length [])
      (final s a n guarded choice) :=
  (call_prefix s a n guarded mi).steps.trans
    ((call_step s a n guarded choice).steps.trans (call_finish s a n guarded choice).steps)

end Silmaril.Wasm.Binaryen.GrowOOMLiteral
