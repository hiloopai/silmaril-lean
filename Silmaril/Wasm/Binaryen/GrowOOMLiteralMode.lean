module

public import Silmaril.Wasm.Binaryen.GrowOOMLiteralCall

@[expose] public section

namespace Silmaril.Wasm.Binaryen.GrowOOMLiteral

open Execution.Core Numerics Validation MemoryGrowFailure Optimization
open Silmaril.Wasm.SingleThreaded.Det

variable {H : Type} {P : Profile}

theorem call_invokeOk_iff (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (guarded : Bool) (mi : MemInst) (args : List Val) :
    InvokeOk (callStore s a n guarded mi) s.funcs.length args ↔ args = [] := by
  constructor
  · rintro ⟨fi, ps, rs, hf, he, hv⟩
    rw [call_func] at hf
    cases hf
    obtain ⟨rfl, _⟩ := GrowWrapper.expand_dt_inv (a := a) he
    change List.Forall₂ _ args [] at hv
    cases hv
    rfl
  · rintro rfl
    exact ⟨_, .nil, _, call_func s a n guarded mi,
      Expand.iff.mpr (GrowWrapper.expand_dt a), .nil⟩

/-- Target and source share the same entire current memory, including every
successful preceding growth. They replay each actual permitted grow edge. -/
theorem session_source_of_guarded (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (mi : MemInst) (script : List Call) {target : List (Behaviour Val)}
    (ht : Session P closedHost (GrowWrapper.moduleInst s a)
      (callStore s a n true mi) script target) :
    ∃ source, Session P closedHost (GrowWrapper.moduleInst s a)
      (callStore s a n false mi) script source ∧ TrapPrefix target source := by
  induction script generalizing mi target with
  | nil => cases ht; exact ⟨[], .nil, .refl _⟩
  | cons call rest ih =>
    obtain ⟨x, args⟩ := call
    cases ht with
    | stop h =>
      refine ⟨[], .stop ?_, .refl _⟩
      intro address ha hok
      obtain ⟨_, rfl⟩ := (GrowWrapper.exportFunc_iff s a x address).mp ha
      exact h _ ha ((call_invokeOk_iff s a n true mi args).mpr
        ((call_invokeOk_iff s a n false mi args).mp hok))
    | @done _ _ _ _ address c result _ ha hok run hr tail =>
      obtain ⟨rfl, rfl⟩ := (GrowWrapper.exportFunc_iff s a x address).mp ha
      obtain rfl := (call_invokeOk_iff s a n true mi args).mp hok
      obtain ⟨choice, rfl, rfl⟩ := call_run_inv s a n true mi run hr
      obtain ⟨source, hs, rel⟩ := ih choice.memory (by simpa [final] using tail)
      refine ⟨(callResult false choice).toBehaviour :: source,
        .done ((GrowWrapper.exportFunc_iff s a "grow" s.funcs.length).mpr ⟨rfl, rfl⟩)
          ((call_invokeOk_iff s a n false mi []).mpr rfl)
          (call_run s a n false choice) rfl (by simpa [final] using hs), ?_⟩
      by_cases failure : choice.result = BitVec.allOnes _
      · simp only [callResult, guardResult, failure, ↓reduceIte, Result.toBehaviour]
        exact .trap _
      · simpa [callResult, guardResult, failure, Result.toBehaviour] using
          TrapPrefix.returns [addrVal a choice.result] rel
    | @diverge _ _ _ _ address ha hok hd =>
      obtain ⟨_, rfl⟩ := (GrowWrapper.exportFunc_iff s a x address).mp ha
      obtain rfl := (call_invokeOk_iff s a n true mi args).mp hok
      exact (call_not_diverges s a n true mi hd).elim

/-- Constructive feasibility, also after caught traps: reuse the source's exact
success memory or its actual permitted/physically forced failure. -/
theorem session_guarded_exists (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (mi : MemInst) (script : List Call) {source : List (Behaviour Val)}
    (hs : Session P closedHost (GrowWrapper.moduleInst s a)
      (callStore s a n false mi) script source) :
    ∃ target, Session P closedHost (GrowWrapper.moduleInst s a)
      (callStore s a n true mi) script target := by
  induction script generalizing mi source with
  | nil => cases hs; exact ⟨[], .nil⟩
  | cons call rest ih =>
    obtain ⟨x, args⟩ := call
    cases hs with
    | stop h =>
      refine ⟨[], .stop ?_⟩
      intro address ha hok
      obtain ⟨_, rfl⟩ := (GrowWrapper.exportFunc_iff s a x address).mp ha
      exact h _ ha ((call_invokeOk_iff s a n false mi args).mpr
        ((call_invokeOk_iff s a n true mi args).mp hok))
    | @done _ _ _ _ address c result _ ha hok run hr tail =>
      obtain ⟨rfl, rfl⟩ := (GrowWrapper.exportFunc_iff s a x address).mp ha
      obtain rfl := (call_invokeOk_iff s a n false mi args).mp hok
      obtain ⟨choice, rfl, rfl⟩ := call_run_inv s a n false mi run hr
      obtain ⟨target, ht⟩ := ih choice.memory (by simpa [final] using tail)
      exact ⟨(callResult true choice).toBehaviour :: target,
        .done ((GrowWrapper.exportFunc_iff s a "grow" s.funcs.length).mpr ⟨rfl, rfl⟩)
          ((call_invokeOk_iff s a n true mi []).mpr rfl)
          (call_run s a n true choice) rfl (by simpa [final] using ht)⟩
    | @diverge _ _ _ _ address ha hok hd =>
      obtain ⟨_, rfl⟩ := (GrowWrapper.exportFunc_iff s a x address).mp ha
      obtain rfl := (call_invokeOk_iff s a n false mi args).mp hok
      exact (call_not_diverges s a n false mi hd).elim

private theorem initial_run_eq (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    {c : Config H} (run : Steps P closedHost (initial s a n) c) : c = initial s a n := by
  rcases run.cases_head with he | ⟨_, hs, _⟩
  · exact he.symm
  · exact (not_step_vals (W := []) hs).elim

private theorem initial_not_diverges (s : Store H) (a : AddrType) (n : BitVec a.intType.width) :
    ¬ Diverges P closedHost (initial s a n) := by
  intro hd
  obtain ⟨_, hs, _⟩ := InfiniteTrace.unfold hd
  exact not_step_vals (W := []) hs

private theorem result_nil {r : Result} (h : ([] : List Admin) = r.toAdmin) :
    r = .values [] := by
  cases r with
  | values vs =>
    have hv : vals ([] : List Val) = vals vs := h
    exact congrArg Result.values (vals_inj.mp hv).symm
  | trap => cases h
  | throw address => cases h

theorem moduleObs_iff (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (imports : List ExternAddr) (script : List Call) (bs : List (Behaviour Val)) :
    bs ∈ moduleObs P closedHost s imports (mod a n) script ↔
      imports = [] ∧ ∃ tail, Session P closedHost (GrowWrapper.moduleInst s a)
        (callStore s a n true (emptyMemory a)) script tail ∧ bs = .returns [] :: tail := by
  constructor
  · rintro ⟨c, hi, ho⟩
    obtain ⟨rfl, rfl⟩ := instantiate_inv hi
    refine ⟨rfl, ?_⟩
    rcases ho with ⟨c', tail, run, _, hs, he⟩ | ⟨c', result, run, hr, hn, _⟩ | ⟨hd, _⟩
    · obtain rfl := initial_run_eq s a n run
      exact ⟨tail, by simpa [initial, store, callStore] using hs, he⟩
    · obtain rfl := initial_run_eq s a n run
      exact (hn (result_nil hr)).elim
    · exact (initial_not_diverges s a n hd).elim
  · rintro ⟨rfl, tail, hs, rfl⟩
    exact ⟨initial s a n, instantiate s a n,
      .inl ⟨initial s a n, tail, .refl, rfl,
        by simpa [initial, store, callStore] using hs, rfl⟩⟩

/-- Actual admission, initialization and arbitrary-length shared-memory sessions
for every same numerical profile and either width, with every literal delta. -/
theorem exportCorrect (a : AddrType) (n : BitVec a.intType.width) :
    Modes.ExportCorrect .trapInsertion P (closedHost (H := H))
      (GrowWrapper.mod a n false) (mod a n) := by
  constructor
  · intro s imports _ ⟨c, hi⟩
    obtain ⟨rfl, _⟩ := GrowWrapper.instantiate_inv hi
    exact ⟨initial s a n, instantiate s a n⟩
  · intro s imports script _
    constructor
    · intro target ht
      obtain ⟨rfl, tail, hs, rfl⟩ := (moduleObs_iff s a n imports script target).mp ht
      obtain ⟨source, hsource, rel⟩ := session_source_of_guarded s a n (emptyMemory a) script hs
      refine .inr ⟨.returns [] :: source,
        (GrowWrapper.moduleObs_iff s a n false [] script _).mpr
          ⟨rfl, source, ?_, rfl⟩, .returns [] rel⟩
      simpa [GrowWrapper.store, callStore] using hsource
    · rintro ⟨source, hs⟩
      obtain ⟨rfl, tail, hsession, rfl⟩ :=
        (GrowWrapper.moduleObs_iff s a n false imports script source).mp hs
      obtain ⟨target, ht⟩ := session_guarded_exists s a n (emptyMemory a) script
        (by simpa [GrowWrapper.store, callStore] using hsession)
      exact ⟨_, (moduleObs_iff s a n [] script _).mpr ⟨rfl, target, ht, rfl⟩⟩

end Silmaril.Wasm.Binaryen.GrowOOMLiteral
