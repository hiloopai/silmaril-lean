module

public import Silmaril.Wasm.Binaryen.GrowOOMCall

@[expose] public section

namespace Silmaril.Wasm.Binaryen.GrowOOM

open Execution.Core Numerics Validation MemoryGrowFailure Optimization
open Silmaril.Wasm.SingleThreaded.Det

variable {H : Type} {P : Profile}

theorem call_invokeOk_iff (s : Store H) (a : AddrType) (guarded : Bool) (args : List Val) :
    InvokeOk (callStore s a guarded) s.funcs.length args ↔ args = [] := by
  cases guarded
  · exact GrowWrapper.invokeOk_iff s a 0 false args
  · exact invokeOk_iff s a args

/-- Every target session has a source session with matching returned values up
to its first inserted trap. Both sessions continue in their actual shared stores. -/
theorem session_source_of_guarded (s : Store H) (a : AddrType) (script : List Call)
    {target : List (Behaviour Val)}
    (ht : Session P closedHost (GrowWrapper.moduleInst s a) (callStore s a true) script target) :
    ∃ source, Session P closedHost (GrowWrapper.moduleInst s a) (callStore s a false) script source ∧
      TrapPrefix target source := by
  induction script generalizing target with
  | nil => cases ht; exact ⟨[], .nil, .refl _⟩
  | cons call rest ih =>
    obtain ⟨x, args⟩ := call
    cases ht with
    | stop h =>
      refine ⟨[], .stop ?_, .refl _⟩
      intro address ha hok
      obtain ⟨_, rfl⟩ := (GrowWrapper.exportFunc_iff s a x address).mp ha
      exact h _ ha ((call_invokeOk_iff s a true args).mpr
        ((call_invokeOk_iff s a false args).mp hok))
    | @done _ _ _ _ address c result _ ha hok run hr tail =>
      obtain ⟨rfl, rfl⟩ := (GrowWrapper.exportFunc_iff s a x address).mp ha
      obtain rfl := (call_invokeOk_iff s a true args).mp hok
      obtain ⟨failure, allowed, rfl, rfl⟩ := call_run_inv s a true run hr
      obtain ⟨source, hs, rel⟩ := ih (by simpa [final] using tail)
      refine ⟨(callResult a false failure).toBehaviour :: source,
        .done ((GrowWrapper.exportFunc_iff s a "grow" s.funcs.length).mpr ⟨rfl, rfl⟩)
          ((call_invokeOk_iff s a false []).mpr rfl)
          (call_run s a false failure allowed) rfl (by simpa [final] using hs), ?_⟩
      cases failure
      · exact .returns _ rel
      · exact .trap _
    | @diverge _ _ _ _ address ha hok hd =>
      obtain ⟨_, rfl⟩ := (GrowWrapper.exportFunc_iff s a x address).mp ha
      obtain rfl := (call_invokeOk_iff s a true args).mp hok
      exact (call_not_diverges s a true hd).elim

/-- Feasibility is constructive: replay each source call with the same permitted
growth choice in the guarded module, including calls after a caught target trap. -/
theorem session_guarded_exists (s : Store H) (a : AddrType) (script : List Call)
    {source : List (Behaviour Val)}
    (hs : Session P closedHost (GrowWrapper.moduleInst s a) (callStore s a false) script source) :
    ∃ target, Session P closedHost (GrowWrapper.moduleInst s a) (callStore s a true) script target := by
  induction script generalizing source with
  | nil => cases hs; exact ⟨[], .nil⟩
  | cons call rest ih =>
    obtain ⟨x, args⟩ := call
    cases hs with
    | stop h =>
      refine ⟨[], .stop ?_⟩
      intro address ha hok
      obtain ⟨_, rfl⟩ := (GrowWrapper.exportFunc_iff s a x address).mp ha
      exact h _ ha ((call_invokeOk_iff s a false args).mpr
        ((call_invokeOk_iff s a true args).mp hok))
    | @done _ _ _ _ address c result _ ha hok run hr tail =>
      obtain ⟨rfl, rfl⟩ := (GrowWrapper.exportFunc_iff s a x address).mp ha
      obtain rfl := (call_invokeOk_iff s a false args).mp hok
      obtain ⟨failure, allowed, rfl, rfl⟩ := call_run_inv s a false run hr
      obtain ⟨target, ht⟩ := ih (by simpa [final] using tail)
      exact ⟨(callResult a true failure).toBehaviour :: target,
        .done ((GrowWrapper.exportFunc_iff s a "grow" s.funcs.length).mpr ⟨rfl, rfl⟩)
          ((call_invokeOk_iff s a true []).mpr rfl)
          (call_run s a true failure allowed) rfl (by simpa [final] using ht)⟩
    | @diverge _ _ _ _ address ha hok hd =>
      obtain ⟨_, rfl⟩ := (GrowWrapper.exportFunc_iff s a x address).mp ha
      obtain rfl := (call_invokeOk_iff s a false args).mp hok
      exact (call_not_diverges s a false hd).elim

private theorem initial_run_eq (s : Store H) (a : AddrType) {c : Config H}
    (run : Steps P closedHost (initial s a) c) : c = initial s a := by
  rcases run.cases_head with he | ⟨_, hs, _⟩
  · exact he.symm
  · exact (not_step_vals (W := []) hs).elim

private theorem initial_not_diverges (s : Store H) (a : AddrType) :
    ¬ Diverges P closedHost (initial s a) := by
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

/-- Initialization is a completed empty run, followed by the actual guarded
session; imports are admitted exactly when the original wrapper admits them. -/
theorem moduleObs_iff (s : Store H) (a : AddrType) (imports : List ExternAddr)
    (script : List Call) (bs : List (Behaviour Val)) :
    bs ∈ moduleObs P closedHost s imports (mod a) script ↔
      imports = [] ∧ ∃ tail,
        Session P closedHost (GrowWrapper.moduleInst s a) (store s a) script tail ∧
          bs = .returns [] :: tail := by
  constructor
  · rintro ⟨c, hi, ho⟩
    obtain ⟨rfl, rfl⟩ := instantiate_inv hi
    refine ⟨rfl, ?_⟩
    rcases ho with ⟨c', tail, run, _, hs, he⟩ | ⟨c', result, run, hr, hn, _⟩ | ⟨hd, _⟩
    · obtain rfl := initial_run_eq s a run
      exact ⟨tail, hs, he⟩
    · obtain rfl := initial_run_eq s a run
      exact (hn (result_nil hr)).elim
    · exact (initial_not_diverges s a hd).elim
  · rintro ⟨rfl, tail, hs, rfl⟩
    exact ⟨initial s a, instantiate s a,
      .inl ⟨initial s a, tail, .refl, rfl, hs, rfl⟩⟩

/-- Fatal-OOM is an insertion-only certificate at actual Core instantiation and
arbitrary-length shared-store export sessions, for every same numerical profile.
Both success/failure grow permissions are retained, including nondeterminism. -/
theorem exportCorrect (a : AddrType) :
    Modes.ExportCorrect .trapInsertion P (closedHost (H := H))
      (GrowWrapper.mod a 0 false) (mod a) := by
  constructor
  · intro s imports _ ⟨c, hi⟩
    obtain ⟨rfl, _⟩ := GrowWrapper.instantiate_inv hi
    exact ⟨initial s a, instantiate s a⟩
  · intro s imports script _
    constructor
    · intro target ht
      obtain ⟨rfl, tail, hs, rfl⟩ := (moduleObs_iff s a imports script target).mp ht
      obtain ⟨source, hsource, rel⟩ := session_source_of_guarded s a script hs
      exact .inr ⟨.returns [] :: source,
        (GrowWrapper.moduleObs_iff s a 0 false [] script _).mpr
          ⟨rfl, source, hsource, rfl⟩, .returns [] rel⟩
    · rintro ⟨source, hs⟩
      obtain ⟨rfl, tail, hsession, rfl⟩ :=
        (GrowWrapper.moduleObs_iff s a 0 false imports script source).mp hs
      obtain ⟨target, ht⟩ := session_guarded_exists s a script hsession
      exact ⟨_, (moduleObs_iff s a [] script _).mpr ⟨rfl, target, ht, rfl⟩⟩

end Silmaril.Wasm.Binaryen.GrowOOM
