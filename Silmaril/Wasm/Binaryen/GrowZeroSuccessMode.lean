module

public import Silmaril.Wasm.Binaryen.GrowZeroSuccess

@[expose] public section

namespace Silmaril.Wasm.Binaryen.GrowZeroSuccess

open Execution.Core Execution.Core.Sim Numerics Validation MemoryGrowFailure Optimization
open Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.SingleThreaded.Exec
open GrowWrapper (Forced)

variable {H : Type} {P : Profile}

/-- The only profile requirement: successful zero growth remains an allowed
source choice at every ambient memory address. Numerical choices are unrestricted. -/
def ZeroGrowSuccess (P : Profile) : Prop :=
  ∀ address, P.growMaySucceed .memory address 0 0

theorem zeroGrowSuccess_spec (nd : Bool) (r : RelaxedChoice) :
    ZeroGrowSuccess (Profile.spec nd r) := by intro address; trivial

/-- Constant zero is forced and leaves the complete allocated store unchanged. -/
theorem target_forced (s : Store H) (a : AddrType) :
    Forced (P := P) (invoke (store s a) s.funcs.length [])
      ⟨store s a, {}, vals [addrVal a 0]⟩ := by
  refine .step (invoke_first s a) ?_ ?_
  · intro c hc
    simpa [func, expression, Frame.forCall, vals, addrVal, Val.toAdmin] using
      GrowWrapper.invoke_first_unique (func_lookup s a)
        (Expand.iff.mpr (GrowWrapper.expand_dt a)) rfl hc
  · simpa [func, expression, vals, addrVal, Val.toAdmin] using
      GrowOOM.finish_values_forced (P := P) (store s a) {}
        {module := GrowWrapper.moduleInst s a} (addrVal a 0)

theorem target_run_inv (s : Store H) (a : AddrType)
    {c : Config H} {r : Result}
    (run : Steps P closedHost (invoke (store s a) s.funcs.length []) c)
    (hr : c.code = r.toAdmin) :
    c = ⟨store s a, {}, vals [addrVal a 0]⟩ ∧ r = .values [addrVal a 0] := by
  have hc := (target_forced (P := P) s a).terminal_eq
    (fun _ => not_step_vals) run ⟨r, hr⟩
  subst c
  refine ⟨rfl, ?_⟩
  have he := (BehaviourRefinement.outcome?_eq_some_of_code hr).symm.trans
    (BehaviourRefinement.outcome?_eq_some_of_code (r := .values [addrVal a 0]) rfl)
  exact Option.some.inj he

/-- Every target session is reproduced by actual successful source calls. The
source and target each retain their own allocated store through every call. -/
theorem session_source_of_target (success : ZeroGrowSuccess P) (s : Store H)
    (a : AddrType) (script : List Call) {bs : List (Behaviour Val)}
    (ht : Session P closedHost (GrowWrapper.moduleInst s a) (store s a) script bs) :
    Session P closedHost (GrowWrapper.moduleInst s a) (GrowOOM.store s a) script bs := by
  induction script generalizing bs with
  | nil => cases ht; exact .nil
  | cons call rest ih =>
    obtain ⟨x, vs⟩ := call
    cases ht with
    | stop h =>
      exact .stop fun addr ha hok => h addr ha (by
        obtain ⟨_, rfl⟩ := (GrowWrapper.exportFunc_iff s a x addr).mp ha
        exact (invokeOk_iff s a vs).mpr ((GrowOOM.invokeOk_iff s a vs).mp hok))
    | @done _ _ _ _ addr c result _ ha hok run hr tail =>
      obtain ⟨rfl, rfl⟩ := (GrowWrapper.exportFunc_iff s a x addr).mp ha
      obtain rfl := (invokeOk_iff s a vs).mp hok
      obtain ⟨rfl, rfl⟩ := target_run_inv s a run hr
      refine .done ((GrowWrapper.exportFunc_iff s a "grow" s.funcs.length).mpr ⟨rfl, rfl⟩)
        ((GrowOOM.invokeOk_iff s a []).mpr rfl)
        (GrowOOM.call_run s a true false (success s.mems.length)) rfl ?_
      simpa [GrowOOM.final, GrowOOM.callStore] using ih tail
    | @diverge _ _ _ _ addr ha hok hd =>
      obtain ⟨_, rfl⟩ := (GrowWrapper.exportFunc_iff s a x addr).mp ha
      obtain rfl := (invokeOk_iff s a vs).mp hok
      exact ((target_forced s a).not_diverges (fun _ => not_step_vals) hd).elim

/-- Feasibility is constructive for every call script and arbitrary profiles;
invalid call requests end the session. No host totality is assumed. -/
theorem target_session_exists (s : Store H) (a : AddrType) (script : List Call) :
    ∃ bs, Session P closedHost (GrowWrapper.moduleInst s a) (store s a) script bs := by
  induction script with
  | nil => exact ⟨[], .nil⟩
  | cons call rest ih =>
    obtain ⟨x, vs⟩ := call
    by_cases hv : x = "grow" ∧ vs = []
    · obtain ⟨rfl, rfl⟩ := hv
      obtain ⟨bs, hb⟩ := ih
      exact ⟨.returns [addrVal a 0] :: bs,
        .done (r := .values [addrVal a 0])
          ((GrowWrapper.exportFunc_iff s a "grow" s.funcs.length).mpr ⟨rfl, rfl⟩)
          ((invokeOk_iff s a []).mpr rfl) (target_forced s a).steps rfl hb⟩
    · exact ⟨[], .stop fun addr ha hok => hv
        ⟨((GrowWrapper.exportFunc_iff s a x addr).mp ha).1,
          (invokeOk_iff s a vs).mp (by
            obtain ⟨_, rfl⟩ := (GrowWrapper.exportFunc_iff s a x addr).mp ha
            exact hok)⟩⟩

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

/-- Initialization is a completed empty run, followed by the constant-return
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

/-- Feasible refinement removes an optional OOM trap by selecting success.
The profile premise is essential: deterministic failure-only growth is excluded. -/
theorem exportCorrect_of_success (success : ZeroGrowSuccess P) (a : AddrType) :
    Modes.ExportCorrect .refinement P (closedHost (H := H)) (GrowOOM.mod a) (mod a) := by
  constructor
  · intro s imports _ ⟨c, hi⟩
    obtain ⟨rfl, _⟩ := GrowOOM.instantiate_inv hi
    exact ⟨initial s a, instantiate s a⟩
  · intro s imports script _
    constructor
    · intro bs ht
      obtain ⟨rfl, tail, hs, rfl⟩ := (moduleObs_iff s a imports script bs).mp ht
      exact (GrowOOM.moduleObs_iff s a [] script _).mpr
        ⟨rfl, tail, session_source_of_target success s a script hs, rfl⟩
    · rintro ⟨bs, hs⟩
      obtain ⟨rfl, _⟩ := (GrowOOM.moduleObs_iff s a imports script bs).mp hs
      obtain ⟨tail, ht⟩ := target_session_exists (P := P) s a script
      exact ⟨_, (moduleObs_iff s a [] script _).mpr ⟨rfl, tail, ht, rfl⟩⟩

theorem exportCorrect (a : AddrType) (nd : Bool := true) (r : RelaxedChoice := {}) :
    Modes.ExportCorrect .refinement (Profile.spec nd r) (closedHost (H := H))
      (GrowOOM.mod a) (mod a) :=
  exportCorrect_of_success (zeroGrowSuccess_spec nd r) a

end Silmaril.Wasm.Binaryen.GrowZeroSuccess
