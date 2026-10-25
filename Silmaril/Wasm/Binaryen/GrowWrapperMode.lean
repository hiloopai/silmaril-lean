module

public import Silmaril.Wasm.Binaryen.GrowWrapperRun

/-! # A feasible module refinement selecting growth failure

The module-level theorem observes initialization and arbitrary sequences of
export calls. All calls share the allocated store. The failure selection leaves
its exported memory untouched, so the same proof applies to later calls.
-/

@[expose] public section

namespace Silmaril.Wasm.Binaryen.GrowWrapper

open Execution.Core Execution.Core.Sim Numerics Validation MemoryGrowFailure
open Silmaril.Wasm.SingleThreaded.Det

variable {H : Type} {P : Profile}

private theorem initial_run_eq (s : Store H) (a : AddrType)
    (n : BitVec a.intType.width) (failure : Bool) {c : Config H}
    (run : Steps P closedHost (initial s a n failure) c) :
    c = initial s a n failure := by
  rcases run.cases_head with he | ⟨_, hs, _⟩
  · exact he.symm
  · exact (not_step_vals (W := []) hs).elim

private theorem initial_not_diverges (s : Store H) (a : AddrType)
    (n : BitVec a.intType.width) (failure : Bool) :
    ¬ Diverges P closedHost (initial s a n failure) := by
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
  | throw addr => cases h

/-- Initialization has one return and no state changes after allocation. Its
remaining observations are exactly the export-session observations. -/
theorem moduleObs_iff (s : Store H) (a : AddrType) (n : BitVec a.intType.width)
    (failure : Bool) (imports : List ExternAddr) (script : List Call)
    (bs : List (Behaviour Val)) :
    bs ∈ moduleObs P closedHost s imports (mod a n failure) script ↔
      imports = [] ∧ ∃ tail,
        Session P closedHost (moduleInst s a) (store s a n failure) script tail ∧
          bs = .returns [] :: tail := by
  constructor
  · rintro ⟨c, hi, ho⟩
    obtain ⟨rfl, rfl⟩ := instantiate_inv hi
    refine ⟨rfl, ?_⟩
    rcases ho with ⟨c', tail, run, _, hs, he⟩ | ⟨c', result, run, hr, hn, _⟩ | ⟨hd, _⟩
    · obtain rfl := initial_run_eq s a n failure run
      exact ⟨tail, hs, he⟩
    · obtain rfl := initial_run_eq s a n failure run
      exact (hn (result_nil hr)).elim
    · exact (initial_not_diverges s a n failure hd).elim
  · rintro ⟨rfl, tail, hs, rfl⟩
    exact ⟨initial s a n failure, instantiate s a n failure,
      .inl ⟨initial s a n failure, tail, .refl, rfl, hs, rfl⟩⟩

/-- Feasible refinement at the actual Core module/session boundary. The
specification permits growth failure at every call, including zero growth. -/
theorem exportCorrect (a : AddrType) (n : BitVec a.intType.width)
    (nd : Bool := true) (r : RelaxedChoice := {}) :
    Modes.ExportCorrect .refinement (Profile.spec nd r) (closedHost (H := H))
      (mod a n false) (mod a n true) := by
  constructor
  · intro s imports _ ⟨c, hi⟩
    obtain ⟨rfl, _⟩ := instantiate_inv hi
    exact ⟨initial s a n true, instantiate s a n true⟩
  · intro s imports script _
    constructor
    · intro bs ht
      obtain ⟨rfl, tail, hs, rfl⟩ := (moduleObs_iff s a n true imports script bs).mp ht
      exact (moduleObs_iff s a n false [] script _).mpr
        ⟨rfl, tail, session_source_of_target s a n nd r script hs, rfl⟩
    · rintro ⟨bs, hs⟩
      obtain ⟨rfl, _⟩ := (moduleObs_iff s a n false imports script bs).mp hs
      obtain ⟨tail, ht⟩ := target_session_exists (P := Profile.spec nd r) s a n script
      exact ⟨_, (moduleObs_iff s a n true [] script _).mpr ⟨rfl, tail, ht, rfl⟩⟩

/-- A genuine source observation missing from the target: initialization
returns, then successful zero growth returns `0` instead of `-1`. -/
theorem strict_module_example (a : AddrType) (nd : Bool) (r : RelaxedChoice) :
    moduleObs (Profile.spec nd r) (closedHost (H := H)) {} [] (mod a 0 false)
        [("grow", [])] ≠
      moduleObs (Profile.spec nd r) (closedHost (H := H)) {} [] (mod a 0 true) [("grow", [])] := by
  have hs : Session (Profile.spec nd r) closedHost (moduleInst ({} : Store H) a)
      (store {} a 0 false) [("grow", [])] [.returns [addrVal a 0]] :=
    .done (r := .values [addrVal a 0])
      ((exportFunc_iff ({} : Store H) a "grow" 0).mpr ⟨rfl, rfl⟩)
      ((invokeOk_iff ({} : Store H) a 0 false []).mpr rfl)
      (source_zero_success a nd r) rfl .nil
  have hobs := (moduleObs_iff ({} : Store H) a 0 false [] [("grow", [])]
    [.returns [], .returns [addrVal a 0]]).mpr ⟨rfl, _, hs, rfl⟩
  intro heq
  rw [heq] at hobs
  obtain ⟨_, tail, ht, he⟩ := (moduleObs_iff ({} : Store H) a 0 true []
    [("grow", [])] [.returns [], .returns [addrVal a 0]]).mp hobs
  rw [target_session_single ({} : Store H) a 0 ht] at he
  have hne : addrVal a 0 ≠ failed a := by cases a <;> decide
  exact hne (List.cons.inj (Behaviour.returns.inj (List.cons.inj (List.cons.inj he).2).1)).1

/-- The new pass needs refinement mode: the same transformation is not an
exact module equivalence, even on valid zero-delta wrappers. -/
theorem not_equivalence (a : AddrType) (nd : Bool) (r : RelaxedChoice) :
    ¬ Modes.ExportCorrect .equivalence (Profile.spec nd r) (closedHost (H := H))
      (mod a 0 false) (mod a 0 true) := by
  intro he
  exact strict_module_example (H := H) a nd r
    (he.observations {} [] [("grow", [])] LoopCex.storeOk_empty)

end Silmaril.Wasm.Binaryen.GrowWrapper
