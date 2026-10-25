module

public import Silmaril.Wasm.Binaryen.Toolkit.CtorEvalCalls

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit.CtorEval

open Execution.Core Execution.Core.Sim Numerics Validation Optimization
open Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.SingleThreaded.Exec
open GrowWrapper (Forced)

variable {H : Type} {P : Profile}

theorem getter_invokeOk_iff (s : Store H) (t : IntType)
    (scratch current value : BitVec t.width) (args : List Val) :
    InvokeOk (store s t scratch current value) (s.funcs.length + 1) args ↔ args = [] := by
  constructor
  · rintro ⟨fi, ps, rs, hf, he, hv⟩
    rw [getter_lookup] at hf
    cases hf
    have hx := (expand_dt t true).symm.trans (Expand.iff.mp he)
    simp only [Option.some.injEq, Ty.func.injEq] at hx
    obtain ⟨rfl, _⟩ := hx
    change List.Forall₂ _ args [] at hv
    cases hv
    rfl
  · rintro rfl
    exact ⟨_, .nil, _, getter_lookup s t scratch current value,
      Expand.iff.mpr (expand_dt t true), .nil⟩

theorem exportFunc_iff (s : Store H) (t : IntType) (x : String) (address : Nat) :
    exportFunc? (moduleInst s t) x = some address ↔ x = "get" ∧ address = s.funcs.length + 1 := by
  by_cases hx : x = "get"
  · subst x; simp [exportFunc?, moduleInst, eq_comm]
  · by_cases hg : x = "state"
    · subst x; simp [exportFunc?, moduleInst]
    · simp [exportFunc?, moduleInst, List.find?, hx, Ne.symm hx,
        show ("state" == x) = false from beq_eq_false_iff_ne.mpr (Ne.symm hg)]

theorem getter_run_inv (s : Store H) (t : IntType) (scratch current value : BitVec t.width)
    {c : Config H} {r : Result}
    (run : Steps P closedHost (invoke (store s t scratch current value) (s.funcs.length + 1) []) c)
    (hr : c.code = r.toAdmin) :
    c = ⟨store s t scratch current value, {}, vals [.num ⟨.int t, current⟩]⟩ ∧
      r = .values [.num ⟨.int t, current⟩] := by
  have hc := (getter_forced (P := P) s t scratch current value).terminal_eq
    (fun _ => not_step_vals) run ⟨r, hr⟩
  subst c
  refine ⟨rfl, ?_⟩
  exact Option.some.inj ((BehaviourRefinement.outcome?_eq_some_of_code hr).symm.trans
    (BehaviourRefinement.outcome?_eq_some_of_code (r := .values [.num ⟨.int t, current⟩]) rfl))

theorem getter_not_diverges (s : Store H) (t : IntType) (scratch current value : BitVec t.width) :
    ¬ Diverges P closedHost (invoke (store s t scratch current value) (s.funcs.length + 1) []) :=
  (getter_forced s t scratch current value).not_diverges (fun _ => not_step_vals)

/-- An explicit store relation: any inaccessible provisional scalar slot may
vary, while the entire active global and retained function layout agree. -/
theorem session_change_scratch (s : Store H) (t : IntType)
    (scratch₁ scratch₂ current value : BitVec t.width) (script : List Call)
    {bs : List (Behaviour Val)}
    (hs : Session P closedHost (moduleInst s t) (store s t scratch₁ current value) script bs) :
    Session P closedHost (moduleInst s t) (store s t scratch₂ current value) script bs := by
  induction script generalizing bs with
  | nil => cases hs; exact .nil
  | cons call rest ih =>
    obtain ⟨x, args⟩ := call
    cases hs with
    | stop h =>
      refine .stop ?_
      intro address ha hok
      obtain ⟨_, rfl⟩ := (exportFunc_iff s t x address).mp ha
      exact h _ ha ((getter_invokeOk_iff s t scratch₁ current value args).mpr
        ((getter_invokeOk_iff s t scratch₂ current value args).mp hok))
    | @done _ _ _ _ address c result _ ha hok run hr tail =>
      obtain ⟨rfl, rfl⟩ := (exportFunc_iff s t x address).mp ha
      obtain rfl := (getter_invokeOk_iff s t scratch₁ current value args).mp hok
      obtain ⟨rfl, rfl⟩ := getter_run_inv s t scratch₁ current value run hr
      exact .done ((exportFunc_iff s t "get" (s.funcs.length + 1)).mpr ⟨rfl, rfl⟩)
        ((getter_invokeOk_iff s t scratch₂ current value []).mpr rfl)
        (getter_forced s t scratch₂ current value).steps rfl (ih tail)
    | @diverge _ _ _ _ address ha hok hd =>
      obtain ⟨_, rfl⟩ := (exportFunc_iff s t x address).mp ha
      obtain rfl := (getter_invokeOk_iff s t scratch₁ current value args).mp hok
      exact (getter_not_diverges s t scratch₁ current value hd).elim

def completed (s : Store H) (t : IntType) (i v : BitVec t.width) (evaluated : Bool) : Config H :=
  ⟨store s t (if evaluated then v else i) v v, {module := moduleInst s t}, []⟩

theorem initialization_forced (s : Store H) (t : IntType) (i v : BitVec t.width) (evaluated : Bool) :
    Forced (P := P) (initial s t i v evaluated) (completed s t i v evaluated) := by
  cases evaluated
  · exact constructor_forced s t i v
  · exact .done _

theorem moduleObs_iff (s : Store H) (t : IntType) (i v : BitVec t.width) (evaluated : Bool)
    (imports : List ExternAddr) (script : List Call) (bs : List (Behaviour Val)) :
    bs ∈ moduleObs P closedHost s imports (mod t i v evaluated) script ↔
      imports = [] ∧ ∃ tail, Session P closedHost (moduleInst s t)
        (store s t (if evaluated then v else i) v v) script tail ∧ bs = .returns [] :: tail := by
  apply moduleObs_iff_of_forced_initialization s imports (mod t i v evaluated)
    (initial s t i v evaluated) (completed s t i v evaluated) _
    (initialization_forced s t i v evaluated) rfl script bs
  intro c
  constructor
  · exact instantiate_inv
  · rintro ⟨rfl, rfl⟩; exact instantiate s t i v evaluated

/-- The serialized module preserves actual admission, initialization and every
closed-host shared-store export session at each same arbitrary profile. -/
theorem exportCorrect (t : IntType) (i v : BitVec t.width) :
    Modes.ExportCorrect .equivalence P (closedHost (H := H))
      (mod t i v false) (mod t i v true) := by
  constructor
  · intro s imports _
    constructor
    · rintro ⟨c, hi⟩
      obtain ⟨rfl, _⟩ := instantiate_inv hi
      exact ⟨_, instantiate s t i v true⟩
    · rintro ⟨c, hi⟩
      obtain ⟨rfl, _⟩ := instantiate_inv hi
      exact ⟨_, instantiate s t i v false⟩
  · intro s imports script _
    apply Set.ext
    intro bs
    rw [moduleObs_iff, moduleObs_iff]
    simp only [Bool.false_eq_true, ↓reduceIte]
    constructor
    · rintro ⟨empty, tail, session, rfl⟩
      exact ⟨empty, tail, session_change_scratch s t i v v v script session, rfl⟩
    · rintro ⟨empty, tail, session, rfl⟩
      exact ⟨empty, tail, session_change_scratch s t v i v v script session, rfl⟩

end Silmaril.Wasm.Binaryen.Toolkit.CtorEval
