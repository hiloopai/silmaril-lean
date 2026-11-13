module

public import Silmaril.Wasm.Models.V10Lime1Back.Defs

/-!
# The converse of `v10own → lime1own` fails at a two-result function

* `v1_stuck`: no 1.0 step leaves `[invoke 0]` over `cxStore` (1.0's `invokeWasm` needs at most
  one result; the function is not a host function; nothing else reduces an invocation);
* `v1_behaviours_empty`: so the 1.0 behaviours of calling address `0` are empty;
* `lime1_returns`: Lime1 returns `[0, 0]` from the same call at the image point
  (`invokeWasm`, `labelDone` under the frame, `frameDone`);
* `cx_dom`: the point lies in the domain of `v10own` (the empty host satisfies every host
  condition, the store has no memory, table or global, and the function's module names no
  function).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V10Lime1Back

open Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V10Lime1Back

/-- A value is not an invocation. -/
theorem value_ne_invoke (v : Value) (a : FuncAddr) :
    Silmaril.Wasm.V1.Execution.value v ≠ .invoke a := by
  rcases v with ⟨t, bits⟩
  cases t <;> simp [Silmaril.Wasm.V1.Execution.value]

/-- A value prefix of `[invoke a]` is empty. -/
theorem values_eq_nil {vs : List Value} {rest : List Silmaril.Wasm.V1.Execution.Admin}
    {a : FuncAddr} (h : Silmaril.Wasm.V1.Execution.values vs ++ rest = [.invoke a]) :
    vs = [] ∧ rest = [.invoke a] := by
  cases vs with
  | nil => exact ⟨rfl, h⟩
  | cons v vs => simp [Silmaril.Wasm.V1.Execution.values] at h

/-- The store's function at address `0`. -/
theorem cx_found : cxStore.funcs[(⟨0⟩ : FuncAddr).value]? = some (.wasm twoType {} twoFn) := rfl

/-- At the invocation of address `0` over `cxStore`, the function found is the two-result one. -/
theorem cx_fi {s : V10.OStore Unit} {a : FuncAddr} {args : List Value}
    {fi : FuncInst Silmaril.Wasm.V1.Func Unit}
    (hc : Silmaril.Wasm.V1.Execution.values args ++ [.invoke a] = [.invoke ⟨0⟩])
    (hs : s = cxStore) (found : s.funcs[a.value]? = some fi) :
    fi = .wasm twoType {} twoFn := by
  have ha : [AdminInstr.invoke a] = [.invoke ⟨0⟩] := (values_eq_nil hc).2
  have ha' : a = ⟨0⟩ := by simpa using ha
  have hsome : some fi = some (.wasm twoType {} twoFn) := by rw [← found, ha', hs]; rfl
  exact Option.some.inj hsome

/-- A step under a value prefix of `[invoke 0]` is a step of `[invoke 0]` itself. -/
theorem context_code {before tail : List Silmaril.Wasm.V1.Execution.Admin} {vs : List Value}
    (hc : Silmaril.Wasm.V1.Execution.values vs ++ before ++ tail = [.invoke ⟨0⟩])
    (hne : Silmaril.Wasm.V1.Execution.firstRedex before ≠ none) :
    before = [.invoke ⟨0⟩] := by
  have hrest : before ++ tail = [.invoke ⟨0⟩] :=
    (values_eq_nil (by simpa [List.append_assoc] using hc)).2
  rcases List.append_eq_singleton_iff.mp hrest with ⟨hb, -⟩ | ⟨hb, -⟩
  · exact absurd (by simp [hb]) hne
  · exact hb

/-- **1.0 is stuck at the invocation.** -/
theorem v1_stuck {src : V10.OHost Unit} {c c' : Silmaril.Wasm.V1.Execution.Config Unit}
    (h : Silmaril.Wasm.V1.Execution.Step src c c') (hs : c.store = cxStore)
    (hc : c.code = [.invoke ⟨0⟩]) : False := by
  induction h with
  | pure s f hp =>
    rename_i before after
    have hc' : before = [.invoke ⟨0⟩] := hc
    exact hp.firstRedex_ne_invoke ⟨0⟩ (by rw [hc']; rfl)
  | context hstep vs tail ih => exact ih hs (context_code hc hstep.firstRedex_ne_none)
  | invokeWasm s f a ft module fn args found arity resultArity =>
    have hft : ft = twoType := (FuncInst.wasm.inj (cx_fi hc hs found)).1
    exact absurd (hft ▸ resultArity) (by decide)
  | invokeHost s s' f a ft fn args r found => exact absurd (cx_fi hc hs found) (by simp)
  | invokeHostDiverges s f a ft fn args found => exact absurd (cx_fi hc hs found) (by simp)
  | _ => simp_all [Silmaril.Wasm.V1.Execution.value]

/-- The 1.0 entry configuration of the call. -/
theorem cx_invoke :
    (Silmaril.Wasm.V1.Execution.invoke cxStore ⟨0⟩ []).code = [.invoke ⟨0⟩] := rfl

/-- **The 1.0 behaviours of the call are empty.** -/
theorem v1_behaviours_empty (src : V10.OHost Unit) :
    Silmaril.Wasm.V1.Execution.behaviours src cxStore ⟨0⟩ [] = ∅ := by
  have hstuck : ∀ c', ¬ Silmaril.Wasm.V1.Execution.Step src
      (Silmaril.Wasm.V1.Execution.invoke cxStore ⟨0⟩ []) c' :=
    fun _ h => v1_stuck h rfl cx_invoke
  refine Set.eq_empty_of_forall_notMem fun b hb => ?_
  rcases hb with ⟨c', r, hrun, hres, -⟩ | ⟨-, hdiv⟩
  · rcases Relation.ReflTransGen.cases_head hrun with heq | ⟨c₁, h₁, -⟩
    · have hcode : Silmaril.Wasm.V1.Execution.result r = [.invoke ⟨0⟩] := by
        rw [← hres, ← heq]; rfl
      cases r with
      | values vs =>
        have h' : Silmaril.Wasm.V1.Execution.values vs ++ [] = [.invoke ⟨0⟩] := by
          simpa [Silmaril.Wasm.V1.Execution.result] using hcode
        exact absurd (values_eq_nil h').2 (by simp)
      | trap => simp [Silmaril.Wasm.V1.Execution.result] at hcode
    · exact hstuck c₁ h₁
  · obtain ⟨c₁, h₁, -⟩ := hdiv.unfold
    exact hstuck c₁ h₁

/-- The Lime1 value `i32 0`. -/
def zero32 : Value := ⟨.int .i32, (0 : BitVec 32)⟩

/-- The Lime1 store of the counterexample point. -/
theorem cx_limeStore_found :
    (V10.limeStore cxPt).funcs[(⟨0⟩ : FuncAddr).value]? =
      some (.wasm twoType {} twoFn.toLime) := rfl

/-- **Lime1 returns `[0, 0]` from the call at the image point**, under any Lime1 host. -/
theorem lime1_steps (tgt : V10.LHost Unit) :
    Silmaril.Wasm.Lime1.Execution.Steps tgt (Lime1Core.invokeL (V10.limeStore cxPt) ⟨0⟩ [])
      ⟨V10.limeStore cxPt, ⟨[], {}⟩, Silmaril.Wasm.Lime1.Execution.values [zero32, zero32]⟩ := by
  have h₁ := Silmaril.Wasm.Lime1.Execution.Step.invokeWasm (host := tgt) (V10.limeStore cxPt)
    ⟨[], {}⟩ ⟨0⟩ twoType {} twoFn.toLime [] cx_limeStore_found rfl
  have h₂ := Silmaril.Wasm.Lime1.Execution.Step.frame (host := tgt)
    (Silmaril.Wasm.Lime1.Execution.Step.pure (host := tgt) (V10.limeStore cxPt)
      ⟨[] ++ twoFn.toLime.locals.map Value.zero, {}⟩
      (Silmaril.Wasm.Lime1.Execution.PureStep.labelDone (types := []) 2 [] [zero32, zero32]))
    2 ⟨[], {}⟩
  have h₃ := Silmaril.Wasm.Lime1.Execution.Step.pure (host := tgt) (V10.limeStore cxPt) ⟨[], {}⟩
    (Silmaril.Wasm.Lime1.Execution.PureStep.frameDone (types := ({} : ModuleInst).types) 2
      ⟨[] ++ twoFn.toLime.locals.map Value.zero, {}⟩ [zero32, zero32] rfl)
  exact ((h₁.steps.tail h₂).tail h₃)

/-- **Lime1 returns `[0, 0]`.** -/
theorem lime1_returns (tgt : V10.LHost Unit) :
    Behaviour.returns [zero32, zero32] ∈ Lime1Core.behavioursL tgt (V10.limeStore cxPt) ⟨0⟩ [] :=
  Or.inl ⟨_, .values [zero32, zero32], lime1_steps tgt, rfl, rfl⟩

/-- **The counterexample point lies in the domain of `v10own`.** -/
theorem cx_dom : V10.dom cxPt := by
  refine ⟨⟨by simp [V10.limeStore, cxPt, cxStore, Store.mapCode],
    by simp [V10.limeStore, cxPt, cxStore, Store.mapCode],
    by simp [V10.limeStore, cxPt, cxStore, Store.mapCode],
    by simp [V10.limeStore, cxPt, cxStore, Store.mapCode],
    by simp [V10.limeStore, cxPt, cxStore, Store.mapCode]⟩, ?_, ?_, ?_, ?_⟩
  · rintro h s vs s' r ⟨_, _, _, _, hb⟩
    exact hb.elim
  · rintro h s vs s' r ⟨_, _, _, _, hb⟩
    exact hb.elim
  · rintro h s vs s' r ⟨_, _, _, _, hb⟩
    exact hb.elim
  · intro fi hfi t m c hc a ha
    have hfi' : fi = .wasm twoType {} twoFn := by simpa [cxPt, cxStore] using hfi
    rw [hfi'] at hc
    simp only [FuncInst.wasm.injEq] at hc
    rw [← hc.2.1] at ha
    simp at ha

end Silmaril.Proofs.Wasm.Models.V10Lime1Back
