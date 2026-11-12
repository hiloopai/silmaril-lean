module

public import Silmaril.Proofs.Wasm.Verify.Check.Assert
public import Silmaril.Proofs.Wasm.Verify.Flow.Plays

/-!
# Soundness of the verifier for assertions, with the flow analysis

The flow check `funcOkF` implies the hypotheses of `FlowIn` (`funcOkF_sound`, `closedBF_sound`,
`flowIn_of_closedBF`). A `proved` verdict of `check m (.assertNeverFalse i)` comes from the
guarded-call check (`GuardIn`) or from the flow check (`FlowIn`); either way the assertion is
never called with `false`, every profile (`check_assert_sound`, `check_assertNeverFalse`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

theorem funcOkF_sound {s : Store Nat} {fs G : List Nat} {i a : Nat} {fi : FuncInst Nat}
    {code : Func} (h : funcOkF s fs G i a = true) (hf : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm code) :
    fi.module.funcs = fs ∧ (∀ ins ∈ code.body, PlOK (CallPl (· ∈ G) (isHost s i) fs) ins) ∧
      okL (stableLocals code.body) (isHost s i) fs ⟨[], .other⟩ code.body = true := by
  simp only [funcOkF, hf, hcode, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hm, hrf⟩, hcall⟩, hok⟩ := h
  refine ⟨hm, fun ins hins => .inr ⟨fun x hx b hb => ?_, fun x hx b hb => ?_⟩, hok⟩
  · simpa [hb] using hrf x (mem_exprRF hins hx)
  · have h₁ := hcall x (mem_exprCalls hins hx)
    simpa only [hb, Bool.or_eq_true, List.contains_iff_mem] using h₁

theorem closedBF_sound {s : Store Nat} {fs G : List Nat} {i : Nat} (h : closedBF s fs G i = true) :
    FuncsClosed (· ∈ G) fs (CallPl (· ∈ G) (isHost s i) fs) s.funcs ∧
      BodiesFlow (· ∈ G) (isHost s i) fs s.funcs := by
  refine ⟨fun a fi code ha hf hcode => ?_, fun a fi code ha hf hcode => ?_⟩
  · have hok := funcOkF_sound (List.all_eq_true.1 h a ha) hf hcode
    exact ⟨hok.1, hok.2.1⟩
  · exact ⟨_, (funcOkF_sound (List.all_eq_true.1 h a ha) hf hcode).2.2⟩

/-- A `proved` decision with the flow check gives `FlowIn`. -/
theorem flowIn_of_closedBF {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (hI : IsInstance m mt I) {i : Nat} (har : arityOne mt i = true) {fs G : List Nat}
    (hc : closedBF I.store fs G i = true) (hr : rootsB G (rootsOf I.store I.addrs) = true)
    (ha : avoidsB I.store G i = true) : FlowIn I (· ∈ G) fs i := by
  have hok : I.Ok := hI.ok
  have hcl := closedBF_sound hc
  exact ⟨hok, hcl.1, hcl.2, storeIn_of_rootsB hr, addr_mem_roots hok hr, avoidsB_sound ha,
    arityOne_sound hI har⟩

/-- A `proved` verdict for an assertion gives the hypotheses of the guarded-call analysis or of
the flow analysis. -/
theorem assertIn_of_check {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (hI : IsInstance m mt I) {i : Nat} (h : (check m (.assertNeverFalse i)).verdict = .proved) :
    (∃ (G : List Nat) (fs : List Nat), GuardIn I (· ∈ G) fs i) ∨
      ∃ (G : List Nat) (fs : List Nat), FlowIn I (· ∈ G) fs i := by
  obtain ⟨har, fs, hd⟩ := check_assert_inv hI h
  rcases decideAssert_proved hd with ⟨G, hc, hr, ha⟩ | ⟨G, hc, hr, ha⟩
  · exact .inl ⟨G, fs, guardIn_of_closedBA hI har hc hr ha⟩
  · exact .inr ⟨G, fs, flowIn_of_closedBF hI har hc hr ha⟩

/-- **Soundness of the verifier for "assert is never called with `false`"** (every profile). -/
theorem check_assert_sound {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (hI : IsInstance m mt I) {i : (ifaceOf I).Imp}
    (h : (check m (.assertNeverFalse i.val)).verdict = .proved) (P : Profile) :
    Models (assertNeverFalse FnType (Behaviour Val)) (wasmSem P) (WasmProg.ofInstance I) i := by
  rcases assertIn_of_check hI h with ⟨G, fs, hR⟩ | ⟨G, fs, hR⟩
  · exact assertNeverFalse_of_guardIn hR P
  · exact assertNeverFalse_of_flowIn hR P

/-- **The verifier on a module, for assertions.** -/
theorem check_assertNeverFalse {m : Module} (hm : (instance? m).isSome = true)
    {i : (ifaceOf (instOf m)).Imp} (h : (check m (.assertNeverFalse i.val)).verdict = .proved)
    (P : Profile) :
    Models (assertNeverFalse FnType (Behaviour Val)) (wasmSem P) (progOf m) i :=
  check_assert_sound (isInstance_instOf hm).choose_spec h P

end Silmaril.Wasm.Verify
