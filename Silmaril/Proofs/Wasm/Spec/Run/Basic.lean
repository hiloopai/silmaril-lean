module

public import Silmaril.Wasm.Spec.Run.Defs
public import Silmaril.Proofs.Wasm.Spec.Wasm.Ground
public import Silmaril.Wasm.Execution.Core.SpecProfile

@[expose] public section

/-!
# The verified refuter: proofs

Decidable typing is sound, a well-formed instance meets `$invoke`'s premises on typed arguments,
and a `refuted` verdict of `refuteRet` exhibits a trace violating the return postcondition, at
every profile admitting the deterministic steps (`refuteRet_sound`, `refuteRet_sound_spec`).
-/

namespace Silmaril.Wasm.Spec

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

/-- Decidable scalar typing is sound. -/
theorem hasValB_sound {t : ScalarType} {v : Val} (h : hasValB t v = true) : t.HasVal v := by
  match t, v, h with
  | .num t, .num ⟨ty, bits⟩, h =>
    have hty : ty = t := by simpa only [hasValB, decide_eq_true_eq] using h
    exact hty ▸ (⟨bits, rfl⟩ : ScalarType.HasVal (.num ty) (.num ⟨ty, bits⟩))
  | .v128, .vec bits, _ => exact ⟨bits, rfl⟩
  | .i31 _, .ref (.i31 b), _ => exact .inl ⟨b, rfl⟩
  | .i31 _, .ref .null, h => exact .inr ⟨h, rfl⟩
  | .num _, .vec _, h | .num _, .ref _, h | .v128, .num _, h | .v128, .ref _, h
  | .i31 _, .num _, h | .i31 _, .vec _, h | .i31 _, .ref (.struct _), h
  | .i31 _, .ref (.array _), h | .i31 _, .ref (.func _), h | .i31 _, .ref (.exn _), h
  | .i31 _, .ref (.host _), h | .i31 _, .ref (.extern _), h =>
    exact absurd h (by simp [hasValB])

/-- Decidable typing of value lists is sound. -/
theorem typedB_sound : ∀ {ts : List ScalarType} {vs : List Val}, typedB ts vs = true →
    List.Forall₂ ScalarType.HasVal ts vs
  | [], [], _ => .nil
  | _ :: _, _ :: _, h => by
    simp only [typedB, Bool.and_eq_true] at h
    exact .cons (hasValB_sound h.1) (typedB_sound h.2)
  | [], _ :: _, h => by simp [typedB] at h
  | _ :: _, [], h => by simp [typedB] at h

/-- A result passing the decidable typing check is an answer. -/
theorem ofResult?_of_resultTypedB {ft : FnType} {r : Result}
    (h : resultTypedB ft.results r = true) : ∃ w, Answer.ofResult? ft r = some w := by
  cases r with
  | values vs =>
    have ht : List.Forall₂ ScalarType.HasVal ft.results vs := typedB_sound h
    exact ⟨.values ⟨vs, ht⟩, by simp [Answer.ofResult?, ht]⟩
  | trap => exact ⟨.trap, rfl⟩
  | throw a => exact ⟨.throw a, rfl⟩

/-- Typed arguments of an export of a well-formed instance meet `$invoke`'s premises. -/
theorem invokeOk_of_wellFormed {I : ScalarInstance} {s : Store Nat} (hw : I.WellFormed s)
    (j : Fin I.exports.length) (a : Typed (I.exports.get j).params) :
    InvokeOk s (I.addr j) a.1 := by
  obtain ⟨fi, hfi, hexp⟩ := hw.export_type j
  refine ⟨fi, Ty.ofList ((I.exports.get j).params.map ScalarType.toC),
    Ty.ofList ((I.exports.get j).results.map ScalarType.toC), hfi, hexp, ?_⟩
  rw [Ty.toList_ofList]
  have hval : ∀ {ts : List ScalarType} {vs : List Val}, List.Forall₂ ScalarType.HasVal ts vs →
      List.Forall₂ (ValOk s) vs (ts.map ScalarType.toC) := by
    intro ts vs h
    induction h with
    | nil => exact .nil
    | cons hv _ ih => exact .cons ((ScalarType.hasVal_iff_valOk s _ _).1 hv) ih
  exact hval a.2

/-- **A refutation is a counterexample** (every profile admitting the deterministic steps). -/
theorem refuteRet_sound {P : Profile} {o : GrowOracle}
    (hPo : ∀ c c' : Config Nat, Step (profile o) Det.noHost c c' → Step P Det.noHost c c')
    {X : WIface} (p : WasmProg X) (hw : p.inst.WellFormed p.store) (j : X.Exp)
    (a : Typed (X.exports.get j).params) (n : Nat) (Q : Behaviour Val → Bool)
    (h : refuteRet o n p j a.1 Q = .refuted) :
    ¬ Models (retPost FnType (List Val) (Behaviour Val)) (wasmSem P) p
      ⟨j, fun b => Q b = true⟩ := by
  intro hmod
  unfold refuteRet at h
  split at h
  next c' b r hrun =>
    show False
    have hc : (resultTypedB (X.exports.get j).results r && !Q r.toBehaviour) = true := by
      by_contra hc
      exact absurd (ite_eq_left_iff.1 h hc) (by decide)
    have hcond : resultTypedB (X.exports.get j).results r = true ∧ Q r.toBehaviour = false := by
      simpa using hc
    have hinv : InvokeOk p.store (p.inst.addr j) a.1 := invokeOk_of_wellFormed hw j a
    have hsteps : Steps (profile o) Det.noHost (invoke p.store (p.inst.addr j) a.1) c' :=
      Exec.InvokeRun.runInvoke?_steps_noHost hw.storeOk hinv hrun
    have hcode : c'.code = r.toAdmin :=
      (Exec.InvokeRun.runInvoke?_sound hw.storeOk hinv hrun).2.2 r rfl
    have hstepsP : Steps P Det.noHost (invoke p.store (p.inst.addr j) a.1) c' :=
      Relation.ReflTransGen.mono hPo _ _ hsteps
    obtain ⟨w, hw'⟩ := ofResult?_of_resultTypedB hcond.1
    have hmem : [Event.call j a.1, Event.ret j (Answer.toBehaviour w)] ∈ (wasmSem P).traces p :=
      (call_ret_mem_iff p j a _).2 ⟨c', r, w, hstepsP, hcode, hw', rfl⟩
    have hQ : Q (Answer.toBehaviour w) = true :=
      (models_iff (retPost FnType (List Val) (Behaviour Val)) (wasmSem P) p _).1 hmod _ hmem _
        (by simp)
    have hwr : Answer.toBehaviour w = r.toBehaviour := by
      unfold Answer.toBehaviour
      rw [Answer.toResult_of_ofResult? hw']
    rw [hwr, hcond.2] at hQ
    cases hQ
  next => cases h

/-- **A refutation is a counterexample for the specification profiles.** -/
theorem refuteRet_sound_spec (nd : Bool) {o : GrowOracle} {X : WIface} (p : WasmProg X)
    (hw : p.inst.WellFormed p.store) (j : X.Exp) (a : Typed (X.exports.get j).params) (n : Nat)
    (Q : Behaviour Val → Bool) (h : refuteRet o n p j a.1 Q = .refuted) :
    ¬ Models (retPost FnType (List Val) (Behaviour Val)) (wasmSem (Profile.spec nd {})) p
      ⟨j, fun b => Q b = true⟩ :=
  refuteRet_sound (fun _ _ hs => Step.deterministic_refines_spec nd hs) p hw j a n Q h

end Silmaril.Wasm.Spec
