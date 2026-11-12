module

public import Silmaril.Proofs.Wasm.FX.Logic.EveryRun.Total

/-!
# Adequacy of the every-run WasmFX logic

* `tsafe_steps`, `safe_steps`: safety is kept along runs;
* `stops_ofResult`: the code of a Wasm result has stopped with its outcome;
* **`tsafe_result`**, **`hwp_result`**: every finished run of safe code satisfies the
  postcondition (partial correctness);
* **`tsafe_not_infinite`**: total safety rules out infinite runs (total correctness);
* **`tsafe_behaviours`**: every `StepFX'` behaviour of totally safe code is the behaviour of a
  result satisfying the postcondition; **`tsafe_behaviours_eq`**: with a postcondition that
  admits only `vs₀`, and one run returning `vs₀`, the behaviours are exactly `{returns vs₀}`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Logic.EveryRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.FX.Logic (OutcomeFX PostFX Conts)
open Silmaril.Wasm.FX.Logic.EveryRun (Stops Safe TSafe HWP)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX} {Q : PostFX H}

theorem tsafe_steps {c d : ConfigFX H} (h : TSafe P fx Q c) (hr : StepsFX' P noHost fx c d) :
    TSafe P fx Q d := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.steps _ hs

theorem safe_step {n : Nat} {c d : ConfigFX H} (h : Safe P fx Q (n + 1) c)
    (hs : StepFX' P noHost fx c d) : Safe P fx Q n d :=
  h.2 d hs

theorem safe_steps {c d : ConfigFX H} (h : ∀ n, Safe P fx Q n c) (hr : StepsFX' P noHost fx c d) :
    ∀ n, Safe P fx Q n d := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact fun n => safe_step (ih (n + 1)) hs

theorem stops_ofResult (s : Store H) (f : Frame) (r : Result) :
    Stops s f (Silmaril.Wasm.FX.Logic.OutcomeFX.ofResult r) (r.toAdmin.map .core) := by
  cases r with
  | values vs => exact map_core_vals vs
  | throw a => rfl
  | trap => rfl

/-- **Partial correctness of total safety.** -/
theorem tsafe_result {c d : ConfigFX H} {r : Result} (h : TSafe P fx Q c)
    (hr : StepsFX' P noHost fx c d) (hd : d.code = r.toAdmin.map .core) :
    Q d.store d.conts d.frame (Silmaril.Wasm.FX.Logic.OutcomeFX.ofResult r) :=
  (tsafe_steps h hr).stops _ (hd ▸ stops_ofResult d.store d.frame r)

/-- **Partial correctness of the every-run weakest precondition.** -/
theorem hwp_result {s : Store H} {K : Conts} {f : Frame} {code : List AdminFX} {d : ConfigFX H}
    {r : Result} (h : HWP P fx s K f code Q) (hr : StepsFX' P noHost fx ⟨s, K, f, code⟩ d)
    (hd : d.code = r.toAdmin.map .core) :
    Q d.store d.conts d.frame (Silmaril.Wasm.FX.Logic.OutcomeFX.ofResult r) :=
  (safe_steps h hr 1).1 _ (hd ▸ stops_ofResult d.store d.frame r)

/-- **Total correctness**: no infinite run. -/
theorem tsafe_not_infinite {c : ConfigFX H} (h : TSafe P fx Q c) :
    ¬ Silmaril.InfiniteTrace (StepFX' P noHost fx) c := by
  induction h with
  | intro _ _ ih =>
    intro hi
    obtain ⟨b, hb, hi'⟩ := hi.unfold
    exact ih b hb hi'

/-- Total safety implies safety for every number of steps. -/
theorem tsafe_hwp {c : ConfigFX H} (h : TSafe P fx Q c) : ∀ n, Safe P fx Q n c := by
  induction h with
  | intro hq _ ih =>
    intro n
    cases n with
    | zero => trivial
    | succ n => exact ⟨hq, fun c' hs => ih c' hs n⟩

/-- **Every behaviour of totally safe code** is a result satisfying the postcondition. -/
theorem tsafe_behaviours {c : ConfigFX H} (h : TSafe P fx Q c) {b : Behaviour Val}
    (hb : b ∈ behavioursFX' P noHost fx c) :
    ∃ (d : ConfigFX H) (r : Result), Q d.store d.conts d.frame
      (Silmaril.Wasm.FX.Logic.OutcomeFX.ofResult r) ∧ b = r.toBehaviour := by
  rcases hb with ⟨d, r, hr, hd, rfl⟩ | ⟨-, hi⟩
  · exact ⟨d, r, tsafe_result h hr hd, rfl⟩
  · exact (tsafe_not_infinite h hi).elim

theorem ofResult_normal {r : Result} {vs : List Val}
    (h : Silmaril.Wasm.FX.Logic.OutcomeFX.ofResult r = .normal (liftV vs)) : r = .values vs := by
  cases r with
  | values ws =>
    have h' : liftV ws = liftV vs := by simpa [Silmaril.Wasm.FX.Logic.OutcomeFX.ofResult] using h
    rw [Silmaril.Proofs.Wasm.Models.FXAsyncBack.liftV_inj h']
  | throw a => cases h
  | trap => cases h

/-- **Exact behaviours**: totally safe code whose postcondition admits only the result `vs₀`,
and which has a run returning `vs₀`, has exactly that behaviour. -/
theorem tsafe_behaviours_eq {c : ConfigFX H} {vs₀ : List Val} (h : TSafe P fx Q c)
    (hQ : ∀ s K f o, Q s K f o → o = .normal (liftV vs₀))
    (hm : Behaviour.returns vs₀ ∈ behavioursFX' P noHost fx c) :
    behavioursFX' P noHost fx c = {.returns vs₀} := by
  ext b
  refine ⟨fun hb => ?_, fun hb => (Set.mem_singleton_iff.mp hb) ▸ hm⟩
  obtain ⟨d, r, hq, rfl⟩ := tsafe_behaviours h hb
  rw [ofResult_normal (hQ _ _ _ _ hq)]
  rfl

theorem ofResult_inj {r r' : Result}
    (h : Silmaril.Wasm.FX.Logic.OutcomeFX.ofResult r = Silmaril.Wasm.FX.Logic.OutcomeFX.ofResult r') :
    r = r' := by
  cases r' with
  | values vs => exact ofResult_normal h
  | throw a =>
    cases r with
    | throw b =>
      have hb : b = a := by simpa [Silmaril.Wasm.FX.Logic.OutcomeFX.ofResult] using h
      rw [hb]
    | _ => cases h
  | trap => cases r <;> first | rfl | cases h

/-- **Exact behaviours** for any result: totally safe code whose postcondition admits only the
outcome of `r₀`, and which has a run to `r₀`, has exactly the behaviour of `r₀`. -/
theorem tsafe_behaviours_eq_result {c : ConfigFX H} {r₀ : Result} (h : TSafe P fx Q c)
    (hQ : ∀ s K f o, Q s K f o → o = Silmaril.Wasm.FX.Logic.OutcomeFX.ofResult r₀)
    (hm : r₀.toBehaviour ∈ behavioursFX' P noHost fx c) :
    behavioursFX' P noHost fx c = {r₀.toBehaviour} := by
  ext b
  refine ⟨fun hb => ?_, fun hb => (Set.mem_singleton_iff.mp hb) ▸ hm⟩
  obtain ⟨d, r, hq, rfl⟩ := tsafe_behaviours h hb
  rw [ofResult_inj (hQ _ _ _ _ hq)]
  rfl

end Silmaril.Proofs.Wasm.FX.Logic.EveryRun
