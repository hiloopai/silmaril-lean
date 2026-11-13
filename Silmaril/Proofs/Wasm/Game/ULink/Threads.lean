module

public import Silmaril.Proofs.Wasm.Game.ULink.Store
public import Silmaril.Proofs.Wasm.Game.ULink.Resolver

/-!
# Threads of the consumer, the provider and the linked module

Machine-level facts for the simulations between the linked module and the composite:

* `internal_cons`: a host-free consumer step (stubbed store) is a linked step (real store);
* `internal_prov`: a host-free provider step at top level is a linked step in the consumer's
  callout context (`step_reframe`, `Ctx.step_fill`);
* `call_internal`: a stub call of the consumer is one linked `call_ref` step into the provider
  function, landing on the provider's first configuration;
* `resume_active`, `callout_comp`: resumption, and the provider's callouts seen in the linked
  thread.

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.ULink

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.ULink Silmaril Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
  Silmaril.Proofs.Wasm.Game.Linking Silmaril.Proofs.Wasm.Game.Linking.Split

variable {L : ULink} {P : Profile}

/-- **Consumer steps are linked steps.** -/
theorem internal_cons {s σ' : Store Nat} {t t' : Thread}
    (h : InternalP P (L.stubS s, t) (σ', t')) :
    ∃ s', σ' = L.stubS s' ∧ s'.funcs = s.funcs ∧ InternalP P (s, t) (s', t') := by
  obtain ⟨f', code', ht', hstep⟩ := h
  have hstep' : Execution.Core.Step P (fun _ _ _ _ => False)
      ⟨L.stubS s, (t.config s).frame, (t.config s).code⟩ ⟨σ', f', code'⟩ := by
    rw [← config_stub]
    exact hstep
  obtain ⟨s', hσ, hf, hs⟩ := consumer_step hstep'
  refine ⟨s', hσ, hf, f', code', ht', ?_⟩
  rw [Thread.config_eta s t]
  exact hs

/-- **Provider steps at top level are linked steps in the consumer's callout context.** -/
theorem internal_prov {s s' : Store Nat} {Y : List Admin} {t' : Thread} (htop : TopOK Y)
    (h : InternalP P (s, .active {} Y) (s', t')) :
    ∃ Y', t' = .active {} Y' ∧ TopOK Y' ∧ s'.funcs = s.funcs ∧
      ∀ (fC : Frame) (E : Ctx), InternalP P (s, .active fC (E.fill Y)) (s', .active fC (E.fill Y')) := by
  obtain ⟨f', Y', rfl, hstep⟩ := h
  obtain ⟨hf, htop', hg⟩ := step_reframe hstep htop
  have hf' : f' = {} := hf
  subst hf'
  refine ⟨Y', rfl, htop', (Step.framesLocal hstep).1, fun fC E => ⟨fC, E.fill Y', rfl, ?_⟩⟩
  exact Ctx.step_fill E (fun g => hg g) fC

/-- Resumption at a callout fills its context. -/
theorem resume_active {s : Store Nat} {t : Thread} {E : Ctx} {a h : Nat} {args : List Val}
    (hd : decompose? s (t.config s).code = some (E, a, h, args)) (r : Result) :
    resumeResult s t r = .active (t.config s).frame (E.fill r.toAdmin) := by
  unfold resumeResult
  simp only
  rw [hd]

/-- **A stub call of the consumer is one linked `call_ref` step into the provider.** -/
theorem call_internal {s : Store Nat} (hl : L.Layout s) {t : Thread} {E : Ctx} {a k : Nat}
    {args : List Val} (hd : decompose? (L.stubS s) (t.config (L.stubS s)).code = some (E, a, k, args))
    {a' : Nat} (ht : L.target k = some a') {fi : FuncInst Nat} {ps rs : Ty (.list .val)}
    {code : Func} (hf : (L.unstubS (L.stubS s)).funcs[a']? = some fi)
    (he : Expand fi.type (.func ps rs)) (hn : args.length = ps.length) (hc : fi.code = .wasm code) :
    InternalP P (s, t) (s, .active (t.config (L.stubS s)).frame (E.fill (callCode fi rs code args))) := by
  have hcode : (t.config (L.stubS s)).code = (t.config s).code := by rw [config_stub]
  have hframe : (t.config (L.stubS s)).frame = (t.config s).frame := by rw [config_stub]
  obtain ⟨ha, fi₀, c, ps₀, rs₀, yy, hf₀, -, -, -, -, hX, hyy⟩ := stub_callout hl hd ht
  subst ha
  rw [unstub_stub hl] at hf
  have hfi : fi₀ = fi := Option.some.inj (hf₀.symm.trans hf)
  subst hfi
  refine ⟨_, _, rfl, ?_⟩
  have hstep : Execution.Core.Step P (fun _ _ _ _ => False)
      ⟨s, (t.config s).frame, E.fill (vals args ++ [.ref (.func a'), yy])⟩
      ⟨s, (t.config s).frame, E.fill (callCode fi₀ rs code args)⟩ :=
    Ctx.step_fill E (fun g => Step.callRefFunc hyy hf₀ he hn hc) _
  rw [Thread.config_eta s t, hframe, ← hcode, hX]
  exact hstep

/-- **The provider's callouts in the linked thread.** -/
theorem callout_comp {s : Store Nat} {Y : List Admin} {h : Nat} {args : List Val}
    (hco : CalloutAt s (.active {} Y) h args) :
    ∃ E' : Ctx, (∀ r, resumeResult s (.active {} Y) r = .active {} (E'.fill r.toAdmin)) ∧
      (TopOK Y → ∀ r : Result, TopOK (E'.fill r.toAdmin)) ∧
      ∀ (fC : Frame) (E : Ctx), CalloutAt s (.active fC (E.fill Y)) h args ∧
        ∀ r, resumeResult s (.active fC (E.fill Y)) r = .active fC (E.fill (E'.fill r.toAdmin)) := by
  obtain ⟨E', a, hd⟩ := hco
  obtain ⟨fi, yy, ps, rs, hf, hcode, hyy, he, hn, hY⟩ := decompose?_sound hd
  have hY' : (Thread.active {} Y).config s = ⟨s, {}, Y⟩ := rfl
  have hYc : Y = E'.fill (vals args ++ [.ref (.func a), yy]) := by
    simpa [hY'] using hY
  refine ⟨E', fun r => resume_active hd r,
    fun htop r => topOK_fill (hYc ▸ htop) (TopOK.result_toAdmin r), fun fC E => ?_⟩
  have hd' : decompose? s ((Thread.active fC (E.fill Y)).config s).code =
      some (Ctx.comp E E', a, h, args) := by
    show decompose? s (E.fill Y) = _
    rw [hYc, ← Ctx.comp_fill]
    exact decompose?_fill _ hyy hf he hn hcode
  refine ⟨⟨_, _, hd'⟩, fun r => ?_⟩
  rw [resume_active hd' r, Ctx.comp_fill]
  rfl

end Silmaril.Proofs.Wasm.Game.ULink
