module

public import Silmaril.Wasm.FX.Logic.Host.Defs
public import Silmaril.Wasm.FX.Logic.EveryRun.Thms
public import Silmaril.Wasm.SingleThreaded.Locality

/-!
# Host calls in the every-run WasmFX logic: the split and the transfer

* **`stepFX'_split_host`**: every step of `StepFX' P host fx` is a step without host calls
  (`StepFX' P noHost fx`) or a host-call step (`HostStep`), by `Step.split_host` at the Core
  rule and induction through the context rules;
* **`tsafeH_of_tsafe`**, `safeH_of_safe`: a proof in the host-free logic holds with any host
  relation for code that reaches no host call (`NoHostCall`);
* `tsafeH_result`, `tsafeH_not_infinite`: adequacy with host calls.

The rule for a host call itself (the host's outcomes continuing in the evaluation context) is
open: it needs the inversion of `decompose?` at FX code.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Logic.Host

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.FX.Logic (OutcomeFX PostFX Conts)
open Silmaril.Wasm.FX.Logic.EveryRun (Safe TSafe)
open Silmaril.Wasm.FX.Logic.Host
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}
  {Q : PostFX H}

theorem blockFX_noHost_eq : blockFX (noHost (H := H)) fx = noHost := by
  funext h s vs out
  simp [blockFX]

/-- A Core step under `blockFX host fx` is a host-free step or a host call. -/
theorem core_split {s s' : Store H} {K : Conts} {f f' : Frame} {cs cs' : List Admin}
    (h : Step P (blockFX host fx) ⟨s, f, cs⟩ ⟨s', f', cs'⟩) :
    StepFX' P noHost fx ⟨s, K, f, cs.map .core⟩ ⟨s', K, f', cs'.map .core⟩ ∨
      HostStep P host fx ⟨s, K, f, cs.map .core⟩ ⟨s', K, f', cs'.map .core⟩ := by
  rcases Silmaril.Wasm.SingleThreaded.Step.split_host h with h' | ⟨E, a, hh, args, hd, hr⟩
  · refine Or.inl (StepFX'.core ?_)
    rw [blockFX_noHost_eq]
    exact h'
  · exact Or.inr (HostStep.call (d := ⟨s', f', cs'⟩) hd hr)

/-- **Every `StepFX'` step is host-free or a host call.** -/
theorem stepFX'_split_host {c c' : ConfigFX H} (h : StepFX' P host fx c c') :
    StepFX' P noHost fx c c' ∨ HostStep P host fx c c' := by
  induction h with
  | core h => exact core_split h
  | seq _ hne ih => exact ih.elim (fun h => .inl (.seq h hne)) (fun h => .inr (.seq h hne))
  | ctxLabel _ ih => exact ih.elim (fun h => .inl (.ctxLabel h)) (fun h => .inr (.ctxLabel h))
  | ctxFrame _ ih => exact ih.elim (fun h => .inl (.ctxFrame h)) (fun h => .inr (.ctxFrame h))
  | ctxHandler _ ih =>
    exact ih.elim (fun h => .inl (.ctxHandler h)) (fun h => .inr (.ctxHandler h))
  | block hbt hm => exact .inl (.block hbt hm)
  | loop hbt hm => exact .inl (.loop hbt hm)
  | ifTrue hc => exact .inl (.ifTrue hc)
  | ifFalse => exact .inl .ifFalse
  | labelVals => exact .inl .labelVals
  | brLabelZero hl hn => exact .inl (.brLabelZero hl hn)
  | brLabelSucc hl => exact .inl (.brLabelSucc hl)
  | brHandler => exact .inl .brHandler
  | returnLabel => exact .inl .returnLabel
  | returnHandler => exact .inl .returnHandler
  | frameVals hn => exact .inl (.frameVals hn)
  | returnFrame hn => exact .inl (.returnFrame hn)
  | handlerVals => exact .inl .handlerVals
  | dropCont => exact .inl .dropCont
  | trapSeq hne => exact .inl (.trapSeq hne)
  | trapLabel => exact .inl .trapLabel
  | trapFrame => exact .inl .trapFrame
  | trapHandler => exact .inl .trapHandler
  | throwSeq hne => exact .inl (.throwSeq hne)
  | throwLabel => exact .inl .throwLabel
  | throwFrame => exact .inl .throwFrame
  | throwHandler => exact .inl .throwHandler
  | invoke hc hf hcode hfx hn => exact .inl (.invoke hc hf hcode hfx hn)
  | contNew hf => exact .inl (.contNew hf)
  | contNewNull => exact .inl .contNewNull
  | contBind hk => exact .inl (.contBind hk)
  | contBindNull => exact .inl .contBindNull
  | contBindUsed hk => exact .inl (.contBindUsed hk)
  | resume hk hr => exact .inl (.resume hk hr)
  | resumeNull => exact .inl .resumeNull
  | resumeUsed hk => exact .inl (.resumeUsed hk)
  | resumeThrow hk ht hr => exact .inl (.resumeThrow hk ht hr)
  | resumeThrowNull => exact .inl .resumeThrowNull
  | suspend ht hE hc => exact .inl (.suspend ht hE hc)
  | switch hk ht hE hc => exact .inl (.switch hk ht hE hc)

/-! ## Transfer -/

theorem noHostCall_step {c d : ConfigFX H} (h : NoHostCall P host fx c)
    (hs : StepFX' P noHost fx c d) : NoHostCall P host fx d :=
  fun e he => h e (Relation.ReflTransGen.head hs he)

theorem noHostCall_not_host {c d : ConfigFX H} (h : NoHostCall P host fx c) :
    ¬ HostStep P host fx c d :=
  h c .refl d

/-- A step from code that reaches no host call is a host-free step. -/
theorem noHostCall_noHost_step {c d : ConfigFX H} (h : NoHostCall P host fx c)
    (hs : StepFX' P host fx c d) : StepFX' P noHost fx c d :=
  (stepFX'_split_host hs).resolve_right (noHostCall_not_host h)

/-- **A host-free proof holds with any host relation**, for code that reaches no host call. -/
theorem tsafeH_of_tsafe {c : ConfigFX H} (h : TSafe P fx Q c) (hn : NoHostCall P host fx c) :
    TSafeH P host fx Q c := by
  induction h with
  | intro hq _ ih =>
    exact .intro hq fun c' hs => ih c' (noHostCall_noHost_step hn hs) (noHostCall_step hn
        (noHostCall_noHost_step hn hs))

/-- **A host-free step-indexed proof holds with any host relation**, without host calls. -/
theorem safeH_of_safe : ∀ {n : Nat} {c : ConfigFX H}, Safe P fx Q n c →
    NoHostCall P host fx c → SafeH P host fx Q n c
  | 0, _, _, _ => trivial
  | _ + 1, _, h, hn => ⟨h.1, fun _ hs =>
      safeH_of_safe (h.2 _ (noHostCall_noHost_step hn hs))
        (noHostCall_step hn (noHostCall_noHost_step hn hs))⟩

/-! ## Stores whose functions are all FX functions -/

/-- A host-call step calls a function with host code that is not an FX function. -/
theorem hostStep_callee {c c' : ConfigFX H} (h : HostStep P host fx c c') :
    ∃ (a : Nat) (fi : FuncInst H) (hh : H), c.store.funcs[a]? = some fi ∧ fi.code = .host hh ∧
      fx hh = none := by
  induction h with
  | call hd hr =>
    obtain ⟨fi, -, -, -, hf, hcode, -⟩ := Silmaril.Wasm.SingleThreaded.decompose?_sound hd
    rcases hr with ⟨_, _, hb, -⟩ | ⟨hb, -⟩
    · exact ⟨_, fi, _, hf, hcode, hb.1⟩
    · exact ⟨_, fi, _, hf, hcode, hb.1⟩
  | seq _ _ ih => exact ih
  | ctxLabel _ ih => exact ih
  | ctxFrame _ ih => exact ih
  | ctxHandler _ ih => exact ih

/-- No host-call step from a store whose host-code functions are all FX functions. -/
theorem no_hostStep {c c' : ConfigFX H} (hs : AllFX fx c.store) : ¬ HostStep P host fx c c' := by
  intro h
  obtain ⟨a, fi, hh, hf, hcode, hn⟩ := hostStep_callee h
  exact hs a fi hh hf hcode hn

/-- A host-free step keeps the store's functions. -/
theorem step_funcs {c c' : ConfigFX H} (h : StepFX' P noHost fx c c') :
    c'.store.funcs = c.store.funcs := by
  induction h with
  | core h =>
    rw [blockFX_noHost_eq] at h
    exact (Silmaril.Wasm.SingleThreaded.Step.framesLocal h).1
  | seq _ _ ih => exact ih
  | ctxLabel _ ih => exact ih
  | ctxFrame _ ih => exact ih
  | ctxHandler _ ih => exact ih
  | _ => rfl

theorem steps_funcs {c c' : ConfigFX H} (h : StepsFX' P noHost fx c c') :
    c'.store.funcs = c.store.funcs := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact (step_funcs hs).trans ih

/-- **Code whose store has only FX functions reaches no host call**, for every host relation. -/
theorem noHostCall_of_allFX {c : ConfigFX H} (hs : AllFX fx c.store) :
    NoHostCall P host fx c := by
  intro d hd d' h
  refine no_hostStep (fun a fi hh hf hcode => hs a fi hh ?_ hcode) h
  rw [← steps_funcs hd]
  exact hf

/-! ## Adequacy with host calls -/

theorem tsafeH_steps {c d : ConfigFX H} (h : TSafeH P host fx Q c)
    (hr : StepsFX' P host fx c d) : TSafeH P host fx Q d := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => cases ih with | intro _ hs' => exact hs' _ hs

/-- **Every finished run with host calls satisfies the postcondition.** -/
theorem tsafeH_result {c d : ConfigFX H} {r : Result} (h : TSafeH P host fx Q c)
    (hr : StepsFX' P host fx c d) (hd : d.code = r.toAdmin.map .core) :
    Q d.store d.conts d.frame (OutcomeFX.ofResult r) := by
  cases tsafeH_steps h hr with
  | intro hq _ =>
    exact hq _ (hd ▸ Silmaril.Proofs.Wasm.FX.Logic.EveryRun.stops_ofResult d.store d.frame r)

/-- **No infinite run with host calls.** -/
theorem tsafeH_not_infinite {c : ConfigFX H} (h : TSafeH P host fx Q c) :
    ¬ Silmaril.InfiniteTrace (StepFX' P host fx) c := by
  induction h with
  | intro _ _ ih =>
    intro hi
    obtain ⟨b, hb, hi'⟩ := hi.unfold
    exact ih b hb hi'

/-- **Exact behaviours with host calls** from total safety and one run. -/
theorem tsafeH_behaviours_eq {c : ConfigFX H} {r₀ : Result} (h : TSafeH P host fx Q c)
    (hQ : ∀ s K f o, Q s K f o → o = OutcomeFX.ofResult r₀)
    (hm : r₀.toBehaviour ∈ behavioursFX' P host fx c) :
    behavioursFX' P host fx c = {r₀.toBehaviour} := by
  ext b
  refine ⟨fun hb => ?_, fun hb => (Set.mem_singleton_iff.mp hb) ▸ hm⟩
  rcases hb with ⟨d, r, hr, hd, rfl⟩ | ⟨-, hi⟩
  · rw [Silmaril.Proofs.Wasm.FX.Logic.EveryRun.ofResult_inj (hQ _ _ _ _ (tsafeH_result h hr hd))]
    rfl
  · exact (tsafeH_not_infinite h hi).elim

/-- **Exact behaviours with any host relation**, from a host-free proof, for a program whose
store has only FX functions. -/
theorem tsafe_behaviours_eq_host {c : ConfigFX H} {r₀ : Result} (h : TSafe P fx Q c)
    (hs : AllFX fx c.store) (hQ : ∀ s K f o, Q s K f o → o = OutcomeFX.ofResult r₀)
    (hm : r₀.toBehaviour ∈ behavioursFX' P host fx c) :
    behavioursFX' P host fx c = {r₀.toBehaviour} :=
  tsafeH_behaviours_eq (tsafeH_of_tsafe h (noHostCall_of_allFX hs)) hQ hm

end Silmaril.Proofs.Wasm.FX.Logic.Host
