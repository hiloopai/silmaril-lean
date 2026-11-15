module

public import Silmaril.Proofs.Wasm.Abstract.HostEval.Whole

/-!
# Blocked and diverging host calls, seen in Core (proofs)

* `pending_stuck`: a configuration at a pending host call with no host outcome
  has no step, in any frame and profile: the `blocked` observation is Core
  stuckness. With `back_whole`, the stuck ends of a Core run of typed native code
  are exactly the ends of `EvalH` runs and the blocked host calls.
* `pendingDiv_diverges`: a configuration at a pending host call the host may
  diverge on diverges in Core (it stutters at the call, `call_ref-hostfunc-div`,
  under its values, labels and frames): the `hostDiv` observation is Core
  divergence.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostEval

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-- **A pending call is not a frame exit form.** -/
theorem pending_not_frameExit {s : Store H} {fi : Frame} {es out : List Admin} {n : Nat}
    (hp : Pending host s es) (hx : FrameExit s fi n es out) : False := by
  obtain ⟨vs, a, r, hes, ha, hk⟩ := pending_head hp
  have key : ∀ (ws : List Val) (b : Admin) (r' : List Admin), b.val? = none →
      es = vals ws ++ b :: r' → a = b := fun ws b r' hb he =>
    (Sim.vals_append_cons_inj ha hb (hes.symm.trans he)).2.1
  have nk : ∀ b, (b = .plain .return_ ∨ b.IsReturnCallRef) → a ≠ b := by
    rintro b hb rfl
    rcases hk with ⟨d, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rcases hb with h | h <;> cases h
  cases hx with
  | vals hn => exact pending_ne_vals hp _ rfl
  | @ret vs' ws rest' hn =>
    exact nk _ (.inl rfl) (key (vs' ++ ws) _ rest' rfl (by simp))
  | trap => exact pending_ne_trap hp rfl
  | throw x => exact pending_ne_throwing hp x rfl
  | @returnCallNull ws c' rest' hc =>
    exact nk _ (.inr hc) (key (ws ++ [.ref .null]) c' rest' (Admin.val?_of_isReturnCallRef hc)
      (by simp [vals, Val.toAdmin]))
  | @returnCallAddr vs' ws a' c' rest' fn ps rs hc hf he hn =>
    exact nk _ (.inr hc) (key (vs' ++ ws ++ [.ref (.func a')]) c' rest'
      (Admin.val?_of_isReturnCallRef hc) (by simp [vals, Val.toAdmin]))

/-- **A blocked host call is stuck**, in any frame and profile. -/
theorem pending_stuck {s : Store H} {es : List Admin} (hp : Pending host s es) :
    ∀ (f : Frame) (c : Config H), ¬ Step P host ⟨s, f, es⟩ c := by
  induction hp with
  | @call ws us a fi hh ps rs rest hf hcode he hn hno =>
    intro f c h
    have h' : Step P host ⟨s, f, vals (ws ++ us) ++ .ref (.func a) :: .callRefType fi.type :: rest⟩
        c := by simpa [List.append_assoc] using h
    obtain ⟨vs₁, vs₂, ps', rs', hsplit, he', hn', hres⟩ :=
      Step.callRef_host_inv_seq (r := .callRefType fi.type) trivial hf hcode h'
    have := (Validation.Expand.iff.1 he).symm.trans (Validation.Expand.iff.1 he')
    simp only [Option.some.injEq, Validation.Ty.func.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    obtain ⟨-, rfl⟩ := List.append_inj' hsplit (hn.trans hn'.symm)
    rcases hres with ⟨s', res, hhost, -⟩ | ⟨hhost, -⟩
    · exact hno _ hhost
    · exact hno _ hhost
  | @label ws n cont es rest hp ih =>
    intro f c h
    obtain ⟨c₀, h₀, -⟩ := Step.ctx_in_seq (X := .label n cont es) trivial (by simpa using h)
    rcases Step.label_inv h₀ with ⟨s', f', es', hin, -⟩ | ⟨out, hex, -⟩
    · exact ih f _ hin
    · exact pending_not_labelExit hp hex
  | @frame ws n F es rest hp ih =>
    intro f c h
    obtain ⟨c₀, h₀, -⟩ := Step.ctx_in_seq (X := .frame n F es) trivial (by simpa using h)
    rcases Step.frame_inv h₀ with ⟨s', F', es', hin, -⟩ | ⟨out, hex, -⟩
    · exact ih F _ hin
    · exact pending_not_frameExit hp hex

/-- A configuration at a pending call the host may diverge on steps to itself. -/
theorem pendingDiv_step_self {s : Store H} {es : List Admin} (hp : PendingDiv host s es) :
    ∀ f : Frame, Step P host ⟨s, f, es⟩ ⟨s, f, es⟩ := by
  induction hp with
  | @call ws us a fi hh ps rs rest hf hcode he hn hdiv =>
    intro f
    have := Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := host) ws rest
      (Step.callRefHostDiv (f := f) (c := .callRefType fi.type) trivial hf he hn hcode hdiv)
    simpa [List.append_assoc] using this
  | @label ws n cont es rest _ ih =>
    intro f
    simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := host) ws rest
      (Step.ctxtLabel (n := n) (cont := cont) (ih f))
  | @frame ws n F es rest _ ih =>
    intro f
    simpa using Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := host) ws rest
      (Step.ctxtFrame (f := f) (n := n) (ih F))

/-- **A host call the host may diverge on makes Core diverge**, in any frame and
profile: it stutters forever. -/
theorem pendingDiv_diverges {s : Store H} {f : Frame} {es : List Admin}
    (hp : PendingDiv host s es) : Diverges P host ⟨s, f, es⟩ :=
  ⟨fun _ => _, rfl, fun _ => pendingDiv_step_self hp f⟩

/-- The end of a native run is stuck: values, a branch, a return or a trap. -/
theorem endsAs_stuck {r : Store H × Frame × Binaryen.Flow} {c : Config H} (h : EndsAs r c) :
    ∀ c', ¬ Step P host c c' := by
  obtain ⟨o, he, hs, hf, hm⟩ := h
  rcases c with ⟨s, f, code⟩
  dsimp only at he hs hf
  by_cases hn : r.2.2.IsNormal
  · rcases hfl : r.2.2 with ws | _ | _ | _ | _ <;> rw [hfl] at hn hm <;>
      simp only [Binaryen.Flow.IsNormal] at hn
    rw [Interp.ends_normal hm he]
    exact fun _ => Sim.Step.not_vals
  · exact ends_abrupt_stuck he hm hn

/-- **The stuck ends of a Core run of typed native code**, deterministic profile:
exactly the ends of `EvalH` runs and the blocked host calls. -/
theorem stuck_iff {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {n : Nat} {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {labels : List Nat} {ret : Nat} {out : Option Nat} {c : Config H}
    (hS : Interp.StoreChk s.funcs)
    (hc : Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out)
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩)
    (hrun : StepsN (SingleThreaded.profile o) host n
      ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ c) :
    (∀ c', ¬ Step (SingleThreaded.profile o) host c c') ↔ BackOut host s f stk es c := by
  constructor
  · exact back_whole hT hH n es s f stk labels ret out c hS hc ht hrun
  · rintro (⟨r, -, he⟩ | ⟨hp, -⟩)
    · exact endsAs_stuck he
    · rcases c with ⟨s', f', code⟩
      exact pending_stuck hp f'

end Silmaril.Proofs.Wasm.Abstract.HostEval
