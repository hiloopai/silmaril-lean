module

public import Silmaril.Proofs.Wasm.Replace.Congruence.Runs

/-!
# Divergence across `Store.replaceFunc`

`diverges_replace_forward` and `diverges_replace_backward` transport an infinite run across the
replacement, from a store satisfying `Reach`. Both are coinductions on the invariant
`DivInv F G`: the configuration diverges, or it runs in finitely many steps to one whose store
is `F σ` for a `σ` satisfying `Reach`, while `G σ` diverges from the same frame and code (`F`
and `G` are the identity and `Store.replaceFunc a b`, in one order or the other). The finite
prefix lets a callee run that `CallSim` jumps contribute many steps at once, though the
coinduction principle asks for one at a time. `divInv_coinduct` is the coinduction, shared by
both directions; `divFwd_progress` and `divBwd_progress` make one step.

At an invocation of `a`, the callee either diverges (then `CallSim` says the other callee
diverges, and `Sealed.diverges_plug` lifts it to the context) or returns (then `CallSim` matches
the run, and `steps_plug_invoke_head` takes its first step).

Ported from an earlier development `Silmaril/Wasm/Equiv/Congruence.lean`. The source's two
coinductions are one lemma here, and the first step of a matched callee run is taken from the
plugged run instead of from `Sealed.step`.
-/

@[expose] public section

namespace Silmaril.Wasm.Replace

open Silmaril.Wasm.V1.Execution
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.V1 (Instr)
open Silmaril (InfiniteTrace)

variable {H : Type}

/-- **Divergence of sealed code transports into any evaluation context**, at any frame: the
infinite analogue of `Sealed.steps_plug`. -/
theorem Sealed.diverges_plug {host : HostSemantics H} {s : Store H} {code : List Admin}
    (hc : Sealed code) (K : EvalCtx Silmaril.Wasm.V1.Instr) (f g : Frame)
    (h : Diverges host ⟨s, g, code⟩) : Diverges host ⟨s, f, K.plug value code⟩ := by
  refine InfiniteTrace.coinduct
    (fun c => ∃ (σ : Store H) (Y : List Admin), c = ⟨σ, f, K.plug value Y⟩ ∧ Sealed Y ∧
      Diverges host ⟨σ, g, Y⟩) ?_ ⟨s, code, rfl, hc, h⟩
  rintro c ⟨σ, Y, rfl, hse, hdv⟩
  obtain ⟨e, hstep, htail⟩ := hdv.unfold
  obtain ⟨(hframe : e.frame = g), hse', hpoly⟩ := Sealed.step hstep hse
  have htail' : Diverges host ⟨e.store, g, e.code⟩ := by
    have he : e = ⟨e.store, g, e.code⟩ := by rw [← hframe]
    exact he ▸ htail
  exact ⟨⟨e.store, f, K.plug value e.code⟩, Step.plug hpoly K f, e.store, e.code, rfl, hse',
    htail'⟩

/-- A diverging callee of an invocation makes the invocation diverge in any context. -/
theorem diverges_plug_invoke {host : HostSemantics H} {s : Store H} {a : FuncAddr}
    {args : List Runtime.Value} (h : Diverges host (invoke s a args)) (K : EvalCtx Silmaril.Wasm.V1.Instr)
    (f : Frame) : Diverges host ⟨s, f, K.plug value (values args ++ [.invoke a])⟩ :=
  Sealed.diverges_plug (by simpa using sealed_invoke args a) K f ⟨[], {}⟩ h

/-- A callee run to a result, in a context, starts with a step: the invocation is not a
result. -/
theorem steps_plug_invoke_head {host : HostSemantics H} {s s₂ : Store H} {a : FuncAddr}
    {args : List Runtime.Value} {r : Runtime.Result}
    (h : Steps host (invoke s a args) ⟨s₂, ⟨[], {}⟩, result r⟩)
    (hrig : Rigid s (values args ++ [.invoke a])) (K : EvalCtx Silmaril.Wasm.V1.Instr) (k : Frame) :
    ∃ c₁ : Config H, Step host ⟨s, k, K.plug value (values args ++ [.invoke a])⟩ c₁ ∧
      Steps host c₁ ⟨s₂, k, K.plug value (result r)⟩ := by
  rcases h.cases_head with heq | ⟨c₁, hstep₁, hrest₁⟩
  · exact absurd (congrArg Config.code heq) (hrig.plug_ne_result .hole r)
  · obtain ⟨-, hse₁, hpoly₁⟩ := Sealed.step hstep₁ (by simpa using sealed_invoke args a)
    exact ⟨_, Step.plug hpoly₁ K k, Sealed.steps_plug hrest₁ hse₁ K k⟩

/-- The coinduction invariant: `c` diverges, or it runs to `⟨F σ, k, Y⟩` with `Reach σ` while
`⟨G σ, k, Y⟩` diverges. -/
def DivInv (host : HostSemantics H) (Reach : Store H → Prop) (F G : Store H → Store H)
    (c : Config H) : Prop :=
  Diverges host c ∨ ∃ (σ : Store H) (k : Frame) (Y : List Admin),
    Reach σ ∧ Steps host c ⟨F σ, k, Y⟩ ∧ Diverges host ⟨G σ, k, Y⟩

/-- A diverging configuration takes a step within the invariant. -/
theorem DivInv.of_diverges {host : HostSemantics H} {Reach : Store H → Prop}
    {F G : Store H → Store H} {c : Config H} (h : Diverges host c) :
    ∃ c', Step host c c' ∧ DivInv host Reach F G c' := by
  obtain ⟨c', hstep, htail⟩ := h.unfold
  exact ⟨c', hstep, .inl htail⟩

/-- **The shared coinduction.** If every configuration `⟨F σ, k, Y⟩` with `Reach σ` and
`⟨G σ, k, Y⟩` diverging takes a step within the invariant, then it diverges. -/
theorem divInv_coinduct {host : HostSemantics H} {Reach : Store H → Prop}
    {F G : Store H → Store H}
    (progress : ∀ (σ : Store H) (k : Frame) (Y : List Admin), Reach σ →
      Diverges host ⟨G σ, k, Y⟩ → ∃ c', Step host ⟨F σ, k, Y⟩ c' ∧ DivInv host Reach F G c')
    {s : Store H} {f : Frame} {X : List Admin} (hreach : Reach s)
    (h : Diverges host ⟨G s, f, X⟩) : Diverges host ⟨F s, f, X⟩ := by
  refine InfiniteTrace.coinduct (DivInv host Reach F G) ?_ (.inr ⟨s, f, X, hreach, .refl, h⟩)
  rintro c (hdc | ⟨σ, k, Y, hreachσ, hsteps, hdv⟩)
  · exact DivInv.of_diverges hdc
  rcases hsteps.cases_head with heq | ⟨c₁, hstep₁, hrest₁⟩
  · exact heq ▸ progress σ k Y hreachσ hdv
  · exact ⟨c₁, hstep₁, .inr ⟨σ, k, Y, hreachσ, hrest₁, hdv⟩⟩

/-- One forward step: a diverging configuration out of a store satisfying `Reach` steps, after
the replacement, within the invariant. -/
theorem divFwd_progress {host : HostSemantics H} {Reach : Store H → Prop}
    {a b : FuncAddr} (hhost : HostRespectsReplace host a b) (hcl : StepClosed host Reach)
    (hsim : CallSimOn Reach host a b) (htyp : SameFuncTypeOn Reach a b)
    (σ : Store H) (k : Frame) (Y : List Admin) (hreach : Reach σ)
    (hdv : Diverges host ⟨id σ, k, Y⟩) :
    ∃ c', Step host ⟨σ.replaceFunc a b, k, Y⟩ c' ∧
      DivInv host Reach (Store.replaceFunc · a b) id c' := by
  obtain ⟨e, hstep, htail⟩ := hdv.unfold
  rcases Step.classify_replace hhost hstep (htyp σ hreach) with
    ⟨K, args, (hY : Y = _), hsat⟩ | htr
  · have hdv' : Diverges host ⟨σ, k, K.plug value (values args ++ [.invoke a])⟩ := hY ▸ hdv
    show ∃ c', Step host ⟨σ.replaceFunc a b, k, Y⟩ c' ∧ _
    rw [hY]
    rcases (Rigid.invoke hsat).diverges_factor K k hdv' with hinside | ⟨σ₂, r, hsub, hafter⟩
    · exact DivInv.of_diverges
        (diverges_plug_invoke (((hsim σ hreach).2.2 args).mp (hinside _)) K k)
    · have hcall : Steps host (invoke (σ.replaceFunc a b) a args)
          ⟨σ₂.replaceFunc a b, ⟨[], {}⟩, result r⟩ := (hsim σ hreach).1 args σ₂ r (hsub _)
      have hrig' : Rigid (σ.replaceFunc a b) (values args ++ [.invoke a]) :=
        Rigid.invoke (saturated_replaceFunc (htyp σ hreach) hsat)
      obtain ⟨c₁, hstep₁, hrest₁⟩ := steps_plug_invoke_head hcall hrig' K k
      exact ⟨c₁, hstep₁, .inr ⟨σ₂, k, _, hcl.steps (hsub ⟨[], {}⟩) hreach, hrest₁, hafter⟩⟩
  · exact ⟨_, htr, .inr ⟨e.store, e.frame, e.code, hcl hreach hstep, .refl, htail⟩⟩

/-- One backward step: a diverging configuration out of a replaced store satisfying `Reach`
steps, before the replacement, within the invariant. -/
theorem divBwd_progress {host : HostSemantics H} {Reach : Store H → Prop}
    {a b : FuncAddr} (hhost : HostRespectsReplace host a b) (hcl : StepClosed host Reach)
    (hsim : CallSimOn Reach host a b) (htyp : SameFuncTypeOn Reach a b)
    (σ : Store H) (k : Frame) (Y : List Admin) (hreach : Reach σ)
    (hdv : Diverges host ⟨σ.replaceFunc a b, k, Y⟩) :
    ∃ c', Step host ⟨id σ, k, Y⟩ c' ∧ DivInv host Reach id (Store.replaceFunc · a b) c' := by
  obtain ⟨e, hstep, htail⟩ := hdv.unfold
  rcases Step.classify_replace_back hhost hstep σ rfl (htyp σ hreach) with
    ⟨K, args, (hY : Y = _), hsat⟩ | ⟨σ₁, hs₁, hstep'⟩
  · have hdv' : Diverges host ⟨σ.replaceFunc a b, k,
        K.plug value (values args ++ [.invoke a])⟩ := hY ▸ hdv
    show ∃ c', Step host ⟨σ, k, Y⟩ c' ∧ _
    rw [hY]
    rcases (Rigid.invoke hsat).diverges_factor K k hdv' with hinside | ⟨t₂, r, hsub, hafter⟩
    · exact DivInv.of_diverges
        (diverges_plug_invoke (((hsim σ hreach).2.2 args).mpr (hinside _)) K k)
    · obtain ⟨σ₂, hσ₂, hcall⟩ := (hsim σ hreach).2.1 args t₂ r (hsub _)
      have hrig : Rigid σ (values args ++ [.invoke a]) :=
        Rigid.invoke (saturated_of_replaceFunc (htyp σ hreach) hsat)
      have hafter' : Diverges host ⟨σ₂.replaceFunc a b, k, K.plug value (result r)⟩ :=
        hσ₂ ▸ hafter
      obtain ⟨c₁, hstep₁, hrest₁⟩ := steps_plug_invoke_head hcall hrig K k
      exact ⟨c₁, hstep₁, .inr ⟨σ₂, k, _, hcl.steps hcall hreach, hrest₁, hafter'⟩⟩
  · have htail' : Diverges host ⟨σ₁.replaceFunc a b, e.frame, e.code⟩ := hs₁ ▸ htail
    exact ⟨_, hstep', .inr ⟨σ₁, e.frame, e.code, hcl hreach hstep', .refl, htail'⟩⟩

/-- **Forward divergence.** An infinite run out of a store satisfying `Reach` is matched by
one after the replacement. -/
theorem diverges_replace_forward {host : HostSemantics H} {Reach : Store H → Prop}
    {a b : FuncAddr} (hhost : HostRespectsReplace host a b) (hcl : StepClosed host Reach)
    (hsim : CallSimOn Reach host a b) (htyp : SameFuncTypeOn Reach a b)
    {s : Store H} {f : Frame} {X : List Admin} (hreach : Reach s)
    (h : Diverges host ⟨s, f, X⟩) : Diverges host ⟨s.replaceFunc a b, f, X⟩ :=
  divInv_coinduct (F := (Store.replaceFunc · a b)) (G := id)
    (divFwd_progress hhost hcl hsim htyp) hreach h

/-- **Backward divergence.** An infinite run out of a replaced store satisfying `Reach` comes
from one before the replacement. -/
theorem diverges_replace_backward {host : HostSemantics H} {Reach : Store H → Prop}
    {a b : FuncAddr} (hhost : HostRespectsReplace host a b) (hcl : StepClosed host Reach)
    (hsim : CallSimOn Reach host a b) (htyp : SameFuncTypeOn Reach a b)
    {s : Store H} {f : Frame} {X : List Admin} (hreach : Reach s)
    (h : Diverges host ⟨s.replaceFunc a b, f, X⟩) : Diverges host ⟨s, f, X⟩ :=
  divInv_coinduct (F := id) (G := (Store.replaceFunc · a b))
    (divBwd_progress hhost hcl hsim htyp) hreach h

end Silmaril.Wasm.Replace
