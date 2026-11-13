module

public import Silmaril.Proofs.Wasm.Replace.Congruence.Classify

/-!
# Finite runs across `Store.replaceFunc`

`steps_replace_forward` and `steps_replace_backward` transport a run that ends in a result
across the replacement, from a store satisfying `Reach`. The simulation is step for step except
at an invocation of `a`, where the two bodies are unrelated; there it jumps the whole callee
run, matched by `CallSim`.

To jump the callee, a run out of an invocation in a context is factored into a run of the
callee to a result and a run of the context filled with it (silmaril-lean's
`Rigid.steps_factor`). The rest of the run produced by the factorisation needs the simulation
again, and is not a syntactic suffix of the run. So, as in the source, each theorem proves the
simulation and the factorisation together, by one `Relation.ReflTransGen.head_induction_on`:
the induction hypothesis covers the suffix the factorisation produces, and no step-counted
reduction relation is needed.

Ported from an earlier development `Silmaril/Wasm/Equiv/Congruence.lean`. The one-step
inversion both factorisation halves start with is a lemma here (`rigid_step_plug_cases`).
-/

@[expose] public section

namespace Silmaril.Wasm.Replace

open Silmaril.Wasm.V1.Execution
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.V1 (Instr)

variable {H : Type}

/-- One step out of rigid code in a context happens at the hole, and leaves rigid code or a
result there. -/
theorem rigid_step_plug_cases {host : HostSemantics H} {s : Store H} {f : Frame}
    {Y : List Admin} {K : EvalCtx Silmaril.Wasm.V1.Instr} {e : Config H} (hrig : Rigid s Y)
    (hstep : Step host ⟨s, f, K.plug value Y⟩ e) :
    ∃ Y' : List Admin, (∀ g : Frame, Step host ⟨s, g, Y⟩ ⟨e.store, g, Y'⟩) ∧
      e = ⟨e.store, f, K.plug value Y'⟩ ∧ (Rigid e.store Y' ∨ ∃ r, Y' = result r) := by
  have hstep' : Step host ⟨s, f, values [] ++ K.plug value Y ++ []⟩
      ⟨e.store, e.frame, e.code⟩ := by simpa [Silmaril.Wasm.V1.Execution.values] using hstep
  obtain ⟨hframe, Y', hpoly, hcode⟩ := hrig.plug_inv K [] [] f e.frame e.store e.code hstep'
  have hcode' : e.code = K.plug value Y' := by simpa [Silmaril.Wasm.V1.Execution.values] using hcode
  have he : e = ⟨e.store, f, K.plug value Y'⟩ := by rw [← hframe, ← hcode']
  exact ⟨Y', hpoly, he, hrig.step_classify (hpoly f)⟩

/-- An invocation of `a` in a context is rigid code in that context. -/
theorem InvokesAt.rigid {s : Store H} {a : FuncAddr} {X : List Admin} (h : InvokesAt s a X) :
    ∃ (K : EvalCtx Silmaril.Wasm.V1.Instr) (args : List Runtime.Value),
      X = K.plug value (values args ++ [.invoke a]) ∧ Rigid s (values args ++ [.invoke a]) := by
  obtain ⟨K, args, hX, hsat⟩ := h
  exact ⟨K, args, hX, Rigid.invoke hsat⟩

/-- The callee of an invocation, run to completion at the empty frame, completes in any
context and at any frame. -/
theorem steps_plug_invoke {host : HostSemantics H} {s s₂ : Store H} {a : FuncAddr}
    {args : List Runtime.Value} {r : Runtime.Result}
    (h : Steps host (invoke s a args) ⟨s₂, ⟨[], {}⟩, result r⟩) (K : EvalCtx Silmaril.Wasm.V1.Instr) (f : Frame) :
    Steps host ⟨s, f, K.plug value (values args ++ [.invoke a])⟩
      ⟨s₂, f, K.plug value (result r)⟩ :=
  Sealed.steps_plug h (by simpa using sealed_invoke args a) K f

/-! ## The forward simulation -/

/-- The forward simulation of a run to `d` from `⟨s, f, X⟩`: it is matched after the
replacement. -/
def SimFwd (host : HostSemantics H) (a b : FuncAddr) (d : Config H) (s : Store H) (f : Frame)
    (X : List Admin) : Prop :=
  Steps host ⟨s.replaceFunc a b, f, X⟩ ⟨d.store.replaceFunc a b, d.frame, d.code⟩

/-- The forward factorisation of a run to `d` from `⟨s, f, X⟩`: if `X` is rigid code `Y` in a
context, the run passes through a result of `Y`, and the rest is matched after the
replacement. -/
def FactorsFwd (host : HostSemantics H) (a b : FuncAddr) (d : Config H) (s : Store H)
    (f : Frame) (X : List Admin) : Prop :=
  ∀ (K : EvalCtx Silmaril.Wasm.V1.Instr) (Y : List Admin), X = K.plug value Y → Rigid s Y →
    ∃ (s₂ : Store H) (r' : Runtime.Result),
      (∀ g : Frame, Steps host ⟨s, g, Y⟩ ⟨s₂, g, result r'⟩) ∧
      SimFwd host a b d s₂ f (K.plug value (result r'))

/-- Both forward properties at every decomposition of `c` with a store satisfying `Reach`: the
motive of the forward induction. -/
def FwdAt (host : HostSemantics H) (Reach : Store H → Prop) (a b : FuncAddr) (d c : Config H) :
    Prop :=
  ∀ (s : Store H) (f : Frame) (X : List Admin), c = ⟨s, f, X⟩ → Reach s →
    FactorsFwd host a b d s f X ∧ SimFwd host a b d s f X

/-- The forward factorisation after one step, from the motive at its target. -/
theorem factorsFwd_head {host : HostSemantics H} {Reach : Store H → Prop} {a b : FuncAddr}
    {d e : Config H} {s : Store H} {f : Frame} {X : List Admin}
    (hstep : Step host ⟨s, f, X⟩ e) (ih : FwdAt host Reach a b d e) (hreach : Reach e.store) :
    FactorsFwd host a b d s f X := by
  intro K Y hX hrig
  obtain ⟨Y', hpoly, he, hcase⟩ := rigid_step_plug_cases hrig (hX ▸ hstep)
  rcases hcase with hrig' | ⟨r', hY'⟩
  · obtain ⟨s₂, r'', hsub, htail⟩ := (ih e.store f _ he hreach).1 K Y' rfl hrig'
    exact ⟨s₂, r'', fun g => (hpoly g).steps.trans (hsub g), htail⟩
  · have he' : e = ⟨e.store, f, K.plug value (result r')⟩ := by rw [he, hY']
    exact ⟨e.store, r', fun g => hY' ▸ (hpoly g).steps, (ih e.store f _ he' hreach).2⟩

/-- The forward simulation after one step, from the factorisation here and the motive at its
target. -/
theorem simFwd_head {host : HostSemantics H} {Reach : Store H → Prop} {a b : FuncAddr}
    (hhost : HostRespectsReplace host a b) (hsim : CallSimOn Reach host a b)
    (htyp : SameFuncTypeOn Reach a b) {d e : Config H} {s : Store H} {f : Frame}
    {X : List Admin} (hreach : Reach s) (hstep : Step host ⟨s, f, X⟩ e)
    (ih : FwdAt host Reach a b d e) (hreach' : Reach e.store)
    (hfact : FactorsFwd host a b d s f X) : SimFwd host a b d s f X := by
  rcases Step.classify_replace hhost hstep (htyp s hreach) with hinv | htrans
  · obtain ⟨K, args, (hX : X = _), hrig⟩ := hinv.rigid
    obtain ⟨s₂, r', hsub, htail⟩ := hfact K _ hX hrig
    have hcall : Steps host (invoke (s.replaceFunc a b) a args)
        ⟨s₂.replaceFunc a b, ⟨[], {}⟩, result r'⟩ := (hsim s hreach).1 args s₂ r' (hsub _)
    show Steps host ⟨s.replaceFunc a b, f, X⟩ _
    rw [hX]
    exact (steps_plug_invoke hcall K f).trans htail
  · exact htrans.steps.trans (ih e.store e.frame e.code rfl hreach').2

/-- **The forward simulation, fused with its factorisation.** From a store satisfying `Reach`,
a run to a result is matched after the replacement (`SimFwd`), and a run out of rigid code in a
context factors through a result of that code (`FactorsFwd`). -/
theorem steps_replace_forward {host : HostSemantics H} {Reach : Store H → Prop}
    {a b : FuncAddr} (hhost : HostRespectsReplace host a b) (hcl : StepClosed host Reach)
    (hsim : CallSimOn Reach host a b) (htyp : SameFuncTypeOn Reach a b)
    {d : Config H} (hd : ∃ r : Runtime.Result, d.code = result r) :
    ∀ {c : Config H}, Steps host c d → FwdAt host Reach a b d c := by
  intro c h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro s f X hc _
    obtain ⟨r, hr⟩ := hd
    have hX' : X = result r := (congrArg Config.code hc).symm.trans hr
    exact ⟨fun K Y hX hrig => absurd (hX.symm.trans hX') (hrig.plug_ne_result K r),
      by rw [hc]; exact Relation.ReflTransGen.refl⟩
  | @head c₀ e hstep _ ih =>
    intro s f X hc hreach
    have hstep₀ : Step host ⟨s, f, X⟩ e := hc ▸ hstep
    have hreach' : Reach e.store := hcl hreach hstep₀
    have hfact : FactorsFwd host a b d s f X := factorsFwd_head hstep₀ ih hreach'
    exact ⟨hfact, simFwd_head hhost hsim htyp hreach hstep₀ ih hreach' hfact⟩

/-! ## The backward simulation

`Store.replaceFunc a b` is not injective, which shapes the statements. The simulation ends in
some store `sd` whose replacement is the final store. The factorisation quantifies its rest of
the run over every original store `s₂` whose replacement the callee returned in, because
`CallSim` hands back some such store, not necessarily the one the induction made; and it ranges
over an arbitrary store `t`, since the stores inside a callee run are jumped by `CallSim`. -/

/-- The backward simulation of a run to `d` from `⟨s.replaceFunc a b, f, X⟩`: it comes from a
run out of `⟨s, f, X⟩` whose final store agrees with `d`'s after the replacement. -/
def SimBwd (host : HostSemantics H) (a b : FuncAddr) (d : Config H) (s : Store H) (f : Frame)
    (X : List Admin) : Prop :=
  ∃ sd : Store H, d.store = sd.replaceFunc a b ∧ Steps host ⟨s, f, X⟩ ⟨sd, d.frame, d.code⟩

/-- The backward factorisation of a run to `d` from `⟨t, f, X⟩`. -/
def FactorsBwd (host : HostSemantics H) (Reach : Store H → Prop) (a b : FuncAddr)
    (d : Config H) (t : Store H) (f : Frame) (X : List Admin) : Prop :=
  ∀ (K : EvalCtx Silmaril.Wasm.V1.Instr) (Y : List Admin), X = K.plug value Y → Rigid t Y →
    ∃ (t₂ : Store H) (r' : Runtime.Result),
      (∀ g : Frame, Steps host ⟨t, g, Y⟩ ⟨t₂, g, result r'⟩) ∧
      ∀ s₂ : Store H, t₂ = s₂.replaceFunc a b → Reach s₂ →
        SimBwd host a b d s₂ f (K.plug value (result r'))

/-- The motive of the backward induction: the factorisation at every decomposition of `c`, and
the simulation at every decomposition whose store is a replacement of one satisfying `Reach`. -/
def BwdAt (host : HostSemantics H) (Reach : Store H → Prop) (a b : FuncAddr) (d c : Config H) :
    Prop :=
  (∀ (t : Store H) (f : Frame) (X : List Admin), c = ⟨t, f, X⟩ →
      FactorsBwd host Reach a b d t f X) ∧
    ∀ (s : Store H) (f : Frame) (X : List Admin), c = ⟨s.replaceFunc a b, f, X⟩ → Reach s →
      SimBwd host a b d s f X

/-- The backward factorisation after one step, from the motive at its target. -/
theorem factorsBwd_head {host : HostSemantics H} {Reach : Store H → Prop} {a b : FuncAddr}
    {d e : Config H} {t : Store H} {f : Frame} {X : List Admin}
    (hstep : Step host ⟨t, f, X⟩ e) (ih : BwdAt host Reach a b d e) :
    FactorsBwd host Reach a b d t f X := by
  intro K Y hX hrig
  obtain ⟨Y', hpoly, he, hcase⟩ := rigid_step_plug_cases hrig (hX ▸ hstep)
  rcases hcase with hrig' | ⟨r', hY'⟩
  · obtain ⟨t₂, r'', hsub, htail⟩ := ih.1 e.store f _ he K Y' rfl hrig'
    exact ⟨t₂, r'', fun g => (hpoly g).steps.trans (hsub g), htail⟩
  · refine ⟨e.store, r', fun g => hY' ▸ (hpoly g).steps, fun s₂ hs₂ hreach₂ => ?_⟩
    have he' : e = ⟨s₂.replaceFunc a b, f, K.plug value (result r')⟩ := by rw [he, hY', hs₂]
    exact ih.2 s₂ f _ he' hreach₂

/-- The backward simulation after one step, from the factorisation here and the motive at its
target. -/
theorem simBwd_head {host : HostSemantics H} {Reach : Store H → Prop} {a b : FuncAddr}
    (hhost : HostRespectsReplace host a b) (hcl : StepClosed host Reach)
    (hsim : CallSimOn Reach host a b) (htyp : SameFuncTypeOn Reach a b) {d e : Config H}
    {s : Store H} {f : Frame} {X : List Admin} (hreach : Reach s)
    (hstep : Step host ⟨s.replaceFunc a b, f, X⟩ e) (ih : BwdAt host Reach a b d e)
    (hfact : FactorsBwd host Reach a b d (s.replaceFunc a b) f X) :
    SimBwd host a b d s f X := by
  rcases Step.classify_replace_back hhost hstep s rfl (htyp s hreach) with
    hinv | ⟨s₁, hs₁, hstep'⟩
  · obtain ⟨K, args, (hX : X = _), hrig⟩ := hinv.rigid
    obtain ⟨t₂, r', hsub, htail⟩ := hfact K _ hX hrig
    obtain ⟨s₂, hs₂, horig⟩ := (hsim s hreach).2.1 args t₂ r' (hsub _)
    obtain ⟨sd, hsd, hrun⟩ := htail s₂ hs₂ (hcl.steps horig hreach)
    have hrun' : Steps host ⟨s, f, X⟩ ⟨sd, d.frame, d.code⟩ := by
      rw [hX]
      exact (steps_plug_invoke horig K f).trans hrun
    exact ⟨sd, hsd, hrun'⟩
  · have he : e = ⟨s₁.replaceFunc a b, e.frame, e.code⟩ := by rw [← hs₁]
    obtain ⟨sd, hsd, hrun⟩ := ih.2 s₁ e.frame e.code he (hcl hreach hstep')
    exact ⟨sd, hsd, hstep'.steps.trans hrun⟩

/-- **The backward simulation, fused with its factorisation.** A run to a result out of a
replaced store satisfying `Reach` comes from a run before the replacement (`SimBwd`), and a run
out of rigid code in a context factors through a result of that code (`FactorsBwd`). -/
theorem steps_replace_backward {host : HostSemantics H} {Reach : Store H → Prop}
    {a b : FuncAddr} (hhost : HostRespectsReplace host a b) (hcl : StepClosed host Reach)
    (hsim : CallSimOn Reach host a b) (htyp : SameFuncTypeOn Reach a b)
    {d : Config H} (hd : ∃ r : Runtime.Result, d.code = result r) :
    ∀ {c : Config H}, Steps host c d → BwdAt host Reach a b d c := by
  intro c h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    obtain ⟨r, hr⟩ := hd
    refine ⟨fun t f X hc K Y hX hrig => ?_, fun s f X hc _ => ⟨s, by rw [hc], by rw [hc]⟩⟩
    exact absurd (hX.symm.trans ((congrArg Config.code hc).symm.trans hr))
      (hrig.plug_ne_result K r)
  | @head c₀ e hstep _ ih =>
    have hfact : ∀ (t : Store H) (f : Frame) (X : List Admin), c₀ = ⟨t, f, X⟩ →
        FactorsBwd host Reach a b d t f X :=
      fun t f X hc => factorsBwd_head (hc ▸ hstep) ih
    refine ⟨hfact, fun s f X hc hreach => ?_⟩
    exact simBwd_head hhost hcl hsim htyp hreach (hc ▸ hstep) ih (hfact _ f X hc)

end Silmaril.Wasm.Replace
