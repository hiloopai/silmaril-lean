module

public import Silmaril.Proofs.Wasm.Component.Reference.CallBase
public import Silmaril.Proofs.Wasm.Component.Reference.FloatABI

/-!
# Branching runs of the copied component machine

`LRun` (`CallBase`) follows the unique step of each configuration. With NaN choices
(`Silmaril.Proofs.Wasm.Component.Reference.FloatABI`) a configuration may have one step per
admissible answer. `TRun Q m`: every machine run from `m` passes only through live
configurations until it reaches a configuration satisfying `Q`.

* `TRun.inv`: a machine run from `m` stops at a live configuration, or passes through a
  configuration satisfying `Q`; `TRun.diverges`: a divergent `m` reaches a divergent
  configuration satisfying `Q`; `TRun.of_lrun`: live runs extend `TRun`;
* `step_choose_inv`: the steps of a configuration running a choice are the admissible answers;
* `ChoiceProg.trun`: a program of NaN choices in focus is a `TRun` to its results.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → P E σ (Ret E)}

variable (prof hr dispatch) in
/-- Every machine run from `m` stays live until it reaches a configuration satisfying `Q`. -/
inductive TRun (Q : Config E σ → Prop) : Config E σ → Prop where
  | done {m : Config E σ} : Q m → TRun Q m
  | step {m : Config E σ} : Live m →
      (∀ l m', Step prof hr dispatch m l m' → TRun Q m') → TRun Q m

namespace TRun

variable {Q : Config E σ → Prop}

/-- **Inversion**: a run from `m` stops at a live configuration, or passes through `Q`. -/
theorem inv {m m' : Config E σ} {tr : List (Label E σ)} (h : TRun prof hr dispatch Q m)
    (h' : Steps prof hr dispatch m tr m') :
    Live m' ∨ ∃ mq tr₁ tr₂, Q mq ∧ tr = tr₁ ++ tr₂ ∧ Steps prof hr dispatch mq tr₂ m' := by
  induction h generalizing tr with
  | @done m hq => exact .inr ⟨m, [], tr, hq, rfl, h'⟩
  | step hl _ ih =>
    cases h' with
    | refl => exact .inl hl
    | cons s r =>
      rcases ih _ _ s r with hl' | ⟨mq, tr₁, tr₂, hq, e, r'⟩
      · exact .inl hl'
      · exact .inr ⟨mq, _ :: tr₁, tr₂, hq, by rw [e]; rfl, r'⟩

/-- A divergent start reaches a divergent configuration satisfying `Q`. -/
theorem diverges {m : Config E σ} (h : TRun prof hr dispatch Q m)
    (d : Diverges prof hr dispatch m) : ∃ mq, Q mq ∧ Diverges prof hr dispatch mq := by
  induction h with
  | @done m hq => exact ⟨m, hq, d⟩
  | step _ _ ih =>
    obtain ⟨m', ⟨l, _, s⟩, d'⟩ := d.unfold
    exact ih l m' s d'

/-- A live run followed by a `TRun`. -/
theorem of_lrun {m m₂ : Config E σ} {tr : List (Label E σ)}
    (h : LRun prof hr dispatch m tr m₂) (h₂ : TRun prof hr dispatch Q m₂) :
    TRun prof hr dispatch Q m := by
  induction h with
  | refl => exact h₂
  | cons hl s _ ih =>
    refine .step hl fun l' m' s' => ?_
    obtain ⟨-, rfl⟩ := s.2 _ _ s'
    exact ih h₂

theorem mono {m : Config E σ} {R : Config E σ → Prop} (h : TRun prof hr dispatch Q m)
    (hQR : ∀ m, Q m → R m) : TRun prof hr dispatch R m := by
  induction h with
  | done hq => exact .done (hQR _ hq)
  | step hl _ ih => exact .step hl ih

end TRun

/-- A step of a configuration running a choice is not a deterministic one. -/
theorem not_det_of_choose {m m' : Config E σ} {l : Label E σ} {th : Option ThreadId}
    {ck : ChoiceKind} {k : ck.Resp → P E σ (Ret E)} {segs : List (Seg E σ)}
    {rest : List (Activation E σ)}
    (hc : m.ctl = ⟨th, .prog (.op (S := Eff E σ) (.choose ck) k), segs⟩ :: rest)
    (h : Step prof hr dispatch m l m') : ¬ Label.Det l := by
  intro hl
  obtain ⟨st, e⟩ := Step.step?_of_det noStep Oracle.first h hl
  simp only [step?, hc, opStep] at e
  obtain ⟨hl₁, -, -⟩ := hl
  revert e
  split
  · exact fun e => by cases e
  · split
    · exact fun e => hl₁ _ _ (Prod.mk.inj (Option.some.inj e)).1.symm
    · exact fun e => by cases e

/-- **The steps of a choice** are its admissible answers. -/
theorem step_choose_inv {m m' : Config E σ} {l : Label E σ} {th : Option ThreadId}
    {ck : ChoiceKind} {k : ck.Resp → P E σ (Ret E)} {segs : List (Seg E σ)}
    {rest : List (Activation E σ)}
    (hc : m.ctl = ⟨th, .prog (.op (S := Eff E σ) (.choose ck) k), segs⟩ :: rest)
    (h : Step prof hr dispatch m l m') :
    ∃ r, Allowed prof ck r ∧ m' = { m with ctl := ⟨th, .prog (k r), segs⟩ :: rest } := by
  have hnd := not_det_of_choose hc h
  cases l with
  | choice k' r =>
    cases h with
    | choose r' hc' ha =>
      rw [hc] at hc'
      cases hc'
      exact ⟨_, ha, rfl⟩
  | core =>
    cases h with
    | coreInternal hc' _ _ =>
      rw [hc] at hc'
      cases (Activation.mk.inj (List.cons.inj hc').1).2.1
  | host ev =>
    have hr' := Step.host_ready h
    rw [hr'.1] at hc
    cases hc
  | tau =>
    exact (hnd ⟨(fun _ _ e => by cases e), (fun e => by cases e), (fun _ e => by cases e)⟩).elim
  | obs o =>
    exact (hnd ⟨(fun _ _ e => by cases e), (fun e => by cases e), (fun _ e => by cases e)⟩).elim
  | trap r =>
    exact (hnd ⟨(fun _ _ e => by cases e), (fun e => by cases e), (fun _ e => by cases e)⟩).elim

/-- A configuration is itself with its control chain written out. -/
theorem eq_withCtl {M : Config E σ} {a : List (Activation E σ)} (hc : M.ctl = a) :
    M = { M with ctl := a } := by
  obtain ⟨⟩ := M
  cases hc
  rfl

/-- **A program of NaN choices in focus** is a branching run to its results. -/
theorem ChoiceProg.trun {α : Type} {Q : α → Prop} {p : P E σ α} (h : ChoiceProg prof Q p) :
    ∀ (M : Config E σ) (f : α → P E σ (Ret E)) (th : Option ThreadId) (segs : List (Seg E σ))
      (rest : List (Activation E σ)), M.ctl = ⟨th, .prog (p >>= f), segs⟩ :: rest →
      M.store.lockdown = false →
      TRun prof hr dispatch
        (fun m => ∃ a, Q a ∧ m = { M with ctl := ⟨th, .prog (f a), segs⟩ :: rest }) M := by
  induction h with
  | @pure a ha =>
    intro M f th segs rest hc _
    exact .done ⟨a, ha, eq_withCtl hc⟩
  | @nan t x k _ ih =>
    intro M f th segs rest hc hl
    refine .step ⟨by rw [hc]; exact List.cons_ne_nil _ _, hl⟩ fun l m' s => ?_
    have hc' : M.ctl = ⟨th, .prog (.op (S := Eff E σ) (.choose (.nan t x))
        fun r => k r >>= f), segs⟩ :: rest := hc
    obtain ⟨r, hr', rfl⟩ := step_choose_inv hc' s
    exact ih r hr' { M with ctl := ⟨th, .prog (k r >>= f), segs⟩ :: rest } f th segs rest rfl hl

end Silmaril.Proofs.Wasm.Component.Reference
