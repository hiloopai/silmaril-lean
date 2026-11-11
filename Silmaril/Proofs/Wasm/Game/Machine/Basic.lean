module

public import Silmaril.Wasm.Game.Machine.Defs
public import Silmaril.Proofs.Wasm.Game.Machine.Profile

/-!
# Host-free runs of the single-threaded machine: proofs

For every profile `P`: results and callouts are normal. For the
deterministic profiles `profile o` only: normal forms of host-free runs are
unique (`reach_normal_unique`, from the `Det.Join` diamond of
`Internal.deterministic`). Agreement with closed-world Core reduction: `Reach.steps`,
`calloutAt_step`, `out_iff_core`, `ret_iff_core`, and `step_answerHost_iff`
(at a callout, the only Core step against `answerHost h args r` resumes with
`r`).
-/

public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game

open Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

/-! ### Normal forms of host-free runs -/

/-- The code of a Core result is quiet (values, a trap, or an uncaught exception). -/
theorem quiet_result_toAdmin (r : Result) : Quiet r.toAdmin := by
  cases r with
  | values vs => exact quiet_vals vs
  | throw a => exact quiet_throwing a
  | trap => exact quiet_trap

/-- Quiet code has no host-call redex. -/
theorem decompose?_none_of_quiet {s : Store Nat} {l : List Admin} (hq : Quiet l) :
    decompose? s l = none := by
  rw [decompose?_eq]
  rcases hq with hq | hq | hq | ⟨a, hq⟩
  · rcases hsp : splitVals l with ⟨vs, r⟩
    rw [hsp] at hq
    simp only at hq
    subst hq
    rfl
  · rw [hq]; rfl
  · rw [hq]; rfl
  · rw [hq]; rfl

/-- Values are not the code of a thrown exception. -/
private theorem vals_ne_throw (vs : List Val) (a : Nat) :
    vals vs ≠ (Result.throw a).toAdmin := fun equal =>
  Det.mem_vals (by rw [equal]; simp [Result.toAdmin] : Admin.plain .throwRef ∈ vals vs) rfl

/-- Values are not the code of a trap. -/
private theorem vals_ne_trap (vs : List Val) : vals vs ≠ Result.trap.toAdmin := fun equal =>
  Det.mem_vals (by rw [equal]; simp [Result.toAdmin] : Admin.trap ∈ vals vs) rfl

/-- `Result.toAdmin` is injective (as `LinkObservation.result_code_injective`). -/
theorem result_toAdmin_injective : Function.Injective Result.toAdmin := by
  intro left right equal
  cases left with
  | values vs =>
    cases right with
    | values ws => exact congrArg Result.values (Det.vals_inj.mp equal)
    | throw a => exact absurd equal (vals_ne_throw vs a)
    | trap => exact absurd equal (vals_ne_trap vs)
  | throw a =>
    cases right with
    | values vs => exact absurd equal.symm (vals_ne_throw vs a)
    | throw b =>
      have addresses : a = b := by simpa only [Result.toAdmin, List.cons.injEq,
        Admin.ref.injEq, Ref.exn.injEq, and_true] using equal
      exact congrArg Result.throw addresses
    | trap => exact absurd equal (by simp [Result.toAdmin])
  | trap =>
    cases right with
    | values vs => exact absurd equal.symm (vals_ne_trap vs)
    | throw a => exact absurd equal (by simp [Result.toAdmin])
    | trap => rfl

/-- A finished thread has no internal step. -/
theorem resultAt_no_internal {P : Profile} {s : Store Nat} {t : Thread} {r : Result}
    (h : ResultAt s t r) : ∀ y, ¬ InternalP P (s, t) y := by
  rintro ⟨s', t'⟩ ⟨f', code', -, hstep⟩
  apply Step.not_quiet hstep
  show Quiet (t.config s).code
  rw [h]
  exact quiet_result_toAdmin r

/-- A thread at a callout has no internal step. -/
theorem calloutAt_no_internal {P : Profile} {s : Store Nat} {t : Thread} {h : Nat}
    {args : List Val} (hc : CalloutAt s t h args) : ∀ y, ¬ InternalP P (s, t) y := by
  rintro ⟨s', t'⟩ ⟨f', code', -, hstep⟩
  have hn := decompose?_none_of_noRedex (Step.noRedex hstep)
  rw [Thread.config_store] at hn
  obtain ⟨E, a, hd⟩ := hc
  rw [hd] at hn
  cases hn

/-- A thread is not both finished and at a callout. -/
theorem resultAt_not_calloutAt {s : Store Nat} {t : Thread} {r : Result} {h : Nat}
    {args : List Val} (hr : ResultAt s t r) : ¬ CalloutAt s t h args := by
  rintro ⟨E, a, hd⟩
  have hn : decompose? s (t.config s).code = none := by
    rw [hr]; exact decompose?_none_of_quiet (quiet_result_toAdmin r)
  rw [hd] at hn
  cases hn

/-- The result of a finished thread is unique (`Result.toAdmin` is injective). -/
theorem resultAt_unique {s : Store Nat} {t : Thread} {r r' : Result} (h : ResultAt s t r)
    (h' : ResultAt s t r') : r = r' :=
  result_toAdmin_injective (h.symm.trans h')

/-- The callout of a stopped thread is unique. -/
theorem calloutAt_unique {s : Store Nat} {t : Thread} {h h' : Nat} {args args' : List Val}
    (hc : CalloutAt s t h args) (hc' : CalloutAt s t h' args') : h = h' ∧ args = args' := by
  obtain ⟨E, a, hd⟩ := hc
  obtain ⟨E', a', hd'⟩ := hc'
  rw [hd] at hd'
  simp only [Option.some.injEq, Prod.mk.injEq] at hd'
  exact ⟨hd'.2.2.1, hd'.2.2.2⟩

/-- **Confluence.** Host-free runs reach at most one normal form. Route: `Internal` has the
diamond property up to one step on each side (`Internal.deterministic`), hence is
confluent, and normal forms of a confluent relation are unique. -/
theorem reach_normal_unique {o : GrowOracle} {x y y' : Store Nat × Thread}
    (h : Reach (profile o) x y) (h' : Reach (profile o) x y')
    (hy : ∀ z, ¬ InternalP (profile o) y z) (hy' : ∀ z, ¬ InternalP (profile o) y' z) :
    y = y' := by
  unfold Reach at h h'
  rw [internalP_profile] at hy hy' h h'
  exact nf_unique_of_join (fun a b => Internal.deterministic a b) h h' hy hy'

/-- Without a callout to decompose, `status` is not a callout. -/
private theorem status_ne_callout_of_none {P : Profile} {s : Store Nat} {t : Thread}
    {h : Nat} {args : List Val} (hd : decompose? s (t.config s).code = none) :
    statusP P s t ≠ .callout h args := by
  unfold statusP
  simp only [hd]
  split_ifs <;> simp

/-- The callout of the single-threaded machine's `status`. -/
theorem calloutAt_iff_status {P : Profile} {s : Store Nat} {t : Thread} {h : Nat}
    {args : List Val} : CalloutAt s t h args ↔ statusP P s t = .callout h args := by
  have fwd : ∀ {E a h' args'}, decompose? s (t.config s).code = some (E, a, h', args') →
      statusP P s t = .callout h' args' := by
    intro E a h' args' hd
    have nq : ¬ Quiet (t.config s).code := fun hq => by
      cases hd.symm.trans (decompose?_none_of_quiet hq)
    unfold statusP
    simp only
    split_ifs with h1 h2 h3
    · exact absurd (by obtain ⟨vs, hvs⟩ := h1; rw [hvs]; exact quiet_vals vs) nq
    · exact absurd (by rw [h2]; exact quiet_trap) nq
    · exact absurd (by obtain ⟨a, ha⟩ := h3; rw [ha]; exact quiet_throwing a) nq
    all_goals simp only [hd]
  constructor
  · rintro ⟨E, a, hd⟩
    exact fwd hd
  · intro hs
    rcases hd : decompose? s (t.config s).code with _ | ⟨E, a, h', args'⟩
    · exact absurd hs (status_ne_callout_of_none hd)
    · obtain ⟨rfl, rfl⟩ : h' = h ∧ args' = args := by simpa using (fwd hd).symm.trans hs
      exact ⟨E, a, hd⟩

/-! ### Agreement with Core reduction -/

/-- Host-free runs are Core runs for every host (`Internal.toStep`). -/
theorem Reach.steps {P : Profile} {host : HostSemantics Nat} {x y : Store Nat × Thread}
    (h : Reach P x y) : Steps P host (x.2.config x.1) (y.2.config y.1) := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail (InternalP.toStep P host hst)

/-- A callout answered by the host is one Core step (`step_iff`). -/
theorem calloutAt_step {P : Profile} {host : HostSemantics Nat} {s s' : Store Nat}
    {t : Thread} {h : Nat} {args : List Val} {r : Result} (hc : CalloutAt s t h args)
    (hr : host h s args (.returned s' r)) :
    Step P host (t.config s) ((resumeResult s t r).config s') := by
  obtain ⟨E, a, hd⟩ := hc
  exact (stepP_iff P host s t _).mpr (Or.inr ⟨E, a, h, args, hd, Or.inl ⟨s', r, hr, rfl⟩⟩)

/-- Every host-free Core run from a thread is the configuration of a host-free run of
the machine. -/
theorem reach_of_steps {P : Profile} {s : Store Nat} {t : Thread} {d : Config Nat}
    (h : Steps P (Det.noHost : HostSemantics Nat) (t.config s) d) :
    ∃ s' t', Reach P (s, t) (s', t') ∧ t'.config s' = d := by
  induction h with
  | refl => exact ⟨s, t, .refl, rfl⟩
  | @tail b e _ hst ih =>
    obtain ⟨s', t', hr, rfl⟩ := ih
    refine ⟨e.store, .active e.frame e.code, hr.tail ⟨e.frame, e.code, rfl, hst⟩, rfl⟩

/-- A host-free Core run to a host-call redex is a run of `Internal` to a callout
(B's `out_iff_thread`). -/
theorem out_iff_core {P : Profile} {s : Store Nat} {t : Thread} {h : Nat}
    {args : List Val} :
    (∃ s' t', Reach P (s, t) (s', t') ∧ CalloutAt s' t' h args) ↔
      ∃ d, Steps P (Det.noHost : HostSemantics Nat) (t.config s) d ∧
        ∃ E a, decompose? d.store d.code = some (E, a, h, args) := by
  constructor
  · rintro ⟨s', t', hr, E, a, hd⟩
    refine ⟨t'.config s', Reach.steps hr, E, a, ?_⟩
    rw [Thread.config_store]
    exact hd
  · rintro ⟨d, hd, E, a, hdec⟩
    obtain ⟨s', t', hr, rfl⟩ := reach_of_steps hd
    refine ⟨s', t', hr, E, a, ?_⟩
    rw [Thread.config_store] at hdec
    exact hdec

/-- A host-free Core run to a result is a run of `Internal` to a result
(B's `ret_iff_thread`). -/
theorem ret_iff_core {P : Profile} {s : Store Nat} {t : Thread} {r : Result} :
    (∃ s' t', Reach P (s, t) (s', t') ∧ ResultAt s' t' r) ↔
      ∃ d, Steps P (Det.noHost : HostSemantics Nat) (t.config s) d ∧
        d.code = r.toAdmin := by
  constructor
  · rintro ⟨s', t', hr, hres⟩
    exact ⟨t'.config s', Reach.steps hr, hres⟩
  · rintro ⟨d, hd, hcode⟩
    obtain ⟨s', t', hr, rfl⟩ := reach_of_steps hd
    exact ⟨s', t', hr, hcode⟩

/-- **Oracle reading of a resumption.** At a callout, the only Core step against the
one-answer host `answerHost h args r` is resuming with `r`. This is what makes the
environment's answer (`Trans.uret`) a step of closed-world reduction. -/
theorem step_answerHost_iff {P : Profile} {s : Store Nat} {t : Thread} {h : Nat}
    {args : List Val} {r : Result} (hc : CalloutAt s t h args) (c' : Config Nat) :
    Step P (answerHost h args r) (t.config s) c' ↔
      c' = (resumeResult s t r).config s := by
  rw [stepP_iff]
  constructor
  · rintro (⟨s', f', code', -, hi⟩ | ⟨E, a, h', args', hd, ⟨s', r', hr, rfl⟩ | ⟨hdiv, -⟩⟩)
    · exact absurd hi (calloutAt_no_internal hc _)
    · obtain ⟨rfl, rfl, hout⟩ := hr
      cases hout
      rfl
    · obtain ⟨-, -, hout⟩ := hdiv
      cases hout
  · rintro rfl
    obtain ⟨E, a, hd⟩ := hc
    exact Or.inr ⟨E, a, h, args, hd, Or.inl ⟨s, r, ⟨rfl, rfl, rfl⟩, rfl⟩⟩

end Silmaril.Proofs.Wasm.Game
