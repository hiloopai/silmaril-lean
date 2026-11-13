module

public import Silmaril.Wasm.Spec.Litmus.Defs
public import Silmaril.Wasm.Spec.Basic.Thms
public import Silmaril.Wasm.Spec.Embed.Defs
public import Silmaril.Wasm.Spec.Env.Thms
import Mathlib.Tactic.IntervalCases

@[expose] public section

/-!
# Litmus tests

On the litmus programs of `Silmaril.Wasm.Spec.Litmus.Defs` (loose semantics):

* simple logics: `okRun_neverCall_log`, `okRun_assert`, `badRun_not_assert`, `okRun_retPost`,
  `okRun_not_neverCallFrom` (assert *is* called from `main`), `debugRun_neverCallFrom`
  (`log` is called from `debug`, never from `main`);
* scopes (the satisfaction condition at work): `debugRun_not_neverCall` (at `X₁` the program
  calls `log`) but `debugRun_scope` (observed through `X₀ ⟶ X₁`, which hides `debug`, it never
  does);
* comorphisms: `okRun_assert_callPre` (via `AssertNeverFalse.toCallPre`), `okRun_tla`
  (`□[¬ log]` via `NeverCall.toAct` and `Act.toTla`);
* LTL: `okRun_mainReturns_max` (liveness over maximal behaviours), `badRun_not_mainReturns_max`,
  `okRun_not_mainReturns_fin` (finite-trace LTL rejects liveness on unfinished prefixes);
* CTL: `okRun_ef_assert` (`EF` "assert has been called": a branching property);
* environments: `assertEnv_iretPost` (variant (c)), `okRun_assume` (an assume-guarantee
  sentence, variant (a), from the plain one).

Wasm-level litmus tests on real Core 3.0 code are `incProvider_neverCall` and
`incProvider_retPost` (`Silmaril.Wasm.Spec.Check.Thms`).
-/

namespace Silmaril.Wasm.Spec.Litmus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- The loose semantics of the litmus tests. -/
abbrev S : Semantics Unit (List Val) (Behaviour Val) := Semantics.ofSets Unit (List Val) (Behaviour Val)

theorem okRun_neverCall_log : Models (neverCall Unit _ _) S (progOf okRun) logI := by
  rw [models_progOf_iff, NeverCall.sat_prefixesOf_iff]
  intro a ha
  simp [okRun, logI, assertI, mainE] at ha

theorem okRun_assert : Models (assertNeverFalse Unit _) S (progOf okRun) assertI := by
  rw [models_progOf_iff, AssertNeverFalse.sat_prefixesOf_iff]
  intro a ha
  simp [okRun, assertI, mainE] at ha
  subst ha
  unfold assertOk
  decide

theorem badRun_not_assert : ¬ Models (assertNeverFalse Unit _) S (progOf badRun) assertI := by
  rw [models_progOf_iff, AssertNeverFalse.sat_prefixesOf_iff]
  intro h
  have := h [Val.i32 0] (by simp [badRun])
  simp [assertOk] at this

theorem okRun_retPost :
    Models (retPost Unit _ _) S (progOf okRun) ⟨mainE, (· = .returns [Val.i32 5])⟩ := by
  rw [models_progOf_iff, RetPost.sat_prefixesOf_iff]
  intro r hr
  simp [okRun, assertI, mainE] at hr
  exact hr

theorem okRun_not_neverCallFrom :
    ¬ Models (neverCallFrom Unit _ _) S (progOf okRun) (assertI, mainE) := by
  rw [models_progOf_iff, NeverCallFrom.sat_prefixesOf_iff]
  intro h
  exact h [.call mainE []] (.icall assertI [Val.i32 1]) _ rfl [Val.i32 1] rfl rfl

theorem debugRun_neverCallFrom :
    Models (neverCallFrom Unit _ _) S (progOf debugRun) (⟨1, by decide⟩, ⟨0, by decide⟩) := by
  rw [models_progOf_iff, NeverCallFrom.sat_prefixesOf_iff]
  show EveryPos _ debugRun
  rw [everyPos_iff_get]
  intro k hk a hea
  have hk' : k < 6 := hk
  interval_cases k
  case «3» => decide
  all_goals simp [debugRun, Event.icall, Event.call, Event.ret, Event.iret] at hea

theorem debugRun_not_neverCall :
    ¬ Models (neverCall Unit _ _) S (progOf debugRun) ⟨1, by decide⟩ := by
  rw [models_progOf_iff, NeverCall.sat_prefixesOf_iff]
  intro h
  exact h [Val.i32 7] (by simp [debugRun])

theorem debugRun_scope :
    Sat (neverCall Unit _ _) S (Model.ofProg (progOf debugRun)) ⟨X₀, ι₀₁, logI⟩ := by
  rw [sat_iff, Model.traces_ofProg]
  rintro t ⟨u, hu, hb⟩ a ha
  have hu' : u ∈ debugRun.inits := (List.mem_inits _ _).2 hu
  simp only [debugRun, List.inits, List.map, List.mem_cons, List.mem_nil_iff, or_false] at hu'
  rcases hu' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show back ι₀₁ [] = some [] from rfl] at hb
    cases hb
    exact absurd ha List.not_mem_nil
  · rw [show back ι₀₁ _ = some [Event.call mainE []] from rfl] at hb
    cases hb
    simp at ha
  · rw [show back ι₀₁ _ = some [Event.call mainE [], Event.ret mainE (.returns [Val.i32 5])]
      from rfl] at hb
    cases hb
    simp at ha
  all_goals (rw [show back ι₀₁ _ = none from rfl] at hb; cases hb)

theorem okRun_assert_callPre :
    Models (callPre Unit _ _) S (progOf okRun) ⟨assertI, assertOk⟩ :=
  ((AssertNeverFalse.toCallPre Unit (Behaviour Val)).models_iff S (progOf okRun) assertI).2
    okRun_assert

theorem okRun_tla :
    Models (tla Unit _ _) S (progOf okRun) (TLA.box fun _ e => ∀ a, e ≠ Event.icall logI a) :=
  (((NeverCall.toAct Unit _ _).comp (Act.toTla Unit _ _)).models_iff S (progOf okRun) logI).2
    okRun_neverCall_log

theorem okRun_mainReturns_max : Models (ltlMax Unit _ _) S (progOf okRun) mainReturns := by
  rw [models_progOf_iff, ltlMax_prefixesOf_iff]
  unfold mainReturns
  rw [LTL.holdsFin_alw]
  intro j _ hj
  have hj' : j < 4 := by simpa [okRun] using hj
  interval_cases j
  · show LTL.HoldsFin okRun 0 (LTL.or _ _)
    refine Or.inr ⟨3, Nat.zero_le _, by decide, ⟨by decide, _, rfl⟩, fun _ _ _ => trivial⟩
  all_goals
    refine Or.inl fun ⟨_, a, ha⟩ => ?_
    simp [okRun, Event.call, Event.icall, Event.iret, Event.ret] at ha

theorem badRun_not_mainReturns_max : ¬ Models (ltlMax Unit _ _) S (progOf badRun) mainReturns := by
  rw [models_progOf_iff, ltlMax_prefixesOf_iff]
  unfold mainReturns
  rw [LTL.holdsFin_alw]
  intro h
  rcases h 0 le_rfl (by decide) with hno | ⟨k, -, hk, ⟨_, r, hr⟩, -⟩
  · exact hno ⟨by decide, [], rfl⟩
  · have hk' : k < 2 := hk
    interval_cases k <;> simp [badRun, Event.call, Event.icall, Event.ret] at hr

theorem okRun_not_mainReturns_fin : ¬ Models (ltlFin Unit _ _) S (progOf okRun) mainReturns := by
  rw [models_progOf_iff]
  intro h
  have hpre : [Event.call mainE []] ∈ prefixesOf okRun := ⟨okRun.drop 1, rfl⟩
  have h₀ := LTL.holdsFin_alw.1 (h _ hpre) 0 le_rfl (by decide)
  rcases h₀ with hno | ⟨k, -, hk, ⟨_, r, hr⟩, -⟩
  · exact hno ⟨by decide, [], rfl⟩
  · have hk' : k < 1 := hk
    interval_cases k
    simp [Event.call, Event.ret] at hr

theorem okRun_ef_assert :
    Models (ctl Unit _ _) S (progOf okRun) (CTL.ef (CTL.atom fun s => ∃ a, Event.icall assertI a ∈ s)) := by
  rw [models_progOf_iff]
  exact ⟨okRun.take 2, List.take_prefix _ _, [Val.i32 1], by simp [okRun]⟩

theorem assertEnv_iretPost :
    Models (iretPost Unit _ _) (envSem Unit _ _) assertEnv (assertI, (· = .returns [])) := by
  rw [envSem_iretPost_iff]
  intro u hu r hr
  have hsub := List.IsPrefix.subset hu hr
  simp [assertI] at hsub
  exact hsub

theorem okRun_assume :
    Models (retPost Unit _ _).assume S (progOf okRun)
      (assertEnv, ⟨mainE, (· = .returns [Val.i32 5])⟩) :=
  (models_assume_iff _ _ _ _ _).2
    (models_withEnv_of_models (Logic.ofTrace_antitone _ _) okRun_retPost assertEnv)

end Silmaril.Wasm.Spec.Litmus
