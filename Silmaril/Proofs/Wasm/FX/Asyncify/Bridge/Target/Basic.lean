module

public import Silmaril.Wasm.FX.Asyncify.Bridge.Target.Defs
public import Silmaril.Wasm.FX.Asyncify.Bridge.Thms

/-!
# The target half of the tool as an instance: proofs

* `simRel_next`: under a positive-step simulation (`SimRel`), the target is still running
  whenever the source is (it takes at least as many steps).
* `calm_fam`, `calm_tool`: on `calmP`, the family's whole-program target is still running after
  6 steps, while the tool's target has stopped.
* `isSim_of_beh_eq`: two deterministic tool systems (no stop with `diverges`) with equal
  behaviours from `x` and `y` are related by a stuttering simulation `Tool.IsSim`: the relation
  "equal behaviours", the measure the number of steps to the source's stop. The source steps
  alone (no target step) while it stops, and in lock step while it diverges.
* `beh_famStep`: the behaviours of `famStep` are the family's host-observed target behaviours,
  read back by `obsOut`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Bridge.Target

open Silmaril.Wasm
open Silmaril.Wasm.Models.FXAsync
open Silmaril.Wasm.FX.Asyncify
open Silmaril.Wasm.FX.Asyncify.Host
open Silmaril.Wasm.FX.Asyncify.Bridge

/-! ## Positive-step simulations make the target run at least as long -/

section Lag

variable {C D V : Type}

theorem runN_next_add {t : D → Res D V} {k : Nat} {y y₁ : D} (h : runN t k y = .next y₁)
    (n : Nat) : runN t (k + n) y = runN t n y₁ := by
  induction k generalizing y with
  | zero =>
    have hy : y = y₁ := Res.next.inj h
    rw [hy, Nat.zero_add]
  | succ k ih =>
    rw [Nat.succ_add]
    cases ht : t y with
    | next y' =>
      have h' : runN t k y' = .next y₁ := by simpa only [runN, ht] using h
      simpa only [runN, ht] using ih h'
    | stop o =>
      have h' : runN t (k + 1) y = .stop o := by simp only [runN, ht]
      rw [h'] at h
      cases h

theorem runN_next_le {t : D → Res D V} : ∀ {m j : Nat} {y z : D}, runN t m y = .next z → j ≤ m →
    ∃ z', runN t j y = .next z'
  | _, 0, y, _, _, _ => ⟨y, rfl⟩
  | 0, _ + 1, _, _, _, hj => absurd hj (by omega)
  | m + 1, j + 1, y, z, h, hj => by
    cases ht : t y with
    | next y' =>
      have h' : runN t m y' = .next z := by simpa only [runN, ht] using h
      obtain ⟨z', hz'⟩ := runN_next_le (j := j) h' (by omega)
      exact ⟨z', by simpa only [runN, ht] using hz'⟩
    | stop o =>
      have h' : runN t (m + 1) y = .stop o := by simp only [runN, ht]
      rw [h'] at h
      cases h

/-- **Under a positive-step simulation the target runs at least as long as the source.** -/
theorem simRel_next {s : C → Res C V} {t : D → Res D V} {R : C → D → Prop} (hS : SimRel s t R) :
    ∀ (n : Nat) {x : C} {y : D} {x' : C}, R x y → runN s n x = .next x' →
      ∃ y', runN t n y = .next y'
  | 0, _, y, _, _, _ => ⟨y, rfl⟩
  | n + 1, x, y, x', hR, h => by
    obtain ⟨k, hk, hres⟩ := hS x y hR
    cases hs : s x with
    | stop o =>
      have h' : runN s (n + 1) x = .stop o := by simp only [runN, hs]
      rw [h'] at h
      cases h
    | next x₁ =>
      have hx : runN s n x₁ = .next x' := by simpa only [runN, hs] using h
      rw [hs] at hres
      cases ht : runN t k y with
      | stop o => rw [ht] at hres; exact hres.elim
      | next y₁ =>
        have hR₁ : R x₁ y₁ := by rw [ht] at hres; exact hres
        obtain ⟨y₂, hy₂⟩ := simRel_next hS n hR₁ hx
        have hlong : runN t (k + n) y = .next y₂ := by rw [runN_next_add ht n]; exact hy₂
        exact runN_next_le hlong (by omega)

end Lag

/-! ## The counterexample -/

theorem calm_wf : calmP.WF := by
  unfold Tool.Prog.WF
  decide

theorem calm_fam : ∃ y, runN (mapObs toolOut (observe (htstep (compPO .whole (trP calmP.env))
    kTest (kHost calmP.env unitHost)))) 6 (tInit 0 (kArgs [5]), ()) = .next y := ⟨_, rfl⟩

theorem calm_tool : runN (asRes (Tool.tgtStep (Tool.asyncifyProg calmP) unitHost)) 6
    (Tool.tgtSt calmP 0 calmFn [5] ()) = .stop (.done [.val (.done [5] ())]) := rfl

theorem calm_src_stop :
    Tool.runN (Tool.srcStep calmP.env unitHost) 2 (Tool.srcCfg 0 calmFn [5], ()) =
      .stop (.done [5] ()) := rfl

theorem calm_depth : Tool.DepthBound calmP unitHost (Tool.srcCfg 0 calmFn [5], ()) := by
  intro n y h
  match n, h with
  | 0, h =>
    have hy : y = (Tool.srcCfg 0 calmFn [5], ()) := (Tool.SRes.next.inj h).symm
    rw [hy]
    decide
  | 1, h =>
    have hy : y = (⟨[⟨0, [5], [5], [], 1⟩], [], fun _ => 0⟩, ()) := (Tool.SRes.next.inj h).symm
    rw [hy]
    decide
  | n + 2, h =>
    have hs := Tool.runN_stop_mono calm_src_stop (show 2 ≤ n + 2 by omega)
    rw [hs] at h
    cases h

/-- On `sleep-add` the family's target has stopped after 18 steps. -/
theorem sa_fam : ∃ o, runN (mapObs toolOut (observe (htstep (compPO .whole (trP saP.env))
    kTest (kHost saP.env exH)))) 18 (tInit 1 (kArgs [5]), 0) = .stop o := ⟨_, rfl⟩

/-- On `sleep-add` the tool's target is still running after 18 steps. -/
theorem sa_tool : ∃ y, runN (asRes (Tool.tgtStep (Tool.asyncifyProg saP) exH)) 18
    (Tool.tgtSt saP 1 saFn [5] 0) = .next y := ⟨_, rfl⟩

/-! ## Equal behaviours give a stuttering simulation -/

section Stutter

variable {X Y σ : Type}

theorem beh_of_next {s : X → Tool.SRes X σ} {x x' : X} (h : s x = .next x') :
    Tool.beh s x' = Tool.beh s x := by
  ext b
  constructor
  · rintro (⟨n, hn⟩ | ⟨rfl, hd⟩)
    · exact .inl ⟨n + 1, by simpa only [Tool.runN, h] using hn⟩
    · refine .inr ⟨rfl, fun n => ?_⟩
      match n with
      | 0 => exact ⟨x, rfl⟩
      | n + 1 =>
        obtain ⟨z, hz⟩ := hd n
        exact ⟨z, by simpa only [Tool.runN, h] using hz⟩
  · rintro (⟨n, hn⟩ | ⟨rfl, hd⟩)
    · match n, hn with
      | 0, hn => cases hn
      | n + 1, hn => exact .inl ⟨n, by simpa only [Tool.runN, h] using hn⟩
    · refine .inr ⟨rfl, fun n => ?_⟩
      obtain ⟨z, hz⟩ := hd (n + 1)
      exact ⟨z, by simpa only [Tool.runN, h] using hz⟩

theorem stop_of_runN {t : Y → Tool.SRes Y σ} : ∀ {n : Nat} {y : Y} {o : Tool.Obs σ},
    Tool.runN t n y = .stop o → ∃ z, t z = .stop o
  | 0, _, _, h => by cases h
  | n + 1, y, o, h => by
    cases ht : t y with
    | next y' => exact stop_of_runN (by simpa only [Tool.runN, ht] using h)
    | stop o' =>
      have ho : o' = o := by simpa only [Tool.runN, ht, Tool.SRes.stop.injEq] using h
      exact ⟨y, by rw [ht, ho]⟩

open Classical in
/-- The number of steps to the stop of `s` from `x` (0 if it diverges). -/
noncomputable def stopTime (s : X → Tool.SRes X σ) (x : X) : Nat :=
  if h : ∃ n o, Tool.runN s n x = .stop o then Nat.find h else 0

theorem stopTime_lt {s : X → Tool.SRes X σ} {x x' : X} (hs : s x = .next x')
    (h : ∃ n o, Tool.runN s n x = .stop o) : stopTime s x' < stopTime s x := by
  classical
  obtain ⟨o, ho⟩ := Nat.find_spec h
  have hpos : Nat.find h ≠ 0 := by
    intro h0
    rw [h0] at ho
    cases ho
  obtain ⟨j, hj⟩ : ∃ j, Nat.find h = j + 1 := ⟨Nat.find h - 1, by omega⟩
  have ho' : Tool.runN s j x' = .stop o := by
    rw [hj] at ho
    simpa only [Tool.runN, hs] using ho
  have h' : ∃ n o, Tool.runN s n x' = .stop o := ⟨j, o, ho'⟩
  have hle : Nat.find h' ≤ j := Nat.find_min' h' ⟨o, ho'⟩
  have e1 : stopTime s x' = Nat.find h' := by simp only [stopTime, h', ↓reduceDIte]
  have e2 : stopTime s x = Nat.find h := by simp only [stopTime, h, ↓reduceDIte]
  omega

/-- A diverging source: the target diverges too and takes one step to equal behaviours. -/
theorem next_of_div {s : X → Tool.SRes X σ} {t : Y → Tool.SRes Y σ} (ht : NoDivStop t)
    {x : X} {y : Y} (hR : Tool.beh s x = Tool.beh t y)
    (hstop : ¬ ∃ n o, Tool.runN s n x = .stop o) :
    ∃ y₁, t y = .next y₁ ∧ Tool.beh t y₁ = Tool.beh t y := by
  have hdiv : Tool.Obs.diverges ∈ Tool.beh s x := by
    refine .inr ⟨rfl, fun n => ?_⟩
    cases hr : Tool.runN s n x with
    | next z => exact ⟨z, rfl⟩
    | stop o => exact (hstop ⟨n, o, hr⟩).elim
  have hdiv' : Tool.Obs.diverges ∈ Tool.beh t y := hR ▸ hdiv
  have hrun : ∀ n, ∃ y', Tool.runN t n y = .next y' := by
    rcases hdiv' with ⟨n, hn⟩ | ⟨-, hd⟩
    · obtain ⟨z, hz⟩ := stop_of_runN hn
      exact (ht z _ hz rfl).elim
    · exact hd
  cases hty : t y with
  | stop o =>
    obtain ⟨z, hz⟩ := hrun 1
    have h1 : Tool.runN t 1 y = .stop o := by simp only [Tool.runN, hty]
    rw [h1] at hz
    cases hz
  | next y₁ => exact ⟨y₁, rfl, beh_of_next hty⟩

/-- **Equal behaviours give a stuttering simulation** (`Tool.IsSim`). -/
theorem isSim_of_beh_eq {s : X → Tool.SRes X σ} {t : Y → Tool.SRes Y σ} (hs : NoDivStop s)
    (ht : NoDivStop t) :
    Tool.IsSim s t (fun x y => Tool.beh s x = Tool.beh t y) (stopTime s) := by
  constructor
  · intro x y o hR hx
    have hmem : o ∈ Tool.beh t y := hR ▸ (.inl ⟨1, by simp only [Tool.runN, hx]⟩)
    rcases hmem with ⟨n, hn⟩ | ⟨hd, -⟩
    · exact ⟨n, hn⟩
    · exact (hs x o hx hd).elim
  · intro x y x' hR hx
    have hR' : Tool.beh s x' = Tool.beh t y := (beh_of_next hx).trans hR
    by_cases hstop : ∃ n o, Tool.runN s n x = .stop o
    · exact ⟨0, y, rfl, hR', .inr (stopTime_lt hx hstop)⟩
    · obtain ⟨y₁, hty, hb⟩ := next_of_div ht hR hstop
      exact ⟨1, y₁, by simp only [Tool.runN, hty], hR'.trans hb.symm, .inl Nat.one_pos⟩

end Stutter

/-! ## The family's target as a tool system -/

variable {σ : Type}

theorem asRes_famStep (Q : Prog (TIns KV)) (test : KV → Bool) (K : KHost KV σ) :
    asRes (famStep Q test K) = mapObs toolOut (observe (htstep Q test K)) := by
  funext y
  unfold asRes famStep mapObs observe
  cases htstep Q test K y <;> rfl

theorem beh_famStep (Q : Prog (TIns KV)) (test : KV → Bool) (K : KHost KV σ) (y : TCfg KV × σ) :
    Tool.beh (famStep Q test K) y = obsOut '' beh (observe (htstep Q test K)) y := by
  rw [Silmaril.Proofs.Wasm.FX.Asyncify.Bridge.tool_beh_asRes, asRes_famStep,
    Silmaril.Proofs.Wasm.FX.Asyncify.Bridge.beh_mapObs, Set.image_image]
  exact congrArg (· '' _) (funext fun b =>
    (Silmaril.Proofs.Wasm.FX.Asyncify.Bridge.obsOut_eq b).symm)

theorem noDivStop_famStep (Q : Prog (TIns KV)) (test : KV → Bool) (K : KHost KV σ) :
    NoDivStop (famStep Q test K) := by
  intro y o h
  unfold famStep at h
  cases hh : htstep Q test K y with
  | next y' => rw [hh] at h; cases h
  | stop o' =>
    rw [hh] at h
    cases o' with
    | done vs =>
      cases h
      unfold HOut.ofOutcome toolOut
      split <;> exact nofun
    | trap => cases h; exact nofun

theorem noDivStop_tgtStep (E : Tool.Env) (H : Tool.Host σ) : NoDivStop (Tool.tgtStep E H) := by
  intro t o h
  unfold Tool.tgtStep at h
  dsimp only at h
  split at h
  all_goals (try split at h)
  all_goals (try split at h)
  all_goals cases h
  all_goals exact nofun

end Silmaril.Proofs.Wasm.FX.Asyncify.Bridge.Target
