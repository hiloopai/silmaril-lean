module

public import Silmaril.Proofs.Games.DivLTSComp.Basic
public import Silmaril.Games.Div.Thms
public import Silmaril.Games.LTS.Thms

/-!
# Following an increasing chain of traces with one coherent run

`Stages L a s`: the states `a n` are reached by one run of `L` reading the
increasing chain of traces `s`, stage by stage. Finite and infinite plays of
`DStrategy.ofLTS L` give such runs:

* `stages_of_cover`: an infinite run `r` whose traces cover every `s n` is
  followed by a staged run along `s` (dependent choice: each stage splits the
  remaining part of `r`, `Run.of_append`). The runs reading the separate stages
  `s n` need not extend one another; this is what makes them coherent.
* `exists_cover`: if every `s n` is a play of `ofLTS L` (for a system denoting
  its strategy) and `s` converges to an infinite play of `ofLTS L` when it
  grows without bound, such a covering infinite run exists (the constant run
  reading the last stage when `s` stops growing).
* `infRun_of_stages`: conversely, a staged run is an infinite run (shifted by
  one stage) with the same limit.

New proofs.
-/

public section

namespace Silmaril.Proofs.Games.DivLTSComp

open Silmaril.Games

universe u

variable {E F : Sig.{u}}

/-- One run of `L` reaching `a n` after reading `s n`, stage by stage. -/
abbrev Stages (L : LTS E F) (a : ℕ → L.State) (s : Chain (Move E F)) : Prop :=
  L.Run L.init (s 0) (a 0) ∧ ∀ n, ∃ w, s (n + 1) = s n ++ w ∧ L.Run (a n) w (a (n + 1))

theorem Stages.run_le {L : LTS E F} {a : ℕ → L.State} {s : Chain (Move E F)}
    (h : Stages L a s) {n m : ℕ} (hnm : n ≤ m) : ∃ w, s m = s n ++ w ∧ L.Run (a n) w (a m) := by
  induction hnm with
  | refl => exact ⟨[], by simp, .nil _⟩
  | step _ ih =>
    obtain ⟨w, hw, hr⟩ := ih
    obtain ⟨w', hw', hr'⟩ := h.2 _
    exact ⟨w ++ w', by rw [hw', hw, List.append_assoc], hr.append hr'⟩

theorem Stages.run {L : LTS E F} {a : ℕ → L.State} {s : Chain (Move E F)}
    (h : Stages L a s) (n : ℕ) : L.Run L.init (s n) (a n) := by
  obtain ⟨w, hw, hr⟩ := h.run_le (Nat.zero_le n)
  rw [hw]
  exact h.1.append hr

theorem Stages.mono {L : LTS E F} {a : ℕ → L.State} {s : Chain (Move E F)}
    (h : Stages L a s) : s.Mono := fun n => by
  obtain ⟨w, hw, -⟩ := h.2 n
  exact ⟨w, hw.symm⟩

/-- An infinite run is a staged run. -/
theorem stages_infRun {L : LTS E F} (r : L.InfRun) : Stages L r.st r.tr :=
  ⟨by rw [r.st_zero, r.tr_zero]; exact .nil _, r.step⟩

/-- The invariant of `stages_of_cover`: from `x`, the rest of stage `n` up to some stage of
`r` can still be read. -/
private def Ahead (L : LTS E F) (r : L.InfRun) (s : Chain (Move E F)) (n : ℕ) (x : L.State) :
    Prop :=
  ∃ m w, r.tr m = s n ++ w ∧ L.Run x w (r.st m)

private theorem ahead_zero {L : LTS E F} (r : L.InfRun) {s : Chain (Move E F)}
    (hc : ∀ n, ∃ m, s n <+: r.tr m) : ∃ x, L.Run L.init (s 0) x ∧ Ahead L r s 0 x := by
  obtain ⟨m, w, hw⟩ := hc 0
  have hrun : L.Run L.init (s 0 ++ w) (r.st m) := hw ▸ (stages_infRun r).run m
  obtain ⟨x, hx, hxw⟩ := LTS.Run.of_append hrun
  exact ⟨x, hx, m, w, hw.symm, hxw⟩

private theorem ahead_succ {L : LTS E F} (r : L.InfRun) {s : Chain (Move E F)}
    (hm : s.Mono) (hc : ∀ n, ∃ m, s n <+: r.tr m) {n : ℕ} {x : L.State}
    (hx : Ahead L r s n x) :
    ∃ x', (∃ w, s (n + 1) = s n ++ w ∧ L.Run x w x') ∧ Ahead L r s (n + 1) x' := by
  obtain ⟨m, w, hw, hrun⟩ := hx
  obtain ⟨m₀, hm₀⟩ := hc (n + 1)
  obtain ⟨v, hv, hrv⟩ := (stages_infRun r).run_le (Nat.le_max_left m m₀)
  have hpre : s (n + 1) <+: r.tr (max m m₀) :=
    hm₀.trans ((Chain.Mono.le r.mono (Nat.le_max_right m m₀)))
  obtain ⟨d, hd⟩ := hm n
  have hlong : r.tr (max m m₀) = s n ++ (w ++ v) := by rw [hv, hw, List.append_assoc]
  have hdpre : d <+: w ++ v := by
    have h₁ : s n ++ d <+: s n ++ (w ++ v) := by rw [hd, ← hlong]; exact hpre
    exact (List.prefix_append_right_inj (s n)).1 h₁
  obtain ⟨e, he⟩ := hdpre
  have hrun' : L.Run x (d ++ e) (r.st (max m m₀)) := he ▸ hrun.append hrv
  obtain ⟨x', hx', hrest⟩ := LTS.Run.of_append hrun'
  refine ⟨x', ⟨d, hd.symm, hx'⟩, max m m₀, e, ?_, hrest⟩
  rw [hlong, ← he, ← hd, List.append_assoc]

/-- **A covering infinite run is followed coherently** along an increasing chain. -/
theorem stages_of_cover {L : LTS E F} (r : L.InfRun) {s : Chain (Move E F)} (hm : s.Mono)
    (hc : ∀ n, ∃ m, s n <+: r.tr m) : ∃ a : ℕ → L.State, Stages L a s := by
  obtain ⟨x₀, hx₀, ha₀⟩ := ahead_zero r hc
  have key : ∀ n x, Ahead L r s n x →
      ∃ x', (∃ w, s (n + 1) = s n ++ w ∧ L.Run x w x') ∧ Ahead L r s (n + 1) x' :=
    fun _ _ hx => ahead_succ r hm hc hx
  choose! nxt hnxt using key
  let a : ℕ → L.State := fun n => Nat.rec x₀ (fun k x => nxt k x) n
  have ha : ∀ n, Ahead L r s n (a n) := by
    intro n
    induction n with
    | zero => exact ha₀
    | succ n ih => exact (hnxt n (a n) ih).2
  exact ⟨a, hx₀, fun n => (hnxt n (a n) (ha n)).1⟩

/-- The infinite run that reads `u` and stops. -/
theorem exists_infRun_const {L : LTS E F} {u : List (Move E F)} {y : L.State}
    (h : L.Run L.init u y) : ∃ r : L.InfRun, ∀ n, u <+: r.tr (n + 1) := by
  let st : ℕ → L.State := fun n => Nat.casesOn n L.init fun _ => y
  let tr : Chain (Move E F) := fun n => Nat.casesOn n [] fun _ => u
  have hstep : ∀ n, ∃ w, tr (n + 1) = tr n ++ w ∧ L.Run (st n) w (st (n + 1)) := by
    intro n
    cases n with
    | zero => exact ⟨u, by simp [tr], h⟩
    | succ n => exact ⟨[], by simp [tr], .nil _⟩
  exact ⟨⟨st, tr, rfl, rfl, hstep⟩, fun n => List.prefix_refl _⟩

/-- **Plays and infinite plays of `ofLTS L` are covered by one infinite run.** -/
theorem exists_cover {L : LTS E F} {σ : Strategy E F} (hL : L.Denotes σ)
    {s : Chain (Move E F)} (hm : s.Mono) (hmem : ∀ n, s n ∈ (DStrategy.ofLTS L).toStrategy)
    (hlim : s.Unbounded → s.lim ∈ (DStrategy.ofLTS L).inf) :
    ∃ r : L.InfRun, ∀ n, ∃ m, s n <+: r.tr m := by
  by_cases hu : s.Unbounded
  · obtain ⟨⟨r, -, hr⟩, -⟩ := hlim hu
    refine ⟨r, fun n => ?_⟩
    have hn : s n ∈ r.tr.lim := hr ▸ Chain.mem_lim_self s n
    exact hn
  · obtain ⟨N, hN⟩ := Chain.Mono.eventually_const hm hu
    have hσ : Strategy.ofLTS L = σ := hL.ofLTS_eq
    have hmN : s N ∈ σ := hσ ▸ hmem N
    obtain ⟨y, hy⟩ := (hL (s N)).2 hmN
    obtain ⟨r, hr⟩ := exists_infRun_const hy
    refine ⟨r, fun n => ⟨1, ?_⟩⟩
    have hle : s n <+: s N := by
      rcases le_total n N with h | h
      · exact Chain.Mono.le hm h
      · rw [hN n h]; exact List.prefix_refl _
    exact hle.trans (hr 0)

/-- **A staged run is an infinite run** with the same limit (shifted by one stage). -/
theorem infRun_of_stages {L : LTS E F} {a : ℕ → L.State} {s : Chain (Move E F)}
    (h : Stages L a s) : ∃ r : L.InfRun, r.tr.lim = s.lim ∧ (s.Unbounded → r.tr.Unbounded) := by
  let st : ℕ → L.State := fun n => Nat.casesOn n L.init a
  let tr : Chain (Move E F) := fun n => Nat.casesOn n [] s
  have hstep : ∀ n, ∃ w, tr (n + 1) = tr n ++ w ∧ L.Run (st n) w (st (n + 1)) := by
    intro n
    cases n with
    | zero => exact ⟨s 0, by simp [tr], h.1⟩
    | succ n => exact h.2 n
  refine ⟨⟨st, tr, rfl, rfl, hstep⟩, ?_, fun hu k => ?_⟩
  · refine Chain.lim_eq_of (fun n => ⟨n, ?_⟩) (fun n => ⟨n + 1, List.prefix_refl _⟩)
    cases n with
    | zero => exact List.nil_prefix
    | succ n => exact Chain.Mono.le h.mono (Nat.le_succ n)
  · obtain ⟨n, hn⟩ := hu k
    exact ⟨n + 1, hn⟩

end Silmaril.Proofs.Games.DivLTSComp
