module

public import Silmaril.Wasm.Models.FXAsyncFX.Thms
public import Silmaril.Wasm.Models.FXVRuns.Thms

/-!
# Backward simulation: inevitability, and behaviours

The forward simulation (`FXAsyncFX.sim_step`) matches each kernel step by a `StepFX'` run. For
the converse, every `StepFX'` run from a related configuration must pass through a related
configuration of the next kernel step (or stop without a result). This module gives the generic
argument:

* `Inev R T G a`: every run of `R` from `a` reaches `G`, or stops at a non-terminal (`¬ T`)
  configuration, in finitely many steps; `InevP`: the same after at least one step;
* `inev_run`, `inevP_run`: a run from `a` to a terminal configuration passes through `G`, by a
  shorter run (`RunN`); `inev_inf`: an infinite trace from `a` passes through `G`;
* `UMatched`: the per-step obligation of the backward simulation;
* **`fx_sub_kernel`**: if every related configuration of the fragment satisfies `UMatched`, every
  `StepFX'` behaviour of a related configuration is `obsB` of a kernel behaviour.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncBack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Proofs.Wasm.Models.FXAsyncFX (SX)

/-! ## Inevitability -/

section Generic

variable {A : Type} (R : A → A → Prop) (T : A → Prop)

/-- Every run of `R` from `a` reaches `G`, or stops at a non-terminal configuration. -/
inductive Inev (G : A → Prop) : A → Prop where
  | base {a : A} (h : G a) : Inev G a
  | step {a : A} (hT : ¬ T a) (h : ∀ b, R a b → Inev G b) : Inev G a

/-- `Inev` after at least one step. -/
def InevP (G : A → Prop) (a : A) : Prop := ¬ T a ∧ ∀ b, R a b → Inev R T G b

/-- Runs of exactly `n` steps. -/
inductive RunN : Nat → A → A → Prop where
  | zero {a : A} : RunN 0 a a
  | succ {n : Nat} {a b c : A} (h : R a b) (h' : RunN n b c) : RunN (n + 1) a c

variable {R T}

theorem runN_of_rtg {a d : A} (h : Relation.ReflTransGen R a d) : ∃ n, RunN R n a d := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .zero⟩
  | head hab _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .succ hab hn⟩

theorem inev_run {G : A → Prop} {a : A} (h : Inev R T G a) :
    ∀ {n : Nat} {d : A}, RunN R n a d → T d → ∃ g m, G g ∧ m ≤ n ∧ RunN R m g d := by
  induction h with
  | base hG => exact fun hr _ => ⟨_, _, hG, le_refl _, hr⟩
  | step hT _ ih =>
    intro n d hr hd
    cases hr with
    | zero => exact absurd hd hT
    | succ hab hr' =>
      obtain ⟨g, m, hg, hm, hgd⟩ := ih _ hab hr' hd
      exact ⟨g, m, hg, by omega, hgd⟩

theorem inevP_run {G : A → Prop} {a : A} (h : InevP R T G a) {n : Nat} {d : A}
    (hr : RunN R n a d) (hd : T d) : ∃ g m, G g ∧ m < n ∧ RunN R m g d := by
  cases hr with
  | zero => exact absurd hd h.1
  | succ hab hr' =>
    obtain ⟨g, m, hg, hm, hgd⟩ := inev_run (h.2 _ hab) hr' hd
    exact ⟨g, m, hg, by omega, hgd⟩

theorem inev_inf {G : A → Prop} {a : A} (h : Inev R T G a) (hi : Silmaril.InfiniteTrace R a) :
    ∃ g, G g ∧ Silmaril.InfiniteTrace R g := by
  induction h with
  | base hG => exact ⟨_, hG, hi⟩
  | step _ _ ih =>
    obtain ⟨b, hab, hb⟩ := hi.unfold
    exact ih b hab hb

theorem inevP_inf {G : A → Prop} {a : A} (h : InevP R T G a)
    (hi : Silmaril.InfiniteTrace R a) : ∃ g, G g ∧ Silmaril.InfiniteTrace R g := by
  obtain ⟨b, hab, hb⟩ := hi.unfold
  exact inev_inf (h.2 b hab) hb

end Generic

/-! ## The backward obligation -/

variable {H : Type} (S : Setup H) {W : Prog (Ins Val)}

/-- A configuration whose code is a Core result. -/
def TermFX (d : ConfigFX H) : Prop := ∃ r : Result, d.code = r.toAdmin.map .core

/-- **The per-step obligation of the backward simulation**: after a kernel step to `x'`, every
`StepFX'` run from `c` reaches a configuration related to `x'` (or stops at a non-result), after
at least one step; when the kernel stops, `c` is its result, Core values. -/
def UMatched (S : Setup H) (W : Prog (Ins Val)) (c : ConfigFX H) :
    Res (SCfg Val) Val → Prop
  | .next x' => InevP (SX S) TermFX (fun c' => Rel S W x' c') c
  | .stop o => ∃ ws, c.code = cvals ws ∧ obsB o.toObs = .returns ws

theorem runN_succ_next {x x' : SCfg Val} (h : sstep W i32Test x = .next x') (n : Nat) :
    runN (sstep W i32Test) (n + 1) x = runN (sstep W i32Test) n x' := by
  simp only [runN, h]

theorem result_eq {ws : List Val} {r : Result} (h : cvals ws = r.toAdmin.map .core) :
    r = .values ws := by
  have h' := congrArg (fun l => (Silmaril.Proofs.Wasm.Models.FXVRuns.fnvF l)) h
  cases r with
  | values vs =>
    have h2 : cvals ws = cvals vs := h
    exact congrArg Result.values (List.map_injective_iff.mpr (fun _ _ h => FVal.val.inj h)
      (by simpa [Silmaril.Proofs.Wasm.Models.FXVRuns.fnvF_cvals, liftV] using
        congrArg (fun l => (Silmaril.Proofs.Wasm.Models.FXVRuns.fnvF l).1) h2)).symm
  | throw a =>
    simp [Silmaril.Proofs.Wasm.Models.FXVRuns.fnvF_cvals, Result.toAdmin,
      Silmaril.Proofs.Wasm.Models.FXVRuns.fnvF, Silmaril.Proofs.Wasm.Models.FXVRuns.fval?,
      Admin.val?] at h'
  | trap =>
    simp [Silmaril.Proofs.Wasm.Models.FXVRuns.fnvF_cvals, Result.toAdmin] at h'

theorem beh_of_next {x x' : SCfg Val} (h : sstep W i32Test x = .next x') {ob : Obs Val}
    (hob : ob ∈ beh (sstep W i32Test) x') : ob ∈ beh (sstep W i32Test) x := by
  rcases hob with ⟨n, o, hrun, rfl⟩ | ⟨rfl, hdiv⟩
  · exact Or.inl ⟨n + 1, o, by rw [runN_succ_next h]; exact hrun, rfl⟩
  · refine Or.inr ⟨rfl, fun n => ?_⟩
    cases n with
    | zero => exact ⟨x, rfl⟩
    | succ n => rw [runN_succ_next h]; exact hdiv n

variable (Sup : SCfg Val → Prop)

/-- The hypotheses of the backward argument: the fragment is stable along kernel runs, every
related configuration of the fragment meets `UMatched`, and Core values do not step. -/
structure BackHyp (S : Setup H) (W : Prog (Ins Val)) (Sup : SCfg Val → Prop) : Prop where
  next : ∀ x x', Sup x → sstep W i32Test x = .next x' → Sup x'
  matched : ∀ x c, Rel S W x c → Sup x → UMatched S W c (sstep W i32Test x)
  stuck : ∀ (c d : ConfigFX H) (ws : List Val), c.code = cvals ws → ¬ SX S c d

variable {S Sup}

theorem fin_stop (hB : BackHyp S W Sup) {x : SCfg Val} {c d : ConfigFX H} {r : Result} {n : Nat}
    {o : Outcome Val} {ws : List Val} (hs : sstep W i32Test x = .stop o) (hc : c.code = cvals ws)
    (ho : obsB o.toObs = .returns ws) (hrun : RunN (SX S) n c d) (hd : d.code = r.toAdmin.map .core) :
    ∃ ob ∈ beh (sstep W i32Test) x, obsB ob = r.toBehaviour := by
  cases hrun with
  | zero =>
    have hr : r = .values ws := result_eq (hc.symm.trans hd)
    refine ⟨o.toObs, Or.inl ⟨1, o, by simp only [runN, hs], rfl⟩, ?_⟩
    rw [ho, hr]
    rfl
  | succ hab _ => exact absurd hab (hB.stuck _ _ ws hc)

theorem fin_sub (hB : BackHyp S W Sup) : ∀ (n : Nat) (x : SCfg Val) (c d : ConfigFX H) (r : Result),
    Rel S W x c → Sup x → RunN (SX S) n c d → d.code = r.toAdmin.map .core →
      ∃ ob ∈ beh (sstep W i32Test) x, obsB ob = r.toBehaviour := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x c d r hR hsup hrun hd
  cases hs : sstep W i32Test x with
  | next x' =>
    have hU : InevP (SX S) TermFX (Rel S W x') c :=
      (hs ▸ hB.matched x c hR hsup : UMatched S W c (.next x'))
    obtain ⟨g, m, hg, hm, hgd⟩ := inevP_run hU hrun ⟨r, hd⟩
    obtain ⟨ob, hob, heq⟩ := ih m hm x' g d r hg (hB.next x x' hsup hs) hgd hd
    exact ⟨ob, beh_of_next hs hob, heq⟩
  | stop o =>
    have hU : ∃ ws, c.code = cvals ws ∧ obsB o.toObs = .returns ws :=
      (hs ▸ hB.matched x c hR hsup : UMatched S W c (.stop o))
    obtain ⟨ws, hc, ho⟩ := hU
    exact fin_stop hB hs hc ho hrun hd

theorem div_sub (hB : BackHyp S W Sup) : ∀ (k : Nat) (x : SCfg Val) (c : ConfigFX H),
    Rel S W x c → Sup x → Silmaril.InfiniteTrace (SX S) c →
      ∃ y, runN (sstep W i32Test) k x = .next y := by
  intro k
  induction k with
  | zero => exact fun x _ _ _ _ => ⟨x, rfl⟩
  | succ k ih =>
    intro x c hR hsup hi
    have hU := hB.matched x c hR hsup
    cases hs : sstep W i32Test x with
    | next x' =>
      rw [hs] at hU
      obtain ⟨g, hg, hgi⟩ := inevP_inf hU hi
      obtain ⟨y, hy⟩ := ih x' g hg (hB.next x x' hsup hs) hgi
      exact ⟨y, by rw [runN_succ_next hs]; exact hy⟩
    | stop o =>
      rw [hs] at hU
      obtain ⟨ws, hc, -⟩ := hU
      obtain ⟨b, hab, -⟩ := hi.unfold
      exact absurd hab (hB.stuck _ _ ws hc)

/-- **Every `StepFX'` behaviour of a related configuration is a kernel behaviour**, given the
backward obligation `BackHyp`. -/
theorem fx_sub_kernel (hB : BackHyp S W Sup) {x : SCfg Val} {c : ConfigFX H} (hR : Rel S W x c)
    (hsup : Sup x) :
    ∀ b ∈ behavioursFX' S.P S.host S.fx c, ∃ ob ∈ beh (sstep W i32Test) x, obsB ob = b := by
  rintro b (⟨d, r, hcd, hd, rfl⟩ | ⟨rfl, hi⟩)
  · obtain ⟨n, hn⟩ := runN_of_rtg hcd
    exact fin_sub hB n x c d r hR hsup hn hd
  · exact ⟨.diverges, Or.inr ⟨rfl, fun k => div_sub hB k x c hR hsup hi⟩, rfl⟩

end Silmaril.Proofs.Wasm.Models.FXAsyncBack
