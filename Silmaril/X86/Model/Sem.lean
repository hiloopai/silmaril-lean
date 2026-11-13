module

public import Silmaril.Machine.Execution
public import Silmaril.X86.Basic

/-!
# Machines with chaos, and maps between them

The x86 models of this repository (`X86.Ext`, `X86.Ext8`, `X86.Ext.Wire` and
every configuration of the feature-parametric machine `X86.Features`) have
different state types and different outcome types. To compare them, each is
viewed as a `Sem σ`: a step from a state to a `Step σ`, which is one of

* `retired next`: the instruction retired;
* `returned final`: a RET popped the designated return address;
* `halted`: a definite stop that every refinement keeps (an architectural
  fault, UD2, a data fault, #DE);
* `unsettled`: anything a more complete model may change. That is chaos (bytes
  no decoder accepts, a decoded instruction whose behaviour is not modelled, a
  condition on an architecturally undefined flag), and the outcomes a larger
  feature set or a larger decoder changes (a missing feature, a fetch fault on a
  truncated encoding).

## Maps

A map `Hom S T` is a state map `f` such that, at every state where `S` is
settled, `T` takes the image step: `T.step exit (f s) = (S.step exit s).map f`.
This is behaviour inclusion with chaos for the unmodelled: `T` may do anything
where `S` is unsettled, and must agree elsewhere. Maps compose (`Hom.comp`) and
`Hom.id` is the identity.

## What a map transfers

* **Existential judgments, unconditionally**: runs (`Hom.run`), reachability
  (`Hom.reaches`), returns (`Hom.returns`) and leads-to (`Hom.leadsTo`).
* **Universal judgments, under `Stable`** (no reachable state is unsettled):
  `T` from `f i` runs exactly the image of the runs of `S` from `i`
  (`Hom.run_eq`), is stable (`Hom.stable`), and every `T`-return is the image of
  an `S`-return (`Hom.returns_back`). Safety (`Hom.safe`) and total correctness
  (`Hom.totalOn`) transfer when their good outcomes are settled.
* **Invariants** (`Hom.invariant`): an inductive invariant whose states are all
  settled transfers to its image.
-/

@[expose] public section

namespace Silmaril.X86.Model

open Silmaril.X86 (Word)

/-- The outcome of one step, as seen by refinement. -/
inductive Step (σ : Type) where
  | retired (next : σ)
  | returned (final : σ)
  /-- A definite stop that every refinement keeps. -/
  | halted
  /-- Chaos, or an outcome a more complete model may change. -/
  | unsettled

namespace Step

variable {σ τ υ : Type}

/-- The image of a step under a state map. -/
def map (f : σ → τ) : Step σ → Step τ
  | .retired s => .retired (f s)
  | .returned s => .returned (f s)
  | .halted => .halted
  | .unsettled => .unsettled

@[simp] theorem map_retired (f : σ → τ) (s : σ) : (Step.retired s).map f = .retired (f s) := rfl
@[simp] theorem map_returned (f : σ → τ) (s : σ) : (Step.returned s).map f = .returned (f s) :=
  rfl
@[simp] theorem map_halted (f : σ → τ) : (Step.halted : Step σ).map f = .halted := rfl
@[simp] theorem map_unsettled (f : σ → τ) : (Step.unsettled : Step σ).map f = .unsettled := rfl

@[simp] theorem map_id (o : Step σ) : o.map id = o := by cases o <;> rfl

theorem map_map (f : σ → τ) (g : τ → υ) (o : Step σ) : (o.map f).map g = o.map (g ∘ f) := by
  cases o <;> rfl

theorem map_ne_unsettled {f : σ → τ} {o : Step σ} (h : o ≠ .unsettled) : o.map f ≠ .unsettled := by
  cases o <;> simp_all [map]

theorem map_eq_retired {f : σ → τ} {o : Step σ} {t : τ} (h : o.map f = .retired t) :
    ∃ s, o = .retired s ∧ f s = t := by
  cases o <;> simp_all [map]

theorem map_eq_returned {f : σ → τ} {o : Step σ} {t : τ} (h : o.map f = .returned t) :
    ∃ s, o = .returned s ∧ f s = t := by
  cases o <;> simp_all [map]

end Step

/-- A machine with chaos: one step per exit address and state. -/
structure Sem (σ : Type) where
  step : Word → σ → Step σ

namespace Sem

variable {σ τ υ : Type} (S : Sem σ) (exit : Word)

/-- Retirement only. -/
def stepOpt (s : σ) : Option σ :=
  match S.step exit s with
  | .retired next => some next
  | _ => none

/-- `n` retirements. -/
def run (n : Nat) (s : σ) : Option σ := Machine.Execution.run (S.stepOpt exit) n s

/-- `m` is reachable from `initial` by retirements. -/
def Reaches (initial m : σ) : Prop := ∃ n, S.run exit n initial = some m

/-- Retirements, then a return to `exit` with final state `final`. -/
def Returns (initial final : σ) : Prop :=
  ∃ n mid, S.run exit n initial = some mid ∧ S.step exit mid = .returned final

/-- No reachable state is unsettled. -/
def Stable (initial : σ) : Prop := ∀ n m, S.run exit n initial = some m → S.step exit m ≠ .unsettled

/-- Every reachable state and its step satisfy `good`. -/
def Safe (initial : σ) (good : σ → Step σ → Prop) : Prop :=
  ∀ n m, S.run exit n initial = some m → good m (S.step exit m)

/-- Total correctness on a family of launches: each is safe and returns into `goal`. -/
def TotalOn {ι : Type} (domain : ι → Prop) (init : ι → σ) (good : σ → Step σ → Prop)
    (goal : ι → σ → Prop) : Prop :=
  ∀ i, domain i → S.Safe exit (init i) good ∧ ∃ final, S.Returns exit (init i) final ∧ goal i final

/-- From every state in `P`, retirements reach a state in `Q`. -/
def LeadsTo (P Q : σ → Prop) : Prop := ∀ s, P s → ∃ n t, S.run exit n s = some t ∧ Q t

/-- `I` is an inductive invariant of settled states: every state in `I` is
settled and its retirement stays in `I`. -/
def Invariant (I : σ → Prop) : Prop :=
  ∀ s, I s → S.step exit s ≠ .unsettled ∧ ∀ next, S.stepOpt exit s = some next → I next

variable {S exit}

theorem stepOpt_eq_some_iff {s next : σ} : S.stepOpt exit s = some next ↔ S.step exit s = .retired next := by
  unfold stepOpt
  split <;> simp_all

theorem run_succ (n : Nat) (s : σ) : S.run exit (n + 1) s = (S.stepOpt exit s).bind (S.run exit n) :=
  rfl

theorem Stable.next {initial m : σ} (h : S.Stable exit initial) (hs : S.stepOpt exit initial = some m) :
    S.Stable exit m := fun n m' hr => h (n + 1) m' (by rw [run_succ, hs]; exact hr)

theorem Invariant.stable {I : σ → Prop} (h : S.Invariant exit I) {s : σ} (hs : I s) :
    S.Stable exit s := by
  intro n m hr
  induction n generalizing s with
  | zero => cases hr; exact (h _ hs).1
  | succ n ih =>
    rw [run_succ] at hr
    cases hn : S.stepOpt exit s with
    | none => rw [hn] at hr; cases hr
    | some next => rw [hn] at hr; exact ih ((h s hs).2 next hn) hr

theorem Safe.stable {initial : σ} {good : σ → Step σ → Prop} (h : S.Safe exit initial good)
    (hg : ∀ m o, good m o → o ≠ .unsettled) : S.Stable exit initial :=
  fun n m hr => hg m _ (h n m hr)

/-! ## Maps -/

/-- A map from `S` to `T`: at every settled state of `S`, `T` takes the image step. -/
structure Hom (S : Sem σ) (T : Sem τ) where
  map : σ → τ
  step : ∀ exit s, S.step exit s ≠ .unsettled → T.step exit (map s) = (S.step exit s).map map

/-- The identity map. -/
def Hom.id (S : Sem σ) : Hom S S where
  map s := s
  step _ _ _ := (Step.map_id _).symm

/-- Maps compose. -/
def Hom.comp {S : Sem σ} {T : Sem τ} {U : Sem υ} (φ : Hom S T) (ψ : Hom T U) : Hom S U where
  map := ψ.map ∘ φ.map
  step exit s h := by
    show U.step exit (ψ.map (φ.map s)) = _
    rw [ψ.step exit (φ.map s) (by rw [φ.step exit s h]; exact Step.map_ne_unsettled h),
      φ.step exit s h, Step.map_map]

/-- A map whose state map is the identity, from stepwise agreement. -/
def Hom.ofAgree {S T : Sem σ} (h : ∀ exit s, S.step exit s ≠ .unsettled → T.step exit s = S.step exit s) :
    Hom S T where
  map s := s
  step exit s hs := by rw [h exit s hs]; exact (Step.map_id _).symm

namespace Hom

variable {T : Sem τ} (φ : Hom S T)

theorem stepOpt {s next : σ} (h : S.stepOpt exit s = some next) :
    T.stepOpt exit (φ.map s) = some (φ.map next) := by
  rw [stepOpt_eq_some_iff] at h ⊢
  rw [φ.step exit s (by rw [h]; nofun), h]; rfl

/-! ### Existential judgments -/

theorem run {n : Nat} {s m : σ} (h : S.run exit n s = some m) :
    T.run exit n (φ.map s) = some (φ.map m) := by
  induction n generalizing s with
  | zero => cases h; rfl
  | succ n ih =>
    rw [run_succ] at h ⊢
    cases hs : S.stepOpt exit s with
    | none => rw [hs] at h; cases h
    | some next => rw [hs] at h; rw [φ.stepOpt hs]; exact ih h

theorem reaches {s m : σ} (h : S.Reaches exit s m) : T.Reaches exit (φ.map s) (φ.map m) :=
  let ⟨n, hn⟩ := h; ⟨n, φ.run hn⟩

theorem returns {s final : σ} (h : S.Returns exit s final) :
    T.Returns exit (φ.map s) (φ.map final) := by
  obtain ⟨n, mid, hr, hs⟩ := h
  exact ⟨n, φ.map mid, φ.run hr, by rw [φ.step exit mid (by rw [hs]; nofun), hs]; rfl⟩

theorem leadsTo {P Q : σ → Prop} (h : S.LeadsTo exit P Q) {s : σ} (hs : P s) :
    ∃ n t, T.run exit n (φ.map s) = some (φ.map t) ∧ Q t :=
  let ⟨n, t, hr, hq⟩ := h s hs; ⟨n, t, φ.run hr, hq⟩

/-- Leads-to along a map whose state map is the identity. -/
theorem leadsTo_id {S T : Sem σ} (φ : Hom S T) (hφ : ∀ s, φ.map s = s) {P Q : σ → Prop}
    (h : S.LeadsTo exit P Q) : T.LeadsTo exit P Q := fun s hs =>
  let ⟨n, t, hr, hq⟩ := φ.leadsTo h hs
  ⟨n, t, by rw [hφ, hφ] at hr; exact hr, hq⟩

/-! ### Universal judgments, under stability -/

/-- From a stable state, `T` runs exactly the image of the runs of `S`. -/
theorem run_eq {initial : σ} (hs : S.Stable exit initial) (n : Nat) :
    T.run exit n (φ.map initial) = (S.run exit n initial).map φ.map := by
  induction n generalizing initial with
  | zero => rfl
  | succ n ih =>
    rw [run_succ, run_succ]
    have hstep := φ.step exit initial (hs 0 initial rfl)
    have : T.stepOpt exit (φ.map initial) = (S.stepOpt exit initial).map φ.map := by
      unfold Sem.stepOpt
      rw [hstep]
      cases S.step exit initial <;> rfl
    rw [this]
    cases hn : S.stepOpt exit initial with
    | none => rfl
    | some next => exact ih (hs.next hn)

theorem run_back {initial : σ} (hs : S.Stable exit initial) {n : Nat} {t : τ}
    (h : T.run exit n (φ.map initial) = some t) : ∃ m, S.run exit n initial = some m ∧ φ.map m = t := by
  rw [φ.run_eq hs] at h
  cases hr : S.run exit n initial with
  | none => rw [hr] at h; cases h
  | some m => rw [hr] at h; exact ⟨m, rfl, Option.some.inj h⟩

theorem stable {initial : σ} (hs : S.Stable exit initial) : T.Stable exit (φ.map initial) := by
  intro n t hr
  obtain ⟨m, hm, rfl⟩ := φ.run_back hs hr
  rw [φ.step exit m (hs n m hm)]
  exact Step.map_ne_unsettled (hs n m hm)

theorem reaches_back {initial : σ} (hs : S.Stable exit initial) {t : τ}
    (h : T.Reaches exit (φ.map initial) t) : ∃ m, S.Reaches exit initial m ∧ φ.map m = t :=
  let ⟨n, hn⟩ := h
  let ⟨m, hm, e⟩ := φ.run_back hs hn
  ⟨m, ⟨n, hm⟩, e⟩

/-- Every return of `T` from the image of a stable state is the image of a return of `S`. -/
theorem returns_back {initial : σ} (hs : S.Stable exit initial) {final : τ}
    (h : T.Returns exit (φ.map initial) final) :
    ∃ f, S.Returns exit initial f ∧ φ.map f = final := by
  obtain ⟨n, mid, hr, hret⟩ := h
  obtain ⟨m, hm, rfl⟩ := φ.run_back hs hr
  rw [φ.step exit m (hs n m hm)] at hret
  obtain ⟨f, hf, e⟩ := Step.map_eq_returned hret
  exact ⟨f, ⟨n, m, hm, hf⟩, e⟩

/-- **Safety transfers** when its good outcomes are settled, to every judgment
`good'` that holds of the images of good states and steps. -/
theorem safe {initial : σ} {good : σ → Step σ → Prop} {good' : τ → Step τ → Prop}
    (h : S.Safe exit initial good) (hg : ∀ m o, good m o → o ≠ .unsettled)
    (hmap : ∀ m o, good m o → good' (φ.map m) (o.map φ.map)) :
    T.Safe exit (φ.map initial) good' := by
  have hs := h.stable hg
  intro n t hr
  obtain ⟨m, hm, rfl⟩ := φ.run_back hs hr
  rw [φ.step exit m (hs n m hm)]
  exact hmap m _ (h n m hm)

/-- **Total correctness transfers** along a map, with goals and good outcomes
mapped as for `safe`. -/
theorem totalOn {ι : Type} {domain : ι → Prop} {init : ι → σ} {good : σ → Step σ → Prop}
    {goal : ι → σ → Prop} {good' : τ → Step τ → Prop} {goal' : ι → τ → Prop}
    (h : S.TotalOn exit domain init good goal) (hg : ∀ m o, good m o → o ≠ .unsettled)
    (hmap : ∀ m o, good m o → good' (φ.map m) (o.map φ.map))
    (hgoal : ∀ i m, goal i m → goal' i (φ.map m)) :
    T.TotalOn exit domain (φ.map ∘ init) good' goal' := fun i hi =>
  let ⟨hsafe, final, hret, hgl⟩ := h i hi
  ⟨φ.safe hsafe hg hmap, φ.map final, φ.returns hret, hgoal i final hgl⟩

/-- An inductive invariant of settled states transfers to its image. -/
theorem invariant {I : σ → Prop} (h : S.Invariant exit I) :
    T.Invariant exit fun t => ∃ s, I s ∧ φ.map s = t := by
  rintro t ⟨s, hs, rfl⟩
  have hset := (h s hs).1
  refine ⟨by rw [φ.step exit s hset]; exact Step.map_ne_unsettled hset, fun next hn => ?_⟩
  rw [stepOpt_eq_some_iff, φ.step exit s hset] at hn
  obtain ⟨s', hs', rfl⟩ := Step.map_eq_retired hn
  exact ⟨s', (h s hs).2 s' (stepOpt_eq_some_iff.mpr hs'), rfl⟩

end Hom

end Sem

end Silmaril.X86.Model
