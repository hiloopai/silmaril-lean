module

public import Silmaril.Compiler.Core.Verified.Sim.Defs

/-! # Loops by productive macro-steps

A loop is simulated between related header states. From a related pair, one `Iteration`
either reaches Core undefined behaviour, or returns in Lir with a Core final state that
allows every crt0 observation of the return, or takes a nonempty path in both machines to
another related pair. A productive iteration in both machines rules out false divergence:
an infinite Lir run is matched by an infinite Core trace, never by stuttering.

`allowed`: every Lir behaviour from a related pair is allowed by Core from its source state
(`Sim.AllowedFrom`); `stuck_ub`: a stuck Lir run means Core reaches undefined behaviour. The
proof needs only the determinism of Lir: a finite Lir run passes through every later related
pair, so it ends by an exit or undefined behaviour, by induction on the chain of iterations
(`Ends`), or the chain is infinite and both machines diverge.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.LoopSim

open Silmaril.Cerberus
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Machine
open Spec
open Sim (UBFrom Final BehFrom AllowedFrom)
open Relation

variable {R : Type} [DecidableEq R]

/-- An infinite path from a predicate that is reached again by a nonempty path. -/
theorem infinite_of_productive {A : Type} {r : A → A → Prop} (P : A → Prop)
    (productive : ∀ a, P a → ∃ b, TransGen r a b ∧ P b) {a : A} (h : P a) :
    InfiniteTrace r a := by
  refine InfiniteTrace.coinduct (fun s => ∃ t, P t ∧ ReflTransGen r s t) ?_ ⟨a, h, .refl⟩
  rintro s ⟨t, valid, path⟩
  rcases ReflTransGen.cases_head path with rfl | ⟨u, step, rest⟩
  · obtain ⟨t', path', valid'⟩ := productive s valid
    obtain ⟨u, step, rest⟩ := TransGen.head'_iff.mp path'
    exact ⟨u, step, t', valid', rest⟩
  · exact ⟨u, step, t, valid, rest⟩

/-- One macro-step from related header states `ts` (Lir) and `cs` (Core). -/
def Iteration (p : Lir.Prog R) (file : Program) (labels : Labels)
    (I : Lir.State R → CState → Prop) (ts : Lir.State R) (cs : CState) : Prop :=
  UBFrom file labels cs ∨
    (∃ ts' cs', TransGen (Lir.Step p) ts ts' ∧ TransGen (coreStep file labels) cs cs' ∧
      I ts' cs') ∨
    ∃ t vs mem c, Lir.Steps p ts t ∧ Lir.step p t = .returned vs mem ∧
      ReflTransGen (coreStep file labels) cs c ∧ ∀ o, LirObs (.returned vs mem) o → Final c o

/-- A finite chain of iterations, ending in undefined behaviour or an exit. -/
inductive Ends (p : Lir.Prog R) (file : Program) (labels : Labels) :
    Lir.State R → CState → Prop where
  | ub {ts cs} : UBFrom file labels cs → Ends p file labels ts cs
  | exit {ts cs t vs mem c} : Lir.Steps p ts t → Lir.step p t = .returned vs mem →
      ReflTransGen (coreStep file labels) cs c → (∀ o, LirObs (.returned vs mem) o → Final c o) →
      Ends p file labels ts cs
  | loop {ts cs ts' cs'} : TransGen (Lir.Step p) ts ts' → TransGen (coreStep file labels) cs cs' →
      Ends p file labels ts' cs' → Ends p file labels ts cs

variable {p : Lir.Prog R} {file : Program} {labels : Labels} {I : Lir.State R → CState → Prop}

/-- Without a finite chain, the iterations go on forever in both machines. -/
theorem ends_or_diverges (step : ∀ ts cs, I ts cs → Iteration p file labels I ts cs)
    {ts : Lir.State R} {cs : CState} (h : I ts cs) :
    Ends p file labels ts cs ∨ Lir.Diverges p ts ∧ InfiniteTrace (coreStep file labels) cs := by
  by_cases e : Ends p file labels ts cs
  · exact .inl e
  right
  have next : ∀ ts cs, I ts cs → ¬ Ends p file labels ts cs → ∃ ts' cs',
      TransGen (Lir.Step p) ts ts' ∧ TransGen (coreStep file labels) cs cs' ∧ I ts' cs' ∧
        ¬ Ends p file labels ts' cs' := by
    intro ts cs h e
    rcases step ts cs h with ub | ⟨ts', cs', lir, core, h'⟩ | ⟨t, vs, mem, c, path, ret, core, fin⟩
    · exact absurd (.ub ub) e
    · exact ⟨ts', cs', lir, core, h', fun e' => e (.loop lir core e')⟩
    · exact absurd (.exit path ret core fin) e
  constructor
  · refine infinite_of_productive (fun ts => ∃ cs, I ts cs ∧ ¬ Ends p file labels ts cs) ?_ ⟨cs, h, e⟩
    rintro ts ⟨cs, h, e⟩
    obtain ⟨ts', cs', lir, -, h', e'⟩ := next ts cs h e
    exact ⟨ts', lir, cs', h', e'⟩
  · refine infinite_of_productive (fun cs => ∃ ts, I ts cs ∧ ¬ Ends p file labels ts cs) ?_ ⟨ts, h, e⟩
    rintro cs ⟨ts, h, e⟩
    obtain ⟨ts', cs', -, core, h', e'⟩ := next ts cs h e
    exact ⟨cs', core, ts', h', e'⟩

/-- A behaviour is a behaviour of every later state of the deterministic Lir run. -/
theorem behaves_of_steps {s s' : Lir.State R} (path : Lir.Steps p s s') :
    ∀ {b : Lir.Behavior}, Lir.Behaves p s b → Lir.Behaves p s' b
  | .returned vs mem, ⟨t, ht, hf⟩ => by
    rcases Lir.Steps.total path ht with h | h
    · exact ⟨t, h, hf⟩
    · rw [Lir.Steps.eq_of_final h (fun x e => by rw [hf] at e; cases e)]
      exact ⟨t, .refl, hf⟩
  | .trapped mem, ⟨t, ht, hf⟩ => by
    rcases Lir.Steps.total path ht with h | h
    · exact ⟨t, h, hf⟩
    · rw [Lir.Steps.eq_of_final h (fun x e => by rw [hf] at e; cases e)]
      exact ⟨t, .refl, hf⟩
  | .stuck, ⟨t, ht, hf⟩ => by
    rcases Lir.Steps.total path ht with h | h
    · exact ⟨t, h, hf⟩
    · rw [Lir.Steps.eq_of_final h (fun x e => by rw [hf] at e; cases e)]
      exact ⟨t, .refl, hf⟩
  | .diverges, d => Lir.Diverges.of_steps d path

/-- A divergent Lir run has no finite behaviour. -/
theorem finite_of_diverges {s : Lir.State R} (d : Lir.Diverges p s) {b : Lir.Behavior}
    (beh : Lir.Behaves p s b) : b = .diverges := by
  have stops : ∀ {t : Lir.State R} {r : Lir.Result R}, Lir.Steps p s t → Lir.step p t = r →
      (∀ x, r ≠ .running x) → False := by
    intro t r path final stopped
    obtain ⟨x, hx⟩ := (d.of_steps path).running
    exact stopped x (final ▸ hx)
  cases b with
  | returned vs mem =>
    obtain ⟨t, path, final⟩ := beh
    exact (stops path final (fun x e => by cases e)).elim
  | trapped mem =>
    obtain ⟨t, path, final⟩ := beh
    exact (stops path final (fun x e => by cases e)).elim
  | stuck =>
    obtain ⟨t, path, final⟩ := beh
    exact (stops path final (fun x e => by cases e)).elim
  | diverges => rfl

theorem AllowedFrom.prefix {c t : CState} {o : Obs} (path : ReflTransGen (coreStep file labels) c t)
    (allowed : AllowedFrom file labels t o) : AllowedFrom file labels c o := by
  rcases allowed with ex | ub | beh
  · exact .inl ex
  · exact .inr (.inl (UBFrom.prefix path ub))
  · exact .inr (.inr (BehFrom.prefix path beh))

theorem Ends.allowed {ts : Lir.State R} {cs : CState} (e : Ends p file labels ts cs) :
    ∀ {b : Lir.Behavior} {o : Obs}, Lir.Behaves p ts b → LirObs b o → AllowedFrom file labels cs o := by
  induction e with
  | ub ub => intro b o _ _; exact .inr (.inl ub)
  | @exit ts cs t vs mem c path ret core fin =>
    intro b o beh obs
    have same := Lir.Behaves.unique beh (show Lir.Behaves p ts (.returned vs mem) from ⟨t, path, ret⟩)
    subst same
    exact .inr (.inr (.finite core (fin o obs)))
  | loop lir core _ ih =>
    intro b o beh obs
    exact AllowedFrom.prefix core.to_reflTransGen (ih (behaves_of_steps lir.to_reflTransGen beh) obs)

theorem Ends.stuck_ub {ts : Lir.State R} {cs : CState} (e : Ends p file labels ts cs) :
    Lir.Behaves p ts .stuck → UBFrom file labels cs := by
  induction e with
  | ub ub => intro _; exact ub
  | @exit ts cs t vs mem c path ret core fin =>
    intro beh
    cases Lir.Behaves.unique beh (show Lir.Behaves p ts (.returned vs mem) from ⟨t, path, ret⟩)
  | loop lir core _ ih =>
    intro beh
    exact UBFrom.prefix core.to_reflTransGen (ih (behaves_of_steps lir.to_reflTransGen beh))

/-- **Every Lir behaviour from related header states is allowed by Core.** -/
theorem allowed (step : ∀ ts cs, I ts cs → Iteration p file labels I ts cs)
    {ts : Lir.State R} {cs : CState} (h : I ts cs) {b : Lir.Behavior} {o : Obs}
    (beh : Lir.Behaves p ts b) (obs : LirObs b o) : AllowedFrom file labels cs o := by
  rcases ends_or_diverges step h with e | ⟨d, trace⟩
  · exact e.allowed beh obs
  · cases finite_of_diverges d beh
    change o = .diverges at obs
    subst obs
    exact .inr (.inr (.diverges trace))

/-- **A stuck Lir run from related header states means Core reaches undefined behaviour.** -/
theorem stuck_ub (step : ∀ ts cs, I ts cs → Iteration p file labels I ts cs)
    {ts : Lir.State R} {cs : CState} (h : I ts cs) (beh : Lir.Behaves p ts .stuck) :
    UBFrom file labels cs := by
  rcases ends_or_diverges step h with e | ⟨d, -⟩
  · exact e.stuck_ub beh
  · cases finite_of_diverges d beh

end Silmaril.Compile.Core.Verified.LoopSim
