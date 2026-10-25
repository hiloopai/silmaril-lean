module

public import Silmaril.Wasm.Behaviour.Semantics.Core
public import Silmaril.Wasm.Behaviour.Relations
public import Silmaril.Wasm.SingleThreaded.Exec.CheckedRun
public import Silmaril.Wasm.SingleThreaded.Exec.InvokeRun
public import Silmaril.Wasm.SingleThreaded.Determinism
public import Silmaril.Wasm.SingleThreaded.Determinism.Stuck
public import Silmaril.Wasm.Execution.Core.Properties

/-!
# The interpreter, restated as a statement about `behaviours`

The interpreter theorems of `Silmaril/Wasm/SingleThreaded/Exec/` speak about
*configurations*: `runInvoke?_sound` says the interpreter's final configuration
is reachable, `runInvoke?_stopped` says it admits no further host-free step, and
`runInvoke?_complete` says every host-free normal form is found with enough fuel.
This file restates all three in the vocabulary of
`Silmaril/Wasm/Behaviour/Semantics/Core.lean`: as equations and refinements
between `Execution.Core.behaviours`, the *set* of observable outcomes of an
entry point, and the singleton set `{r.toBehaviour}` that the interpreter
computes. Nothing here is new proof work about Wasm; it is the existing
theorems in the behaviour vocabulary, plus the two general facts about abstract
rewriting that the translation needs.

## The three ingredients of the singleton theorem

the interpreter-conformance contract asks for "`runChecked?` sound and complete as
`behaviours = {run result}` under the deterministic profile". That equation
splits into three obligations, and **only two of them are discharged here**.

1. **Soundness** — `r.toBehaviour ∈ behaviours …`. Immediate from
   `runInvoke?_steps_noHost` and `mem_behavioursOf`
   (`mem_behaviours_of_runInvoke?`).
2. **No other terminating behaviour** — discharged. A terminating behaviour is
   witnessed by a run to a configuration whose code is a lifted result; such a
   configuration is a host-free normal form (`not_step_of_terminal`, from the
   `Determinism/Stuck.lean` no-step lemmas, which need no typing); host-free
   reduction in the single-threaded profile is *subcommutative*
   (`Det.DStep.join'`), hence confluent, hence has unique normal forms
   (`eq_of_steps_of_nf`); and `Config.outcome?` is injective on the code
   (`outcome?_eq_some_of_code`). This gives
   `behavioursOf … c ⊆ {r.toBehaviour, Behaviour.diverges}` unconditionally.
3. **No divergence** — **not** discharged, and not dischargeable from what
   `Silmaril/Wasm/SingleThreaded/Determinism/` currently proves. See below.

## The determinism situation, in detail

`Determinism/Join.lean` proves `Det.DStep.join'`: host-free reduction in the
deterministic profile is **subcommutative**, i.e. two successors are joinable in
*at most one* step on each side (`Det.Join`). It is explicitly *not* a function:
`Step_pure/trap-instrs` overlaps with `Step/ctxt-instrs` on a shorter bubble, so
`v₁ v₂ TRAP` steps both to `TRAP` and to `v₁ TRAP`. That non-determinism is
recorded formally here as `exists_step_not_unique`, which is why **taking
determinism of `Step (profile o) noHost` as a hypothesis would be vacuous** and
is not done. `Determinism.lean`'s `Step.deterministic_profile` and
`Internal.deterministic` are the same `Join` statement, not functionality.

Subcommutativity gives confluence and unique normal forms — ingredient 2 — but
it does **not** give "a reachable normal form forbids an infinite trace".
Counterexample: `R = {(a,a), (a,b)}` with `b` a normal form is subcommutative
(join `a` and `b` at `b`), `a` reaches the normal form `b`, and `a → a → ⋯` is
infinite. The *strict* diamond property would suffice, and it is false here for
the same bubbling reason: `TRAP` and `v₁ TRAP` cannot be joined in exactly one
step each, because `TRAP` is already normal.

So the singleton form is stated with the missing ingredient as an explicit,
manifestly non-vacuous hypothesis, in two interchangeable shapes:

* `behaviours_eq_singleton_of_runInvoke?` takes
  `¬ Diverges (profile o) noHost (invoke s a vs)` — the fact about *this* entry
  point that is missing;
* `behaviours_eq_singleton_of_runInvoke?_of_weakToStrong` takes the global
  property `WeakToStrong (Step (profile o) noHost)` — "weak normalization
  implies strong normalization" — which is believed true of Wasm's host-free
  deterministic reduction but is not proved anywhere in this development.

`weakToStrong_of_deterministic` discharges `WeakToStrong` from determinism; as
just explained, that instance does *not* apply to `Step (profile o) noHost`.
Closing the gap needs a new result in `Determinism/`, for example that each of
the two bubbling successors reaches the common join by a *measure-decreasing*
route, which would give random descent and hence the implication.

What survives unconditionally is sharp, and is the honest headline:

* `behaviours_subset_of_runInvoke?` — `behaviours … ⊆ {r.toBehaviour, diverges}`;
* `behavioursOf_cases_of_steps_nf` — the behaviour set is *exactly* one of those
  two sets, the larger one only when the entry point diverges;
* `behaviours_equiv_singleton_of_runInvoke?` — `Behaviours.Equiv` at
  `Behaviour.TrapRefinesDiv`: the interpreter computes the behaviour set **up to
  divergence**. This is the strongest *named relation* of
  `Silmaril/Wasm/Behaviour/Relations.lean` that holds with no extra hypothesis,
  but it is not the sharpest fact — `behaviours_subset_of_runInvoke?` is
  strictly more informative, since `TrapRefinesDiv` would also tolerate a stray
  `traps` that the subset statement excludes.

## Completeness

`exists_runInvoke?_of_mem_behaviours` and `exists_runChecked?_of_mem_behavioursOf`
say every *terminating* behaviour is found by the interpreter with enough fuel.
The hypothesis of `runInvoke?_complete` is that the target is a host-free normal
form; the connection from "terminal configuration" to "no further step" is
`not_step_of_terminal`, which comes straight from `Determinism/Stuck.lean` and
so needs no typing — the type-safety route through
`Execution.Core.Soundness.Headline.invoke_safe` is not needed.
`terminating_behaviours_eq_runInvoke?` packages soundness and completeness as a
single set equation. Fuel monotonicity (`runInvoke?_mono`, `runChecked?_mono`)
is cheap, being `run?_mono` pushed through the two wrappers.

## Engine conformance is **not** trap insertion

The issue's framing — a resource-limited engine refines the spec by
`Behaviour.TrapRefines` — is **wrong for the grow oracle**, and this file states
the true relation instead.

`GrowOracle` is the *only* parameter of the single-threaded profile
(`profile o = Profile.deterministic o` pins `nd`, `relaxed` and `nan`), and it is
consumed in exactly two places: `MemoryStep.growSucceed`/`growFail` and
`TableStep.growSucceed`/`growFail`. A refused grow **does not trap**: it leaves
the store untouched and pushes `-1` (`BitVec.allOnes`), exactly as a physically
impossible grow does. The two are literally the same configuration. So an engine
with a restrictive oracle differs from a permissive one by a *returned value*,
not by an inserted trap, and `TrapRefines` — whose `returns_cases` says a
refinement of a returning behaviour either traps or returns *the same* values —
does not relate them. `memoryGrow_refused_returns`,
`memoryGrow_allowed_returns` and `not_trapRefines_memoryGrow` make this concrete.

The sharp true conformance statement is **plain inclusion**, which is strictly
stronger than trap insertion: `Step.deterministic_refines` gives
`Step (profile o) host ⊆ Step (Profile.spec false {}) host` for every oracle, so
`behavioursOf_subset_spec` holds — the oracle only *resolves* the spec's grow
nondeterminism and never adds behaviour. `behavioursOf_refines_spec` is that as
`Behaviours.Refines (· = ·)`; `behavioursOf_trapRefines_spec` weakens it to
`Behaviours.Refines Behaviour.TrapRefines` only so that the trap-policy composition contract phrasing is
available, and should not be mistaken for the sharp result. Trap insertion
remains the right notion for the compiler's stack overflow
(`Silmaril/Wasm/Behaviour/Relations.lean`); it is not the right notion here.
-/

@[expose] public section

namespace Silmaril.Wasm.Behaviour.Refinement

universe u

variable {A : Type u}

/-- `b` is a normal form of `R`: no transition leaves it. -/
def NormalForm (R : A → A → Prop) (b : A) : Prop := ∀ x, ¬ R b x

/-- A run out of a normal form goes nowhere. -/
theorem eq_of_normalForm {R : A → A → Prop} {a b : A} (h : Relation.ReflTransGen R a b)
    (hn : NormalForm R a) : a = b := by
  rcases h.cases_head with rfl | ⟨c, hc, -⟩
  · rfl
  · exact absurd hc (hn c)

/-- **Unique normal forms** from subcommutativity: two normal forms reachable
from a common source are equal. The hypothesis is Mathlib's
`Relation.church_rosser` premise, which `Det.DStep.join'` supplies. -/
theorem eq_of_normalForm_of_subcommutative {R : A → A → Prop}
    (hsub : ∀ a b c, R a b → R a c →
      ∃ d, Relation.ReflGen R b d ∧ Relation.ReflTransGen R c d)
    {a b₁ b₂ : A} (h₁ : Relation.ReflTransGen R a b₁) (h₂ : Relation.ReflTransGen R a b₂)
    (n₁ : NormalForm R b₁) (n₂ : NormalForm R b₂) : b₁ = b₂ := by
  obtain ⟨d, hd₁, hd₂⟩ := Relation.church_rosser hsub h₁ h₂
  rw [eq_of_normalForm hd₁ n₁, eq_of_normalForm hd₂ n₂]

/-- "Weak normalization implies strong normalization": reaching a normal form
rules out an infinite trace from the same source. This is the ingredient the
singleton theorem is missing for Wasm's host-free reduction — subcommutativity
does *not* imply it (see the module docstring). -/
def WeakToStrong (R : A → A → Prop) : Prop :=
  ∀ a b, Relation.ReflTransGen R a b → NormalForm R b → ¬ InfiniteTrace R a

/-- A **deterministic** relation with a reachable normal form has no infinite
trace: the trace is forced to follow the path to the normal form and then stops.
This is the general lemma the interpreter-conformance contract asks for; it does not apply to
`Step (profile o) noHost`, which is not deterministic
(`exists_step_not_unique`). -/
theorem weakToStrong_of_deterministic {R : A → A → Prop}
    (hdet : ∀ a b c, R a b → R a c → b = c) : WeakToStrong R := by
  intro a b h hn
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro ht
    obtain ⟨x, hx, -⟩ := ht.unfold
    exact hn x hx
  | head h' _ ih =>
    intro ht
    obtain ⟨x, hx, htx⟩ := ht.unfold
    exact ih (hdet _ _ _ hx h' ▸ htx)

end Silmaril.Wasm.Behaviour.Refinement

namespace Silmaril.Wasm.SingleThreaded.Exec

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.Behaviour.Refinement

namespace BehaviourRefinement

variable {H : Type} {o : GrowOracle}

/-! ## Terminal configurations are host-free normal forms -/

/-- A terminal configuration — one whose code is a lifted `Result` — admits no
host-free step, whatever the profile. This is the bridge from
`Config.Terminal` to the normal-form hypothesis of `runInvoke?_complete`, and it
comes from `Determinism/Stuck.lean` alone: no typing hypothesis is needed. -/
theorem not_step_of_terminal {P : Profile} {c c' : Config H} (h : c.Terminal) :
    ¬ Step P noHost c c' := by
  obtain ⟨r, hr⟩ := h
  rcases c with ⟨s, f, code⟩
  simp only at hr
  subst hr
  cases r with
  | values vs => exact fun hst => not_step_vals hst
  | throw a => exact fun hst => not_step_throwing hst
  | trap => exact fun hst => not_step_trap hst

/-- `mapM Admin.val?` recovers the values of a lifted value list, which is what
makes the `values` branch of `codeOutcome?` fire. -/
theorem mapM_val?_vals : ∀ vs : List Val, (vals vs).mapM Admin.val? = some vs
  | [] => rfl
  | v :: vs => by
    simp only [vals, List.map_cons, List.mapM_cons, Admin.val?_toAdmin]
    simp only [vals] at mapM_val?_vals
    rw [mapM_val?_vals vs]
    rfl

/-- **Completeness of the outcome classifier**, the converse of
`codeOutcome?_sound`: every lifted result is classified back as itself. The
`values` branch needs the other two patterns to be ruled out, which
`mapM_val?_vals` does because neither `TRAP` nor `THROW_REF` is a value. -/
theorem codeOutcome?_toAdmin : ∀ r : Result, codeOutcome? r.toAdmin = some r
  | .throw _ => rfl
  | .trap => rfl
  | .values vs => by
    show codeOutcome? (vals vs) = _
    unfold codeOutcome?
    split
    · rename_i h
      exfalso
      have hv := mapM_val?_vals vs
      rw [h] at hv
      simp [Admin.val?] at hv
    · rename_i h
      exfalso
      have hv := mapM_val?_vals vs
      rw [h] at hv
      simp [Admin.val?] at hv
    · simp only [mapM_val?_vals vs, Option.map_some]

/-- A configuration whose code is a lifted result is classified as exactly that
result. With `Config.outcome?_sound` this makes the result carried by a terminal
configuration unique, which is what turns "the same normal form" into "the same
behaviour". -/
theorem outcome?_eq_some_of_code {c : Config H} {r : Result} (h : c.code = r.toAdmin) :
    c.outcome? = some r := by
  unfold Config.outcome?
  rw [h]
  exact codeOutcome?_toAdmin r

/-! ## Determinism up to bubbling, and unique normal forms -/

/-- Host-free reduction in the single-threaded profile is **subcommutative**,
in the shape `Relation.church_rosser` wants: this is `Det.DStep.join'` with the
right-hand `Relation.ReflGen` weakened to `Relation.ReflTransGen`. -/
theorem step_subcommutative (o : GrowOracle) (c c₁ c₂ : Config H)
    (h₁ : Step (profile o) (noHost : HostSemantics H) c c₁)
    (h₂ : Step (profile o) noHost c c₂) :
    ∃ d, Relation.ReflGen (Step (profile o) noHost) c₁ d ∧
      Relation.ReflTransGen (Step (profile o) noHost) c₂ d := by
  obtain ⟨d, hd₁, hd₂⟩ := Det.DStep.join' (o := o) h₁ h₂
  exact ⟨d, hd₁, hd₂.to_reflTransGen⟩

/-- Host-free reduction is genuinely **not** a function, even in the
single-threaded profile: a trap bubbling out of a value prefix may be taken in
one jump or one value at a time, so `v₁ v₂ TRAP` steps both to `TRAP` and to
`v₁ TRAP`. Assuming determinism of `Step (profile o) noHost` would therefore be
a *vacuous* hypothesis; see the module docstring. -/
theorem exists_step_not_unique (s : Store H) (f : Frame) (v₁ v₂ : Val) :
    ∃ c₁ c₂ : Config H,
      Step (profile o) (noHost : HostSemantics H)
          ⟨s, f, [v₁.toAdmin, v₂.toAdmin, Admin.trap]⟩ c₁ ∧
        Step (profile o) noHost ⟨s, f, [v₁.toAdmin, v₂.toAdmin, Admin.trap]⟩ c₂ ∧ c₁ ≠ c₂ := by
  refine ⟨⟨s, f, [Admin.trap]⟩, ⟨s, f, [v₁.toAdmin, Admin.trap]⟩, ?_, ?_, by simp⟩
  · have h := Step.trapInstrs (P := profile o) (host := (noHost : HostSemantics H))
      (s := s) (f := f) (vs := [v₁, v₂]) (rest := []) (Or.inl (by simp))
    simpa [vals] using h
  · have h := Step.ctxtInstrs (P := profile o) (host := (noHost : HostSemantics H))
      (vs := [v₁]) (rest := [])
      (Step.trapInstrs (P := profile o) (host := (noHost : HostSemantics H))
        (s := s) (f := f) (vs := [v₂]) (rest := []) (Or.inl (by simp)))
      (Or.inl (by simp))
    simpa [vals] using h

/-- **Unique host-free normal form**: any two host-free normal forms reachable
from a configuration are the same configuration. This is ingredient 2 of the
singleton theorem, and the only place the `Determinism/` results are used. -/
theorem eq_of_steps_of_nf {c c₁ c₂ : Config H}
    (h₁ : Steps (profile o) (noHost : HostSemantics H) c c₁)
    (h₂ : Steps (profile o) noHost c c₂)
    (n₁ : ∀ x, ¬ Step (profile o) noHost c₁ x)
    (n₂ : ∀ x, ¬ Step (profile o) noHost c₂ x) : c₁ = c₂ :=
  eq_of_normalForm_of_subcommutative (step_subcommutative o) h₁ h₂ n₁ n₂

/-! ## The behaviour set of a run that stops -/

/-- **Ingredients 1 and 2, unconditionally**: a run to a host-free normal form
carrying the result `r` pins every observable behaviour to `r.toBehaviour` or
divergence. Divergence cannot be excluded here; see the module docstring. -/
theorem behavioursOf_subset_of_steps_nf {c c' : Config H} {r : Result}
    (hsteps : Steps (profile o) (noHost : HostSemantics H) c c')
    (hnf : ∀ x, ¬ Step (profile o) noHost c' x) (hcode : c'.code = r.toAdmin) :
    behavioursOf (profile o) noHost c ⊆ {r.toBehaviour, Behaviour.diverges} := by
  intro b hb
  by_cases hd : b = Behaviour.diverges
  · simp [hd]
  · obtain ⟨c'', r'', hst, hfin, rfl⟩ := exists_result_of_mem hb hd
    have hcc : c'' = c' :=
      eq_of_steps_of_nf hst hsteps (fun x => not_step_of_terminal ⟨r'', hfin⟩) hnf
    subst hcc
    have h1 := outcome?_eq_some_of_code hfin
    have h2 := outcome?_eq_some_of_code hcode
    rw [h1, Option.some.injEq] at h2
    subst h2
    simp

/-- **Ingredient 1**: the result the interpreter stops at is an observable
behaviour of the configuration it started from. -/
theorem mem_behavioursOf_of_steps {c c' : Config H} {r : Result}
    (hsteps : Steps (profile o) (noHost : HostSemantics H) c c') (hcode : c'.code = r.toAdmin) :
    r.toBehaviour ∈ behavioursOf (profile o) noHost c :=
  mem_behavioursOf hsteps hcode

/-- **The unconditional headline in the issue's vocabulary**: the interpreter
computes the behaviour set **up to divergence**. `Behaviour.TrapRefinesDiv` is
the finest relation of `Silmaril/Wasm/Behaviour/Relations.lean` under which this
equivalence holds with no extra hypothesis, since the one behaviour that may
escape the singleton is `diverges`, and `diverges` is `NoResult`. Note that
`behavioursOf_subset_of_steps_nf` above is strictly sharper. -/
theorem behavioursOf_equiv_singleton_of_steps_nf {c c' : Config H} {r : Result}
    (hsteps : Steps (profile o) (noHost : HostSemantics H) c c')
    (hnf : ∀ x, ¬ Step (profile o) noHost c' x) (hcode : c'.code = r.toAdmin) :
    Behaviours.Equiv Behaviour.TrapRefinesDiv (behavioursOf (profile o) noHost c)
      {r.toBehaviour} := by
  refine ⟨fun b hb => ⟨r.toBehaviour, rfl, ?_⟩, ?_⟩
  · have hc := behavioursOf_subset_of_steps_nf hsteps hnf hcode hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with h | rfl
    · exact Or.inr h
    · exact Or.inl trivial
  · rintro b rfl
    exact ⟨r.toBehaviour, mem_behavioursOf_of_steps hsteps hcode, Or.inr rfl⟩

/-- **The singleton theorem**, with the missing ingredient 3 supplied as an
explicit hypothesis: a run to a host-free normal form determines the behaviour
set exactly, provided the source does not diverge. The hypothesis is not
vacuous — it holds of every terminating entry point — but it is also not proved
anywhere, which is the honest state of play. -/
theorem behavioursOf_eq_singleton_of_steps_nf {c c' : Config H} {r : Result}
    (hsteps : Steps (profile o) (noHost : HostSemantics H) c c')
    (hnf : ∀ x, ¬ Step (profile o) noHost c' x) (hcode : c'.code = r.toAdmin)
    (hconv : ¬ Diverges (profile o) noHost c) :
    behavioursOf (profile o) noHost c = {r.toBehaviour} := by
  refine Set.eq_singleton_iff_unique_mem.mpr
    ⟨mem_behavioursOf_of_steps hsteps hcode, fun b hb => ?_⟩
  have hc := behavioursOf_subset_of_steps_nf hsteps hnf hcode hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  rcases hc with h | rfl
  · exact h
  · exact absurd (diverges_mem_behavioursOf_iff.mp hb) hconv

/-- The sharp unconditional dichotomy: the interpreter pins the behaviour set to
one of exactly *two* sets, and the larger one arises precisely when the source
diverges. This is the strongest equational form available without ingredient
3. -/
theorem behavioursOf_cases_of_steps_nf {c c' : Config H} {r : Result}
    (hsteps : Steps (profile o) (noHost : HostSemantics H) c c')
    (hnf : ∀ x, ¬ Step (profile o) noHost c' x) (hcode : c'.code = r.toAdmin) :
    behavioursOf (profile o) noHost c = {r.toBehaviour} ∨
      behavioursOf (profile o) noHost c = {r.toBehaviour, Behaviour.diverges} := by
  by_cases hdv : Diverges (profile o) noHost c
  · refine Or.inr (Set.Subset.antisymm
      (behavioursOf_subset_of_steps_nf hsteps hnf hcode) fun b hb => ?_)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
    rcases hb with rfl | rfl
    · exact mem_behavioursOf_of_steps hsteps hcode
    · exact diverges_mem_behavioursOf_iff.mpr hdv
  · exact Or.inl (behavioursOf_eq_singleton_of_steps_nf hsteps hnf hcode hdv)

/-! ## `runInvoke?` -/

/-- What a stopped `runInvoke?` delivers, assembled from `runInvoke?_steps_noHost`,
`runInvoke?_stopped` and `Config.outcome?_sound`: a host-free run from
`invoke s a vs` to a normal form whose code is the lifted result `r`. Every
`runInvoke?` statement below is this fact fed to the generic lemmas. -/
theorem runInvoke?_steps_nf {n : Nat} {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hi : InvokeOk s a vs) {c' : Config H} {r : Result}
    (h : runInvoke? o n s a vs = some (c', true, some r)) :
    Steps (profile o) noHost (invoke s a vs) c' ∧
      (∀ x, ¬ Step (profile o) noHost c' x) ∧ c'.code = r.toAdmin := by
  obtain ⟨-, hr⟩ := InvokeRun.runInvoke?_eq_some h
  exact ⟨InvokeRun.runInvoke?_steps_noHost hs hi h, (InvokeRun.runInvoke?_stopped hs hi h).2,
    Config.outcome?_sound hr.symm⟩

/-- **Soundness as a behaviour**: what `runInvoke?` returns is an observable
behaviour of the invocation. -/
theorem mem_behaviours_of_runInvoke? {n : Nat} {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hi : InvokeOk s a vs) {c' : Config H} {r : Result}
    (h : runInvoke? o n s a vs = some (c', true, some r)) :
    r.toBehaviour ∈ Execution.Core.behaviours (profile o) noHost s a vs :=
  let ⟨hst, _, hcode⟩ := runInvoke?_steps_nf hs hi h
  mem_behavioursOf_of_steps hst hcode

/-- **The sharp unconditional form of the singleton theorem**: nothing but the
interpreter's result and divergence is observable. -/
theorem behaviours_subset_of_runInvoke? {n : Nat} {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hi : InvokeOk s a vs) {c' : Config H} {r : Result}
    (h : runInvoke? o n s a vs = some (c', true, some r)) :
    Execution.Core.behaviours (profile o) noHost s a vs ⊆
      {r.toBehaviour, Behaviour.diverges} :=
  let ⟨hst, hnf, hcode⟩ := runInvoke?_steps_nf hs hi h
  behavioursOf_subset_of_steps_nf hst hnf hcode

/-- **The unconditional headline for `runInvoke?`**: the behaviour set of the
invocation and the interpreter's singleton agree up to divergence. -/
theorem behaviours_equiv_singleton_of_runInvoke? {n : Nat} {s : Store H} {a : Nat}
    {vs : List Val} (hs : StoreOk s) (hi : InvokeOk s a vs) {c' : Config H} {r : Result}
    (h : runInvoke? o n s a vs = some (c', true, some r)) :
    Behaviours.Equiv Behaviour.TrapRefinesDiv
      (Execution.Core.behaviours (profile o) noHost s a vs) {r.toBehaviour} :=
  let ⟨hst, hnf, hcode⟩ := runInvoke?_steps_nf hs hi h
  behavioursOf_equiv_singleton_of_steps_nf hst hnf hcode

/-- **The singleton theorem for `runInvoke?`** — the statement
the interpreter-conformance contract asks for, with the one hypothesis that the existing
`Determinism/` results cannot supply: that the invocation does not diverge. -/
theorem behaviours_eq_singleton_of_runInvoke? {n : Nat} {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hi : InvokeOk s a vs) {c' : Config H} {r : Result}
    (h : runInvoke? o n s a vs = some (c', true, some r))
    (hconv : ¬ Diverges (profile o) noHost (invoke s a vs)) :
    Execution.Core.behaviours (profile o) noHost s a vs = {r.toBehaviour} :=
  let ⟨hst, hnf, hcode⟩ := runInvoke?_steps_nf hs hi h
  behavioursOf_eq_singleton_of_steps_nf hst hnf hcode hconv

/-- The same singleton theorem, taking the missing ingredient in its global
form: if host-free reduction in the single-threaded profile satisfies "weak
normalization implies strong normalization", then `runInvoke?` determines the
behaviour set of *every* invocation it stops on. -/
theorem behaviours_eq_singleton_of_runInvoke?_of_weakToStrong {n : Nat} {s : Store H} {a : Nat}
    {vs : List Val} (hs : StoreOk s) (hi : InvokeOk s a vs) {c' : Config H} {r : Result}
    (hws : WeakToStrong (Step (profile o) (noHost : HostSemantics H)))
    (h : runInvoke? o n s a vs = some (c', true, some r)) :
    Execution.Core.behaviours (profile o) noHost s a vs = {r.toBehaviour} :=
  let ⟨hst, hnf, hcode⟩ := runInvoke?_steps_nf hs hi h
  behavioursOf_eq_singleton_of_steps_nf hst hnf hcode (hws _ _ hst hnf)

/-! ## `runChecked?` -/

/-- What a stopped `runChecked?` delivers: a host-free run from the concretely
instantiated configuration `c` to a normal form whose code is the lifted result
`r`. The entry point is `instantiateInit?`, which is where
`runChecked?_steps_noHost` starts. -/
theorem runChecked?_steps_nf {n : Nat} {s : Store H} {m : Module} {xas : List ExternAddr}
    (hs : StoreOk s) {c c' : Config H} {r : Result}
    (hc : instantiateInit? s m xas = some c)
    (h : runChecked? o n s m xas = some (c', true, some r)) :
    Steps (profile o) noHost c c' ∧
      (∀ x, ¬ Step (profile o) noHost c' x) ∧ c'.code = r.toAdmin := by
  obtain ⟨c₀, hc₀, hst⟩ := CheckedRun.runChecked?_steps_noHost hs h
  rw [hc] at hc₀
  have hcc : c = c₀ := Option.some_inj.mp hc₀
  subst hcc
  exact ⟨hst, (CheckedRun.runChecked?_stopped hs h).2,
    (CheckedRun.runChecked?_sound hs h).2.2 r rfl⟩

/-- **Soundness as a behaviour** for the validate-instantiate-run pipeline. -/
theorem mem_behavioursOf_of_runChecked? {n : Nat} {s : Store H} {m : Module}
    {xas : List ExternAddr} (hs : StoreOk s) {c c' : Config H} {r : Result}
    (hc : instantiateInit? s m xas = some c)
    (h : runChecked? o n s m xas = some (c', true, some r)) :
    r.toBehaviour ∈ behavioursOf (profile o) noHost c :=
  let ⟨hst, _, hcode⟩ := runChecked?_steps_nf hs hc h
  mem_behavioursOf_of_steps hst hcode

/-- **The sharp unconditional form** for the checked pipeline. -/
theorem behavioursOf_subset_of_runChecked? {n : Nat} {s : Store H} {m : Module}
    {xas : List ExternAddr} (hs : StoreOk s) {c c' : Config H} {r : Result}
    (hc : instantiateInit? s m xas = some c)
    (h : runChecked? o n s m xas = some (c', true, some r)) :
    behavioursOf (profile o) noHost c ⊆ {r.toBehaviour, Behaviour.diverges} :=
  let ⟨hst, hnf, hcode⟩ := runChecked?_steps_nf hs hc h
  behavioursOf_subset_of_steps_nf hst hnf hcode

/-- **The unconditional headline** for the checked pipeline: equality of
behaviour sets up to divergence. -/
theorem behavioursOf_equiv_singleton_of_runChecked? {n : Nat} {s : Store H} {m : Module}
    {xas : List ExternAddr} (hs : StoreOk s) {c c' : Config H} {r : Result}
    (hc : instantiateInit? s m xas = some c)
    (h : runChecked? o n s m xas = some (c', true, some r)) :
    Behaviours.Equiv Behaviour.TrapRefinesDiv (behavioursOf (profile o) noHost c)
      {r.toBehaviour} :=
  let ⟨hst, hnf, hcode⟩ := runChecked?_steps_nf hs hc h
  behavioursOf_equiv_singleton_of_steps_nf hst hnf hcode

/-- **The singleton theorem for `runChecked?`**, with the same non-divergence
hypothesis as `behaviours_eq_singleton_of_runInvoke?`. -/
theorem behavioursOf_eq_singleton_of_runChecked? {n : Nat} {s : Store H} {m : Module}
    {xas : List ExternAddr} (hs : StoreOk s) {c c' : Config H} {r : Result}
    (hc : instantiateInit? s m xas = some c)
    (h : runChecked? o n s m xas = some (c', true, some r))
    (hconv : ¬ Diverges (profile o) noHost c) :
    behavioursOf (profile o) noHost c = {r.toBehaviour} :=
  let ⟨hst, hnf, hcode⟩ := runChecked?_steps_nf hs hc h
  behavioursOf_eq_singleton_of_steps_nf hst hnf hcode hconv

/-! ## Completeness -/

/-- **Completeness as a behaviour statement**: every *terminating* behaviour of
an invocation is found by `runInvoke?` with enough fuel, as an actual returned
`Result`. Divergent behaviours are of course not found by any fuel. -/
theorem exists_runInvoke?_of_mem_behaviours {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hi : InvokeOk s a vs) {b : Behaviour Val}
    (mem : b ∈ Execution.Core.behaviours (profile o) noHost s a vs) (term : b.Terminates) :
    ∃ (n : Nat) (c' : Config H) (r : Result),
      runInvoke? o n s a vs = some (c', true, some r) ∧ r.toBehaviour = b := by
  obtain ⟨c', r, hst, hfin, rfl⟩ := terminates_of_mem mem term
  obtain ⟨n, hn⟩ :=
    InvokeRun.runInvoke?_complete hs hi hst fun x => not_step_of_terminal ⟨r, hfin⟩
  exact ⟨n, c', r, by rw [hn, outcome?_eq_some_of_code hfin], rfl⟩

/-- **Sound and complete in one equation**: the terminating behaviours of an
invocation are *exactly* the results `runInvoke?` returns, over all fuels. -/
theorem terminating_behaviours_eq_runInvoke? {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hi : InvokeOk s a vs) :
    {b ∈ Execution.Core.behaviours (profile o) noHost s a vs | b.Terminates} =
      {b | ∃ (n : Nat) (c' : Config H) (r : Result),
            runInvoke? o n s a vs = some (c', true, some r) ∧ r.toBehaviour = b} := by
  ext b
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hmem, hterm⟩
    exact exists_runInvoke?_of_mem_behaviours hs hi hmem hterm
  · rintro ⟨n, c', r, hn, rfl⟩
    exact ⟨mem_behaviours_of_runInvoke? hs hi hn, Result.terminates_toBehaviour r⟩

/-- **Completeness as a behaviour statement** for the checked pipeline. The
validation and import hypotheses are those of `runChecked?_complete`; they are
what lets the pipeline get past its two decidable guards. -/
theorem exists_runChecked?_of_mem_behavioursOf {s : Store H} {m : Module}
    {xas : List ExternAddr} {mt : CModuleType} (hs : StoreOk s) (hm : validate? m = some mt)
    (hx : List.Forall₂ (ExternAddrOk s) xas mt.imports) {c : Config H}
    (hc : instantiateInit? s m xas = some c) {b : Behaviour Val}
    (mem : b ∈ behavioursOf (profile o) noHost c) (term : b.Terminates) :
    ∃ (n : Nat) (c' : Config H) (r : Result),
      runChecked? o n s m xas = some (c', true, some r) ∧ r.toBehaviour = b := by
  obtain ⟨c', r, hst, hfin, rfl⟩ := terminates_of_mem mem term
  obtain ⟨n, hn⟩ :=
    CheckedRun.runChecked?_complete hs hm hx hc hst fun x => not_step_of_terminal ⟨r, hfin⟩
  exact ⟨n, c', r, by rw [hn, outcome?_eq_some_of_code hfin], rfl⟩

/-! ## Fuel monotonicity -/

/-- **Fuel monotonicity**: more fuel does not change a stopped `runInvoke?`, so
the behaviour statements above are independent of the fuel that produced them.
This is `run?_mono` pushed through the wrapper. -/
theorem runInvoke?_mono {n n' : Nat} {s : Store H} {a : Nat} {vs : List Val}
    {c' : Config H} {r : Option Result} (h : runInvoke? o n s a vs = some (c', true, r))
    (hnn' : n ≤ n') : runInvoke? o n' s a vs = some (c', true, r) := by
  obtain ⟨hrun, hr⟩ := InvokeRun.runInvoke?_eq_some h
  have hmono := run?_mono (head := interpHead o) hrun hnn'
  unfold runInvoke?
  simp only [runI]
  rw [hmono, hr]

/-- **Fuel monotonicity** for the checked pipeline. The two decidable guards do
not depend on the fuel, so the same argument goes through. -/
theorem runChecked?_mono {n n' : Nat} {s : Store H} {m : Module} {xas : List ExternAddr}
    {c' : Config H} {r : Option Result} (h : runChecked? o n s m xas = some (c', true, r))
    (hnn' : n ≤ n') : runChecked? o n' s m xas = some (c', true, r) := by
  obtain ⟨-, hrm⟩ := CheckedRun.runChecked?_inv h
  obtain ⟨c, hc, hrun, hr⟩ := EndToEnd.runModule?_eq_some hrm
  have hmod : EndToEnd.runModule? (interpHead o) n' s m xas = some (c', true, r) := by
    unfold EndToEnd.runModule?
    rw [hc]
    simp only [run?_mono (head := interpHead o) hrun hnn', hr]
  unfold runChecked? at h ⊢
  split at h
  · exact absurd h (by simp)
  · split at h
    · rename_i hx
      simp only [hx, ↓reduceIte]
      exact hmod
    · exact absurd h (by simp)

/-! ## Engine conformance -/

/-- A run of the single-threaded profile is a run of the spec profile with
`$ND = false`: the oracle only prunes. Induction on `Steps` over
`Step.deterministic_refines`. -/
theorem steps_spec_of_steps {host : HostSemantics H} {c c' : Config H}
    (h : Steps (profile o) host c c') : Steps (Profile.spec false {}) host c c' := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (Step.deterministic_refines hstep)

/-- Divergence transfers to the spec profile, by mapping the infinite trace
along the identity. -/
theorem diverges_spec_of_diverges {host : HostSemantics H} {c : Config H}
    (h : Diverges (profile o) host c) : Diverges (Profile.spec false {}) host c :=
  InfiniteTrace.map id (fun _ _ hst => Step.deterministic_refines hst) h

/-- **Engine conformance**: every behaviour of the engine under any grow oracle
is a behaviour of the specification. This — plain inclusion — is the sharp
statement; it is *strictly stronger* than trap insertion, and trap insertion is
in any case the wrong relation here (see the module docstring). -/
theorem behavioursOf_subset_spec {host : HostSemantics H} (c : Config H) :
    behavioursOf (profile o) host c ⊆ behavioursOf (Profile.spec false {}) host c := by
  rintro b (⟨c'', r, hst, hfin, rfl⟩ | ⟨rfl, hdv⟩)
  · exact Or.inl ⟨c'', r, steps_spec_of_steps hst, hfin, rfl⟩
  · exact Or.inr ⟨rfl, diverges_spec_of_diverges hdv⟩

/-- Engine conformance in the vocabulary of `Behaviours.Refines`: refinement at
equality, which `refines_eq_iff` identifies with the inclusion above. -/
theorem behavioursOf_refines_spec {host : HostSemantics H} (c : Config H) :
    Behaviours.Refines (· = ·) (behavioursOf (profile o) host c)
      (behavioursOf (Profile.spec false {}) host c) :=
  Behaviours.refines_eq_iff.mpr (behavioursOf_subset_spec c)

/-- The the trap-policy composition contract phrasing, available a fortiori because `Eq ⊆
TrapRefines` — but it is **strictly weaker** than
`behavioursOf_refines_spec` and does **not** express what the grow oracle does,
since a refused grow returns `-1` rather than trapping. Recorded only so the
trap-policy composition contract relation is present; `not_trapRefines_memoryGrow` is the sharp statement
about oracles. -/
theorem behavioursOf_trapRefines_spec {host : HostSemantics H} (c : Config H) :
    Behaviours.Refines Behaviour.TrapRefines (behavioursOf (profile o) host c)
      (behavioursOf (Profile.spec false {}) host c) :=
  (behavioursOf_refines_spec (o := o) c).mono fun _ _ h => Behaviour.TrapRefines.of_eq h

/-- Engine conformance specialised to an invocation entry point. -/
theorem behaviours_subset_spec {host : HostSemantics H} (s : Store H) (a : Nat)
    (vs : List Val) :
    Execution.Core.behaviours (profile o) host s a vs ⊆
      Execution.Core.behaviours (Profile.spec false {}) host s a vs :=
  behavioursOf_subset_spec _

/-- A **refused** `memory.grow` leaves the store alone and **returns `-1`**: its
observable behaviour is `returns`, not `traps`. This is the formal content of
the `MemoryStep.growFail` rule, and the reason the grow oracle is not a
trap-insertion knob. -/
theorem memoryGrow_refused_returns {s : Store H} {f : Frame} {x : MemIdx} {a : AddrType}
    {n : BitVec a.intType.width} {ma : Nat} {mi : MemInst}
    (hm : s.mem? f x = some (ma, mi)) (hfail : o .memory ma mi.pages n.toNat = true) :
    Behaviour.returns [Val.num ⟨.int a.intType, BitVec.allOnes a.intType.width⟩] ∈
      behavioursOf (profile o) (noHost : HostSemantics H)
        ⟨s, f, [aconst a n, .plain (.memoryGrow x)]⟩ := by
  refine returns_mem_behavioursOf
    (c' := ⟨s, f, [aconst a (BitVec.allOnes a.intType.width)]⟩)
    (Relation.ReflTransGen.single (.memory (.growFail hm (Or.inl hfail)))) rfl

/-- An **allowed** `memory.grow` returns the old size in pages. Same program,
same store, different oracle, different *returned value*. -/
theorem memoryGrow_allowed_returns {s : Store H} {f : Frame} {x : MemIdx} {a : AddrType}
    {n : BitVec a.intType.width} {ma : Nat} {mi mi' : MemInst}
    (hm : s.mem? f x = some (ma, mi)) (hok : o .memory ma mi.pages n.toNat = false)
    (hg : mi.grow? n.toNat = some mi') :
    Behaviour.returns [Val.num ⟨.int a.intType, BitVec.ofNat a.intType.width mi.pages⟩] ∈
      behavioursOf (profile o) (noHost : HostSemantics H)
        ⟨s, f, [aconst a n, .plain (.memoryGrow x)]⟩ := by
  refine returns_mem_behavioursOf
    (c' := ⟨s.setMem ma mi', f, [aconst a (BitVec.ofNat a.intType.width mi.pages)]⟩)
    (Relation.ReflTransGen.single (.memory (.growSucceed hm hg hok))) rfl

/-- Two different returned values are unrelated by `Behaviour.TrapRefines`:
trap insertion may replace a behaviour by `traps`, never by another `returns`. -/
theorem not_trapRefines_returns_of_ne {vs ws : List Val} (h : vs ≠ ws) :
    ¬ Behaviour.TrapRefines (Behaviour.returns vs) (Behaviour.returns ws) := by
  rintro (hc | hc)
  · exact absurd hc (by simp)
  · exact h (by simpa using hc)

/-- **The conformance relation is not trap insertion.** Two oracles that disagree
at a single `memory.grow` make the *same* program return two *different* values,
and two different returned values are unrelated by `Behaviour.TrapRefines` in
either direction. -/
theorem not_trapRefines_memoryGrow {o₁ o₂ : GrowOracle} {s : Store H} {f : Frame}
    {x : MemIdx} {a : AddrType} {n : BitVec a.intType.width} {ma : Nat} {mi mi' : MemInst}
    (hm : s.mem? f x = some (ma, mi)) (hfail : o₁ .memory ma mi.pages n.toNat = true)
    (hok : o₂ .memory ma mi.pages n.toNat = false) (hg : mi.grow? n.toNat = some mi')
    (hne : (Val.num ⟨.int a.intType, BitVec.allOnes a.intType.width⟩ : Val) ≠
      Val.num ⟨.int a.intType, BitVec.ofNat a.intType.width mi.pages⟩) :
    ∃ b ∈ behavioursOf (profile o₁) (noHost : HostSemantics H)
        ⟨s, f, [aconst a n, .plain (.memoryGrow x)]⟩,
      ∃ b' ∈ behavioursOf (profile o₂) (noHost : HostSemantics H)
          ⟨s, f, [aconst a n, .plain (.memoryGrow x)]⟩,
        ¬ Behaviour.TrapRefines b b' :=
  ⟨_, memoryGrow_refused_returns hm hfail, _, memoryGrow_allowed_returns hm hok hg,
    not_trapRefines_returns_of_ne (by simpa using hne)⟩

end BehaviourRefinement

end Silmaril.Wasm.SingleThreaded.Exec
