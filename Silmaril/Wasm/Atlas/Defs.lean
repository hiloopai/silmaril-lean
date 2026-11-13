module

public import Mathlib.Data.Set.Basic

/-!
# An atlas of Wasm semantics: charts and transition maps

Wasm has many semantics in this repository: Core reduction (`Step P host` at every profile),
game strategies, the component IR and the reference Component Model machine, Binaryen IR,
program logics, determinism fragments and the SpecTec relations. Each is good at something and
adequate only on a fragment. This module gives the vocabulary to present them as **charts** of
one logic of interface behaviours, related by **transition maps** that record in which
direction satisfaction is preserved. See `docs/projects/wasm-components.md`.

* `Dir`: a direction of preservation, a pair of flags. `fwd`: source satisfaction implies target
  satisfaction (the transition *preserves*); `bwd`: target satisfaction implies source
  satisfaction (the transition *reflects*). `equal` has both. Directions compose by meet.
* `Chart`: points (programs, instances, configurations in the chart's own syntax), sentences,
  a *domain* (the fragment on which the chart is adequate) and satisfaction.
* `Transition A B`: maps points and sentences of `A` to those of `B`, carries `A`'s domain into
  `B`'s, and on a class `cls` of sentences relates satisfaction in direction `dir`. A
  comorphism is the case `cls = ⊤`, `dir = equal`; a *semi-comorphism* only preserves or only
  reflects, or only on a sentence class (e.g. safety sentences).
* `Path A B`: a chain of transitions; it composes to one transition (`Path.toTransition`).
* `ChartAtlas`: a base chart (Core) and a family of charts, each with a transition to the base.

The shared sentence language for call-level charts is `BSen C B`: interface behaviour
sentences over calls `C` and observations `B` (`always c φ`: every observation of `c`
satisfies `φ`; `may c φ`: some does; conjunction, truth). A **behaviour chart** (`BChart`) is
given by a map from points to observation sets. Its signature morphisms are renamings of calls
`σ : C → C'`, with the satisfaction condition `BSen.sat_rename`. Transitions between behaviour
charts are built from equalities and inclusions of observation sets (`BTrans`).
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas

universe u v u' v' u'' v''

/-! ## Directions -/

/-- A direction of preservation. `fwd`: source satisfaction implies target satisfaction.
`bwd`: target satisfaction implies source satisfaction. -/
@[ext] structure Dir where
  /-- The transition preserves satisfaction (source ⊨ ⇒ target ⊨). -/
  fwd : Bool
  /-- The transition reflects satisfaction (target ⊨ ⇒ source ⊨). -/
  bwd : Bool
deriving DecidableEq, Repr

namespace Dir

/-- Satisfaction is equal on both sides (a comorphism on its class). -/
def equal : Dir := ⟨true, true⟩
/-- Source satisfaction implies target satisfaction. -/
def preserves : Dir := ⟨true, false⟩
/-- Target satisfaction implies source satisfaction. -/
def reflects : Dir := ⟨false, true⟩
/-- No information. -/
def none : Dir := ⟨false, false⟩

/-- Composition of directions: the meet of the flags. -/
def comp (d e : Dir) : Dir := ⟨d.fwd && e.fwd, d.bwd && e.bwd⟩

/-- `d` is at least as strong as `e`. -/
def Stronger (d e : Dir) : Prop := (e.fwd = true → d.fwd = true) ∧ (e.bwd = true → d.bwd = true)

/-- The relation between source and target satisfaction recorded by a direction. -/
def Rel (d : Dir) (p q : Prop) : Prop := (d.fwd = true → p → q) ∧ (d.bwd = true → q → p)

end Dir

/-! ## Charts and transitions -/

/-- A chart: a model presentation with its own points and sentences, the domain (fragment) on
which it is adequate, and satisfaction. -/
structure Chart where
  /-- Points: programs, instances or configurations in the chart's own syntax. -/
  Pt : Type u
  /-- Sentences of the chart. -/
  Sen : Type v
  /-- The domain: the fragment of points on which the chart is adequate. -/
  dom : Pt → Prop
  /-- Satisfaction. -/
  Sat : Pt → Sen → Prop

/-- Two points of a chart are **equivalent** (model equivalence) when they satisfy the same
sentences. -/
def Chart.Equiv (A : Chart.{u, v}) (p q : A.Pt) : Prop := ∀ φ, A.Sat p φ ↔ A.Sat q φ

/-- A transition map between charts: points and sentences forwards, the source domain into the
target domain, and satisfaction related in direction `dir` on the sentence class `cls`. -/
structure Transition (A : Chart.{u, v}) (B : Chart.{u', v'}) where
  /-- The point map. -/
  pt : A.Pt → B.Pt
  /-- The sentence map. -/
  sen : A.Sen → B.Sen
  /-- The sentence class on which satisfaction is related. -/
  cls : A.Sen → Prop
  /-- The recorded direction of preservation. -/
  dir : Dir
  /-- The source domain lands in the target domain (the overlap of the two charts). -/
  dom_pt : ∀ p, A.dom p → B.dom (pt p)
  /-- Satisfaction is related on the domain and the class. -/
  sat : ∀ p φ, A.dom p → cls φ → dir.Rel (A.Sat p φ) (B.Sat (pt p) (sen φ))

namespace Transition

/-- The identity transition (equal on every sentence). -/
def id (A : Chart.{u, v}) : Transition A A where
  pt p := p
  sen φ := φ
  cls _ := True
  dir := .equal
  dom_pt _ h := h
  sat _ _ _ _ := ⟨fun _ h => h, fun _ h => h⟩

/-- Composition of transitions: classes pull back, directions meet. -/
def comp {A : Chart.{u, v}} {B : Chart.{u', v'}} {C : Chart.{u'', v''}}
    (T : Transition A B) (U : Transition B C) : Transition A C where
  pt p := U.pt (T.pt p)
  sen φ := U.sen (T.sen φ)
  cls φ := T.cls φ ∧ U.cls (T.sen φ)
  dir := T.dir.comp U.dir
  dom_pt p h := U.dom_pt _ (T.dom_pt p h)
  sat p φ hp hφ := by
    have h₁ := T.sat p φ hp hφ.1
    have h₂ := U.sat (T.pt p) (T.sen φ) (T.dom_pt p hp) hφ.2
    refine ⟨fun hf hs => ?_, fun hb ht => ?_⟩
    · simp only [Dir.comp, Bool.and_eq_true] at hf
      exact h₂.1 hf.2 (h₁.1 hf.1 hs)
    · simp only [Dir.comp, Bool.and_eq_true] at hb
      exact h₁.2 hb.1 (h₂.2 hb.2 ht)

/-- Shrink the sentence class. -/
def restrictCls {A : Chart.{u, v}} {B : Chart.{u', v'}} (T : Transition A B)
    (cls' : A.Sen → Prop) (h : ∀ φ, cls' φ → T.cls φ) : Transition A B :=
  { T with cls := cls', sat := fun p φ hp hφ => T.sat p φ hp (h φ hφ) }

/-- Forget part of the recorded direction. -/
def weaken {A : Chart.{u, v}} {B : Chart.{u', v'}} (T : Transition A B) (d : Dir)
    (h : T.dir.Stronger d) : Transition A B :=
  { T with dir := d,
           sat := fun p φ hp hφ =>
             ⟨fun hf => (T.sat p φ hp hφ).1 (h.1 hf), fun hb => (T.sat p φ hp hφ).2 (h.2 hb)⟩ }

end Transition

/-! ## Paths -/

/-- A chain of transitions between charts of one universe. -/
inductive Path : Chart.{u, v} → Chart.{u, v} → Type (max (u + 1) (v + 1)) where
  /-- The empty chain. -/
  | nil (A : Chart.{u, v}) : Path A A
  /-- A transition followed by a chain. -/
  | cons {A B C : Chart.{u, v}} (T : Transition A B) (p : Path B C) : Path A C

namespace Path

/-- The composite transition of a chain. -/
def toTransition : {A B : Chart.{u, v}} → Path A B → Transition A B
  | _, _, nil A => Transition.id A
  | _, _, cons T p => T.comp p.toTransition

/-- Every transition of the chain is equal on its class. -/
def AllEqual : {A B : Chart.{u, v}} → Path A B → Prop
  | _, _, nil _ => True
  | _, _, cons T p => T.dir = .equal ∧ p.AllEqual

end Path

/-! ## Atlases -/

/-- An atlas: a base chart and a family of charts, each with a transition to the base. -/
structure ChartAtlas where
  /-- The base chart (for Wasm: Core reduction). -/
  base : Chart.{u, v}
  /-- Chart names. -/
  ι : Type
  /-- The charts. -/
  chart : ι → Chart.{u, v}
  /-- Each chart's transition to the base. -/
  toBase : ∀ i, Transition (chart i) base

/-! ## Interface behaviour sentences -/

/-- Interface behaviour sentences over calls `C` and observations `B`. -/
inductive BSen (C : Type u) (B : Type v) : Type (max u v) where
  /-- Every observation of the call satisfies `φ` (partial correctness, safety). -/
  | always (c : C) (φ : B → Prop)
  /-- Some observation of the call satisfies `φ` (possibility, a test witness). -/
  | may (c : C) (φ : B → Prop)
  /-- Conjunction. -/
  | and (s t : BSen C B)
  /-- Truth. -/
  | top

namespace BSen

variable {C : Type u} {C' : Type u'} {C'' : Type u''} {B : Type v}

/-- Satisfaction by an observation map `obs : C → Set B`. -/
def Sat (obs : C → Set B) : BSen C B → Prop
  | always c φ => ∀ b ∈ obs c, φ b
  | may c φ => ∃ b ∈ obs c, φ b
  | and s t => Sat obs s ∧ Sat obs t
  | top => True

/-- Sentence translation along a signature morphism (a renaming of calls). -/
def rename (σ : C → C') : BSen C B → BSen C' B
  | always c φ => always (σ c) φ
  | may c φ => may (σ c) φ
  | and s t => and (rename σ s) (rename σ t)
  | top => top

/-- Only `always` atoms: safety / partial-correctness sentences (closed under fewer
observations). -/
def Universal : BSen C B → Prop
  | always _ _ => True
  | may _ _ => False
  | and s t => Universal s ∧ Universal t
  | top => True

/-- Only `may` atoms: existential / witness sentences (closed under more observations). -/
def Existential : BSen C B → Prop
  | always _ _ => False
  | may _ _ => True
  | and s t => Existential s ∧ Existential t
  | top => True

/-- The sentence does not care about the observation `d`: `always` atoms accept it and `may`
atoms reject it. For `d = .diverges`: divergence-tolerant partial correctness and terminating
witnesses. -/
def Ignores (d : B) : BSen C B → Prop
  | always _ φ => φ d
  | may _ φ => ¬ φ d
  | and s t => Ignores d s ∧ Ignores d t
  | top => True

/-- Every atom's predicate respects `R`: related observations are indistinguishable. -/
def Respects (R : B → B → Prop) : BSen C B → Prop
  | always _ φ => ∀ b b', R b b' → (φ b ↔ φ b')
  | may _ φ => ∀ b b', R b b' → (φ b ↔ φ b')
  | and s t => Respects R s ∧ Respects R t
  | top => True

end BSen

/-- A behaviour chart: points with observation sets per call, a domain, and `BSen`
satisfaction. -/
def BChart (Pt : Type u) (C : Type u') (B : Type v) (dom : Pt → Prop)
    (obs : Pt → C → Set B) : Chart.{u, max u' v} where
  Pt := Pt
  Sen := BSen C B
  dom := dom
  Sat p s := s.Sat (obs p)

/-! ## Behaviour sentences: the satisfaction condition and observation lemmas -/

namespace BSen

variable {C : Type u} {C' : Type u'} {B : Type v}

/-- **Satisfaction condition** for renamings of calls. -/
theorem sat_rename (σ : C → C') (obs : C' → Set B) (s : BSen C B) :
    (s.rename σ).Sat obs ↔ s.Sat (fun c => obs (σ c)) := by
  induction s with
  | always c φ => exact Iff.rfl
  | may c φ => exact Iff.rfl
  | and s t ih₁ ih₂ => exact and_congr ih₁ ih₂
  | top => exact Iff.rfl

@[simp] theorem rename_id (s : BSen C B) : s.rename id = s := by
  induction s with
  | always => rfl
  | may => rfl
  | and s t ih₁ ih₂ => exact congrArg₂ and ih₁ ih₂
  | top => rfl

theorem rename_rename {C'' : Type u''} (σ : C → C') (τ : C' → C'') (s : BSen C B) :
    (s.rename σ).rename τ = s.rename (fun c => τ (σ c)) := by
  induction s with
  | always => rfl
  | may => rfl
  | and s t ih₁ ih₂ => exact congrArg₂ and ih₁ ih₂
  | top => rfl

/-- Equal observations satisfy the same sentences. -/
theorem sat_congr {obs obs' : C → Set B} (h : ∀ c, obs c = obs' c) (s : BSen C B) :
    s.Sat obs ↔ s.Sat obs' := by
  rw [show obs = obs' from funext h]

/-- Fewer observations: universal sentences go down. -/
theorem sat_of_subset_univ {obs obs' : C → Set B} (h : ∀ c, obs c ⊆ obs' c) {s : BSen C B}
    (hs : s.Universal) (h' : s.Sat obs') : s.Sat obs := by
  induction s with
  | always c φ => exact fun b hb => h' b (h c hb)
  | may c φ => exact hs.elim
  | and s t ih₁ ih₂ => exact ⟨ih₁ hs.1 h'.1, ih₂ hs.2 h'.2⟩
  | top => trivial

/-- More observations: existential sentences go up. -/
theorem sat_of_subset_exist {obs obs' : C → Set B} (h : ∀ c, obs c ⊆ obs' c) {s : BSen C B}
    (hs : s.Existential) (h' : s.Sat obs) : s.Sat obs' := by
  induction s with
  | always c φ => exact hs.elim
  | may c φ => obtain ⟨b, hb, hφ⟩ := h'; exact ⟨b, h c hb, hφ⟩
  | and s t ih₁ ih₂ => exact ⟨ih₁ hs.1 h'.1, ih₂ hs.2 h'.2⟩
  | top => trivial

/-- Adding only copies of an ignored observation `d` does not change satisfaction. -/
theorem sat_union_iff {obs D : C → Set B} {d : B} (hD : ∀ c, ∀ b ∈ D c, b = d)
    {s : BSen C B} (hs : s.Ignores d) : s.Sat (fun c => obs c ∪ D c) ↔ s.Sat obs := by
  induction s with
  | always c φ =>
    refine ⟨fun h b hb => h b (Or.inl hb), fun h b hb => ?_⟩
    rcases hb with hb | hb
    · exact h b hb
    · rw [hD c b hb]; exact hs
  | may c φ =>
    refine ⟨fun ⟨b, hb, hφ⟩ => ?_, fun ⟨b, hb, hφ⟩ => ⟨b, Or.inl hb, hφ⟩⟩
    rcases hb with hb | hb
    · exact ⟨b, hb, hφ⟩
    · rw [hD c b hb] at hφ; exact (hs hφ).elim
  | and s t ih₁ ih₂ => exact and_congr (ih₁ hs.1) (ih₂ hs.2)
  | top => exact Iff.rfl

/-- **Observations related up to `R` both ways** satisfy the same `R`-respecting sentences. -/
theorem sat_iff_upto {obs obs' : C → Set B} {R : B → B → Prop}
    (h₁ : ∀ c, ∀ b ∈ obs c, ∃ b' ∈ obs' c, R b b') (h₂ : ∀ c, ∀ b' ∈ obs' c, ∃ b ∈ obs c, R b b')
    {s : BSen C B} (hs : s.Respects R) : s.Sat obs ↔ s.Sat obs' := by
  induction s with
  | always c φ =>
    refine ⟨fun h b' hb' => ?_, fun h b hb => ?_⟩
    · obtain ⟨b, hb, r⟩ := h₂ c b' hb'; exact (hs b b' r).1 (h b hb)
    · obtain ⟨b', hb', r⟩ := h₁ c b hb; exact (hs b b' r).2 (h b' hb')
  | may c φ =>
    refine ⟨fun ⟨b, hb, hφ⟩ => ?_, fun ⟨b', hb', hφ⟩ => ?_⟩
    · obtain ⟨b', hb', r⟩ := h₁ c b hb; exact ⟨b', hb', (hs b b' r).1 hφ⟩
    · obtain ⟨b, hb, r⟩ := h₂ c b' hb'; exact ⟨b, hb, (hs b b' r).2 hφ⟩
  | and s t ih₁ ih₂ => exact and_congr (ih₁ hs.1) (ih₂ hs.2)
  | top => exact Iff.rfl

/-- **Observations simulated up to `R`**: universal `R`-respecting sentences go down. -/
theorem sat_upto_univ {obs obs' : C → Set B} {R : B → B → Prop}
    (h₁ : ∀ c, ∀ b ∈ obs c, ∃ b' ∈ obs' c, R b b') {s : BSen C B} (hu : s.Universal)
    (hs : s.Respects R) (h : s.Sat obs') : s.Sat obs := by
  induction s with
  | always c φ => intro b hb; obtain ⟨b', hb', r⟩ := h₁ c b hb; exact (hs b b' r).2 (h b' hb')
  | may c φ => exact hu.elim
  | and s t ih₁ ih₂ => exact ⟨ih₁ hu.1 hs.1 h.1, ih₂ hu.2 hs.2 h.2⟩
  | top => trivial

/-- **Observations simulated up to `R`**: existential `R`-respecting sentences go up. -/
theorem sat_upto_exist {obs obs' : C → Set B} {R : B → B → Prop}
    (h₁ : ∀ c, ∀ b ∈ obs c, ∃ b' ∈ obs' c, R b b') {s : BSen C B} (he : s.Existential)
    (hs : s.Respects R) (h : s.Sat obs) : s.Sat obs' := by
  induction s with
  | always c φ => exact he.elim
  | may c φ =>
    obtain ⟨b, hb, hφ⟩ := h; obtain ⟨b', hb', r⟩ := h₁ c b hb; exact ⟨b', hb', (hs b b' r).1 hφ⟩
  | and s t ih₁ ih₂ => exact ⟨ih₁ he.1 hs.1 h.1, ih₂ he.2 hs.2 h.2⟩
  | top => trivial

theorem respects_rename (σ : C → C') {R : B → B → Prop} {s : BSen C B} (h : s.Respects R) :
    (s.rename σ).Respects R := by
  induction s with
  | always => exact h
  | may => exact h
  | and s t ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | top => trivial

theorem universal_rename (σ : C → C') {s : BSen C B} (h : s.Universal) :
    (s.rename σ).Universal := by
  induction s with
  | always => trivial
  | may => exact h.elim
  | and s t ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | top => trivial

theorem existential_rename (σ : C → C') {s : BSen C B} (h : s.Existential) :
    (s.rename σ).Existential := by
  induction s with
  | always => exact h.elim
  | may => trivial
  | and s t ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | top => trivial

theorem ignores_rename (σ : C → C') {d : B} {s : BSen C B} (h : s.Ignores d) :
    (s.rename σ).Ignores d := by
  induction s with
  | always => exact h
  | may => exact h
  | and s t ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | top => trivial

end BSen

/-! ## Transitions between behaviour charts -/

namespace BTrans

variable {Pt : Type u} {Pt' : Type u''} {C : Type u'} {C' : Type u'} {B : Type v}
  {dom : Pt → Prop} {dom' : Pt' → Prop} {obs : Pt → C → Set B} {obs' : Pt' → C' → Set B}

/-- **Equal observations** along a point map `f` and a call renaming `σ`: a comorphism, equal
on every sentence. -/
def ofEq (f : Pt → Pt') (σ : C → C') (hdom : ∀ p, dom p → dom' (f p))
    (h : ∀ p, dom p → ∀ c, obs' (f p) (σ c) = obs p c) :
    Transition (BChart Pt C B dom obs) (BChart Pt' C' B dom' obs') where
  pt := f
  sen := BSen.rename σ
  cls _ := True
  dir := .equal
  dom_pt := hdom
  sat p s hp _ := by
    have e : (s.rename σ).Sat (obs' (f p)) ↔ s.Sat (obs p) :=
      (BSen.sat_rename σ _ s).trans (BSen.sat_congr (h p hp) s)
    exact ⟨fun _ => e.2, fun _ => e.1⟩

/-- **Source observations are target observations** (soundness of the source chart): the target
reflects universal sentences. -/
def ofSubsetUniv (f : Pt → Pt') (σ : C → C') (hdom : ∀ p, dom p → dom' (f p))
    (h : ∀ p, dom p → ∀ c, obs p c ⊆ obs' (f p) (σ c)) :
    Transition (BChart Pt C B dom obs) (BChart Pt' C' B dom' obs') where
  pt := f
  sen := BSen.rename σ
  cls := BSen.Universal
  dir := .reflects
  dom_pt := hdom
  sat p s hp hs := ⟨fun e => absurd e (by decide), fun _ ht =>
    BSen.sat_of_subset_univ (h p hp) hs ((BSen.sat_rename σ _ s).1 ht)⟩

/-- **Source observations are target observations**: the target preserves existential
sentences (a witness found in the source is a witness in the target). -/
def ofSubsetExist (f : Pt → Pt') (σ : C → C') (hdom : ∀ p, dom p → dom' (f p))
    (h : ∀ p, dom p → ∀ c, obs p c ⊆ obs' (f p) (σ c)) :
    Transition (BChart Pt C B dom obs) (BChart Pt' C' B dom' obs') where
  pt := f
  sen := BSen.rename σ
  cls := BSen.Existential
  dir := .preserves
  dom_pt := hdom
  sat p s hp hs := ⟨fun _ hsrc =>
    (BSen.sat_rename σ _ s).2 (BSen.sat_of_subset_exist (h p hp) hs hsrc),
    fun e => absurd e (by decide)⟩

/-- **Target observations are source observations** (completeness of the source chart): the
target preserves universal sentences into the source. -/
def ofSupsetUniv (f : Pt → Pt') (σ : C → C') (hdom : ∀ p, dom p → dom' (f p))
    (h : ∀ p, dom p → ∀ c, obs' (f p) (σ c) ⊆ obs p c) :
    Transition (BChart Pt C B dom obs) (BChart Pt' C' B dom' obs') where
  pt := f
  sen := BSen.rename σ
  cls := BSen.Universal
  dir := .preserves
  dom_pt := hdom
  sat p s hp hs := ⟨fun _ hsrc =>
    (BSen.sat_rename σ _ s).2 (BSen.sat_of_subset_univ (h p hp) hs hsrc),
    fun e => absurd e (by decide)⟩

/-- **Equal up to copies of an ignored observation `d`** in the target (for `d = .diverges`:
the target may additionally diverge): equal on the sentences that ignore `d`. -/
def ofEqUnion (d : B) (f : Pt → Pt') (σ : C → C') (hdom : ∀ p, dom p → dom' (f p))
    (D : Pt → C → Set B) (hD : ∀ p c, ∀ b ∈ D p c, b = d)
    (h : ∀ p, dom p → ∀ c, obs' (f p) (σ c) = obs p c ∪ D p c) :
    Transition (BChart Pt C B dom obs) (BChart Pt' C' B dom' obs') where
  pt := f
  sen := BSen.rename σ
  cls := BSen.Ignores d
  dir := .equal
  dom_pt := hdom
  sat p s hp hs := by
    have e : (s.rename σ).Sat (obs' (f p)) ↔ s.Sat (obs p) :=
      (BSen.sat_rename σ _ s).trans ((BSen.sat_congr (h p hp) s).trans
        (BSen.sat_union_iff (hD p) hs))
    exact ⟨fun _ => e.2, fun _ => e.1⟩

/-- **Observations related up to `R` both ways**: equal on `R`-respecting sentences. -/
def ofUpTo (R : B → B → Prop) (f : Pt → Pt') (σ : C → C') (hdom : ∀ p, dom p → dom' (f p))
    (h₁ : ∀ p, dom p → ∀ c, ∀ b ∈ obs p c, ∃ b' ∈ obs' (f p) (σ c), R b b')
    (h₂ : ∀ p, dom p → ∀ c, ∀ b' ∈ obs' (f p) (σ c), ∃ b ∈ obs p c, R b b') :
    Transition (BChart Pt C B dom obs) (BChart Pt' C' B dom' obs') where
  pt := f
  sen := BSen.rename σ
  cls := BSen.Respects R
  dir := .equal
  dom_pt := hdom
  sat p s hp hs := by
    have e : s.Sat (obs p) ↔ (s.rename σ).Sat (obs' (f p)) :=
      (BSen.sat_iff_upto (obs' := fun c => obs' (f p) (σ c)) (h₁ p hp) (h₂ p hp) hs).trans
        (BSen.sat_rename σ _ s).symm
    exact ⟨fun _ => e.1, fun _ => e.2⟩

/-- **Source observations simulated up to `R` in the target**: the target reflects universal
`R`-respecting sentences. -/
def ofUpToUniv (R : B → B → Prop) (f : Pt → Pt') (σ : C → C')
    (hdom : ∀ p, dom p → dom' (f p))
    (h₁ : ∀ p, dom p → ∀ c, ∀ b ∈ obs p c, ∃ b' ∈ obs' (f p) (σ c), R b b') :
    Transition (BChart Pt C B dom obs) (BChart Pt' C' B dom' obs') where
  pt := f
  sen := BSen.rename σ
  cls s := s.Universal ∧ s.Respects R
  dir := .reflects
  dom_pt := hdom
  sat p s hp hs := ⟨fun e => absurd e (by decide), fun _ ht =>
    BSen.sat_upto_univ (obs' := fun c => obs' (f p) (σ c)) (h₁ p hp) hs.1 hs.2
      ((BSen.sat_rename σ _ s).1 ht)⟩

/-- **Source observations simulated up to `R` in the target**: the target preserves
existential `R`-respecting sentences. -/
def ofUpToExist (R : B → B → Prop) (f : Pt → Pt') (σ : C → C')
    (hdom : ∀ p, dom p → dom' (f p))
    (h₁ : ∀ p, dom p → ∀ c, ∀ b ∈ obs p c, ∃ b' ∈ obs' (f p) (σ c), R b b') :
    Transition (BChart Pt C B dom obs) (BChart Pt' C' B dom' obs') where
  pt := f
  sen := BSen.rename σ
  cls s := s.Existential ∧ s.Respects R
  dir := .preserves
  dom_pt := hdom
  sat p s hp hs := ⟨fun _ hsrc => (BSen.sat_rename σ _ s).2
      (BSen.sat_upto_exist (obs' := fun c => obs' (f p) (σ c)) (h₁ p hp) hs.1 hs.2 hsrc),
    fun e => absurd e (by decide)⟩

end BTrans

end Silmaril.Wasm.Atlas
