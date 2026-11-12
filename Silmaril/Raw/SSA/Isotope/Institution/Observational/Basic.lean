module

public import Silmaril.Logic.Institution.Borrowing
public import Silmaril.Logic.Institution.Observational.Sentence
public import Silmaril.SSA.Isotope.LambdaSSA.Thms
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.Data.Set.Function

/-!
# Observational institutions

The compiler calculi of `Silmaril.Isotope` (let-case, let-iter, lambda-SSA) share one operational
interface: an execution is parameterised by an atomic instruction relation, a primitive-fault
relation and a primitive-divergence predicate over arbitrary value and machine-state carriers,
and it is run in an environment of bound values. A program then has a *behaviour* at such a
choice of parameters: the finite results it can reach (with initial and final states), the
faults it can reach, and the initial states from which it diverges.

This file turns any such behavioural semantics into an institution in the sense of
`Silmaril.Logic.Institution` (a functor `Sign ⥤ Room`):

* signatures are numbers of ambient bound variables, the discrete category `Discrete ℕ`;
* models at `n` are the semantic parameters together with an environment of `n` bound values
  (`Model`), forming a discrete category;
* sentences are observational equations `a ≐ b` and observational refinements `a ⊑ b`
  between programs in scope `n` (`Sentence`);
* `M ⊨ a ≐ b` iff `a` and `b` have the same behaviour at `M`, and `M ⊨ a ⊑ b` iff every
  observable outcome of `a` at `M` is one of `b`.

A *translation* of behavioural semantics (`Behaviour.Translation`) maps programs forwards and
observations forwards, injectively on the observations that can occur, so that the behaviour of a
translated program is the image of the behaviour of the source. Every translation is an
institution comorphism whose signature functor and model functor are identities
(`Behaviour.Translation.coHom`); its satisfaction condition is the injectivity of the image map.
Because the model functors are identities, these comorphisms are model-expansive, so semantic
consequence is borrowed along them (`Behaviour.Translation.entails_iff`).

The concrete calculi are in `Silmaril.Isotope.Institution.Observational.Calculi`, the
compilations in `...Observational.Compilations`, and the lambda-SSA / let-iter isomorphism in
`...Observational.Isomorphism`.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Institution.Observational

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Observational

/-! ## Models: semantic parameters and environments -/

/-- A model of an observational institution at `n` bound variables: carriers of atomic values
and machine states, an atomic instruction relation, a primitive-fault relation, a
primitive-divergence predicate, and an environment of `n` bound values.

These are exactly the parameters over which `LetIter.LocallyNameless.Tm.Obs` and
`LambdaSSA.Region.Obs` quantify. -/
structure Model (Φ : Type u) (n : Nat) : Type (max u (v + 1) (w + 1)) where
  /-- The carrier of atomic values. -/
  α : Type v
  /-- The machine states. -/
  σ : Type w
  /-- The atomic instruction relation `instr f input before output after`. -/
  instr : Φ → Value α → σ → Value α → σ → Prop
  /-- The primitive-fault relation `faults f input before after`. -/
  faults : Φ → Value α → σ → σ → Prop
  /-- The primitive-divergence predicate `prim f input before`. -/
  prim : Φ → Value α → σ → Prop
  /-- The values of the `n` ambient bound variables. -/
  bound : Fin n → Value α

/-! ## Observations -/

/-- One observable outcome of a run: a finite result from an initial to a final state, a fault
from an initial to a final state, or divergence from an initial state. `V` is the type of
results (a value, or an exit label together with a value). -/
inductive Observation (V : Type v) (σ : Type w) : Type (max v w) where
  /-- A finite run from `s` returning `value` in final state `s'`. -/
  | ret (s : σ) (value : V) (s' : σ)
  /-- A run from `s` faulting in state `s'`. -/
  | fault (s s' : σ)
  /-- An infinite run from `s`, internal or inside a divergent primitive. -/
  | diverge (s : σ)

namespace Observation

variable {V V' : Type v} {σ : Type w}

/-- The set of observations described by a result predicate, a fault predicate and a
divergence predicate. -/
def Holds (ret : σ → V → σ → Prop) (fault : σ → σ → Prop) (diverge : σ → Prop) :
    Observation V σ → Prop
  | .ret s value s' => ret s value s'
  | .fault s s' => fault s s'
  | .diverge s => diverge s

/-- Translate the result of an observation, leaving faults and divergences alone. -/
def mapValue (g : V → V') : Observation V σ → Observation V' σ
  | .ret s value s' => .ret s (g value) s'
  | .fault s s' => .fault s s'
  | .diverge s => .diverge s

/-- The results of an observation lie in `S` (faults and divergences carry no result). -/
def ValuesIn (S : Set V) : Observation V σ → Prop
  | .ret _ value _ => value ∈ S
  | .fault _ _ => True
  | .diverge _ => True

@[simp] theorem mapValue_id : mapValue (σ := σ) (id : V → V) = id := by
  funext o
  cases o <;> rfl

/-- Result translation is injective on the observations whose results lie in a set on which
the translation is injective. -/
theorem mapValue_injOn {g : V → V'} {S : Set V} (h : Set.InjOn g S) :
    Set.InjOn (mapValue (σ := σ) g) {o | o.ValuesIn S} := by
  intro o ho o' ho' heq
  cases o <;> cases o' <;> simp only [mapValue, ret.injEq, fault.injEq, diverge.injEq,
    reduceCtorEq] at heq ⊢
  all_goals first
    | exact heq
    | (obtain ⟨rfl, hv, rfl⟩ := heq; exact ⟨rfl, h ho ho' hv, rfl⟩)

variable {g : V → V'} {S : Set (Observation V σ)}

/-- A finite result lies in an image exactly when some source result maps to it. -/
theorem ret_mem_image_iff {s s' : σ} {y : V'} :
    Observation.ret s y s' ∈ mapValue g '' S ↔ ∃ x, g x = y ∧ Observation.ret s x s' ∈ S := by
  constructor
  · rintro ⟨o, ho, h⟩
    cases o with
    | ret s₀ x s₀' =>
        simp only [mapValue, ret.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨x, rfl, ho⟩
    | fault _ _ => simp [mapValue] at h
    | diverge _ => simp [mapValue] at h
  · rintro ⟨x, rfl, hx⟩
    exact ⟨_, hx, rfl⟩

/-- A fault lies in an image exactly when it lies in the source. -/
theorem fault_mem_image_iff {s s' : σ} :
    Observation.fault s s' ∈ mapValue g '' S ↔ Observation.fault s s' ∈ S := by
  constructor
  · rintro ⟨o, ho, h⟩
    cases o with
    | ret _ _ _ => simp [mapValue] at h
    | fault s₀ s₀' =>
        simp only [mapValue, fault.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ho
    | diverge _ => simp [mapValue] at h
  · intro h
    exact ⟨_, h, rfl⟩

/-- A divergence lies in an image exactly when it lies in the source. -/
theorem diverge_mem_image_iff {s : σ} :
    Observation.diverge s ∈ mapValue g '' S ↔ Observation.diverge s ∈ S := by
  constructor
  · rintro ⟨o, ho, h⟩
    cases o with
    | ret _ _ _ => simp [mapValue] at h
    | fault _ _ => simp [mapValue] at h
    | diverge s₀ =>
        simp only [mapValue, diverge.injEq] at h
        subst h
        exact ho
  · intro h
    exact ⟨_, h, rfl⟩

/-- Two behaviours are equal exactly when they agree on results, faults and divergences. -/
theorem set_eq_iff {B B' : Set (Observation V σ)} :
    B = B' ↔ (∀ s x s', Observation.ret s x s' ∈ B ↔ Observation.ret s x s' ∈ B') ∧
      (∀ s s', Observation.fault s s' ∈ B ↔ Observation.fault s s' ∈ B') ∧
      (∀ s, Observation.diverge s ∈ B ↔ Observation.diverge s ∈ B') := by
  constructor
  · rintro rfl
    exact ⟨fun _ _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ => Iff.rfl⟩
  · rintro ⟨hr, hf, hd⟩
    ext o
    cases o with
    | ret s x s' => exact hr s x s'
    | fault s s' => exact hf s s'
    | diverge s => exact hd s

/-- One behaviour is included in another exactly when its results, faults and divergences
are. -/
theorem set_subset_iff {B B' : Set (Observation V σ)} :
    B ⊆ B' ↔ (∀ s x s', Observation.ret s x s' ∈ B → Observation.ret s x s' ∈ B') ∧
      (∀ s s', Observation.fault s s' ∈ B → Observation.fault s s' ∈ B') ∧
      (∀ s, Observation.diverge s ∈ B → Observation.diverge s ∈ B') := by
  constructor
  · intro h
    exact ⟨fun _ _ _ m => h m, fun _ _ m => h m, fun _ m => h m⟩
  · rintro ⟨hr, hf, hd⟩ o
    cases o with
    | ret s x s' => exact hr s x s'
    | fault s s' => exact hf s s'
    | diverge s => exact hd s

end Observation

/-! Sentences `Sentence.eq`/`Sentence.le` and `Sentence.Holds` are the public
`Silmaril.Logic.Institution.Observational.Sentence` (identical to the legacy definition). -/

/-! ## Behavioural semantics and their institutions -/

/-- A behavioural semantics over instruction alphabet `Φ`: programs in scope `n`, a result type
for each value carrier, and the behaviour of a program at a model. -/
structure Behaviour (Φ : Type u) : Type (max (u + 1) (v + 1) (w + 1)) where
  /-- Programs with `n` ambient bound variables. -/
  Prog : Nat → Type u
  /-- The type of finite results over a value carrier (a value, or a label and a value). -/
  Out : Type v → Type v
  /-- The behaviour of a program at a model. -/
  beh : {n : Nat} → (M : Model.{u, v, w} Φ n) → Prog n → Set (Observation (Out M.α) M.σ)

namespace Behaviour

variable {Φ : Type u}

/-- The room of a behavioural semantics at `n` bound variables: observational sentences,
the discrete category of models, and behavioural satisfaction. -/
def room (B : Behaviour.{u, v, w} Φ) (n : Nat) :
    Room.{u, max u (v + 1) (w + 1), max u (v + 1) (w + 1)} where
  Sen := Sentence (B.Prog n)
  Mod := Cat.of (Discrete (Model.{u, v, w} Φ n))
  Sat M φ := φ.Holds (B.beh (M : Discrete (Model.{u, v, w} Φ n)).as)

/-- The observational institution of a behavioural semantics, over the discrete category of
scopes. -/
def inst (B : Behaviour.{u, v, w} Φ) :
    Inst.{0, 0, u, max u (v + 1) (w + 1), max u (v + 1) (w + 1)} where
  Sign := Discrete ℕ
  I := Discrete.functor B.room

/-- Observational equivalence relative to a behavioural semantics: validity of the equation in
every model, i.e. semantic consequence from no hypotheses. -/
def ObsEq (B : Behaviour.{u, v, w} Φ) {n : Nat} (a b : B.Prog n) : Prop :=
  (B.room n).Entails ∅ (.eq a b)

/-- Observational refinement relative to a behavioural semantics. -/
def ObsLe (B : Behaviour.{u, v, w} Φ) {n : Nat} (a b : B.Prog n) : Prop :=
  (B.room n).Entails ∅ (.le a b)

theorem obsEq_iff (B : Behaviour.{u, v, w} Φ) {n : Nat} (a b : B.Prog n) :
    B.ObsEq a b ↔ ∀ M : Model.{u, v, w} Φ n, B.beh M a = B.beh M b :=
  ⟨fun h M => h (Discrete.mk M) (fun _ hψ => False.elim hψ), fun h M _ => h (Discrete.as M)⟩

theorem obsLe_iff (B : Behaviour.{u, v, w} Φ) {n : Nat} (a b : B.Prog n) :
    B.ObsLe a b ↔ ∀ M : Model.{u, v, w} Φ n, B.beh M a ⊆ B.beh M b :=
  ⟨fun h M => h (Discrete.mk M) (fun _ hψ => False.elim hψ), fun h M _ => h (Discrete.as M)⟩

/-- A translation of behavioural semantics: programs map forwards, results map forwards
injectively on the results that can occur, and the behaviour of a translated program is the
image of the behaviour of its source at the same model. -/
structure Translation (A B : Behaviour.{u, v, w} Φ) where
  /-- The program translation (the compiler). -/
  prog : {n : Nat} → A.Prog n → B.Prog n
  /-- The result translation. -/
  out : {α : Type v} → A.Out α → B.Out α
  /-- The results that source programs can produce. -/
  dom : {α : Type v} → Set (A.Out α)
  /-- The result translation is injective on the results that can occur. -/
  injOn : ∀ {α : Type v}, Set.InjOn (out (α := α)) dom
  /-- Source behaviours only produce results in `dom`. -/
  beh_sub : ∀ {n : Nat} (M : Model.{u, v, w} Φ n) (p : A.Prog n),
    A.beh M p ⊆ {o | o.ValuesIn dom}
  /-- Semantic preservation and reflection: the translated behaviour is the image. -/
  beh_prog : ∀ {n : Nat} (M : Model.{u, v, w} Φ n) (p : A.Prog n),
    B.beh M (prog p) = Observation.mapValue out '' A.beh M p

namespace Translation

variable {A B : Behaviour.{u, v, w} Φ}

/-- The satisfaction condition of a translation, at one model: a translated sentence holds
exactly when its source does. -/
theorem holds_map_iff (T : Translation A B) {n : Nat} (M : Model.{u, v, w} Φ n)
    (φ : Sentence (A.Prog n)) : (φ.map T.prog).Holds (B.beh M) ↔ φ.Holds (A.beh M) := by
  cases φ with
  | eq a b =>
      change B.beh M (T.prog a) = B.beh M (T.prog b) ↔ A.beh M a = A.beh M b
      rw [T.beh_prog, T.beh_prog]
      exact (Observation.mapValue_injOn T.injOn).image_eq_image_iff (T.beh_sub M a)
        (T.beh_sub M b)
  | le a b =>
      change B.beh M (T.prog a) ⊆ B.beh M (T.prog b) ↔ A.beh M a ⊆ A.beh M b
      rw [T.beh_prog, T.beh_prog]
      exact (Observation.mapValue_injOn T.injOn).image_subset_image_iff (T.beh_sub M a)
        (T.beh_sub M b)

/-- The corridor of a translation at `n` bound variables: sentence translation is the program
translation on both sides, and model translation is the identity. -/
def corridor (T : Translation A B) (n : Nat) : A.room n ⟶ B.room n where
  sen := Sentence.map T.prog
  mod := 𝟭 _
  sat M φ := T.holds_map_iff (M : Discrete (Model.{u, v, w} Φ n)).as φ

/-- The comorphism of observational institutions induced by a translation: the identity on
signatures and models, the program translation on sentences. -/
def coHom (T : Translation A B) : Inst.CoHom A.inst B.inst where
  Φ := 𝟭 _
  ρ := Discrete.natTrans (fun n => T.corridor n.as)

/-- The comorphism of a translation is model-expansive: its model functors are identities. -/
theorem coHom_modelExpansive (T : Translation A B) : T.coHom.ModelExpansive :=
  fun _ M => ⟨M, rfl⟩

/-- Borrowing along a translation: consequence in the source is consequence of the translated
sentences in the target. -/
theorem entails_iff (T : Translation A B) (n : Nat) (Γ : Set (Sentence (A.Prog n)))
    (φ : Sentence (A.Prog n)) :
    (A.room n).Entails Γ φ ↔ (B.room n).Entails (Sentence.map T.prog '' Γ) (φ.map T.prog) :=
  T.coHom.entails_iff T.coHom_modelExpansive (Discrete.mk n) Γ φ

/-- A translation preserves and reflects observational equivalence. -/
theorem obsEq_iff (T : Translation A B) {n : Nat} (a b : A.Prog n) :
    B.ObsEq (T.prog a) (T.prog b) ↔ A.ObsEq a b := by
  rw [Behaviour.obsEq_iff, Behaviour.obsEq_iff]
  exact forall_congr' fun M => T.holds_map_iff M (.eq a b)

/-- A translation preserves and reflects observational refinement. -/
theorem obsLe_iff (T : Translation A B) {n : Nat} (a b : A.Prog n) :
    B.ObsLe (T.prog a) (T.prog b) ↔ A.ObsLe a b := by
  rw [Behaviour.obsLe_iff, Behaviour.obsLe_iff]
  exact forall_congr' fun M => T.holds_map_iff M (.le a b)

end Translation

end Behaviour

end Silmaril.Isotope.Institution.Observational
