module

public import Silmaril.Compile.Category.Compiler
public import Mathlib.Logic.Relation

@[expose] public section

/-!
# Execution semantics, cofunctors and simulations

The runtime half of the category of compilers, missing from the pinned silmaril-lean.

An execution semantics `Exec L` of a language has configurations, initial configurations of
each program, a step relation and final observations; it is *adequate* when the behaviours of
the language are exactly the observations of finite complete runs. Its execution category is
the thin category of configurations and runs (`Exec.Cfg`, the reachability preorder).

The runtime half of a compiler is a *relational cofunctor* (`RelCofunctor`): a matching of
configurations such that every target run from a matched pair lifts to a source run ending
matched (configurations forward, runs backward; Aguiar's cofunctors as presented by Ahman and
Uustalu, *Taking updates seriously*, 2017, p. 8, in a relational, thin form).
`BackwardSim` (with a stuttering measure, Leroy 2009, §2.1 Definition 2 and §3.7
Definition 12) gives one; `ForwardSim` (Definition 4) gives validity for deterministic
targets (the flip of Leroy 2009, §2.1, Figure 2). Theorems are in
`Silmaril.Wasm.Category.Exec.Thms`.

Only finite complete runs are observed: an `Exec` is adequate only for a language whose
behaviours are finite observations. The Wasm languages of `Silmaril.Wasm.Category` observe
divergence, so they are related by realisations (`Silmaril.Wasm.Category.Institution`) rather
than by `Exec`; this file is the generic interface.
-/

namespace Silmaril.Wasm.Category

open CategoryTheory Relation Silmaril.Compile.Category

universe u

/-- An execution semantics: configurations, initial configurations, steps and final
observations, adequate for the behaviours of the language. -/
structure Exec (L : Language.{u}) : Type (u + 1) where
  /-- Configurations. -/
  Conf : Type u
  /-- Initial configurations of a program. -/
  init : L.Prog → Set Conf
  /-- One step of execution. -/
  step : Conf → Conf → Prop
  /-- `final s o`: configuration `s` has terminated with observation `o`. -/
  final : Conf → L.Obs → Prop
  /-- Adequacy: behaviours are the observations of finite complete runs. -/
  adequate : ∀ p, L.beh p = {o | ∃ s ∈ init p, ∃ t, ReflTransGen step s t ∧ final t o}

namespace Exec

variable {L : Language.{u}} (E : Exec L)

/-- The objects of the execution category: configurations. -/
def Cfg : Type u := E.Conf

/-- Runs order configurations by reachability; the execution category is the associated thin
category. -/
instance : Preorder E.Cfg where
  le := ReflTransGen E.step
  le_refl _ := ReflTransGen.refl
  le_trans _ _ _ := ReflTransGen.trans

/-- Deterministic executions: one initial configuration, deterministic steps, final
configurations are stuck and have one observation. -/
structure Deterministic : Prop where
  init : ∀ p, (E.init p).Subsingleton
  step : ∀ s t t', E.step s t → E.step s t' → t = t'
  final_stuck : ∀ s o t, E.final s o → ¬ E.step s t
  final : ∀ s o o', E.final s o → E.final s o' → o = o'

end Exec

variable {L L' L'' : Language.{u}}

/-- A relational cofunctor between execution categories: matched configurations, with every
target run from a matched configuration lifted to a source run ending matched. -/
structure RelCofunctor (E : Exec L) (E' : Exec L') where
  /-- Matching of source and target configurations. -/
  M : E.Conf → E'.Conf → Prop
  /-- Lifting of runs, backwards. -/
  lift : ∀ {s s' t'}, M s s' → ReflTransGen E'.step s' t' →
    ∃ t, ReflTransGen E.step s t ∧ M t t'

namespace RelCofunctor

variable {E : Exec L} {E' : Exec L'} {E'' : Exec L''}

/-- The identity cofunctor. -/
def id (E : Exec L) : RelCofunctor E E where
  M := (· = ·)
  lift h r := by
    subst h
    exact ⟨_, r, rfl⟩

/-- Composition of relational cofunctors. -/
def comp (κ : RelCofunctor E E') (κ' : RelCofunctor E' E'') : RelCofunctor E E'' where
  M := Relation.Comp κ.M κ'.M
  lift := by
    rintro s s'' t'' ⟨s', h, h'⟩ r''
    obtain ⟨t', r', ht'⟩ := κ'.lift h' r''
    obtain ⟨t, r, ht⟩ := κ.lift h r'
    exact ⟨t, r, t', ht, ht'⟩

/-- A cofunctor with a function on objects (Aguiar's form, in the thin case): every target run
from the image of a configuration is the image of a source run. -/
def ofFunction (F : E.Conf → E'.Conf)
    (hF : ∀ {s t'}, ReflTransGen E'.step (F s) t' → ∃ t, ReflTransGen E.step s t ∧ F t = t') :
    RelCofunctor E E' where
  M s s' := F s = s'
  lift h r := by
    subst h
    exact hF r

end RelCofunctor

/-- A backward simulation with a stuttering measure, for a fixed source/target program pair. -/
structure BackwardSim (c : L ⟶ L') (E : Exec L) (E' : Exec L') (p : L.Prog) (p' : L'.Prog) where
  /-- Matching of configurations. -/
  M : E.Conf → E'.Conf → Prop
  /-- The stuttering measure on target configurations. -/
  measure : E'.Conf → ℕ
  /-- Every target initial configuration is matched. -/
  init : ∀ s' ∈ E'.init p', ∃ s ∈ E.init p, M s s'
  /-- A target step is matched by source steps, or by a stutter that decreases the measure. -/
  step : ∀ {s s' t'}, M s s' → E'.step s' t' →
    (∃ t, TransGen E.step s t ∧ M t t') ∨ (M s t' ∧ measure t' < measure s')
  /-- Matched target final observations realise source final observations. -/
  final : ∀ {s s' o'}, M s s' → E'.final s' o' →
    ∃ o, c.R o o' ∧ ∃ t, ReflTransGen E.step s t ∧ E.final t o

/-- The relational cofunctor of a backward simulation. -/
def BackwardSim.toRelCofunctor {c : L ⟶ L'} {E : Exec L} {E' : Exec L'} {p : L.Prog}
    {p' : L'.Prog} (σ : BackwardSim c E E' p p') : RelCofunctor E E' where
  M := σ.M
  lift := by
    intro s s' t' hM r'
    induction r' with
    | refl => exact ⟨s, ReflTransGen.refl, hM⟩
    | tail _ hstep ih =>
      obtain ⟨t, r, ht⟩ := ih
      rcases σ.step ht hstep with ⟨u, ru, hu⟩ | ⟨hu, -⟩
      · exact ⟨u, r.trans ru.to_reflTransGen, hu⟩
      · exact ⟨t, r, hu⟩

/-- A forward simulation for a fixed source/target program pair. -/
structure ForwardSim (c : L ⟶ L') (E : Exec L) (E' : Exec L') (p : L.Prog) (p' : L'.Prog) where
  /-- Matching of configurations. -/
  M : E.Conf → E'.Conf → Prop
  /-- Every source initial configuration is matched. -/
  init : ∀ s ∈ E.init p, ∃ s' ∈ E'.init p', M s s'
  /-- A source step is matched by target steps. -/
  step : ∀ {s s' t}, M s s' → E.step s t → ∃ t', ReflTransGen E'.step s' t' ∧ M t t'
  /-- Source final observations are realised by target final observations. -/
  final : ∀ {s s' o}, M s s' → E.final s o →
    ∃ o', c.R o o' ∧ ∃ t', ReflTransGen E'.step s' t' ∧ E'.final t' o'

end Silmaril.Wasm.Category
