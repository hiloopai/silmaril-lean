module

public import Silmaril.Wasm.Institution.Generic.Defs
public import Silmaril.Games.Handler.Thms
public import Silmaril.Games.LTS.Thms
public import Mathlib.CategoryTheory.Category.Preorder
public import Silmaril.Wasm.Binaryen.Behaviour

@[expose] public section

/-!
# Reduction semantics versus game semantics, as institutions

Three observational semantics (`ObsSemantics`) built on the game-semantics core `Silmaril.Games`,
and the translations between them.

## Interfaces

Game signatures `Silmaril.Games.Sig.{0}` live in `Type 1`, but the graph of
`Silmaril.Wasm.Institution.Graph` lives at `Inst.{1,0,0,0,0}`: interfaces must form a small
category. So interfaces are a small category `I` *indexing* game signatures
(`GameIfaces`): `sig : I → Sig`, with every interface morphism sent to a signature renaming
`hom f : Sig.Hom (sig X) (sig Y)` (functorially), and a top interface through which programs
are given. The reduct of a strategy along `f` is `Strategy.restrict` along `hom f` (hiding the
operations outside the image). For Wasm, `exportIfaces`: interfaces are export-name sets
`X : Set String`, and `sig X` has one operation per invocation `(x, vs)` with `x ∈ X`, answered
by a behaviour.

## The three logics (lower signature `E`, the calls a component may make)

* `gameSem G E`: semantic objects are **strategies** `Strategy E (sig X)`; programs are
  strategies at the top interface; `⊑` is strategy refinement (inclusion of plays); operators
  are strategies `τ : Strategy E E` plugged below (`τ.comp σ`, an environment for the calls).
* `redSem G E red`: programs are elements of a type `RProg` with a **reduction semantics**
  `red : RProg → Reduction E (sig top)` (a language: syntax plus small-step reduction with
  external calls). Its semantic objects are again strategies; a program denotes the strategy of
  its traces, `Strategy.ofReduction`. `valid_red_top_iff_traces` (in `Thms`) reads validity of
  `p ⊑ q` as trace inclusion: every legal trace of `red p` is a play of `red q`'s strategy.
* `ltsSem G E lts`: the same for transition systems (`Strategy.ofLTS`), which may keep state
  across questions.

Reductions and transition systems are in `Type 1` as well. They therefore enter through a small
index of programs. This is also the natural reading: a language's syntax together with its
reduction semantics.

## Translations

* `redToGame`: `p ↦ ⟨ofReduction (red p)⟩`. The satisfaction condition is the adequacy equation
  `sem_den`: the strategy denoted by the translated program is the reduction program's
  denotation. In `Silmaril.Games` the strategy of a reduction is *defined* from its traces, so
  this equation holds by `rfl`. The content of adequacy is the trace characterization
  (`Strategy.ofLTS_le_iff`, used in `valid_red_top_iff_traces`).
* `redToLts`: `p ↦ (red p).toLTS` (`ofReduction = ofLTS ∘ toLTS`), and `ltsToGame`.
* All three have identity semantic maps, so they are model-expansive and borrow entailment.
  Their duals `toHom` are institution morphisms `game → red`, `game → lts`, `lts → red`, which
  project the game logic onto the operational ones.
-/

namespace Silmaril.Wasm.Institution.Games

open CategoryTheory ObsSemantics

/-- A small category of interfaces indexing game signatures, with a top interface. -/
structure GameIfaces where
  /-- Interfaces. -/
  I : Type
  [cat : Category.{0} I]
  /-- The game signature of an interface (the operations offered). -/
  sig : I → Silmaril.Games.Sig.{0}
  /-- Interface morphisms as signature renamings. -/
  hom : ∀ {X Y : I}, (X ⟶ Y) → Silmaril.Games.Sig.Hom (sig X) (sig Y)
  hom_id : ∀ X : I, hom (𝟙 X) = Silmaril.Games.Sig.Hom.id (sig X)
  hom_comp : ∀ {X Y Z : I} (f : X ⟶ Y) (g : Y ⟶ Z), hom (f ≫ g) = (hom f).comp (hom g)
  /-- The top interface, through which programs are given. -/
  top : I
  /-- Every interface sits in the top one. -/
  toTop : ∀ X : I, X ⟶ top
  toTop_top : toTop top = 𝟙 top

attribute [instance] GameIfaces.cat

namespace GameIfaces

variable (G : GameIfaces) (E : Silmaril.Games.Sig.{0})

/-- Restriction of strategies along interface morphisms. -/
def res {X Y : G.I} (f : X ⟶ Y) (σ : Silmaril.Games.Strategy E (G.sig Y)) :
    Silmaril.Games.Strategy E (G.sig X) :=
  σ.restrict (G.hom f)

theorem res_id {X : G.I} (σ : Silmaril.Games.Strategy E (G.sig X)) : G.res E (𝟙 X) σ = σ := by
  rw [res, G.hom_id]
  exact Silmaril.Games.Strategy.restrict_id σ

theorem res_comp {X Y Z : G.I} (f : X ⟶ Y) (g : Y ⟶ Z)
    (σ : Silmaril.Games.Strategy E (G.sig Z)) : G.res E (f ≫ g) σ = G.res E f (G.res E g σ) := by
  rw [res, res, res, G.hom_comp]
  exact Silmaril.Games.Strategy.restrict_comp σ (G.hom f) (G.hom g)

/-- The strategy semantics with programs `RProg` denoting top-level strategies via `str`. -/
def stratSem (RProg : Type) (str : RProg → Silmaril.Games.Strategy E (G.sig G.top)) :
    ObsSemantics G.I where
  Sem X := Silmaril.Games.Strategy E (G.sig X)
  restrict f σ := G.res E f σ
  restrict_id σ := G.res_id E σ
  restrict_comp f g σ := G.res_comp E f g σ
  Prog := RProg
  den X p := G.res E (G.toTop X) (str p)
  Op := Silmaril.Games.Strategy E E
  op _ τ σ := τ.comp σ
  Le _ σ τ := σ ≤ τ

end GameIfaces

variable (G : GameIfaces) (E : Silmaril.Games.Sig.{0})

/-- **The game-semantics logic**: models assign strategies, programs are strategies. -/
abbrev gameSem : ObsSemantics G.I := G.stratSem E (Silmaril.Games.Strategy E (G.sig G.top)) id

/-- **The reduction-semantics logic** of a language `red : RProg → Reduction`. -/
abbrev redSem {RProg : Type} (red : RProg → Silmaril.Games.Reduction E (G.sig G.top)) :
    ObsSemantics G.I :=
  G.stratSem E RProg fun p => Silmaril.Games.Strategy.ofReduction (red p)

/-- **The transition-system logic** of a language `lts : RProg → LTS`. -/
abbrev ltsSem {RProg : Type} (lts : RProg → Silmaril.Games.LTS E (G.sig G.top)) :
    ObsSemantics G.I :=
  G.stratSem E RProg fun p => Silmaril.Games.Strategy.ofLTS (lts p)

/-- A change of programs preserving the denoted strategy is a translation of strategy
semantics. -/
def stratT {P Q : Type} {s : P → Silmaril.Games.Strategy E (G.sig G.top)}
    {t : Q → Silmaril.Games.Strategy E (G.sig G.top)} (g : P → Q) (hg : ∀ p, t (g p) = s p) :
    Translation (𝟭 G.I) (G.stratSem E P s) (G.stratSem E Q t) where
  sem _ σ := σ
  sem_restrict _ _ := rfl
  prog := g
  sem_den X p := congrArg (G.res E (G.toTop X)) (hg p)
  op o := o
  sem_op _ _ _ := rfl
  atom a b := .le a b
  atom_mapVars _ _ _ := rfl
  atom_holds _ _ _ _ _ := Iff.rfl

theorem stratT_surjective {P Q : Type} {s : P → Silmaril.Games.Strategy E (G.sig G.top)}
    {t : Q → Silmaril.Games.Strategy E (G.sig G.top)} (g : P → Q) (hg : ∀ p, t (g p) = s p)
    (X : G.I) : Function.Surjective ((stratT G E g hg).sem X) := fun σ => ⟨σ, rfl⟩

variable {RProg : Type}

/-- **Reduction semantics into game semantics**: a program goes to the strategy of its
reduction; the satisfaction condition is adequacy (`sem_den`). -/
def redToGame (red : RProg → Silmaril.Games.Reduction E (G.sig G.top)) :
    Translation (𝟭 G.I) (redSem G E red) (gameSem G E) :=
  stratT G E (fun p => Silmaril.Games.Strategy.ofReduction (red p)) (fun _ => rfl)

/-- Reduction semantics into transition systems. -/
def redToLts (red : RProg → Silmaril.Games.Reduction E (G.sig G.top)) :
    Translation (𝟭 G.I) (redSem G E red) (ltsSem G E fun p => (red p).toLTS) :=
  stratT G E id (fun _ => rfl)

/-- Transition systems into game semantics. -/
def ltsToGame (lts : RProg → Silmaril.Games.LTS E (G.sig G.top)) :
    Translation (𝟭 G.I) (ltsSem G E lts) (gameSem G E) :=
  stratT G E (fun p => Silmaril.Games.Strategy.ofLTS (lts p)) (fun _ => rfl)

/-! ## Wasm export interfaces -/

/-- The game signature of an export set: one operation per invocation `(x, vs)` of an export
`x ∈ X`, answered by a behaviour. -/
def exportSig (X : Set String) : Silmaril.Games.Sig.{0} :=
  ⟨{c : String × List Silmaril.Wasm.Execution.Core.Val // c.1 ∈ X},
    fun _ => Silmaril.Wasm.Behaviour Silmaril.Wasm.Execution.Core.Val⟩

/-- Export-name sets as game interfaces: inclusions rename invocations, top is all names. -/
def exportIfaces : GameIfaces where
  I := Set String
  sig := exportSig
  hom f := ⟨fun c => ⟨c.1, f.le c.2⟩, fun _ n => n⟩
  hom_id _ := rfl
  hom_comp _ _ := rfl
  top := Set.univ
  toTop X := homOfLE (Set.subset_univ X)
  toTop_top := rfl

/-! ## A reduction semantics grounded in Wasm Core

What is grounded: configurations, internal reduction (`Execution.Core.Step P host`), export
lookup (`Binaryen.exportFunc?`), invocation (`invoke`) and results are silmaril's Core 3.0
definitions, for an *already instantiated* module (a store and a module instance). What is not:
host calls are not exposed as game moves. The lower signature is `Sig.empty`, and host
functions run inside `Step` through the `host` relation. Each question (an export invocation)
starts afresh from the same store, because `Silmaril.Games.Reduction` keeps no state between
questions. This is the single-invocation shape of `Equiv.EntryPoints`, not the store-sharing
session shape of `ExportRefines`.
-/

section Wasm

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} (P : Profile) (host : HostSemantics H)

/-- An instantiated module: a store and a module instance. -/
abbrev Inst (H : Type) : Type := Store H × ModuleInst

/-- The reduction semantics of an instantiated module, one export invocation per question. -/
def wasmRed (w : Inst H) :
    Silmaril.Games.Reduction Silmaril.Games.Sig.empty (exportIfaces.sig exportIfaces.top) where
  Conf _ := Option (Config H)
  start q := (Binaryen.exportFunc? w.2 q.1.1).map fun a => invoke w.1 a q.1.2
  step c c' := ∃ d d', c = some d ∧ c' = some d' ∧ Step P host d d'
  call _ m _ := PEmpty.elim m
  done c r := ∃ (d : Config H) (res : Result), c = some d ∧ d.code = res.toAdmin ∧
    r = res.toBehaviour

/-- The single-invocation entry points of instantiated modules. -/
def instEntry : Equiv.EntryPoints (Inst H) String Val where
  Ok w x vs := ∃ a, Binaryen.exportFunc? w.2 x = some a ∧ InvokeOk w.1 a vs
  beh w x vs := {b | ∃ a, Binaryen.exportFunc? w.2 x = some a ∧ b ∈ behaviours P host w.1 a vs}

/-- **Open, not proved (frozen statement).** This is the converse of `finite_beh_of_le`: if
every non-divergent behaviour of every export invocation of `w` is one of `w'`, then the
strategy of `w` refines that of `w'`. It would need a characterization of all plays of
`ofReduction (wasmRed P host w)` as sequences of independent two-move exchanges, possibly ending
with a pending question. Nothing depends on it. -/
def Task.wasmRed_le_of_finite_beh : Prop :=
  ∀ w w' : Inst H, (∀ x vs (b : Behaviour Val), b ≠ .diverges →
      b ∈ (instEntry P host).beh w x vs → b ∈ (instEntry P host).beh w' x vs) →
    Silmaril.Games.Strategy.ofReduction (wasmRed P host w) ≤
      Silmaril.Games.Strategy.ofReduction (wasmRed P host w')

end Wasm

end Silmaril.Wasm.Institution.Games
