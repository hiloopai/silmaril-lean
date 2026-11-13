module

public import Silmaril.Wasm.Institution.Graph.Defs

@[expose] public section

/-!
# Phase-2 hooks: component and game-semantic logics

Phase 1 (`Silmaril.Wasm.Institution.Graph`) covers reduction-semantics logics of Core and
Binaryen IR modules. Phase 2 will add a *component* logic and a *game-semantic* logic. This file
fixes the interface through which they attach; it makes no claim about them.

## How a new logic attaches

A new logic is an `ObsSemantics J` over its own interface category `J`, together with an
interface functor `embed : Set String ⥤ J` and translations
`ObsSemantics.Translation embed (Graph.sem P host Env a) target` from chosen phase-1 nodes `a`
(`Hook`). `Hook.graph` adds it as a new node of the logic graph, with one comorphism edge per
translation (`LogicGraph.extend`). If its translations have surjective semantic maps, every path
of the extended graph stays model-expansive (`Hook.pathModelExpansive`), so heterogeneous
borrowing (`LogicGraph.entails_lift_path_iff`) applies to it unchanged.

## Component logic (planned)

* `J`: component interfaces (named imports/exports with types); `embed X`: the interface of a
  core module exporting `X` (no imports).
* Models: assignments of *component behaviours* to component variables
  (`target.Sem`); `target.Le`: component refinement.
* Translation from `⟨session, core, n⟩`: `prog m ↦` the trivial component wrapping `m`;
  `sem` observes a component behaviour through its core-module exports.
  - `sem_den` says wrapping preserves meaning: the observation of the wrapped component is the
    module's denotation;
  - `atom_holds` says component refinement, observed through core exports, is module
    refinement (for `atom := le`), which is the satisfaction condition of the comorphism.

## Game-semantic logic (on `Silmaril.Games`)

Implemented in `Silmaril.Wasm.Institution.Games` and `Silmaril.Wasm.Institution.GameGraph`: the game,
reduction and transition-system logics are joined to the phase-1 graph by
`LogicGraph.sum`, so far without cross edges. What follows describes the still-missing cross
edge from the module-level session logic.

* Models: assignments of *strategies* to program variables; `target.Le`: strategy refinement.
* Translation from `⟨session, core, refEq⟩` (reduction semantics ↦ games): `prog m ↦` the
  strategy of `m` (its traces); `sem σ` is the session object observed from the strategy `σ`
  (interaction with a script-playing opponent).
  - `sem_den` is **adequacy**: the observations of the strategy of `m` are `m`'s reduction
    semantics `den P host X m`;
  - `atom_holds` (with `atom := le`) asks that strategy refinement agree with refinement of the
    observed session objects. If `target.Le` is chosen finer than that, use a different atom
    or a theoroidal comorphism; this choice is left to phase 2.
  - `sem` surjective (every session object is observed from some strategy) gives
    model-expansiveness, hence borrowing of reduction-semantics entailment from games.
-/

namespace Silmaril.Wasm.Institution

open CategoryTheory Silmaril.Logic.Institution Silmaril.Wasm Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics ObsSemantics

namespace LogicGraph

/-- Comorphism edges of a logic graph extended by one node (`none`). -/
def ExtComor (L : Silmaril.Inst.LogicGraph₁)
    (In : L.Logics → Type) : Option L.Logics → Option L.Logics → Type
  | some a, some b => L.Comor a b
  | some a, none => In a
  | none, _ => PEmpty

/-- Morphism edges of a logic graph extended by one node. -/
def ExtMor (L : Silmaril.Inst.LogicGraph₁) :
    Option L.Logics → Option L.Logics → Type
  | some a, some b => L.Mor a b
  | _, _ => PEmpty

/-- Institutions of a logic graph extended by one node. -/
def extInst (L : Silmaril.Inst.LogicGraph₁)
    (J : Silmaril.Inst.Institution₁) : Option L.Logics → Silmaril.Inst.Institution₁
  | some a => L.inst a
  | none => J

/-- **Extend a logic graph by one logic `J`**, with comorphism edges `In a` from existing logics
`a` into `J`. -/
def extend (L : Silmaril.Inst.LogicGraph₁)
    (J : Silmaril.Inst.Institution₁) (In : L.Logics → Type)
    (inE : ∀ {a}, In a → Inst.CoHom (L.inst a) J) :
    Silmaril.Inst.LogicGraph₁ where
  Logics := Option L.Logics
  inst := extInst L J
  Comor := ExtComor L In
  comor := fun {a b} e =>
    match a, b, e with
    | some _, some _, e => L.comor e
    | some _, none, e => inE e
    | none, _, e => e.elim
  Mor := ExtMor L
  mor := fun {a b} e =>
    match a, b, e with
    | some _, some _, e => L.mor e
    | some _, none, e => e.elim
    | none, _, e => e.elim

/-- If the old edges and the new edges are model-expansive, so is every edge of the
extension. -/
theorem extend_edge_modelExpansive (L : Silmaril.Inst.LogicGraph₁)
    (J : Silmaril.Inst.Institution₁) (In : L.Logics → Type)
    (inE : ∀ {a}, In a → Inst.CoHom (L.inst a) J)
    (hL : ∀ {a b} (e : L.Comor a b), (L.comor e).ModelExpansive)
    (hIn : ∀ {a} (e : In a), (inE e).ModelExpansive) :
    ∀ {a b : Option L.Logics} (e : ExtComor L In a b), ((extend L J In inE).comor e).ModelExpansive
  | some _, some _, e => hL e
  | some _, none, e => hIn e
  | none, _, e => e.elim

/-- Paths of the extension are model-expansive under the same hypotheses. -/
theorem extend_pathModelExpansive
    (L : Silmaril.Inst.LogicGraph₁)
    (J : Silmaril.Inst.Institution₁) (In : L.Logics → Type)
    (inE : ∀ {a}, In a → Inst.CoHom (L.inst a) J)
    (hL : ∀ {a b} (e : L.Comor a b), (L.comor e).ModelExpansive)
    (hIn : ∀ {a} (e : In a), (inE e).ModelExpansive) :
    ∀ {a b : (extend L J In inE).Idx} (p : Quiver.Path a b),
      (extend L J In inE).PathModelExpansive p
  | _, _, .nil => trivial
  | _, _, .cons p e =>
    ⟨extend_pathModelExpansive L J In inE hL hIn p,
      extend_edge_modelExpansive L J In inE hL hIn e⟩

/-- Comorphism edges of the sum of two logic graphs, with cross edges `Cross a b` from the
first into the second. -/
def SumComor (L₁ L₂ : Silmaril.Inst.LogicGraph₁)
    (Cross : L₁.Logics → L₂.Logics → Type) : L₁.Logics ⊕ L₂.Logics → L₁.Logics ⊕ L₂.Logics → Type
  | .inl a, .inl b => L₁.Comor a b
  | .inr a, .inr b => L₂.Comor a b
  | .inl a, .inr b => Cross a b
  | .inr _, .inl _ => PEmpty

/-- Morphism edges of the sum of two logic graphs (no cross morphisms). -/
def SumMor (L₁ L₂ : Silmaril.Inst.LogicGraph₁) :
    L₁.Logics ⊕ L₂.Logics → L₁.Logics ⊕ L₂.Logics → Type
  | .inl a, .inl b => L₁.Mor a b
  | .inr a, .inr b => L₂.Mor a b
  | _, _ => PEmpty

/-- Institutions of the sum of two logic graphs. -/
def sumInst (L₁ L₂ : Silmaril.Inst.LogicGraph₁) :
    L₁.Logics ⊕ L₂.Logics → Silmaril.Inst.Institution₁
  | .inl a => L₁.inst a
  | .inr b => L₂.inst b

/-- **The sum of two logic graphs** with comorphism cross edges from the first into the
second. -/
def sum (L₁ L₂ : Silmaril.Inst.LogicGraph₁)
    (Cross : L₁.Logics → L₂.Logics → Type)
    (cross : ∀ {a b}, Cross a b → Inst.CoHom (L₁.inst a) (L₂.inst b)) :
    Silmaril.Inst.LogicGraph₁ where
  Logics := L₁.Logics ⊕ L₂.Logics
  inst := sumInst L₁ L₂
  Comor := SumComor L₁ L₂ Cross
  comor := fun {a b} e =>
    match a, b, e with
    | .inl _, .inl _, e => L₁.comor e
    | .inr _, .inr _, e => L₂.comor e
    | .inl _, .inr _, e => cross e
    | .inr _, .inl _, e => e.elim
  Mor := SumMor L₁ L₂
  mor := fun {a b} e =>
    match a, b, e with
    | .inl _, .inl _, e => L₁.mor e
    | .inr _, .inr _, e => L₂.mor e
    | .inl _, .inr _, e => e.elim
    | .inr _, .inl _, e => e.elim

/-- Every edge of a sum is model-expansive when the edges of its parts are. -/
theorem sum_edge_modelExpansive
    (L₁ L₂ : Silmaril.Inst.LogicGraph₁)
    (Cross : L₁.Logics → L₂.Logics → Type)
    (cross : ∀ {a b}, Cross a b → Inst.CoHom (L₁.inst a) (L₂.inst b))
    (h₁ : ∀ {a b} (e : L₁.Comor a b), (L₁.comor e).ModelExpansive)
    (h₂ : ∀ {a b} (e : L₂.Comor a b), (L₂.comor e).ModelExpansive)
    (hc : ∀ {a b} (e : Cross a b), (cross e).ModelExpansive) :
    ∀ {a b : L₁.Logics ⊕ L₂.Logics} (e : SumComor L₁ L₂ Cross a b),
      ((sum L₁ L₂ Cross cross).comor e).ModelExpansive
  | .inl _, .inl _, e => h₁ e
  | .inr _, .inr _, e => h₂ e
  | .inl _, .inr _, e => hc e
  | .inr _, .inl _, e => e.elim

/-- Every path of a sum is model-expansive when all its edges are. -/
theorem sum_pathModelExpansive
    (L₁ L₂ : Silmaril.Inst.LogicGraph₁)
    (Cross : L₁.Logics → L₂.Logics → Type)
    (cross : ∀ {a b}, Cross a b → Inst.CoHom (L₁.inst a) (L₂.inst b))
    (h₁ : ∀ {a b} (e : L₁.Comor a b), (L₁.comor e).ModelExpansive)
    (h₂ : ∀ {a b} (e : L₂.Comor a b), (L₂.comor e).ModelExpansive)
    (hc : ∀ {a b} (e : Cross a b), (cross e).ModelExpansive) {a b : (sum L₁ L₂ Cross cross).Idx}
    (p : Quiver.Path a b) : (sum L₁ L₂ Cross cross).PathModelExpansive p := by
  induction p with
  | nil => trivial
  | cons _ e ih => exact ⟨ih, sum_edge_modelExpansive L₁ L₂ Cross cross h₁ h₂ hc e⟩

end LogicGraph

namespace Graph

variable {H : Type} (P : Profile) (host : HostSemantics H)
  (Env : Module → Store H → List ExternAddr → Prop)

/-- **A phase-2 hook**: a new observational logic over its own interfaces, with translations
from chosen phase-1 nodes. See the module docstring for the intended component and
game-semantic instances. -/
structure Hook where
  /-- The interfaces of the new logic. -/
  J : Type
  [cat : Category.{0} J]
  /-- The new logic (models: component behaviours, or strategies). -/
  target : ObsSemantics J
  /-- Export sets as interfaces of the new logic. -/
  embed : Set String ⥤ J
  /-- The phase-1 nodes it is reached from (and by how many edges). -/
  Src : Node → Type
  /-- The translations (component wrapping; strategy of traces with adequacy as `sem_den`). -/
  tr : ∀ {a}, Src a → Translation embed (sem P host Env a) target

attribute [instance] Hook.cat

/-- The phase-1 graph extended by the logic of a hook. -/
def Hook.graph (h : Hook P host Env) : Silmaril.Inst.LogicGraph₁ :=
  LogicGraph.extend (Graph.graph P host Env) h.target.inst h.Src (fun e => (h.tr e).coHom)

/-- If the hook's translations have surjective semantic maps, every path of the extended graph
is model-expansive, so heterogeneous borrowing applies to it. -/
theorem Hook.pathModelExpansive (h : Hook P host Env)
    (hs : ∀ {a} (e : h.Src a) X, Function.Surjective ((h.tr e).sem X))
    {a b : (h.graph P host Env).Idx} (p : Quiver.Path a b) :
    (h.graph P host Env).PathModelExpansive p :=
  LogicGraph.extend_pathModelExpansive _ _ _ _ (fun e => edge_modelExpansive P host Env e)
    (fun e => (h.tr e).coHom_modelExpansive (hs e)) p

end Graph

end Silmaril.Wasm.Institution
