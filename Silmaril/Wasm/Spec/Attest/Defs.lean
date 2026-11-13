module

public import Silmaril.Wasm.Spec.Attest.Relabel.Defs
public import Silmaril.Proofs.Wasm.Spec.Attest.Relabel
public import Silmaril.Games.Pair.Defs
public import Silmaril.Games.Composition.Defs
public import Silmaril.Logic.Institution.Room

/-!
# Positive propositional logic by "may call `attest`"

A module *attests* when, in some run, against some environment, after export calls in any
order, it calls its import `attest`. This topic reads positive propositional logic off that
property:

| formula | module |
| --- | --- |
| a variable `x` | a module `μ x` |
| `⊤` | a module whose export calls `attest` |
| `⊥` | a module that never calls `attest` |
| `φ ∨ ψ` | the two modules side by side, exports united, one `attest` |
| `φ ∧ ψ` | the two modules linked to a gate `A` that calls the real `attest` once both have called it |

and proves that the encoding of `φ` may attest exactly when `φ` holds under the valuation
"`x` holds iff `μ x` may attest" (`Silmaril.Wasm.Spec.Attest.Thms`).

## The semantic domain

Modules are read in the game semantics of `Silmaril.Games`: a module with imports `E` and
exports `F` is a strategy `σ : Strategy E F` (prefix-closed, receptive sets of plays). For a
Core 3.0 module this is `I.strategy P s` of `Silmaril.Wasm.Game.Strategy`, the plays defined by
Core `Step P` reduction at an arbitrary profile `P`, with the store hidden and persisting from
one export call to the next (`Silmaril.Wasm.Spec.Attest.Core`). These are the traces of
`wasmSem P`, the models of the specification institutions `Silmaril.Wasm.Spec`.

* `MayCall σ`: some play of `σ` contains a lower question. With `E` the single import
  `attest`, this is "may attest"; for a Core module it is the negation of the `neverCall`
  sentence (`Silmaril.Wasm.Spec.Attest.Core.Thms`, `mayCall_iff_not_neverCall`).
* `TrapProp σ stopE stopF`: after a lower question is answered with `stopE` (for Wasm: a trap),
  the pending export call returns `stopF` (a trap) at once. Core traps cannot be caught, so every
  Core module has it; the combinators preserve it. It is what lets the left conjunct give control
  back to the environment after its call of `attestL`, so that the environment can go on and
  drive the right conjunct.

## The combinators

* `relabel σ ι`: the lower operations renamed along `ι : Relabel E E'` (plays mapped).
* `orM M N`: `M.σ.pair N.σ`, the pairing of `Silmaril.Games.Pair`: each export question served by its
  own side, both sharing the import `attest`, each side keeping its state.
* `andM K M N`: `K.gate.comp ((relabel M.σ K.ι₁).pair (relabel N.σ K.ι₂))`: `M`'s `attest` is
  the gate's export `ι₁` (`attestL`), `N`'s is `ι₂` (`attestR`), and the gate, composed below,
  owns the real `attest`. Composition `Strategy.comp` hides the interaction at the gate's
  exports. The gate's own export interface is not re-exported.

**What "link" means.** The combinators are the game-semantic link: pairing and composition of
strategies. For Core modules, the statically linked module's strategy *is* this composite in the
fragments where Silmaril proves M3: `Setup.link_is_composition_profile` and
`Setup.link_is_composition_div` (silmaril-lean's `link?`, closed providers) and
`ULink.link_eq_comp` (the untyped shared-store game, with partial linking and shared state).
The theorems here do not depend on either: they hold for arbitrary strategies with the stated
properties, so they cover every module whose strategy is given, Core or composite. The untyped
game is not used as the substrate: its export questions carry the store, so the Opponent may
pass a store in which an export's code calls `attest`; "may ever call" needs the store threaded
from instantiation, which is the hidden persistent store of `I.strategy P s`.

## Kits

A `Kit E` packages a gate (with exports `G` and the two relabellings `ι₁`, `ι₂`) and the two
constant modules `tt`, `ff`. `Kit.Ok` lists what the theorems need of them: the gate is
trap-propagating, it may call its import only after both of its exports were called (`safe`),
and it does so after `ι₁` was called and answered `stop` and `ι₂` was called (`live`);
`tt` may attest, `ff` may not. The Core 3.0 kit is `Silmaril.Wasm.Spec.Attest.Core.Defs`.

## Encoding and rooms

* `PForm V`: positive formulas (variables, `⊤`, `⊥`, `∨`, `∧`); `PForm.Holds v φ`.
* `enc K μ φ`: the module of `φ` when the variables are the modules `μ x`.
* `plRoom V`: the room (sentences, models, satisfaction; `Silmaril.Logic.Institution.Room`)
  of positive logic over `V`, models the valuations `V → Prop`.
* `attRoom K stopE V`: sentences `PForm V`, models the trap-propagating module valuations
  `V → AMod E`, satisfaction `M ⊨ φ` iff `enc K M φ` may call `attest`.

The corridor `plRoom V → attRoom K stopE V` and its satisfaction condition are in
`Silmaril.Wasm.Spec.Attest.Thms`.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Spec.Attest

open Silmaril.Games CategoryTheory Silmaril.Logic.Institution

universe u

variable {E E' F F₁ F₂ G : Sig.{u}}

/-! ## Relabelling a strategy -/

/-- **The strategy relabelled along `ι`**: the images of its plays. -/
def relabel (σ : Strategy E F) (ι : Relabel E E') : Strategy E' F where
  plays := {p | ∃ q ∈ σ, p = q.map ι.move}
  nil_mem := ⟨[], σ.nil_mem, rfl⟩
  legal := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨y, hy⟩ := σ.legal hq
    exact ⟨_, Silmaril.Proofs.Wasm.Spec.Attest.path_map ι hy⟩
  of_prefix := by
    rintro s _ ⟨q, hq, rfl⟩ hs
    obtain ⟨q', hq', rfl⟩ := Silmaril.Proofs.Wasm.Spec.Attest.prefix_map _ hs
    exact ⟨q', σ.of_prefix hq hq', rfl⟩
  receptive := by
    rintro _ x y o ⟨q, hq, rfl⟩ hx hxy ho
    obtain ⟨x₀, hx₀⟩ := σ.legal hq
    have hxeq : ι.pos x₀ = x := Path.det (Silmaril.Proofs.Wasm.Spec.Attest.path_map ι hx₀) hx
    obtain ⟨o₀, y₀, hst, ho₀, rfl⟩ := Silmaril.Proofs.Wasm.Spec.Attest.receptive_map ι hxeq hxy ho
    exact ⟨q ++ [o₀], σ.receptive hq hx₀ hst ho₀, by simp⟩

/-! ## May call, trap propagation -/

/-- **`σ` may call its import**: some play contains a lower question. -/
def MayCall (σ : Strategy E F) : Prop := ∃ p ∈ σ, ∃ m : E.Op, (.inl (.ask m) : Move E F) ∈ p

/-- **Trap propagation**: whenever the strategy waits for the answer to its call `m` while
answering `q`, the answer `stopE m` makes it answer `q` with `stopF q` at once. -/
def TrapProp (σ : Strategy E F) (stopE : ∀ m : E.Op, E.Ar m) (stopF : ∀ q : F.Op, F.Ar q) :
    Prop :=
  ∀ (p : List (Move E F)) (q : F.Op) (m : E.Op), p ∈ σ → Path .idle p (.wait q m) →
    p ++ [.inl (.ans m (stopE m)), .inr (.ans q (stopF q))] ∈ σ

/-! ## Modules over a fixed import -/

/-- A module importing `E`: its exports, the answer it gives when trapping, and its strategy. -/
structure AMod (E : Sig.{u}) where
  /-- The exports. -/
  F : Sig.{u}
  /-- The trap answer of each export. -/
  stop : ∀ q : F.Op, F.Ar q
  /-- The strategy. -/
  σ : Strategy E F

/-- The trap answers of two modules side by side. -/
def sumStop {F₁ F₂ : Sig.{u}} (s₁ : ∀ q : F₁.Op, F₁.Ar q) (s₂ : ∀ q : F₂.Op, F₂.Ar q) :
    ∀ q : (F₁ ⊕ₛ F₂).Op, (F₁ ⊕ₛ F₂).Ar q
  | .inl q => s₁ q
  | .inr q => s₂ q

/-- **Disjunction**: the two modules side by side (pairing), sharing the import. -/
def orM (M N : AMod E) : AMod E := ⟨M.F ⊕ₛ N.F, sumStop M.stop N.stop, M.σ.pair N.σ⟩

/-- A gate and the two constant modules. -/
structure Kit (E : Sig.{u}) where
  /-- The gate's exports. -/
  G : Sig.{u}
  /-- The gate's trap answers. -/
  stopG : ∀ g : G.Op, G.Ar g
  /-- The gate: a provider of `G` that imports `E`. -/
  gate : Strategy E G
  /-- The left conjunct's import as a gate export (`attestL`). -/
  ι₁ : Relabel E G
  /-- The right conjunct's import as a gate export (`attestR`). -/
  ι₂ : Relabel E G
  /-- A module that may attest. -/
  tt : AMod E
  /-- A module that never attests. -/
  ff : AMod E

/-- **Conjunction**: `M`'s import resolved to the gate's `ι₁`, `N`'s to `ι₂`, the gate below. -/
def andM (K : Kit E) (M N : AMod E) : AMod E :=
  ⟨M.F ⊕ₛ N.F, sumStop M.stop N.stop, K.gate.comp ((relabel M.σ K.ι₁).pair (relabel N.σ K.ι₂))⟩

/-- **What the theorems need of a kit.** -/
structure Kit.Ok (K : Kit E) (stopE : ∀ m : E.Op, E.Ar m) : Prop where
  /-- The gate propagates traps. -/
  gate_tp : TrapProp K.gate stopE K.stopG
  /-- A trap of `ι₁` is a trap of the left conjunct's import. -/
  stop₁ : ∀ m, K.ι₁.ar m (K.stopG (K.ι₁.op m)) = stopE m
  /-- A trap of `ι₂` is a trap of the right conjunct's import. -/
  stop₂ : ∀ m, K.ι₂.ar m (K.stopG (K.ι₂.op m)) = stopE m
  /-- The two exports are different. -/
  disjoint : ∀ a b, K.ι₁.op a ≠ K.ι₂.op b
  /-- **Safety**: the gate calls its import only in plays where both exports were called. -/
  safe : ∀ s ∈ K.gate, (∃ m : E.Op, (.inl (.ask m) : Move E K.G) ∈ s) →
    (∃ a, (.inr (.ask (K.ι₁.op a)) : Move E K.G) ∈ s) ∧ (∃ a, (.inr (.ask (K.ι₂.op a)) : Move E K.G) ∈ s)
  /-- **Liveness**: `ι₁` called and trapped, then `ι₂` called, may call the import. -/
  live : ∀ a₁ a₂, ∃ m : E.Op, [.inr (.ask (K.ι₁.op a₁)),
    .inr (.ans (K.ι₁.op a₁) (K.stopG (K.ι₁.op a₁))), .inr (.ask (K.ι₂.op a₂)), .inl (.ask m)] ∈
      K.gate
  /-- `tt` may attest. -/
  tt_may : MayCall K.tt.σ
  /-- `ff` never attests. -/
  ff_not : ¬ MayCall K.ff.σ
  /-- `tt` propagates traps. -/
  tt_tp : TrapProp K.tt.σ stopE K.tt.stop
  /-- `ff` propagates traps. -/
  ff_tp : TrapProp K.ff.σ stopE K.ff.stop

/-! ## Positive formulas -/

/-- Positive propositional formulas over the variables `V`. -/
inductive PForm (V : Type u) where
  /-- A variable. -/
  | var (x : V)
  /-- Truth. -/
  | tt
  /-- Falsity. -/
  | ff
  /-- Disjunction. -/
  | or (φ ψ : PForm V)
  /-- Conjunction. -/
  | and (φ ψ : PForm V)

namespace PForm

variable {V W : Type u}

/-- Truth under a valuation. -/
def Holds (v : V → Prop) : PForm V → Prop
  | .var x => v x
  | .tt => True
  | .ff => False
  | .or φ ψ => Holds v φ ∨ Holds v ψ
  | .and φ ψ => Holds v φ ∧ Holds v ψ

/-- Renaming variables (the sentence translation along a signature morphism `V → W`). -/
def rename (f : V → W) : PForm V → PForm W
  | .var x => .var (f x)
  | .tt => .tt
  | .ff => .ff
  | .or φ ψ => .or (rename f φ) (rename f ψ)
  | .and φ ψ => .and (rename f φ) (rename f ψ)

end PForm

/-- **The encoding**: the module of `φ` when each variable `x` is the module `μ x`. -/
def enc {V : Type u} (K : Kit E) (μ : V → AMod E) : PForm V → AMod E
  | .var x => μ x
  | .tt => K.tt
  | .ff => K.ff
  | .or φ ψ => orM (enc K μ φ) (enc K μ ψ)
  | .and φ ψ => andM K (enc K μ φ) (enc K μ ψ)

/-- The valuation read off module valuations: `x` holds iff `μ x` may attest. -/
def valOf {V : Type u} (μ : V → AMod E) : V → Prop := fun x => MayCall (μ x).σ

/-! ## Rooms -/

/-- A type with equalities as morphisms (discrete category). -/
def Disc (α : Type 1) : Type 1 := α

instance (α : Type 1) : Category.{0} (Disc α) where
  Hom a b := PLift (a = b)
  id _ := ⟨rfl⟩
  comp f g := ⟨f.down.trans g.down⟩

/-- **The room of positive logic over `V`**: models are valuations. -/
def plRoom (V : Type) : Room.{0, 0, 1} where
  Sen := PForm V
  Mod := Cat.of (Disc (ULift.{1} (V → Prop)))
  Sat v φ := φ.Holds (ULift.down (α := V → Prop) v)

/-- Trap-propagating module valuations. -/
def TPVal {E : Sig.{0}} (stopE : ∀ m : E.Op, E.Ar m) (V : Type) : Type 1 :=
  {μ : V → AMod E // ∀ x, TrapProp (μ x).σ stopE (μ x).stop}

/-- **The room of attesting modules over `V`**: the models are trap-propagating module
valuations, and `μ ⊨ φ` iff the encoding of `φ` may call `attest`. -/
def attRoom {E : Sig.{0}} (K : Kit E) (stopE : ∀ m : E.Op, E.Ar m) (V : Type) : Room.{0, 0, 1} where
  Sen := PForm V
  Mod := Cat.of (Disc (TPVal stopE V))
  Sat μ φ := MayCall (enc K (Subtype.val (p := fun μ : V → AMod E =>
    ∀ x, TrapProp (μ x).σ stopE (μ x).stop) μ) φ).σ

end Silmaril.Wasm.Spec.Attest
