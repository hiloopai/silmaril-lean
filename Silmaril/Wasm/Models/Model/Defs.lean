module

public import Silmaril.Wasm.Models.Features.Defs
public import Silmaril.Wasm.Atlas.Defs
public import Silmaril.Games.Strategy.Defs

/-!
# Wasm models and embeddings

A **model** is syntax, validation and an observational semantics; game semantics is an optional
extension.

* `WasmModel`: the feature set it covers (informative), modules and their validity, semantic
  points, calls, observations `obs : Pt → Call → Set Obs` and the domain on which the model is
  adequate; `WasmModel.chart`: its behaviour chart (`Silmaril.Wasm.Atlas.BChart`);
* `GameModel`: a model with import/export game signatures per point, a strategy per point, a
  read-off of observations from strategies, and **adequacy** (`obs = readOff ∘ strat` on the
  domain, the M2 shape of `Silmaril.Wasm.Game`);
* `EmbDir`: what an embedding proves about observations: equal (`eq`), source ⊆ target
  (`sub`, soundness of the source) or target ⊆ source (`sup`, completeness of the source);
* `WasmModel.Emb A B`: an embedding: module map preserving validity, point and call maps landing
  in the domain, a read-back of target observations into source observations, a direction and
  the corresponding fact about `A.obs` and the read-back of `B.obs` (`WasmModel.view`);
* `Emb.Conservative`: validity is also reflected and observations are equal on the image (a
  conservative extension).

`Thms`: `Emb.toTransition` (an atlas transition, through `BTrans.ofEq`, `ofSubsetUniv` or
`ofSupsetUniv`), `Emb.toTransitionExist`, `Emb.id`, and the restricted Core models.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models

open Silmaril.Wasm.Atlas

/-- **A Wasm model**: syntax, validation and observations. -/
structure WasmModel where
  /-- The feature set the syntax covers (informative). -/
  feats : FeatureSet
  /-- Modules. -/
  Module : Type
  /-- Validity of modules. -/
  Valid : Module → Prop
  /-- Semantic points (a store and a host, or an instantiated module). -/
  Pt : Type
  /-- Calls. -/
  Call : Type
  /-- Observations. -/
  Obs : Type
  /-- The observations of a call at a point. -/
  obs : Pt → Call → Set Obs
  /-- The points on which the model is adequate. -/
  dom : Pt → Prop

namespace WasmModel

/-- The behaviour chart of a model. -/
def chart (A : WasmModel) : Chart := BChart A.Pt A.Call A.Obs A.dom A.obs

/-- The observations of `B` read back into another observation type. -/
def view (B : WasmModel) {O : Type} (rb : B.Obs → Option O) (p : B.Pt) (c : B.Call) : Set O :=
  {o | ∃ b ∈ B.obs p c, rb b = some o}

/-- The chart of `B` with observations read back along `rb`. -/
def viewChart (B : WasmModel) {O : Type} (rb : B.Obs → Option O) : Chart :=
  BChart B.Pt B.Call O B.dom (B.view rb)

end WasmModel

/-- **A game model**: a Wasm model with a strategy per point and adequacy. -/
structure GameModel extends WasmModel where
  /-- The import (lower) game signature of a point. -/
  E : Pt → Silmaril.Games.Sig.{0}
  /-- The export (upper) game signature of a point. -/
  F : Pt → Silmaril.Games.Sig.{0}
  /-- The strategy of a point. -/
  strat : (p : Pt) → Silmaril.Games.Strategy (E p) (F p)
  /-- How observations are read off a strategy. -/
  readOff : (p : Pt) → Silmaril.Games.Strategy (E p) (F p) → Call → Set Obs
  /-- **Adequacy**: on the domain, observations are read off the strategy. -/
  adequate : ∀ p, dom p → ∀ c, obs p c = readOff p (strat p) c

/-- What an embedding proves about observations. -/
inductive EmbDir where
  /-- Equal observations. -/
  | eq
  /-- Source observations are target observations (the source is sound). -/
  | sub
  /-- Target observations are source observations (the source is complete). -/
  | sup
  deriving DecidableEq, Repr

/-- The fact an embedding direction asks for, between source observations `s` and read-back
target observations `t`. -/
def EmbDir.Holds {O : Type} : EmbDir → Set O → Set O → Prop
  | .eq, s, t => t = s
  | .sub, s, t => s ⊆ t
  | .sup, s, t => t ⊆ s

/-- **An embedding** of model `A` into model `B`. -/
structure WasmModel.Emb (A B : WasmModel) where
  /-- The module map. -/
  mod : A.Module → B.Module
  /-- Validity is preserved. -/
  valid : ∀ m, A.Valid m → B.Valid (mod m)
  /-- The point map. -/
  pt : A.Pt → B.Pt
  /-- The call map. -/
  call : A.Call → B.Call
  /-- Reading target observations back. -/
  readback : B.Obs → Option A.Obs
  /-- The domain lands in the domain. -/
  dom : ∀ p, A.dom p → B.dom (pt p)
  /-- What is proved about observations. -/
  dir : EmbDir
  /-- The fact. -/
  sat : ∀ p, A.dom p → ∀ c, dir.Holds (A.obs p c) (B.view readback (pt p) (call c))

/-- **A conservative embedding**: validity is reflected and observations are equal. -/
structure WasmModel.Emb.Conservative {A B : WasmModel} (e : A.Emb B) : Prop where
  /-- Validity is reflected. -/
  reflect : ∀ m, B.Valid (e.mod m) → A.Valid m
  /-- Observations are equal on the image. -/
  dir_eq : e.dir = .eq

end Silmaril.Wasm.Models
