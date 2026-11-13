module

public import Silmaril.Project.Defs
public import Silmaril.Wasi.Host.Defs
public import Silmaril.Wasi.Component.Defs
public import Silmaril.Wasm.Wit.Project.Ext.Defs
public import Silmaril.Wasm.Wit.Project.Valid.Defs
public import Silmaril.Wasm.Wit.Project.IR.Defs

/-!
# Standard problem shapes: WebAssembly components

The shapes a registry of Wasm components (packages `namespace:name@version`, each release a
content digest) states about its releases. A release is a value `X : Value V` of a component
format; a row of a shape on the decoded component is `X.Satisfies (fun c => …)`, as for
`silmaril.shapes.wasm.*`. The semantic shapes take a **model** of a WASI world
(`Silmaril.Wasi.World.Model W`, a strategy with uninterpreted imports): an IR component gives one
by `Silmaril.Wasi.Layout.compModel C L c` (core semantics `C`, names `L`), a hand-written WASI
body by `Silmaril.Wasi.ofBody`.

| name | Lean | statement |
|---|---|---|
| `silmaril.shapes.component.valid` | `CompValid (c : Ast)` | the binary component is well scoped (`wellScopedC`) |
| `silmaril.shapes.component.has_world` | `HasWorld (c : Ast) (W : WorldType)` | its WIT projection (`projectX`) is `W`, up to the WAT normal form of names |
| `silmaril.shapes.component.has_ir_world` | `HasIRWorld (c : Comp M) (W : IRWorld)` | the IR component imports and exports the functions of `W` |
| `silmaril.shapes.component.wasi_sat` | `WasiSat (σ : W.Model) T G` | under the WASI theory `T` on the host's answers, every play satisfies the guarantee `G` (`agP T G`) |
| `silmaril.shapes.component.wasi_every_host` | `WasiEveryHost (σ : W.Model) T G` | linked over **every** host satisfying `T` (any lower interface), the export events satisfy `G` |
| `silmaril.shapes.component.refines` | `Refines (impl spec : W.Model)` | every play of `impl` is a play of `spec` (`impl ≤ spec`) |
| `silmaril.shapes.component.upgrade_compatible` | `UpgradeCompatible (f : W₁ ⟶ W₂) (v₂ : W₂.Model) (v₁ : W₁.Model)` | `W₂` fits `W₁` (fewer imports, more exports) and `v₂`, used at `W₁`, refines `v₁` |
| `silmaril.shapes.component.behaviour_eq` | `BehaviourEq (σ τ : W.Model)` | the two models have the same plays |
| `silmaril.shapes.component.digest_behaviour_eq` | `DigestBehaviourEq (den : V → W.Model) (X Y : Value V)` | both releases decode, to components with one denotation |

`CompValid` is the part of validation the library checks on the binary AST: index scoping (no
validator of the full component-model rules exists here, `Silmaril.Wasm.Wit.Project.Valid`).
`WasiSat` is the sentence with uninterpreted imports; `WasiEveryHost` is its consequence for
the linked system (`WasiSat.everyHost`, `Silmaril.Wasi.link_satP`), stated for the client's view.
All these properties of models are **safety** properties, so they are inherited along
refinement (`Silmaril.Project.Shapes.Component.Thms`).

**Digests.** A release's digest (SHA-256 in the wa.dev/OCI registries, the CID in
`silmaril/artifacts.toml`) names its bytes; Lean sees the bytes. Two values with one digest
have the same bytes (up to a hash collision, outside the logic), and
`DigestBehaviourEq.of_bytes_eq` makes them behaviourally equal under every denotation once one
of them decodes. Equal behaviour at *different* digests is the interesting case (the same
source, rebuilt; an optimised build), stated by the same shape.

Open shapes, not defined here: *implements WASI version A via B* (from the WASI-versions work)
and *a WAC composition has world W* (once WAC is on main).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.Component

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component.Binary (Ast)
open Silmaril.Wasm.Wit.Project (WorldType IRWorld compWorld projectX wellScopedC)
open Silmaril.Wasm.Resource (Protocol)

/-- **The binary component `c` is well scoped**: every index it uses is bound before (the part
of validation the library checks, `Silmaril.Wasm.Wit.Project.wellScopedC`). -/
@[problem "silmaril.shapes.component.valid"
  (title := "A Wasm component is valid (index scoping)")]
def CompValid (c : Ast) : Prop := wellScopedC c = true

/-- **The binary component `c` has the world `W`**: its WIT projection is `W`, up to the WAT
normal form of names. -/
@[problem "silmaril.shapes.component.has_world"
  (title := "A Wasm component has a given WIT world")]
def HasWorld (c : Ast) (W : WorldType) : Prop :=
  ∃ w, projectX c = some w ∧
    Silmaril.Wasm.Component.Wat.normComponentDecls w = Silmaril.Wasm.Component.Wat.normComponentDecls W

/-- **The IR component `c` has the function world `W`.** -/
@[problem "silmaril.shapes.component.has_ir_world"
  (title := "A component of the IR imports and exports given functions")]
def HasIRWorld {M : Type} (c : Silmaril.Wasm.Component.Comp M) (W : IRWorld) : Prop :=
  compWorld c = W

/-- **The component satisfies the WASI theory `T`**: with uninterpreted imports, every play
whose host answers satisfy `T` satisfies the guarantee `G`. -/
@[problem "silmaril.shapes.component.wasi_sat"
  (title := "A WASI component meets a guarantee under a WASI theory")]
def WasiSat {W : World} {S S' : Type} (σ : W.Model) (T : Protocol S WEv) (G : Protocol S' WEv) :
    Prop :=
  (agP T G).holds σ

/-- **For every host satisfying `T`**: linked over any host `η` (any lower interface `Y`) whose
answers satisfy `T`, the export events of every play satisfy `G`. -/
@[problem "silmaril.shapes.component.wasi_every_host"
  (title := "A WASI component meets a guarantee over every host of a theory")]
def WasiEveryHost {W : World} {S S' : Type} (σ : W.Model) (T : Protocol S WEv)
    (G : Protocol S' WEv) : Prop :=
  ∀ (Y : Sig.{0}) (η : Host Y W.imports), (hostSat T.Accepts).holds η →
    ∀ p ∈ link η σ, G.Accepts (xtrace p)

/-- **`impl` refines `spec`**: every play of `impl` is one of `spec`. -/
@[problem "silmaril.shapes.component.refines"
  (title := "A WASI component refines a specification")]
def Refines {W : World} (impl spec : W.Model) : Prop := impl ≤ spec

/-- **`v₂` is an upgrade-compatible successor of `v₁`**: `v₂`'s world fits `v₁`'s along `f`
(no more imports, at least the exports) and `v₂`, used at `v₁`'s world (`Game.reduct`),
refines `v₁`. -/
@[problem "silmaril.shapes.component.upgrade_compatible"
  (title := "A component release is upgrade-compatible with an earlier one")]
def UpgradeCompatible {W₁ W₂ : World} (f : W₁ ⟶ W₂) (v₂ : W₂.Model) (v₁ : W₁.Model) : Prop :=
  Game.reduct (World.toGame.map f) v₂ ≤ v₁

/-- **Behavioural equality**: the two models have the same plays. -/
@[problem "silmaril.shapes.component.behaviour_eq"
  (title := "Two WASI components behave the same")]
def BehaviourEq {W : World} (σ τ : W.Model) : Prop := σ = τ

/-- **Behavioural equality of two releases** under the denotation `den`: both decode, to
components with the same denotation. -/
@[problem "silmaril.shapes.component.digest_behaviour_eq"
  (title := "Two component releases behave the same")]
def DigestBehaviourEq {V : Type} {W : World} (den : V → W.Model) (X Y : Value V) : Prop :=
  ∃ a b, X.parse = some a ∧ Y.parse = some b ∧ den a = den b

/-- The loosest model of the contract `agP T G`: the strategy generated by the plays that meet
the guarantee when the host meets the theory. A model satisfying the contract refines it
(`Refines.of_wasiSat`). -/
def agSpec {W : World} {S S' : Type} (T : Protocol S WEv) (G : Protocol S' WEv) : W.Model :=
  Strategy.generate {s | T.Accepts (hostView (wtrace s)) → G.Accepts (wtrace s)}

end Silmaril.Project.Shapes.Component

end
