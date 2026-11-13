module

public import Silmaril.Wasm.Institution.Session.Thms
public import Silmaril.Wasm.Institution.Entry.Thms
public import Silmaril.Logic.Institution.Hets.LogicGraph
public import Silmaril.Wasm.Institution.Api.Defs

@[expose] public section

/-!
# The Wasm logic graph (phase 1)

A Hets logic graph (`Silmaril.Logic.Institution.LogicGraph`) whose nodes are the Wasm
observational logics and whose edges are the translations between them. Parameters: a profile
`P`, a host semantics `host` and, for the single-invocation family, an instantiation
environment `Env`.

**Nodes** `⟨family, lang, notion⟩` (12 logics):

* `family`: `session` (export sessions sharing a store: `ExportRefines`/`ExportEquiv`) or
  `entry` (single invocations: `Equiv.ModuleRefines`/`ModuleEquiv` of `moduleEntryPoints`);
* `lang`: `core` (Core 3.0 modules) or `bir` (Binaryen IR modules, meaning their lowering);
* `notion`: `equiv` (equivalence under `Eq`), `refEq` (refinement under `Eq`) or `refTrapsUB`
  (refinement under `TrapsUB`, Binaryen's `trapsNeverHappen`).

**Comorphism edges** (`Edge`; all over the identity interface functor, all model-expansive):

* `lower f n : ⟨f, bir, n⟩ → ⟨f, core, n⟩` and `lift f n : ⟨f, core, n⟩ → ⟨f, bir, n⟩`;
* `equivRef f l : ⟨f, l, equiv⟩ → ⟨f, l, refEq⟩` (`t ≈ u ↦ t ≐ u`);
* `close f l : ⟨f, l, refTrapsUB⟩ → ⟨f, l, refEq⟩` (`t ⊑ u ↦ t ⊑ close TrapsUB u`).

**Morphism edges** (`Proj`): the same corridors as `close` and `equivRef`, read as institution
morphisms `⟨f, l, refEq⟩ → ⟨f, l, refTrapsUB⟩` and `⟨f, l, refEq⟩ → ⟨f, l, equiv⟩`: the
`Eq`-refinement logic projects onto the coarser notions.

Because every edge is model-expansive, every path is (`pathModelExpansive`), and consequence in
the Grothendieck institution of the graph is borrowed along any path (`entails_path_iff`).
-/

namespace Silmaril.Wasm.Institution.Graph

open CategoryTheory Silmaril.Logic.Institution Silmaril.Wasm Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics ObsSemantics

/-- Observation families. -/
inductive Family where
  /-- Export sessions sharing a store (`ExportRefines`). -/
  | session
  /-- Single invocations (`Equiv.ModuleRefines` of `moduleEntryPoints`). -/
  | entry
  deriving DecidableEq

/-- Program representations. -/
inductive Lang where
  /-- Core 3.0 modules. -/
  | core
  /-- Binaryen IR modules. -/
  | bir
  deriving DecidableEq

/-- Notions of equivalence and refinement. -/
inductive Notion where
  /-- Equivalence under `Eq`. -/
  | equiv
  /-- Refinement under `Eq`. -/
  | refEq
  /-- Refinement under `TrapsUB` (`trapsNeverHappen`). -/
  | refTrapsUB
  deriving DecidableEq

/-- A node of the graph. -/
structure Node where
  family : Family
  lang : Lang
  notion : Notion
  deriving DecidableEq

/-- The programs of a representation. -/
def Lang.Prog : Lang → Type
  | .core => Module
  | .bir => BModule

variable {H : Type} (P : Profile) (host : HostSemantics H)
  (Env : Module → Store H → List ExternAddr → Prop)

/-- Session denotations of a representation. -/
def sessionDen : (l : Lang) → ∀ X : Session.Iface, l.Prog → Session.Obj H X
  | .core => Session.den P host
  | .bir => fun X m => Session.den P host X (BModule.lower m)

/-- Session refinement relations of a notion. -/
def sessionLe : Notion → ∀ X : Session.Iface, Session.Obj H X → Session.Obj H X → Prop
  | .equiv => fun _ => Session.Equiv (· = ·)
  | .refEq => fun _ => Session.Refines (· = ·)
  | .refTrapsUB => fun _ => Session.Refines TrapsUB

/-- Entry points of a representation. -/
def entryE : (l : Lang) → Equiv.EntryPoints l.Prog String Val
  | .core => moduleEntryPoints P host Env
  | .bir => entryPoints P host Env

/-- Entry refinement relations of a notion. -/
def entryLe : Notion → ∀ X : Set String, Entry.Obj String Val X → Entry.Obj String Val X → Prop
  | .equiv => fun _ => Entry.Equiv (· = ·)
  | .refEq => fun _ => Entry.Refines (· = ·)
  | .refTrapsUB => fun _ => Entry.Refines TrapsUB

/-- The observational semantics of a node. -/
def sem : Node → ObsSemantics (Set String)
  | ⟨.session, l, n⟩ => Session.mk l.Prog (sessionDen P host l) (sessionLe n)
  | ⟨.entry, l, n⟩ => Entry.mk (entryE P host Env l) (entryLe n)

/-- Comorphism edges. -/
inductive Edge : Node → Node → Type where
  /-- Lowering Binaryen IR to Core. -/
  | lower (f : Family) (n : Notion) : Edge ⟨f, .bir, n⟩ ⟨f, .core, n⟩
  /-- Lifting Core into Binaryen IR. -/
  | lift (f : Family) (n : Notion) : Edge ⟨f, .core, n⟩ ⟨f, .bir, n⟩
  /-- Equivalence into `Eq`-refinement. -/
  | equivRef (f : Family) (l : Lang) : Edge ⟨f, l, .equiv⟩ ⟨f, l, .refEq⟩
  /-- `TrapsUB`-refinement into `Eq`-refinement, via the closure. -/
  | close (f : Family) (l : Lang) : Edge ⟨f, l, .refTrapsUB⟩ ⟨f, l, .refEq⟩

/-- Morphism (projection) edges. -/
inductive Proj : Node → Node → Type where
  /-- `Eq`-refinement projects onto `TrapsUB`-refinement. -/
  | trapsUB (f : Family) (l : Lang) : Proj ⟨f, l, .refEq⟩ ⟨f, l, .refTrapsUB⟩
  /-- `Eq`-refinement projects onto `Eq`-equivalence. -/
  | equiv (f : Family) (l : Lang) : Proj ⟨f, l, .refEq⟩ ⟨f, l, .equiv⟩

/-- Lifting for the entry family: lowering a lifted module gives the module back. -/
def entryLiftT (n : Notion) :
    Translation (𝟭 (Set String)) (sem P host Env ⟨.entry, .core, n⟩)
      (sem P host Env ⟨.entry, .bir, n⟩) :=
  Entry.progT (moduleEntryPoints P host Env) (entryPoints P host Env) BModule.lift
    (fun X m => by
      show Entry.den (moduleEntryPoints P host Env) X (BModule.lift m).lower = _
      rw [lower_lift])
    (entryLe n)

/-- The translation of an edge. -/
def edgeT : {a b : Node} → Edge a b →
    Translation (𝟭 (Set String)) (sem P host Env a) (sem P host Env b)
  | _, _, .lower .session n => Session.lowerT P host (sessionLe n)
  | _, _, .lower .entry n => Entry.comapT (moduleEntryPoints P host Env) BModule.lower (entryLe n)
  | _, _, .lift .session n => Session.liftT P host (sessionLe n)
  | _, _, .lift .entry n => entryLiftT P host Env n
  | _, _, .equivRef .session l => Session.equivT (sessionDen P host l)
  | _, _, .equivRef .entry l => Entry.equivT (entryE P host Env l)
  | _, _, .close .session l => Session.closeT (sessionDen P host l) TrapsUB
  | _, _, .close .entry l => Entry.closeT (entryE P host Env l) TrapsUB

/-- Every edge has identity semantic maps, hence surjective ones. -/
theorem edgeT_surjective : ∀ {a b : Node} (e : Edge a b) (X : Set String),
    Function.Surjective ((edgeT P host Env e).sem X)
  | _, _, .lower .session _, _ => fun a => ⟨a, rfl⟩
  | _, _, .lower .entry _, _ => fun a => ⟨a, rfl⟩
  | _, _, .lift .session _, _ => fun a => ⟨a, rfl⟩
  | _, _, .lift .entry _, _ => fun a => ⟨a, rfl⟩
  | _, _, .equivRef .session _, _ => fun a => ⟨a, rfl⟩
  | _, _, .equivRef .entry _, _ => fun a => ⟨a, rfl⟩
  | _, _, .close .session _, _ => fun a => ⟨a, rfl⟩
  | _, _, .close .entry _, _ => fun a => ⟨a, rfl⟩

/-- The institution morphism of a projection edge. -/
def projHom : {a b : Node} → Proj a b → Inst.Hom (sem P host Env a).inst (sem P host Env b).inst
  | _, _, .trapsUB f l => (edgeT P host Env (.close f l)).toHom
  | _, _, .equiv f l => (edgeT P host Env (.equivRef f l)).toHom

/-- **The phase-1 Wasm logic graph.** -/
def graph : Silmaril.Inst.LogicGraph₁ where
  Logics := Node
  inst a := (sem P host Env a).inst
  Comor := Edge
  comor e := (edgeT P host Env e).coHom
  Mor := Proj
  mor e := projHom P host Env e

/-- Every comorphism edge is model-expansive. -/
theorem edge_modelExpansive {a b : Node} (e : Edge a b) :
    ((graph P host Env).comor e).ModelExpansive :=
  (edgeT P host Env e).coHom_modelExpansive (edgeT_surjective P host Env e)

/-- Every projection edge is a sound institution morphism. -/
theorem proj_sound {a b : Node} (e : Proj a b) : ((graph P host Env).mor e).Sound := by
  cases e with
  | trapsUB f l =>
    exact (edgeT P host Env (.close f l)).toHom_sound (edgeT_surjective P host Env _)
  | equiv f l =>
    exact (edgeT P host Env (.equivRef f l)).toHom_sound (edgeT_surjective P host Env _)

/-- Every path of the graph is model-expansive. -/
theorem pathModelExpansive : ∀ {a b : (graph P host Env).Idx} (p : Quiver.Path a b),
    (graph P host Env).PathModelExpansive p
  | _, _, .nil => trivial
  | _, _, .cons p e => ⟨pathModelExpansive p, edge_modelExpansive P host Env e⟩

/-- **Heterogeneous borrowing**: consequence in the Grothendieck institution of the Wasm logic
graph is preserved and reflected along every path of translations. -/
theorem entails_path_iff {a b : (graph P host Env).Idx} (p : Quiver.Path a b)
    (S : LogicGraph.Sign (graph P host Env) a)
    (Γ : Set (LogicGraph.FlatRoom (graph P host Env) a S).Sen)
    (φ : (LogicGraph.FlatRoom (graph P host Env) a S).Sen) :
    (LogicGraph.FlatRoom (graph P host Env) a S).Entails Γ φ ↔
      (LogicGraph.FlatRoom (graph P host Env) b
          (LogicGraph.pathSig (graph P host Env) p S)).Entails
        (LogicGraph.pathSen (graph P host Env) p S '' Γ)
        (LogicGraph.pathSen (graph P host Env) p S φ) :=
  (graph P host Env).entails_lift_path_iff p (pathModelExpansive P host Env p) S Γ φ

/-- **Verifying a `trapsNeverHappen` refinement of Binaryen IR is verifying an `Eq`-refinement
of Core against the trap closure**: validity along `lower` then `close`. -/
theorem valid_bir_trapsUB_iff_core_eq {K : Sig (Set String)}
    (s : Sen (sem P host Env ⟨.session, .bir, .refTrapsUB⟩) K) :
    (sem P host Env ⟨.session, .bir, .refTrapsUB⟩).Valid s ↔
      (sem P host Env ⟨.session, .core, .refEq⟩).Valid
        ((edgeT P host Env (.close .session .core)).sen
          ((edgeT P host Env (.lower .session .refTrapsUB)).sen s)) :=
  ((edgeT P host Env (.lower .session .refTrapsUB)).valid_iff
      (edgeT_surjective P host Env _) s).trans
    ((edgeT P host Env (.close .session .core)).valid_iff (edgeT_surjective P host Env _) _)

end Silmaril.Wasm.Institution.Graph
