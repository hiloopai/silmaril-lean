module

public import Silmaril.Wasi.World.Thms
public import Silmaril.Wasi.Versions.Stateful.Defs
public import Silmaril.Wasi.Versions.P2.World.Defs
public import Silmaril.Wasi.Versions.P2OverP3.World.Defs
public import Silmaril.Wasi.Versions.P3OverP2.Impl.Defs
public import Silmaril.Games.InstGraph.Defs
public import Silmaril.Logic.Institution.Hets.StructuredSpec
public import Silmaril.Logic.Institution.Hets.DevGraph
public import Mathlib.CategoryTheory.Category.ULift

@[expose] public section

/-!
# WASI specifications as Hets structured specifications

A pilot of silmaril's Hets layer (`Silmaril.Logic.Institution.Hets`: structured
specifications, development graphs, heterogeneous specification) on the WASI institution
`WasiInst` of `Silmaril.Wasi.World`. See `docs/projects/wasm-wasi.md`, section *Hets*.

## WIT `include` is not a signature morphism of `WasiInst`

A morphism `W ⟶ W'` of `WasiInst` exists when `W'` fits `W`: fewer imports and more exports.
WIT `include` of `V` into `W` gives `W ∪ V` (`World.union`), whose imports *and* exports grow.
There is a morphism `W ⟶ W ∪ V` exactly when `V` adds no import, and `W ∪ V ⟶ W` exactly when
`V` adds no export (`Silmaril.Wasi.Spec.Thms`). So `include` is a morphism only in degenerate cases:
a component of `W ∪ V` may call `V`'s imports, so it is not a component of `W`, and a component
of `W` lacks `V`'s exports.

`IWorld` is the signature category of `include`: worlds with inclusions on both sides
(`IWorld.inclLeft`, `IWorld.inclRight`). Its institution `IncInst` reads a world `W` through
`IWorld.openFun` as the world `⟨univ, W.exports⟩` with *open* imports: models are components
that may call any function, and the import discipline becomes a sentence, `callsWithin I`
(every import event names a function of `I`). `compSpec W` is the presentation "components
calling only `W`'s imports". `IncInst` is the restriction of `WasiInst` along `openFun`, so
`IncInst.toWasi` (identity corridors) is a model-expansive comorphism into `WasiInst`, and every
component of a world, reduced along `toOpen`, is a model of `compSpec`, and every model of
`compSpec W` arises so (`mem_compSpec_iff`, through `widen`, `fwd` and `pull`).

## Version theories as structured specifications

A WASI theory `T` (a protocol on the host's answers, `Silmaril.Wasi.Versions`) constrains the
host, whose imports a component leaves uninterpreted. A closed host of the functions `I` is a
component of the world `hostWorld I = ⟨∅, I⟩` that exports `I` (`Silmaril.Wasi.Host`: the dual
game), so `T` is the presentation `thSpec I T`: closed hosts whose returns, read as answers
(`retG`), satisfy `T`. Products of theories are unions (`models_thSpec_prod`), slices at fewer
functions translate along `hostIncl`, and the version specs are `p2Spec r` (0.2, reading `r`),
`p3Spec` (the 0.3 theory of `P2OverP3`) and `p3SpecC F` (the corrected 0.3 theory of
`P3OverP2`). On the component side, `agSpec W T G` is the presentation of the components of
`W` guaranteeing `G` under `T`.

`p3Dev` is a development graph over `WasiInst` (three nodes at the 0.3 host world): the 0.3
theory of `P2OverP3`, its typing slice with a global definition link into it, and the corrected
theory without reads, the target of a global theorem link (`Silmaril.Wasi.Spec.Thms`).

## A logic graph with `WasiInst` and the game institutions

`WasiInst : Inst.{0, …}` and the game institutions (`Inst.{1, …}`) differ in the universe of
signatures. `WasiInst₁` lifts the signatures with `ULift`; `wasiToGInst` is the comorphism
`WasiInst₁ → GInst` (`World.toGame` on signatures, identity corridors), and `wasiSpec` is the
`GraphSpec` with `WasiInst₁` and the game graph `GInstRef → GInst → DGInst`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Spec

open CategoryTheory Silmaril.Games Silmaril.Logic.Institution
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions (retG)

attribute [local instance] uliftCategory

/-! ## The signature category of WIT `include` -/

/-- A world, ordered by inclusion of imports and of exports (the signatures of WIT
`include`). -/
structure IWorld where
  /-- The world. -/
  world : World

namespace IWorld

/-- `W` is included in `W'`: both the imports and the exports grow. -/
def Le (W W' : IWorld) : Prop :=
  W.world.imports ⊆ W'.world.imports ∧ W.world.exports ⊆ W'.world.exports

/-- Worlds and inclusions form a (thin) category. -/
instance category : Category.{0} IWorld where
  Hom W W' := PLift (Le W W')
  id _ := ⟨⟨subset_rfl, subset_rfl⟩⟩
  comp f g := ⟨⟨f.down.1.trans g.down.1, f.down.2.trans g.down.2⟩⟩

/-- WIT `include`: `W` into `W ∪ V`. -/
def inclLeft (W V : World) : (⟨W⟩ : IWorld) ⟶ ⟨W.union V⟩ :=
  ⟨⟨Set.subset_union_left, Set.subset_union_left⟩⟩

/-- WIT `include`: `V` into `W ∪ V`. -/
def inclRight (W V : World) : (⟨V⟩ : IWorld) ⟶ ⟨W.union V⟩ :=
  ⟨⟨Set.subset_union_right, Set.subset_union_right⟩⟩

/-- The world with open imports: every function may be imported. -/
def openWorld (W : IWorld) : World := ⟨Set.univ, W.world.exports⟩

/-- Open imports turn inclusions into fittings. -/
def openFun : IWorld ⥤ World where
  obj := openWorld
  map f := ⟨⟨subset_rfl, f.down.2⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

end IWorld

/-- **The institution of WIT `include`**: worlds with inclusions on both sides; models are
components with open imports, sentences those of `WasiInst` at the open world. -/
def IncInst : Inst.{0, 0, 0, 0, 0} := ⟨IWorld, IWorld.openFun ⋙ WasiInst.I⟩

/-- `IncInst` maps into `WasiInst` by identity corridors. -/
def IncInst.toWasi : Inst.CoHom IncInst WasiInst := ⟨IWorld.openFun, 𝟙 _⟩

/-- A world fits its open form: every component of `W` is a component with open imports. -/
def toOpen (W : World) : IWorld.openWorld ⟨W⟩ ⟶ W := ⟨⟨Set.subset_univ _, subset_rfl⟩⟩

/-- The import function a WASI event names (a request or an answer). -/
def callee : WEv → Option FnName
  | .req f _ => some f
  | .imp f _ _ => some f
  | _ => none

/-- Every import event names a function of `I`. -/
def CallsWithin (I : Set FnName) (t : List WEv) : Prop := ∀ e ∈ t, ∀ f ∈ callee e, f ∈ I

/-- The sentence: a component calls only functions of `I`. -/
def callsWithin {I' X : Set FnName} (I : Set FnName) : GSen (nsig I') (nsig X) :=
  guar (CallsWithin I)

/-- **The components of `W` in `IncInst`**: components with open imports that call only `W`'s
imports. -/
def compSpec (W : IWorld) : StrSpec IncInst.I W :=
  .basic W {(callsWithin W.world.imports : GSen (nsig Set.univ) (nsig W.world.exports))}

/-! ## Components with wider imports -/

/-- The world morphism that widens the imports from `I` to `I'` (exports `X` unchanged). -/
def widen {I I' : Set FnName} (h : I ⊆ I') (X : Set FnName) : (⟨I', X⟩ : World) ⟶ ⟨I, X⟩ :=
  ⟨⟨h, subset_rfl⟩⟩

/-- A move of a component of the imports `I`, seen with the imports `I'`. -/
def fwd {I I' X : Set FnName} (h : I ⊆ I') : Move (nsig I) (nsig X) → Move (nsig I') (nsig X)
  | .inl (.ask m) => .inl (.ask ((nsigHom h).op m))
  | .inl (.ans m n) => .inl (.ans ((nsigHom h).op m) n)
  | .inr e => .inr e

/-- A position of a component of the imports `I`, seen with the imports `I'`. -/
def posFwd {I I' X : Set FnName} (h : I ⊆ I') : Pos (nsig I) (nsig X) → Pos (nsig I') (nsig X)
  | .idle => .idle
  | .run q => .run q
  | .wait q m => .wait q ((nsigHom h).op m)

/-! ## Version theories as structured specifications -/

/-- Structured specifications over `WasiInst`. -/
abbrev WSpec (W : World) : Type := StrSpec WasiInst.I W

/-- The world of a closed host of the functions `I`: no imports, exports `I`. -/
def hostWorld (I : Set FnName) : World := ⟨∅, I⟩

/-- Host worlds grow with their functions. -/
def hostIncl {I I' : Set FnName} (h : I ⊆ I') : hostWorld I ⟶ hostWorld I' := ⟨⟨subset_rfl, h⟩⟩

/-- The sentence of a WASI theory on a closed host: its returns, read as answers, satisfy
`T`. -/
def thSen {SG : Type} (I : Set FnName) (T : Protocol SG WEv) :
    GSen (nsig (∅ : Set FnName)) (nsig I) :=
  guar (retG T).Accepts

/-- **A WASI theory as a presentation**: the closed hosts of `I` satisfying `T`. -/
def thSpec {SG : Type} (I : Set FnName) (T : Protocol SG WEv) : WSpec (hostWorld I) :=
  .basic (hostWorld I) {thSen I T}

/-- The components of `W` that guarantee `G` under the host theory `T`. -/
def agSpec {SG SG' : Type} (W : World) (T : Protocol SG WEv) (G : Protocol SG' WEv) : WSpec W :=
  .basic W {(agP T G : GSen (nsig W.imports) (nsig W.exports))}

/-- **WASI 0.2** (`P2.p2Th r`) over the functions of `P2.p2Command`. -/
def p2Spec (r : Versions.P2.Reading) : WSpec (hostWorld Versions.P2.p2Command.imports) :=
  thSpec _ (Versions.P2.p2Th r)

/-- **WASI 0.3** (the theory of `P2OverP3`: typing, clock, stdout) over the functions of
`P3.p3World`. -/
def p3Spec : WSpec (hostWorld Versions.P3.p3World.imports) := thSpec _ Versions.P2OverP3.p3Th

/-- **The corrected WASI 0.3 theory** of `P3OverP2`, with file contents `F`. -/
def p3SpecC (F : BitVec 32 → List (BitVec 8)) : WSpec (hostWorld Versions.P3.p3World.imports) :=
  thSpec _ (Versions.P3OverP2.p3Th F)

/-! ## A development graph of the 0.3 theories -/

/-- The nodes: the 0.3 theory of `P2OverP3`, its typing slice, and the corrected theory
without reads. -/
inductive P3Node : Type
  | orig
  | typed
  | corr
  deriving DecidableEq

/-- The host world of the 0.3 functions. -/
abbrev p3HW : World := hostWorld Versions.P3.p3World.imports

/-- The local axioms of a node. -/
def p3Axioms : P3Node → Set (GSen (nsig (∅ : Set FnName)) (nsig Versions.P3.p3World.imports))
  | .orig => {thSen _ Versions.P2OverP3.p3Th}
  | .typed => {thSen _ Versions.P3.typed3}
  | .corr => {thSen _ Versions.P3.typed3, thSen _ Versions.P3OverP2.clockTh3s,
      thSen _ Versions.P3OverP2.stdoutTh3w}

/-- The global definition links: the typing slice into the theory. -/
def p3Global : P3Node → P3Node → Set (p3HW ⟶ p3HW)
  | .typed, .orig => Set.univ
  | _, _ => ∅

/-- The rank of a node: links go up. -/
def p3Rank : P3Node → Nat
  | .orig => 1
  | _ => 0

/-- **The development graph of the 0.3 theories.** -/
def p3Dev : DevGraph.{0} WasiInst.I where
  Node := P3Node
  sig _ := p3HW
  axioms := p3Axioms
  globalDef := p3Global
  localDef _ _ := ∅
  hidingDef _ _ := ∅
  wf := Subrelation.wf (r := InvImage (· < ·) p3Rank)
    (fun {M N} h => by
      rcases h with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
      · cases M <;> cases N <;>
          first | exact absurd h (Set.notMem_empty _) | exact Nat.zero_lt_one
      · exact absurd h (Set.notMem_empty _)
      · exact absurd h (Set.notMem_empty _))
    (InvImage.wf p3Rank wellFounded_lt)

/-! ## `WasiInst` in a logic graph with the game institutions -/

/-- `WasiInst` with its signatures lifted to `Type 1`, the shape of the game institutions. -/
def WasiInst₁ : Inst.{1, 0, 0, 0, 0} := ⟨ULift.{1} World, ULift.downFunctor ⋙ WasiInst.I⟩

/-- **`WasiInst` into `GInst`**: worlds as games, identity corridors. -/
def wasiToGInst : Inst.CoHom WasiInst₁ GInst := ⟨ULift.downFunctor ⋙ World.toGame, 𝟙 _⟩

/-- The institution of a node: `WasiInst₁` (`none`) or a node of the game graph. -/
def wasiInst : Option InstGraph.Node → Silmaril.Inst.Institution₁
  | none => WasiInst₁
  | some b => InstGraph.inst b

/-- **`WasiInst` with the game graph**: `WasiInst₁ → GInst`, `GInstRef → GInst → DGInst`. -/
def wasiSpec : Silmaril.Inst.GraphSpec wasiInst where
  comors := [⟨none, some .plain, wasiToGInst⟩, ⟨some .ref, some .plain, GInstRef.toGInst⟩,
    ⟨some .plain, some .div, GInst.toDGInst⟩]

/-- The graph of `wasiSpec`. -/
abbrev wasiGraph : Silmaril.Logic.Institution.LogicGraph.{0, 0, 1, 0, 0, 0, 0} :=
  wasiSpec.toLogicGraph

end Silmaril.Wasi.Spec
