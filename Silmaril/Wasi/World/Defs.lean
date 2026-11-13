module

public import Silmaril.Games.Institution.Defs
public import Silmaril.Wasm.Component.Iface.Defs
public import Silmaril.Wasm.Resource.Protocol.Defs

@[expose] public section

/-!
# WASI worlds as signatures

WASI is specified *above* the Component Model: a WASI world (`wasi:cli/command`, …) is a WIT
world, a set of imported and exported interface functions, and a WASI proposal says what the
host's implementations of the imports do. This module makes worlds the signatures of an
institution whose models are components, read as strategies of the game semantics of
`Silmaril.Games` (the same semantic objects as the component logics of
`Silmaril.Wasm.Institution.Components`). See `docs/projects/wasm-wasi.md`.

## Names, signatures and worlds

* `FnName`: a WIT function, by interface (`wasi:clocks/monotonic-clock`) and function name
  (`now`, `[method]descriptor.write`, `[resource-drop]descriptor`). Resource methods and drops
  are functions with the canonical-ABI names.
* `nsig N`: the game signature of a set `N` of functions: call `f ∈ N` with argument values
  (`Silmaril.Wasm.Component.Val`); the answer is the result values, or `none` for a trap. As in the
  component IR (`Silmaril.Wasm.Component.sigU`) arguments are dynamically typed; typing is part of
  the WASI *theories* (axioms on the host's answers), not of the signature.
* `World`: imported and exported functions. A morphism `W ⟶ W'` exists when `W'` *fits* `W`:
  `W'` needs no more imports (`W'.imports ⊆ W.imports`) and offers at least the exports
  (`W.exports ⊆ W'.exports`). A component of `W'` is then a component of `W`
  (`World.toGame` turns this into a lens-like game morphism). Worlds form a preorder. WIT
  `include` is *not* a morphism in general: it unions imports and exports alike, so
  `W ⟶ W ∪ V` exists only when `V` adds no import (`Silmaril.Wasi.Spec.nonempty_hom_union_iff`),
  and `Silmaril.Wasi.Spec.not_include_hom` gives worlds with no morphism either way. Its
  signature category, with inclusions on both sides, is `Silmaril.Wasi.Spec.IncInst`, which
  maps into `WasiInst` by a comorphism.

## The institution `WasiInst`

`WasiInst = ⟨World, World.toGame ⋙ GInst.institution⟩`: the institution of game semantics
(`Silmaril.Games.GInst`) restricted along `World.toGame`. Models at `W` are strategies
`Strategy (nsig W.imports) (nsig W.exports)`: the imports are **uninterpreted** (a strategy is
receptive: it accepts every answer of the environment). Sentences are properties of
strategies; the satisfaction condition is that of `GInst` (`WasiInst.sat_map_iff`).

## Named traces and assume–guarantee sentences

* `WEv`: a WASI event: an import request `req f args`, an import answer `imp f args res`, an
  export call `call f args` and its return `ret f args res`. `wev` reads a move as an event,
  `wtrace` a play as a list of events. Theories are stated over `WEv`, independently of worlds.
* `hostView` (the import answers) and `expView` (the export calls and returns) are the views of
  an event list on the host's and on the client's side.
* `ag A G`: **assume–guarantee sentences**: every play whose events satisfy the assumption `A`
  (about the host's answers) satisfies the guarantee `G`. `agP T G` is the protocol form
  (`Silmaril.Wasm.Resource.Protocol`), with `T` read on the host view: a WASI theory constrains
  the otherwise uninterpreted imports.

A Silmaril addition.
-/

namespace Silmaril.Wasi

open CategoryTheory Silmaril.Games Silmaril.Logic.Institution
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-- A WIT function: an interface (`package:namespace/interface`) and a function name. -/
structure FnName where
  /-- The interface, e.g. `wasi:clocks/monotonic-clock`. -/
  iface : String
  /-- The function, e.g. `now` or `[method]descriptor.write`. -/
  fn : String
  deriving DecidableEq, Repr

/-- The game signature of a set of WIT functions: call one with argument values; the answer is
the result values, or `none` (a trap). -/
abbrev nsig (N : Set FnName) : Sig.{0} := ⟨{f // f ∈ N} × List Val, fun _ => Option (List Val)⟩

/-- The inclusion of signatures of an inclusion of function sets. -/
def nsigHom {N N' : Set FnName} (h : N ⊆ N') : Sig.Hom (nsig N) (nsig N') :=
  ⟨fun q => (⟨q.1.1, h q.1.2⟩, q.2), fun _ n => n⟩

/-- A WIT world: imported and exported functions. -/
structure World where
  /-- The imported functions (provided by the host). -/
  imports : Set FnName
  /-- The exported functions (provided by the component). -/
  exports : Set FnName

namespace World

/-- `W'` fits `W`: fewer imports, more exports. -/
def Fits (W W' : World) : Prop := W'.imports ⊆ W.imports ∧ W.exports ⊆ W'.exports

/-- Worlds and fitting form a (thin) category. -/
instance category : Category.{0} World where
  Hom W W' := PLift (Fits W W')
  id W := ⟨⟨subset_rfl, subset_rfl⟩⟩
  comp f g := ⟨⟨g.down.1.trans f.down.1, f.down.2.trans g.down.2⟩⟩

/-- The game of a world: the imports below, the exports above. -/
abbrev game (W : World) : Game.{0} := ⟨nsig W.imports, nsig W.exports⟩

/-- The models of a world: components, as strategies with uninterpreted imports. -/
abbrev Model (W : World) : Type := Strategy (nsig W.imports) (nsig W.exports)

/-- **Worlds as games**: a fitting is a lens-like game morphism. -/
def toGame : World ⥤ Game.{0} where
  obj := game
  map f := ⟨nsigHom f.down.1, nsigHom f.down.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The union of two worlds (WIT `include` of both). -/
def union (W W' : World) : World := ⟨W.imports ∪ W'.imports, W.exports ∪ W'.exports⟩

/-- A world with only imports. -/
def ofImports (I : Set FnName) (X : Set FnName := ∅) : World := ⟨I, X⟩

end World

/-- **The WASI institution**: worlds, components (strategies) and properties of them, the
game-semantics institution `GInst` restricted along `World.toGame`. -/
def WasiInst : Inst.{0, 0, 0, 0, 0} := ⟨World, World.toGame ⋙ GInst.institution⟩

/-! ## Named events -/

/-- A WASI event. -/
inductive WEv where
  /-- The component calls the import `f` with `args`. -/
  | req (f : FnName) (args : List Val)
  /-- The host answers the import call `f args` with `res` (`none`: a trap). -/
  | imp (f : FnName) (args : List Val) (res : Option (List Val))
  /-- The environment calls the export `f` with `args`. -/
  | call (f : FnName) (args : List Val)
  /-- The export call `f args` returns `res` (`none`: a trap). -/
  | ret (f : FnName) (args : List Val) (res : Option (List Val))

namespace WEv

/-- An import answer. -/
def isImp : WEv → Bool
  | imp .. => true
  | _ => false

/-- An export call or return. -/
def isExp : WEv → Bool
  | call .. | ret .. => true
  | _ => false

end WEv

/-- The event of a move of a component of the imports `I` and exports `X`. -/
def wev {I X : Set FnName} : Move (nsig I) (nsig X) → WEv
  | .inl (.ask m) => .req m.1.1 m.2
  | .inl (.ans m n) => .imp m.1.1 m.2 n
  | .inr (.ask q) => .call q.1.1 q.2
  | .inr (.ans q n) => .ret q.1.1 q.2 n

/-- The events of a play. -/
def wtrace {I X : Set FnName} (s : List (Move (nsig I) (nsig X))) : List WEv := s.map wev

/-- The host's view of an event list: the import answers. -/
def hostView (t : List WEv) : List WEv := t.filter WEv.isImp

/-- The client's view of an event list: the export calls and returns. -/
def expView (t : List WEv) : List WEv := t.filter WEv.isExp

/-! ## Assume–guarantee sentences -/

/-- **Assume–guarantee**: every play whose events satisfy `A` satisfies `G`. -/
def ag {I X : Set FnName} (A G : List WEv → Prop) : GSen (nsig I) (nsig X) :=
  ⟨fun σ => ∀ s ∈ σ, A (wtrace s) → G (wtrace s)⟩

/-- A guarantee with no assumption: it holds for every host. -/
def guar {I X : Set FnName} (G : List WEv → Prop) : GSen (nsig I) (nsig X) := ag (fun _ => True) G

/-- The protocol form: the theory `T` on the host's view of the imports, the guarantee `G` on
all events. -/
def agP {I X : Set FnName} {S S' : Type} (T : Protocol S WEv) (G : Protocol S' WEv) :
    GSen (nsig I) (nsig X) :=
  ag (fun t => T.Accepts (hostView t)) G.Accepts

end Silmaril.Wasi
