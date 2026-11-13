module

public import Silmaril.Wasm.Component.IR.Defs

/-!
# The game semantics of components

`Comp.den C c : Strategy c.imports.sig (sigN c.exports.length)` is the
strategy of a component: it implements the exports by calling the imports. It
is `Comp.denU C c : Strategy sigU sigU` seen at the interface sizes
(`atSizes`); `denU` is defined compositionally from the `Silmaril.Games`
combinators:

* the environment starts as the forwarding of the imports (`maskH`: copycat
  on the imports, calls out of range trap);
* each node extends the environment (`ext e D N`): the instance `N` runs on
  top of the current environment `D`, side by side with the forwarding of the
  old functions (`Strategy.pair` with copycat); instantiation and linking are
  `Strategy.comp`;
* the wiring of a node's imports is the handler `implsH` of its `Impl`s,
  composed below the instance (`Strategy.ofHandler`, `Strategy.comp`); the
  canonical-ABI adapters are part of these handlers;
* a nested component instance is the denotation of the nested component,
  below its wiring; a core instance is `C.sem m`;
* the exports are the handler of the export `Impl`s on top of the final
  environment.

## Parametricity in the core semantics

Core modules enter only through `C : CoreSem M`, an arbitrary strategy for
each module over its flat import and export signatures. Every definition and
theorem of the component IR is stated for an arbitrary `C`: nothing depends on
how core modules compute. In particular, any operational core semantics given
as a reduction or a transition system (`Strategy.ofReduction`,
`Strategy.ofLTS`, for instance silmaril's core interpreter) can be plugged
in. Results about specific transformations of core modules (such as merging
two core modules) are stated relative to explicit hypotheses on `C`.

State persists in a core instance from one call to the next because `C.sem m`
is an arbitrary strategy (not a handler). Start functions and
instantiation-time effects are not modelled: an instance does nothing until
it is called.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open Silmaril.Games

variable {M : Type} [CoreModule M]

/-- A semantics of core modules: a strategy for each module, over its flat
import and export signatures. -/
structure CoreSem (M : Type) [CoreModule M] where
  /-- The strategy of a core module. -/
  sem : (m : M) → Strategy (CoreIface.sig (CoreModule.imports m))
    (CoreIface.sig (CoreModule.exports m))

/-- A core instance of `m` with the wiring `args`, as a strategy over `sigU`. -/
def coreNode (C : CoreSem M) (e : Nat) (m : M) (args : List Impl) : Strategy sigU sigU :=
  (Strategy.ofHandler (implsN e args (CoreModule.imports m).length)).comp
    ((C.sem m).comp (Strategy.ofHandler (widenH (CoreModule.exports m).length)))

/-- The handler of the exports. -/
abbrev exportsH (e : Nat) (xs : List Export) : Handler sigU sigU :=
  implsH e (xs.map Export.impl)

mutual
/-- The strategy of a component, over `sigU`. -/
def Comp.denU (C : CoreSem M) : Comp M → Strategy sigU sigU
  | .mk I ns xs =>
    (denNodes C I.length ns (Strategy.ofHandler (maskH I.length))).comp
      (Strategy.ofHandler (exportsH (envAfter I.length ns) xs))

/-- Extend the environment `D` (of `e` functions) by the nodes `ns`. -/
def denNodes (C : CoreSem M) {X : Sig.{0}} : Nat → List (Node M) → Strategy X sigU →
    Strategy X sigU
  | _, [], D => D
  | e, n :: ns, D => denNodes C (e + n.width) ns (ext e D (Node.den C e n))

/-- The strategy of a node, over an environment of `e` functions. -/
def Node.den (C : CoreSem M) : Nat → Node M → Strategy sigU sigU
  | e, .core m args => coreNode C e m args
  | e, .inst c args => (Strategy.ofHandler (implsH e args)).comp (Comp.denU C c)
end

/-- **The strategy of a component**, at its interface signatures: it
implements the exports by calling the imports. -/
def Comp.den (C : CoreSem M) (c : Comp M) :
    Strategy c.imports.sig (sigN c.exports.length) :=
  atSizes _ _ (c.denU C)

/-- The strategy of a flat component, over `sigU`. -/
def Linked.denU (C : CoreSem M) (l : Linked M) : Strategy sigU sigU :=
  (go l.imports.length l.nodes (Strategy.ofHandler (maskH l.imports.length))).comp
    (Strategy.ofHandler (exportsH (linkedEnv l.imports.length l.nodes) l.exports))
where
  /-- Extend the environment by core instances. -/
  go {X : Sig.{0}} : Nat → List (M × List Impl) → Strategy X sigU → Strategy X sigU
    | _, [], D => D
    | e, n :: ns, D =>
      go (e + (CoreModule.exports n.1).length) ns (ext e D (coreNode C e n.1 n.2))

/-- The strategy of a program: the component, restricted to the observed
exports. -/
def Program.denU (C : CoreSem M) (p : Program M) : Strategy sigU sigU :=
  match p.observe with
  | none => p.comp.denU C
  | some obs => (p.comp.denU C).comp (Strategy.ofHandler (selectH obs))

end Silmaril.Wasm.Component
